"""replay metamath source proofs and bind their exact steps to a separately checked export."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import itertools
import json
from pathlib import Path
import re


class ProofError(ValueError):
    """a source statement, scoped assumption, or proof step is invalid."""


def require(condition, message):
    if not condition:
        raise ProofError(message)


def encoded(value):
    return json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode()


def fingerprint(value):
    return hashlib.sha256(encoded(value)).hexdigest()


def pair(left, right):
    require(left != right, "a disjoint-variable pair identifies its variables")
    return tuple(sorted((left, right)))


def object_pairs(items):
    """reject ambiguous json records before interpreting their fields."""
    result = {}
    for key, value in items:
        require(key not in result, "duplicate json field: " + key)
        result[key] = value
    return result


def disjoint_pairs(items):
    require(type(items) is list, "disjoint conditions are not a list")
    result = set()
    for item in items:
        require(type(item) is list and len(item) == 2 and
                all(type(token) is str for token in item), "invalid disjoint pair")
        value = pair(*item)
        require(value not in result, "duplicate disjoint pair")
        result.add(value)
    return result


def math_tokens(fragment):
    """remove comments while retaining every source token outside them."""
    result = []
    comment = False
    for match in re.finditer(rb"\S+", fragment):
        token = match.group()
        if comment:
            require(token != b"$(", "nested comment")
            if token == b"$)":
                comment = False
        elif token == b"$(":
            comment = True
        else:
            require(token != b"$)", "unmatched comment terminator")
            result.append(token.decode("ascii"))
    require(not comment, "unterminated comment")
    return result


@dataclass(frozen=True)
class Rule:
    label: str
    kind: str
    expression: tuple[str, ...]
    ordinal: int
    hypotheses: tuple[str, ...] = ()
    disjoint: frozenset[tuple[str, str]] = frozenset()
    axioms: int = 0


@dataclass(frozen=True)
class Result:
    expression: tuple[str, ...]
    tree: str


class Auditor:
    """keep source scopes separate from the rule applications proved inside them."""

    def __init__(self):
        self.constants = set()
        self.variables = set()
        self.declared_symbols = set()
        self.declared_variables = set()
        self.floating = {}
        self.essential = []
        self.disjoint = set()
        self.scopes = []
        self.rules = {}
        self.axiom_labels = []
        self.source_counts = {}
        self.proof_count = 0
        self.raw_steps = 0
        self.dag_steps = 0

    def expression(self, tokens):
        require(tokens and tokens[0] in self.constants, "an expression has no constant typecode")
        require(all(token in self.constants or token in self.variables for token in tokens),
                "expression uses an inactive or undeclared symbol")
        return tuple(tokens)

    def frame(self, expression):
        mandatory = self.variables.intersection(expression)
        for label in self.essential:
            mandatory.update(self.variables.intersection(self.rules[label].expression))
        require(mandatory <= self.floating.keys(), "mandatory variable has no active floating hypothesis")
        hypotheses = [self.floating[variable] for variable in mandatory] + self.essential
        hypotheses.sort(key=lambda label: self.rules[label].ordinal)
        conditions = frozenset(item for item in self.disjoint if set(item) <= mandatory)
        return tuple(hypotheses), conditions, mandatory

    def apply(self, label, arguments, used):
        require(label in self.rules, "unknown, future, or circular proof reference: " + label)
        rule = self.rules[label]
        if rule.kind in {"Floating", "Essential"}:
            active = set(self.floating.values()) | set(self.essential)
            require(label in active, "proof uses an inactive hypothesis: " + label)
            require(not arguments, "a hypothesis has proof arguments")
            expression = rule.expression
        else:
            require(len(arguments) == len(rule.hypotheses), "wrong number of proof arguments")
            substitution = {}
            for hypothesis, argument in zip(rule.hypotheses, arguments):
                expected = self.rules[hypothesis]
                if expected.kind == "Floating":
                    require(argument.expression and argument.expression[0] == expected.expression[0],
                            "floating hypothesis has the wrong typecode")
                    substitution[expected.expression[1]] = argument.expression[1:]
                else:
                    require(self.substitute(expected.expression, substitution) == argument.expression,
                            "essential hypothesis does not match its substitution")
            for left, right in rule.disjoint:
                left_vars = self.variables.intersection(substitution[left])
                right_vars = self.variables.intersection(substitution[right])
                for x in left_vars:
                    for y in right_vars:
                        require(pair(x, y) in self.disjoint, "missing active disjoint-variable restriction")
            expression = self.substitute(rule.expression, substitution)
            used.add(label)
        expression_digest = fingerprint(expression)
        return Result(expression, fingerprint([label, [argument.tree for argument in arguments], expression_digest]))

    @staticmethod
    def substitute(expression, substitution):
        return tuple(itertools.chain.from_iterable(substitution.get(token, (token,)) for token in expression))

    def source_proof(self, proof, hypotheses):
        stack = []
        used = set()
        steps = 0

        def invoke(label):
            nonlocal steps
            require(label in self.rules, "unknown, forward, or circular source proof reference: " + label)
            rule = self.rules[label]
            count = len(rule.hypotheses)
            require(count <= len(stack), "proof stack underflow")
            arguments = stack[-count:] if count else []
            if count:
                del stack[-count:]
            stack.append(self.apply(label, arguments, used))
            steps += 1

        require(proof, "proof is empty")
        if proof[0] == "(":
            require(")" in proof, "compressed proof has no label-list terminator")
            boundary = proof.index(")")
            labels = list(hypotheses) + proof[1:boundary]
            for label in labels:
                require(label in self.rules, "unknown compressed-proof label: " + label)
                rule = self.rules[label]
                if rule.kind in {"Floating", "Essential"}:
                    require(label in set(self.floating.values()) | set(self.essential),
                            "inactive compressed-proof hypothesis")
            saved = []
            accumulator = 0
            can_save = False
            for token in proof[boundary + 1:]:
                for character in token:
                    if "U" <= character <= "Y":
                        accumulator = 5 * accumulator + ord(character) - ord("U") + 1
                        can_save = False
                    elif "A" <= character <= "T":
                        number = 20 * accumulator + ord(character) - ord("A") + 1
                        accumulator = 0
                        if number <= len(labels):
                            invoke(labels[number - 1])
                        else:
                            index = number - len(labels) - 1
                            require(index < len(saved), "forward or missing saved proof step")
                            stack.append(saved[index])
                        can_save = True
                    elif character == "Z":
                        require(accumulator == 0 and stack and can_save, "invalid saved proof step")
                        saved.append(stack[-1])
                        can_save = False
                    else:
                        raise ProofError("invalid or incomplete compressed proof character")
            require(accumulator == 0, "unfinished compressed proof number")
        else:
            for label in proof:
                require(":" not in label and "=" not in label,
                        "packed or explicit proof requires its own reviewed parser")
                invoke(label)
        require(len(stack) == 1, "proof does not end with exactly one stack entry")
        return stack[0], used, steps

    def exported_proof(self, dag, proof, hypotheses):
        require(type(dag) is dict and set(dag) == {"root", "nodes"} and
                type(dag["nodes"]) is list, "missing or invalid proof dag")
        results = []
        references = []
        for index, node in enumerate(dag["nodes"]):
            require(type(node) is dict and set(node) == {"reference", "arguments", "expression_digest"},
                    "invalid proof-node fields")
            require(type(node["reference"]) is str, "proof-node reference is not a label")
            require(type(node["arguments"]) is list and all(type(child) is int and 0 <= child < index
                    for child in node["arguments"]), "forward or cyclic proof-node reference")
            used = set()
            result = self.apply(node["reference"], [results[child] for child in node["arguments"]], used)
            require(fingerprint(result.expression) == node["expression_digest"], "proof expression digest differs")
            results.append(result)
            references.append(used)
        root = dag.get("root")
        require(type(root) is int and 0 <= root < len(results), "invalid qed proof node")
        pending, seen, used = [root], set(), set()
        while pending:
            index = pending.pop()
            if index not in seen:
                seen.add(index)
                used.update(references[index])
                pending.extend(dag["nodes"][index]["arguments"])
        prepared = []
        if proof[0] == "(":
            prepared = list(hypotheses) + [label for label in proof[1:proof.index(")")]
                if self.rules[label].kind in {"Floating", "Essential"}]
        require(len(prepared) <= len(results), "proof dag omits prepared hypotheses")
        for index, label in enumerate(prepared):
            require(dag["nodes"][index]["reference"] == label and not dag["nodes"][index]["arguments"],
                    "prepared proof hypothesis differs from source")
        require(set(range(len(results))) - seen <= set(range(len(prepared))),
                "proof dag contains unused derivation nodes")
        return results[root], used

    def statement(self, row, fragment, bind_export=True):
        tokens = math_tokens(fragment)
        kind = row["kind"]
        label = row["label"]
        self.source_counts[kind] = self.source_counts.get(kind, 0) + 1
        if not tokens:
            require(label is None and row["frame"] is None and row["proof_dag"] is None,
                    "comment or end-of-file entry has logical data")
            require(not row["expression"] and not row["proof"], "comment has math tokens")
            require(kind == "Eof" or "Comment" in kind, "logical statement has no tokens")
            return None
        short = {"$c": "Constant", "$v": "Variable", "$d": "Disjoint",
                 "${": "OpenGroup", "$}": "CloseGroup"}
        if tokens[0] in short:
            require(kind == short[tokens[0]] and label is None, "source statement kind differs")
            require(row["frame"] is None and row["proof_dag"] is None and not row["proof"],
                    "nonassertion contains proof data")
            if tokens[0] in {"${", "$}"}:
                require(len(tokens) == 1 and not row["expression"], "scope marker contains math")
                if tokens[0] == "${":
                    self.scopes.append((self.variables.copy(), self.floating.copy(),
                                        self.essential.copy(), self.disjoint.copy()))
                else:
                    require(self.scopes, "closing a scope which was not opened")
                    self.variables, self.floating, self.essential, self.disjoint = self.scopes.pop()
                return None
            require(tokens[-1] == "$." and row["expression"] == tokens[1:-1], "source symbols differ")
            symbols = tokens[1:-1]
            require(symbols and len(set(symbols)) == len(symbols), "empty or duplicate symbol declaration")
            if kind == "Constant":
                require(not self.scopes and not set(symbols) & (self.constants | self.declared_variables),
                        "invalid constant declaration")
                self.constants.update(symbols)
            elif kind == "Variable":
                require(not set(symbols) & (self.constants | self.variables), "invalid variable declaration")
                self.variables.update(symbols)
                self.declared_variables.update(symbols)
            else:
                require(len(symbols) >= 2 and set(symbols) <= self.variables, "invalid disjoint-variable statement")
                self.disjoint.update(pair(a, b) for a, b in itertools.combinations(symbols, 2))
            if kind in {"Constant", "Variable"}:
                require(not set(symbols).intersection(self.rules), "math symbol duplicates a label")
                self.declared_symbols.update(symbols)
            return None
        require(len(tokens) >= 4 and tokens[1] in {"$f", "$e", "$a", "$p"}, "unrecognized source statement")
        expected_kind = {"$f": "Floating", "$e": "Essential", "$a": "Axiom", "$p": "Provable"}[tokens[1]]
        require(kind == expected_kind and label == tokens[0] and label not in self.rules,
                "source label or kind differs, or label is reused")
        require(re.fullmatch(r"[A-Za-z0-9_.-]+", label) is not None and label not in self.declared_symbols,
                "invalid label or label duplicates a math symbol")
        require(tokens[-1] == "$." and "$[" not in tokens, "invalid statement ending or unarchived include")
        boundary = tokens.index("$=") if kind == "Provable" else len(tokens) - 1
        expression = self.expression(tokens[2:boundary])
        proof = tokens[boundary + 1:-1] if kind == "Provable" else []
        require(list(expression) == row["expression"] and proof == row["proof"], "exported source tokens differ")
        ordinal = row["ordinal"]
        if kind == "Floating":
            require(len(expression) == 2 and expression[1] in self.variables and expression[1] not in self.floating,
                    "invalid or duplicate active floating hypothesis")
            self.floating[expression[1]] = label
            self.rules[label] = Rule(label, kind, expression, ordinal)
            require(row["frame"] is None and row["proof_dag"] is None, "hypothesis contains proof data")
            return None
        if kind == "Essential":
            require(self.variables.intersection(expression) <= self.floating.keys(), "untyped essential variable")
            self.essential.append(label)
            self.rules[label] = Rule(label, kind, expression, ordinal)
            require(row["frame"] is None and row["proof_dag"] is None, "hypothesis contains proof data")
            return None
        hypotheses, disjoint, mandatory = self.frame(expression)
        if bind_export:
            frame = row["frame"]
            require(type(frame) is dict and set(frame) == {"hypotheses", "mandatory_variables", "variables",
                    "mandatory_disjoint", "proof_disjoint"}, "invalid assertion frame")
            for field in ["hypotheses", "mandatory_variables", "variables"]:
                require(type(frame[field]) is list and all(type(item) is str for item in frame[field]),
                        "invalid frame label or variable list")
            require(frame["hypotheses"] == list(hypotheses), "ordered mandatory hypotheses differ")
            require(len(set(frame["mandatory_variables"])) == len(frame["mandatory_variables"]) and
                    set(frame["mandatory_variables"]) == mandatory, "mandatory variables differ")
            require(disjoint_pairs(frame["mandatory_disjoint"]) == disjoint,
                    "mandatory disjoint conditions differ")
            require(disjoint_pairs(frame["proof_disjoint"]) == self.disjoint,
                    "active proof disjoint conditions differ")
            all_frame_variables = mandatory | set(itertools.chain.from_iterable(self.disjoint))
            require(len(set(frame["variables"])) == len(frame["variables"]) and
                    set(frame["variables"]) == all_frame_variables, "proof variables differ")
        if kind == "Axiom":
            require(row["proof_dag"] is None, "axiom has a fabricated proof")
            bits = 1 << len(self.axiom_labels)
            self.axiom_labels.append(label)
            dependencies = set()
            proof_digest = None
        else:
            raw, dependencies, raw_steps = self.source_proof(proof, hypotheses)
            require(raw.expression == expression, "qed expression differs from the theorem")
            if bind_export:
                exported, exported_dependencies = self.exported_proof(row["proof_dag"], proof, hypotheses)
                require(exported.expression == expression, "exported qed expression differs from the theorem")
                require(raw.tree == exported.tree, "source proof and exported proof dag have different derivations")
                require(dependencies == exported_dependencies, "source and exported proof dependencies differ")
            bits = 0
            for dependency in dependencies:
                bits |= self.rules[dependency].axioms
            proof_digest = raw.tree
            self.proof_count += 1
            self.raw_steps += raw_steps
            if bind_export:
                self.dag_steps += len(row["proof_dag"]["nodes"])
        self.rules[label] = Rule(label, kind, expression, ordinal, hypotheses, disjoint, bits)
        return {"label": label, "kind": kind, "expression": expression, "hypotheses": hypotheses,
                "disjoint": sorted(disjoint), "dependencies": sorted(dependencies),
                "axiom_bits": hex(bits), "proof_digest": proof_digest}


def verify_source(source):
    """parse and verify a complete source independently of the rust export."""
    if isinstance(source, str):
        source = source.encode()
    auditor = Auditor()
    previous = 0
    statement = []
    comment = False
    count = 0
    directives = {"$c": "Constant", "$v": "Variable", "$d": "Disjoint",
                  "${": "OpenGroup", "$}": "CloseGroup", "$f": "Floating",
                  "$e": "Essential", "$a": "Axiom", "$p": "Provable"}
    for match in re.finditer(rb"\S+", source):
        token = match.group()
        if comment:
            require(token != b"$(", "nested comment")
            if token == b"$)":
                comment = False
            continue
        if token == b"$(":
            comment = True
            continue
        require(token != b"$)", "unmatched comment terminator")
        statement.append(token.decode("ascii"))
        if token not in {b"$.", b"${", b"$}"}:
            continue
        require(token == b"$." or len(statement) == 1, "scope marker inside a statement")
        label = None if statement[0].startswith("$") else statement[0]
        directive = statement[0 if label is None else 1]
        require(directive in directives, "unsupported or invalid source directive")
        kind = directives[directive]
        offset = 1 if label is None else 2
        boundary = statement.index("$=") if kind == "Provable" else len(statement) - 1
        expression = statement[offset:boundary] if kind not in {"OpenGroup", "CloseGroup"} else []
        proof = statement[boundary + 1:-1] if kind == "Provable" else []
        row = {"kind": kind, "ordinal": count, "label": label, "expression": expression,
               "proof": proof, "frame": None, "proof_dag": None}
        auditor.statement(row, source[previous:match.end()], bind_export=False)
        count += 1
        previous = match.end()
        statement = []
    require(not statement and not comment and not auditor.scopes, "unfinished statement, comment, or scope")
    return auditor


def audit(source_path, export_path, writer=None):
    """validate all source bytes, proof nodes, rule dependencies, and axiom closures."""
    source = Path(source_path).read_bytes()
    source_digest = hashlib.sha256(source).hexdigest()
    auditor = Auditor()
    previous = 0
    count = assertions = 0
    current_line = 1
    summary = None
    with Path(export_path).open() as stream:
        header = json.loads(next(stream), object_pairs_hook=object_pairs)
        require(type(header) is dict and set(header) == {"record", "schema_version", "proof_system", "database",
                "source_sha256", "source_bytes", "retained_warnings"}, "invalid export header fields")
        require(header["record"] == "header" and header["proof_system"] == "metamath" and
                type(header["schema_version"]) is int and header["schema_version"] == 1, "invalid export header")
        require(header["database"] == Path(source_path).name and type(header["source_bytes"]) is int,
                "export database identity differs")
        require(header["source_sha256"] == source_digest and header["source_bytes"] == len(source),
                "export is not bound to the original database bytes")
        warnings = []
        if source_digest == "664669725ff42cb35a4b4c10823b5a7664d8f404eab94385de0ace79e6aa501e":
            warnings = [{"kind": "comment_marker_not_start", "start": 22496, "end": 22498}]
        require(header["retained_warnings"] == warnings, "retained diagnostic differs from reviewed source")
        for line in stream:
            row = json.loads(line, object_pairs_hook=object_pairs)
            require(type(row) is dict, "export record is not an object")
            require(summary is None, "records follow the final summary")
            if row["record"] == "summary":
                require(set(row) == {"record", "source_sha256", "counts", "proof_nodes", "assertions"},
                        "invalid summary fields")
                require(type(row["assertions"]) is int and type(row["proof_nodes"]) is int and
                        type(row["counts"]) is dict and all(type(value) is int for value in row["counts"].values()),
                        "invalid summary counts")
                summary = row
                continue
            require(set(row) == {"record", "ordinal", "kind", "label", "expression", "proof", "frame",
                                "proof_dag", "source"}, "invalid statement fields")
            require(row["record"] == "statement" and type(row["ordinal"]) is int and row["ordinal"] == count,
                    "missing, duplicate, or reordered source statement")
            start, end = row["source"]["start"], row["source"]["end"]
            require(type(row["source"]) is dict and set(row["source"]) == {"start", "end", "line", "end_line"},
                    "invalid source span fields")
            require(type(start) is int and type(end) is int and start == previous and start <= end <= len(source),
                    "source spans omit, duplicate, or reorder bytes")
            end_line = current_line + source[start:end].count(b"\n")
            require(type(row["source"]["line"]) is int and type(row["source"]["end_line"]) is int and
                    row["source"]["line"] == current_line and row["source"]["end_line"] == end_line,
                    "source line references differ from archived bytes")
            current_line = end_line
            previous = end
            checked = auditor.statement(row, source[start:end])
            if checked is not None:
                assertions += 1
                if writer is not None:
                    writer(checked)
            count += 1
    require(previous == len(source) and not auditor.scopes and summary is not None, "source coverage or scopes incomplete")
    require(summary["source_sha256"] == source_digest and summary["counts"] == auditor.source_counts and
            summary["proof_nodes"] == auditor.dag_steps and summary["assertions"] == assertions,
            "export summary disagrees with independently replayed statements")
    return {"state": "passed", "source_sha256": source_digest, "statements": count,
            "assertions": assertions, "theorems": auditor.proof_count, "axiom_rules": len(auditor.axiom_labels),
            "source_steps": auditor.raw_steps, "exported_nodes": auditor.dag_steps,
            "axiom_labels": auditor.axiom_labels}
