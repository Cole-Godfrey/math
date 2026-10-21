"""validate extracted expressions, dependency closure, and foundation policy."""

from __future__ import annotations

import hashlib
import json
from collections import defaultdict, deque
from collections.abc import Sequence
from typing import Any


class RepositoryError(ValueError):
    """a declaration or artifact violates the repository's verification policy."""


KINDS = {
    "axiom", "definition", "theorem", "opaque", "quotient_primitive",
    "inductive", "constructor", "recursor",
}
VALUE_KINDS = {"definition", "theorem", "opaque"}
BINDERS = {"explicit", "implicit", "strict_implicit", "instance_implicit"}


def _json_default(value):
    if isinstance(value, PackedHexDigests):
        return list(value)
    raise TypeError(f"object of type {type(value).__name__} is not json serializable")


def canonical(value: Any) -> bytes:
    """encode stable json for content identifiers."""
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"), default=_json_default).encode()


def digest(value: Any) -> str:
    return hashlib.sha256(canonical(value)).hexdigest()


def canonical_chunks(value: Any, chunk_size: int = 64 * 1024):
    """stream canonical json while encoding individual records with the json encoder."""
    def parts(item, depth):
        if depth and isinstance(item, dict) and all(isinstance(key, str) for key in item):
            yield b"{"
            for index, key in enumerate(sorted(item)):
                if index:
                    yield b","
                yield canonical(key) + b":"
                yield from parts(item[key], depth - 1)
            yield b"}"
        elif depth and isinstance(item, (list, tuple, PackedHexDigests)):
            yield b"["
            for index, child in enumerate(item):
                if index:
                    yield b","
                yield from parts(child, depth - 1)
            yield b"]"
        else:
            yield canonical(item)

    require(chunk_size > 0, "invalid json chunk size")
    buffered, length = [], 0
    for part in parts(value, 2):
        buffered.append(part)
        length += len(part)
        if length >= chunk_size:
            yield b"".join(buffered)
            buffered, length = [], 0
    if buffered:
        yield b"".join(buffered)


def stream_digest(value: Any) -> str:
    """hash complete artifacts without allocating their serialized form."""
    result = hashlib.sha256()
    for chunk in canonical_chunks(value):
        result.update(chunk)
    return result.hexdigest()


def registered_modules(policy: dict) -> dict[str, dict]:
    libraries = policy.get("libraries", {})
    require(isinstance(libraries, dict), "invalid library registry")
    result = {}
    for package, library in libraries.items():
        require(isinstance(library, dict), f"{package}: invalid library registration")
        require(isinstance(library.get("repository"), str), f"{package}: missing repository")
        revision = library.get("revision")
        require(isinstance(revision, str) and len(revision) == 40
                and all(c in "0123456789abcdef" for c in revision),
                f"{package}: library revision must be an exact commit")
        require(bool(library.get("license")) and bool(library.get("license_file")),
                f"{package}: missing license attribution")
        bibliography = library.get("bibliography")
        if bibliography is not None:
            require(isinstance(bibliography, str) and bool(bibliography)
                    and not bibliography.startswith("/") and "\\" not in bibliography
                    and ".." not in bibliography.split("/"), f"{package}: invalid bibliography path")
        modules = library.get("modules")
        require(isinstance(modules, dict) and bool(modules), f"{package}: no registered modules")
        for name, module in modules.items():
            require(isinstance(name, str) and all(part and "/" not in part and "\\" not in part
                                                for part in name.split(".")), "invalid library module")
            require(not (name == "Math" or name.startswith("Math.")), "reserved project module")
            require(name not in result, f"duplicate library module: {name}")
            require(isinstance(module, dict), f"{name}: invalid module policy")
            result[name] = module
    return result


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RepositoryError(message)


def string_list(value: Any, context: str) -> set[str]:
    require(isinstance(value, list), f"{context}: expected a list")
    require(all(isinstance(x, str) and x for x in value), f"{context}: expected names")
    require(len(value) == len(set(value)), f"{context}: duplicate names")
    return set(value)


def subject_policy(policy: dict, modules: set[str]) -> dict:
    subjects = policy.get("subjects", {})
    require(isinstance(subjects, dict), "invalid subject hierarchy")
    covered = set()
    for name, subject in subjects.items():
        require(isinstance(name, str) and bool(name) and isinstance(subject, dict), "invalid subject")
        require(isinstance(subject.get("title"), str) and bool(subject["title"]), f"{name}: missing subject title")
        require("parent" in subject, f"{name}: missing parent subject")
        parent = subject.get("parent")
        require(parent is None or isinstance(parent, str) and parent in subjects, f"{name}: unknown parent subject")
        selected = string_list(subject.get("modules"), f"{name}: subject modules")
        require(selected <= modules, f"{name}: unknown subject module")
        covered |= selected
        ancestors = {name}
        while parent is not None:
            require(parent not in ancestors, "cyclic subject hierarchy")
            ancestors.add(parent)
            require(isinstance(subjects[parent], dict), "invalid parent subject")
            parent = subjects[parent].get("parent")
            require(parent is None or isinstance(parent, str) and parent in subjects, "unknown parent subject")
    if subjects:
        require(covered == modules, "selected modules are missing from the subject hierarchy")
    return subjects


def selected_module_roots(catalog: dict) -> dict[str, set[str]]:
    """group roots by every selecting module while retaining canonical provenance."""
    roots = set(catalog["roots"])
    memberships = catalog.get("module_declarations_by_module")
    if memberships is not None:
        return {module: roots & set(names) for module, names in memberships.items()}
    result: dict[str, set[str]] = defaultdict(set)
    for node in catalog["declarations"]:
        if node["name"] in roots:
            result[node["module"]].add(node["name"])
    return dict(result)


def natural(value: Any, context: str) -> None:
    require(type(value) is int and value >= 0, f"{context}: expected a natural number")


def level_parameters(level: Any) -> set[str]:
    require(isinstance(level, dict), "invalid universe expression")
    tag = level.get("tag")
    if tag == "zero":
        return set()
    if tag == "param":
        require(isinstance(level.get("name"), str) and bool(level["name"]), "invalid universe parameter")
        return {level["name"]}
    if tag == "succ":
        return level_parameters(level.get("of"))
    if tag in {"max", "imax"}:
        return level_parameters(level.get("left")) | level_parameters(level.get("right"))
    raise RepositoryError(f"invalid or unresolved universe: {tag}")


CHILD_FIELDS = {
    "app": ("function", "argument"), "lam": ("type", "body"), "forall": ("type", "body"),
    "let": ("type", "value", "body"), "proj": ("expression",),
}


class PackedHexDigests(Sequence):
    """retain sha256 values as bytes while exposing their original hexadecimal strings."""

    def __init__(self):
        self.data = bytearray()

    def append(self, value):
        raw = bytes.fromhex(value)
        require(len(raw) == 32 and raw.hex() == value, "invalid expression digest")
        self.data.extend(raw)

    def __len__(self):
        return len(self.data) // 32

    def __getitem__(self, index):
        if isinstance(index, slice):
            return [self[i] for i in range(*index.indices(len(self)))]
        if index < 0:
            index += len(self)
        if not 0 <= index < len(self):
            raise IndexError(index)
        return self.data[index * 32:(index + 1) * 32].hex()

    def __iter__(self):
        for offset in range(0, len(self.data), 32):
            yield self.data[offset:offset + 32].hex()

    def __eq__(self, other):
        if not isinstance(other, (list, PackedHexDigests)):
            return NotImplemented
        return len(self) == len(other) and all(a == b for a, b in zip(self, other))


class ExpressionPool:
    """audit a shared term graph, including binder scope at each declaration root."""

    def __init__(self, records: Any):
        require(isinstance(records, list), "missing shared expressions")
        self.records = records
        self.loose: list[int] = []
        self.parameters: list[frozenset[str]] = []
        universe_sets: dict[frozenset[str], frozenset[str]] = {}
        self.hashes = PackedHexDigests()
        self.used = bytearray(len(records))
        self.cache: dict[int, set[str]] = {}
        for index, node in enumerate(records):
            require(isinstance(node, dict), "invalid expression")
            tag = node.get("tag")
            fields = CHILD_FIELDS.get(tag, ())
            children = [node.get(field) for field in fields]
            require(all(type(child) is int and 0 <= child < index for child in children),
                    "expression references must point to earlier nodes")
            parameters = set().union(*(self.parameters[child] for child in children))
            loose = max((self.loose[child] for child in children), default=0)
            if tag == "bvar":
                natural(node.get("index"), "bound variable")
                loose = node["index"] + 1
            elif tag == "sort":
                parameters |= level_parameters(node.get("level"))
            elif tag == "const":
                require(isinstance(node.get("name"), str) and bool(node["name"]), "invalid constant")
                require(isinstance(node.get("levels"), list), "missing universe arguments")
                for level in node["levels"]:
                    parameters |= level_parameters(level)
            elif tag in {"lam", "forall", "let"}:
                require(isinstance(node.get("name"), str), "invalid binder name")
                if tag == "let":
                    require(type(node.get("nondependent")) is bool, "invalid let annotation")
                    loose = max(self.loose[children[0]], self.loose[children[1]],
                                self.loose[children[2]] - 1)
                else:
                    require(node.get("binder") in BINDERS, "invalid binder")
                    loose = max(self.loose[children[0]], self.loose[children[1]] - 1)
            elif tag == "proj":
                require(isinstance(node.get("name"), str) and bool(node["name"]), "invalid projection")
                natural(node.get("index"), "projection")
            elif tag == "nat":
                natural(node.get("value"), "literal")
            elif tag == "string":
                require(isinstance(node.get("value"), str), "invalid string literal")
            elif tag != "app":
                raise RepositoryError(f"invalid or unresolved expression: {tag}")
            self.loose.append(loose)
            frozen = frozenset(parameters)
            self.parameters.append(universe_sets.setdefault(frozen, frozen))
            self.hashes.append(digest({**node, **{field: self.hashes[child]
                                                 for field, child in zip(fields, children)}}))

    def references(self, reference: Any, universes: set[str]) -> set[str]:
        require(type(reference) is int and 0 <= reference < len(self.records), "invalid expression reference")
        require(self.loose[reference] == 0, "unbound variable in declaration")
        require(self.parameters[reference] <= universes, "undeclared universe parameter")
        if reference not in self.cache:
            seen = set()
            pending = [reference]
            names = set()
            while pending:
                index = pending.pop()
                if index in seen:
                    continue
                seen.add(index)
                self.used[index] = 1
                node = self.records[index]
                if node["tag"] in {"const", "proj"}:
                    names.add(node["name"])
                pending.extend(node[field] for field in CHILD_FIELDS.get(node["tag"], ()))
            self.cache[reference] = names
        return self.cache[reference].copy()

    def declaration_hash(self, node: dict) -> str:
        record = {**node, "type": self.hashes[node["type"]],
                  "value": self.hashes[node["value"]] if node["value"] is not None else None}
        if node["kind"] == "recursor":
            record["structure"] = {**node["structure"], "rules": [
                {**rule, "rhs": self.hashes[rule["rhs"]]} for rule in node["structure"]["rules"]]}
        return digest(record)


def declaration_expressions(catalog: dict, node: dict) -> dict[str, dict]:
    pending = [node["type"]]
    if node["value"] is not None:
        pending.append(node["value"])
    if node["kind"] == "recursor":
        pending.extend(rule["rhs"] for rule in node["structure"]["rules"])
    result = {}
    while pending:
        index = pending.pop()
        if str(index) in result:
            continue
        expression = catalog["expressions"][index]
        result[str(index)] = expression
        pending.extend(expression[field] for field in CHILD_FIELDS.get(expression["tag"], ()))
    return dict(sorted(result.items(), key=lambda pair: int(pair[0])))


def expression_names(node: dict, expressions) -> set[str]:
    """collect exact logical name identities needed to interpret a term download."""
    result = {node["name"], *node["universes"], *node.get("definition_group", [])}
    structure = node.get("structure") or {}
    result.update(structure.get("mutual", []))
    result.update(structure.get("constructors", []))
    if "inductive" in structure:
        result.add(structure["inductive"])
    result.update(rule["constructor"] for rule in structure.get("rules", []))
    for expression in expressions:
        tag = expression["tag"]
        if tag in {"const", "proj"}:
            result.add(expression["name"])
        pending = [expression["level"]] if tag == "sort" else list(expression.get("levels", []))
        while pending:
            level = pending.pop()
            if level["tag"] == "param":
                result.add(level["name"])
            elif level["tag"] == "succ":
                pending.append(level["of"])
            elif level["tag"] in {"max", "imax"}:
                pending.extend([level["left"], level["right"]])
    return result


def structural_refs(node: dict, expressions: ExpressionPool) -> set[str]:
    structure = node.get("structure")
    kind = node["kind"]
    if kind not in {"inductive", "constructor", "recursor", "quotient_primitive"}:
        require(structure is None, "unexpected structural data")
        return set()
    require(isinstance(structure, dict), "missing structural data")
    if kind == "quotient_primitive":
        require(structure.get("primitive") in {"type", "constructor", "lift", "induction"},
                "unknown quotient primitive")
        return set()
    if kind == "constructor":
        name = structure.get("inductive")
        require(isinstance(name, str) and bool(name), "missing constructor parent")
        return {name}
    refs = string_list(structure.get("mutual"), "mutual inductives")
    if kind == "inductive":
        return refs | string_list(structure.get("constructors"), "constructors")
    require(isinstance(structure.get("rules"), list), "missing recursor rules")
    for rule in structure["rules"]:
        require(isinstance(rule, dict), "invalid recursor rule")
        name = rule.get("constructor")
        require(isinstance(name, str) and bool(name), "missing recursor constructor")
        refs.add(name)
        refs |= expressions.references(rule.get("rhs"), set(node["universes"]))
    return refs


def axiom_closure(nodes: dict[str, dict]) -> dict[str, set[str]]:
    """propagate axioms to a fixed point across inductive dependency cycles."""
    result = {name: ({name} if node["kind"] == "axiom" else set())
              for name, node in nodes.items()}
    parents: dict[str, set[str]] = defaultdict(set)
    for name, node in nodes.items():
        for dep in node["dependencies"]:
            parents[dep].add(name)
    pending = deque(name for name, axioms in result.items() if axioms)
    while pending:
        name = pending.popleft()
        for parent in parents[name]:
            if not result[name] <= result[parent]:
                result[parent] |= result[name]
                pending.append(parent)
    return result


def module_order(modules: dict[str, dict], project: set[str]) -> list[str]:
    """order modules by their actual Lean imports."""
    remaining = {name: set(modules[name]["imports"]) & project for name in project}
    result = []
    while remaining:
        ready = sorted(name for name, deps in remaining.items() if not deps)
        require(bool(ready), "cyclic project module imports")
        result.extend(ready)
        for name in ready:
            del remaining[name]
        for deps in remaining.values():
            deps.difference_update(ready)
    return result


def validate(raw: dict, policy: dict) -> dict:
    """audit declarations and every expression; proof typing is checked independently."""
    require(raw.get("schema_version") == 3, "unsupported export schema")
    revision = raw.get("lean_revision")
    require(isinstance(revision, str) and len(revision) == 40
            and all(c in "0123456789abcdef" for c in revision), "missing Lean source revision")
    require(policy.get("schema_version") == 1, "unsupported foundation policy")
    require(isinstance(policy.get("foundation"), dict) and bool(policy["foundation"].get("rules")),
            "missing kernel foundation rules")
    require(isinstance(policy.get("axioms"), dict), "missing axiom policy")
    require(isinstance(policy.get("modules"), dict), "missing module policy")
    for name, info in policy["axioms"].items():
        require(name not in {"sorryAx", "Lean.trustCompiler"}, f"forbidden axiom: {name}")
        require(bool(info.get("description")) and bool(info.get("reference")),
                f"undocumented axiom: {name}")
    require(isinstance(raw.get("declarations"), list), "missing declarations")
    require(isinstance(raw.get("modules"), list), "missing modules")
    nodes: dict[str, dict] = {}
    for node in raw["declarations"]:
        require(isinstance(node, dict), "invalid declaration")
        name = node.get("name")
        require(isinstance(name, str) and bool(name), "missing declaration name")
        require(name not in nodes, f"duplicate declaration: {name}")
        require(node.get("kind") in KINDS, f"{name}: unknown declaration kind")
        require(node.get("unsafe") is False, f"{name}: unsafe declaration")
        require(node.get("partial") is False, f"{name}: partial declaration in proof dependency closure")
        require(type(node.get("meta")) is bool, f"{name}: missing compiler phase annotation")
        require(isinstance(node.get("statement"), str), f"{name}: missing statement")
        group = string_list(node.get("definition_group"), f"{name}: definition group")
        require(node["kind"] in VALUE_KINDS or not group, f"{name}: unexpected definition group")
        hints = node.get("reducibility")
        if node["kind"] == "definition":
            if isinstance(hints, dict):
                require(set(hints) == {"regular"}, f"{name}: invalid reduction hints")
                natural(hints["regular"], "reduction height")
                require(hints["regular"] < 2 ** 32, f"{name}: invalid reduction height")
            else:
                require(hints in {"abbrev", "opaque"}, f"{name}: missing reduction hints")
        else:
            require(hints is None, f"{name}: unexpected reduction hints")
        nodes[name] = node
    modules: dict[str, dict] = {}
    for module in raw["modules"]:
        require(isinstance(module, dict), "invalid module")
        name = module.get("name")
        require(isinstance(name, str) and bool(name), "missing module name")
        require(name not in modules, f"duplicate module: {name}")
        require(isinstance(module.get("imports"), list), f"{name}: missing imports")
        require(all(isinstance(x, str) and x for x in module["imports"]), f"{name}: invalid imports")
        modules[name] = module
    for name, module in modules.items():
        require(set(module["imports"]) <= modules.keys(), f"{name}: unresolved module import")
    project = {name for name in modules if name == "Math" or name.startswith("Math.")}
    require(project == policy["modules"].keys(), "project modules differ from foundation policy")
    libraries = registered_modules(policy)
    require(libraries.keys() <= modules.keys(), "registered library module was not imported")
    root_policy = {**policy["modules"], **libraries}
    selected = project | libraries.keys()
    subjects = subject_policy(policy, selected)
    order = [name for name in module_order(modules, set(modules)) if name in selected]
    for name, info in root_policy.items():
        allowed = string_list(info.get("allowed_axioms"), f"{name}: allowed axioms")
        require(allowed <= policy["axioms"].keys(), f"{name}: undeclared allowed axiom")
        require(bool(info.get("title")), f"{name}: missing title")
    roots = string_list(raw.get("roots"), "roots")
    inventory = string_list(raw.get("module_declarations"), "module declarations")
    membership = raw.get("module_declarations_by_module")
    require(isinstance(membership, dict) and membership.keys() == selected,
            "missing or invalid serialized module inventories")
    selecting_modules: dict[str, set[str]] = defaultdict(set)
    for module, names in membership.items():
        for name in string_list(names, f"{module}: serialized declarations"):
            selecting_modules[name].add(module)
    require(selecting_modules.keys() == inventory, "serialized module inventory is incomplete")
    nonlogical = raw.get("nonlogical_declarations")
    require(isinstance(nonlogical, list), "missing nonlogical declaration inventory")
    nonlogical_names = set()
    for entry in nonlogical:
        require(isinstance(entry, dict) and isinstance(entry.get("name"), str), "invalid nonlogical declaration")
        name = entry["name"]
        require(name not in nonlogical_names, "duplicate nonlogical declaration")
        require(entry.get("safety") in {"partial", "unsafe"}, f"{name}: invalid nonlogical classification")
        classification = entry["safety"]
        require(entry.get("module") in modules, f"{name}: unknown nonlogical declaration module")
        require(bool(selecting_modules[name]) and selecting_modules[name] <= libraries.keys(),
                f"{name}: {classification} declarations are not allowed in project modules")
        nonlogical_names.add(name)
    require(not nonlogical_names & nodes.keys(), "nonlogical implementation occurs in proof dependency closure")
    require(inventory == roots | nonlogical_names, "declaration inventory is incomplete")
    require(roots <= nodes.keys() and roots == inventory - nonlogical_names and
            {n for n, node in nodes.items() if node.get("module") in selected} <= roots,
            "root list does not cover all project declarations")
    for name, node in nodes.items():
        if node.get("module") in selected:
            require(node["module"] in selecting_modules[name], f"{name}: missing canonical module membership")
    require(bool(roots), "empty mathematical repository")
    require(isinstance(raw.get("name_data"), dict) and bool(raw["name_data"]), "missing lossless logical names")
    records = raw.get("expressions")
    require(isinstance(records, list), "missing shared expressions")

    # reject inconsistent reported graphs before allocating term audit state.
    for name, node in nodes.items():
        try:
            require(node.get("module") in modules, "unknown declaration module")
            string_list(node.get("universes"), "universe parameters")
            value = node.get("value")
            require((value is not None) == (node["kind"] in VALUE_KINDS), "missing or unexpected body")
            references = [node.get("type")] + ([value] if value is not None else [])
            if node["kind"] == "recursor":
                structure = node.get("structure")
                require(isinstance(structure, dict), "missing structural data")
                require(isinstance(structure.get("rules"), list), "missing recursor rules")
                for rule in structure["rules"]:
                    require(isinstance(rule, dict), "invalid recursor rule")
                    references.append(rule.get("rhs"))
            for reference in references:
                require(type(reference) is int and 0 <= reference < len(records), "invalid expression reference")
            type_deps = string_list(node.get("type_dependencies"), "type_dependencies")
            value_deps = string_list(node.get("value_dependencies"), "value_dependencies")
            structural_deps = string_list(node.get("structural_dependencies"), "structural_dependencies")
            dependencies = string_list(node.get("dependencies"), "dependencies")
            require(dependencies == type_deps | value_deps | structural_deps,
                    "dependencies differ from declared expression roles")
            require(dependencies <= nodes.keys(), "unresolved dependency")
            if node["kind"] == "axiom":
                require(name in policy["axioms"], "undeclared foundational axiom")
            string_list(node.get("axioms"), "axioms")
            string_list(node.get("lean_axioms"), "cached Lean axioms")
        except RepositoryError as exc:
            raise RepositoryError(f"{name}: {exc}") from exc
    reached = set()
    pending = list(roots)
    while pending:
        name = pending.pop()
        if name not in reached:
            reached.add(name)
            pending.extend(nodes[name]["dependencies"])
    require(reached == nodes.keys(), "export contains unreachable declarations")
    closure = axiom_closure(nodes)
    for name, node in nodes.items():
        require(closure[name] == set(node["axioms"]), f"{name}: axiom closure differs from fresh Lean traversal")
        require(set(node["lean_axioms"]) <= closure[name], f"{name}: cached Lean axioms missing from dependency graph")
        if name in roots:
            for module in selecting_modules[name]:
                allowed = set(root_policy[module]["allowed_axioms"])
                require(closure[name] <= allowed, f"{name}: module axiom budget exceeded in {module}: "
                        + ", ".join(sorted(closure[name] - allowed)))

    # every accepted edge must still match the complete expression graph.
    expressions = ExpressionPool(records)
    for name, node in nodes.items():
        try:
            universes = set(node["universes"])
            type_deps = expressions.references(node["type"], universes)
            value = node["value"]
            value_deps = expressions.references(value, universes) if value is not None else set()
            structural_deps = structural_refs(node, expressions)
            for field, expected in (("type_dependencies", type_deps),
                                    ("value_dependencies", value_deps),
                                    ("structural_dependencies", structural_deps),
                                    ("dependencies", type_deps | value_deps | structural_deps)):
                require(set(node[field]) == expected, f"{field} differs from expressions")
        except RepositoryError as exc:
            raise RepositoryError(f"{name}: {exc}") from exc
    require(all(expressions.used), "export contains unreachable expressions")
    return {
        **raw,
        "foundation": policy["foundation"],
        "axiom_policy": policy["axioms"],
        "module_policy": root_policy,
        "local_modules": sorted(project),
        "library_policy": policy.get("libraries", {}),
        "subjects": subjects,
        "module_order": order,
        "expression_hashes": expressions.hashes,
        "declaration_hashes": {n: expressions.declaration_hash(node) for n, node in sorted(nodes.items())},
        "axiom_audit": {"method": "independent Lean and Python fixed points over full kernel dependencies",
                        "cached_summary_differences": sum(set(node["axioms"]) != set(node["lean_axioms"])
                                                          for node in nodes.values())},
    }


def dependency_path(nodes: dict[str, dict], start: str, target: str) -> list[str] | None:
    """find a shortest derivation path without looping through inductive blocks."""
    require(start in nodes, f"unknown declaration: {start}")
    require(target in nodes, f"unknown declaration: {target}")
    parents: dict[str, str | None] = {start: None}
    pending = deque([start])
    while pending:
        name = pending.popleft()
        if name == target:
            result = []
            cursor: str | None = name
            while cursor is not None:
                result.append(cursor)
                cursor = parents[cursor]
            return list(reversed(result))
        for dep in sorted(nodes[name]["dependencies"]):
            if dep not in parents:
                parents[dep] = name
                pending.append(dep)
    return None
