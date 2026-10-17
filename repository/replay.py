"""bind indexed logical declarations to the independently checked proof export."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re

from .core import RepositoryError, canonical, natural, require


def fingerprint(tag: str, *values) -> bytes:
    return hashlib.sha256(canonical([tag, *values])).digest()


ANONYMOUS = fingerprint("name")
ZERO = fingerprint("level.zero")


class Hashes:
    """retain dense fingerprints in packed bytes and accept sparse external ids."""

    def __init__(self, initial=()):
        self.data = bytearray().join(initial)
        self.sparse = {}

    def __len__(self):
        return len(self.data) // 32 + len(self.sparse)

    def get(self, index):
        natural(index, "replay reference")
        if index < len(self.data) // 32:
            return bytes(self.data[index * 32:(index + 1) * 32])
        require(index in self.sparse, f"undefined replay reference: {index}")
        return self.sparse[index]

    def add(self, index, value):
        natural(index, "replay index")
        count = len(self.data) // 32
        require(index >= count and index not in self.sparse, f"duplicate replay index: {index}")
        if index == count:
            self.data.extend(value)
            while len(self.data) // 32 in self.sparse:
                self.data.extend(self.sparse.pop(len(self.data) // 32))
        else:
            self.sparse[index] = value


def name_hashes(data: dict) -> dict[str, bytes]:
    require(isinstance(data, dict), "missing lossless logical names")
    result, seen = {}, set()
    for text, parts in data.items():
        require(isinstance(text, str) and isinstance(parts, list), "invalid logical name")
        value = ANONYMOUS
        for part in parts:
            require(isinstance(part, dict) and len(part) == 1, "invalid logical name component")
            if "str" in part:
                require(isinstance(part["str"], str), "invalid string name component")
                value = fingerprint("name.str", value.hex(), part["str"])
            elif "num" in part:
                natural(part["num"], "numeric name component")
                value = fingerprint("name.num", value.hex(), part["num"])
            else:
                raise RepositoryError("unknown logical name component")
        require(value not in seen, "duplicate logical name identity")
        seen.add(value)
        result[text] = value
    return result


class IndexedTerms:
    """fingerprint logical terms while ignoring binder labels and optimization hints."""

    def __init__(self, catalog):
        self.names = name_hashes(catalog.get("name_data"))
        self.levels = {}
        self.expressions = Hashes()
        for index, node in enumerate(catalog["expressions"]):
            tag = node["tag"]
            child = lambda field: self.expressions.get(node[field]).hex()
            if tag == "bvar":
                value = fingerprint(tag, node["index"])
            elif tag == "sort":
                value = fingerprint(tag, self.level(node["level"]).hex())
            elif tag == "const":
                value = fingerprint(tag, self.name(node["name"]), [self.level(item).hex() for item in node["levels"]])
            elif tag == "app":
                value = fingerprint(tag, child("function"), child("argument"))
            elif tag in {"lam", "forall"}:
                value = fingerprint(tag, child("type"), child("body"))
            elif tag == "let":
                value = fingerprint(tag, child("type"), child("value"), child("body"))
            elif tag == "proj":
                value = fingerprint(tag, self.name(node["name"]), node["index"], child("expression"))
            elif tag in {"nat", "string"}:
                value = fingerprint(tag, str(node["value"]))
            else:
                raise RepositoryError(f"unsupported indexed expression: {tag}")
            self.expressions.add(index, value)

    def name(self, text):
        require(text in self.names, f"missing logical name identity: {text}")
        return self.names[text].hex()

    def level(self, root):
        pending, results = [(root, False)], []
        while pending:
            node, visited = pending.pop()
            tag = node["tag"]
            fields = {"succ": ("of",), "max": ("left", "right"), "imax": ("left", "right")}.get(tag, ())
            if fields and not visited:
                pending.append((node, True))
                pending.extend((node[field], False) for field in reversed(fields))
                continue
            if tag == "zero":
                value = ZERO
            else:
                if tag == "param":
                    key = (tag, self.name(node["name"]))
                elif fields:
                    children = tuple(item.hex() for item in results[-len(fields):])
                    del results[-len(fields):]
                    key = (tag, *children)
                else:
                    raise RepositoryError(f"unsupported indexed universe: {tag}")
                if key not in self.levels:
                    self.levels[key] = fingerprint("level." + tag, *key[1:])
                value = self.levels[key]
            results.append(value)
        require(len(results) == 1, "invalid indexed universe")
        return results[0]

    def declaration(self, node):
        expr = lambda index: self.expressions.get(index).hex()
        names = lambda values: [self.name(value) for value in values]
        structure = node["structure"]
        if structure is not None:
            structure = dict(structure)
            for key in ["mutual", "constructors"]:
                if key in structure:
                    structure[key] = names(structure[key])
            if "inductive" in structure:
                structure["inductive"] = self.name(structure["inductive"])
            if "rules" in structure:
                structure["rules"] = [{"constructor": self.name(rule["constructor"]), "fields": rule["fields"],
                                        "rhs": expr(rule["rhs"])} for rule in structure["rules"]]
        return fingerprint("declaration", node["kind"], self.name(node["name"]), names(node["universes"]),
                           expr(node["type"]), expr(node["value"]) if node["value"] is not None else None,
                           structure, names(node["definition_group"]), node["reducibility"])


def _unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate replay json field: {key}")
        result[key] = value
    return result


class ReplayTerms:
    """read checker input independently of the index's expression numbering."""

    def __init__(self, expected):
        self.expected = expected
        self.names = Hashes([ANONYMOUS])
        self.levels = Hashes([ZERO])
        self.expressions = Hashes()
        self.seen = set()
        self.matched = set()

    def name(self, index):
        return self.names.get(index).hex()

    def names_list(self, values):
        return [self.name(value) for value in values]

    def expr(self, index):
        return self.expressions.get(index).hex()

    def declaration(self, kind, node, structure=None):
        name = self.names.get(node["name"])
        require(name not in self.seen, "duplicate replay declaration")
        self.seen.add(name)
        require(node.get("isUnsafe", False) is False, "unsafe replay declaration")
        if kind == "definition":
            require(node["safety"] == "safe", "unsafe or partial replay definition")
        signature = fingerprint("declaration", kind, name.hex(), self.names_list(node["levelParams"]),
                                self.expr(node["type"]), self.expr(node["value"]) if "value" in node else None,
                                structure, self.names_list(node.get("all", [])) if kind in {"definition", "theorem", "opaque"} else [],
                                node["hints"] if kind == "definition" else None)
        if name in self.expected:
            text, expected = self.expected[name]
            require(signature == expected, f"indexed declaration differs from checked replay: {text}")
            self.matched.add(name)

    def primitive(self, row):
        if "in" in row:
            index = row["in"]
            tag = "str" if "str" in row else "num"
            require(set(row) == {"in", tag}, "invalid replay name record")
            data = row[tag]
            value = data["str"] if tag == "str" else data["i"]
            require(isinstance(value, str), "invalid replay name string") if tag == "str" else natural(value, "replay name number")
            self.names.add(index, fingerprint("name." + tag, self.name(data["pre"]), value))
        elif "il" in row:
            tags = set(row) - {"il"}
            require(len(tags) == 1, "invalid replay universe record")
            tag = next(iter(tags))
            value = row[tag]
            if tag == "param":
                children = [self.name(value)]
            elif tag == "succ":
                children = [self.levels.get(value).hex()]
            elif tag in {"max", "imax"}:
                require(isinstance(value, list) and len(value) == 2, "invalid replay universe pair")
                children = [self.levels.get(item).hex() for item in value]
            else:
                raise RepositoryError(f"unsupported replay universe: {tag}")
            self.levels.add(row["il"], fingerprint("level." + tag, *children))
        else:
            tags = set(row) - {"ie"}
            require("ie" in row and len(tags) == 1, "invalid replay expression record")
            tag = next(iter(tags))
            value = row[tag]
            if tag == "bvar":
                natural(value, "replay bound variable")
                result = fingerprint(tag, value)
            elif tag == "sort":
                result = fingerprint(tag, self.levels.get(value).hex())
            elif tag == "const":
                result = fingerprint(tag, self.name(value["name"]), [self.levels.get(item).hex() for item in value["us"]])
            elif tag == "app":
                result = fingerprint(tag, self.expr(value["fn"]), self.expr(value["arg"]))
            elif tag in {"lam", "forallE"}:
                result = fingerprint("forall" if tag == "forallE" else tag, self.expr(value["type"]), self.expr(value["body"]))
            elif tag == "letE":
                result = fingerprint("let", self.expr(value["type"]), self.expr(value["value"]), self.expr(value["body"]))
            elif tag == "proj":
                result = fingerprint(tag, self.name(value["typeName"]), value["idx"], self.expr(value["struct"]))
            elif tag == "natVal":
                require(isinstance(value, str) and value.isascii() and value.isdecimal() and
                        (value == "0" or not value.startswith("0")), "invalid replay natural literal")
                result = fingerprint("nat", value)
            elif tag == "strVal":
                require(isinstance(value, str), "invalid replay string literal")
                result = fingerprint("string", value)
            elif tag == "mdata":
                result = self.expressions.get(value["expr"])
            else:
                raise RepositoryError(f"unsupported replay expression: {tag}")
            self.expressions.add(row["ie"], result)

    def item(self, row):
        require(isinstance(row, dict), "invalid replay object")
        if any(key in row for key in ["in", "il", "ie"]):
            self.primitive(row)
            return
        require(len(row) == 1, "invalid replay declaration record")
        tag, node = next(iter(row.items()))
        kinds = {"axiom": "axiom", "def": "definition", "thm": "theorem", "opaque": "opaque"}
        if tag in kinds:
            self.declaration(kinds[tag], node)
        elif tag == "quot":
            primitive = {"type": "type", "ctor": "constructor", "lift": "lift", "ind": "induction"}
            require(node["kind"] in primitive, "invalid replay quotient kind")
            self.declaration("quotient_primitive", node, {"primitive": primitive[node["kind"]]})
        elif tag == "inductive":
            for value in node["types"]:
                self.declaration("inductive", value, {"mutual": self.names_list(value["all"]),
                    "constructors": self.names_list(value["ctors"]), "parameters": value["numParams"],
                    "indices": value["numIndices"], "nested": value["numNested"],
                    "recursive": value["isRec"], "reflexive": value["isReflexive"]})
            for value in node["ctors"]:
                self.declaration("constructor", value, {"inductive": self.name(value["induct"]),
                    "index": value["cidx"], "parameters": value["numParams"], "fields": value["numFields"]})
            for value in node["recs"]:
                self.declaration("recursor", value, {"mutual": self.names_list(value["all"]),
                    "parameters": value["numParams"], "indices": value["numIndices"],
                    "motives": value["numMotives"], "minors": value["numMinors"], "k": value["k"],
                    "rules": [{"constructor": self.name(rule["ctor"]), "fields": rule["nfields"],
                               "rhs": self.expr(rule["rhs"])} for rule in value["rules"]]})
        else:
            raise RepositoryError(f"unsupported replay declaration: {tag}")


def bind_replay(catalog: dict, path: Path) -> dict:
    """compare every indexed logical declaration with the proof checker input."""
    indexed = IndexedTerms(catalog)
    expected = {bytes.fromhex(indexed.name(node["name"])): (node["name"], indexed.declaration(node))
                for node in catalog["declarations"]}
    require(len(expected) == len(catalog["declarations"]), "duplicate indexed logical declaration")
    del indexed
    replay = ReplayTerms(expected)
    export_digest = hashlib.sha256()
    with path.open("rb") as handle:
        first = handle.readline()
        export_digest.update(first)
        try:
            metadata = json.loads(first, object_pairs_hook=_unique)["meta"]
            require(metadata["format"]["version"] == "3.1.0", "unsupported replay format")
            require(metadata["lean"]["version"] == catalog["lean_version"] and
                    metadata["lean"]["githash"] == catalog["lean_revision"], "replay toolchain differs from index")
        except (KeyError, TypeError, ValueError) as exc:
            raise RepositoryError(f"invalid replay metadata: {exc}") from exc
        for number, line in enumerate(handle, 2):
            export_digest.update(line)
            try:
                replay.item(json.loads(line, object_pairs_hook=_unique))
            except (KeyError, TypeError, ValueError, IndexError) as exc:
                raise RepositoryError(f"replay line {number}: {exc}") from exc
    missing = expected.keys() - replay.matched
    require(not missing, "checked replay omits indexed declarations: " + ", ".join(sorted(expected[name][0] for name in missing)[:5]))
    logical = hashlib.sha256()
    for name, (_, value) in sorted(expected.items()):
        logical.update(name + value)
    return {"schema_version": 1, "method": "logical term fingerprints against lean4export 3.1.0",
            "indexed_declarations": len(expected), "matched_declarations": len(replay.matched),
            "proof_declarations": len(replay.seen), "indexed_expressions": len(catalog["expressions"]),
            "proof_expressions": len(replay.expressions), "logical_digest": logical.hexdigest(),
            "proof_export_digest": export_digest.hexdigest()}


def validate_binding_receipt(metadata: dict, declarations: int, expressions: int):
    """require published proof binding to cover this artifact and checker input."""
    binding = metadata.get("proof_binding")
    require(isinstance(binding, dict) and type(binding.get("schema_version")) is int and binding["schema_version"] == 1,
            "missing or invalid proof binding")
    for field in ["indexed_declarations", "matched_declarations", "proof_declarations", "indexed_expressions", "proof_expressions"]:
        natural(binding.get(field), "proof binding count")
    require(binding["indexed_declarations"] == declarations == binding["matched_declarations"] and
            binding["indexed_expressions"] == expressions and binding["proof_declarations"] >= declarations and
            (binding["proof_expressions"] > 0 or expressions == 0),
            "proof binding coverage mismatch")
    for field in ["logical_digest", "proof_export_digest"]:
        require(isinstance(binding.get(field), str) and re.fullmatch(r"[0-9a-f]{64}", binding[field]) is not None,
                "invalid proof binding digest")
    require(binding["proof_export_digest"] == metadata.get("provenance", {}).get("proof_export_digest"),
            "proof binding export digest mismatch")
