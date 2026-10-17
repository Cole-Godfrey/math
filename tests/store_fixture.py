"""small storage fixtures; mathematical verification is covered by repository tests."""

from __future__ import annotations

import hashlib
from pathlib import Path

from repository.build import input_hashes
from repository.core import ExpressionPool, canonical, digest
from repository.store import create_store, file_digest


def fixture(root: Path):
    source = "namespace Math.Fixture\ntheorem truth : True := True.intro\ntheorem alias_truth : True := truth\ntheorem identity (P : Prop) (h : P) : P := h\nend Math.Fixture\n"
    (root / "Math").mkdir()
    (root / "Math/Fixture.lean").write_text(source)
    (root / "Math.lean").write_text("import Math.Fixture\n")
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
    (root / "lakefile.toml").write_text('name = "math"\n')
    (root / "lake-manifest.json").write_bytes(canonical({"packages": [], "packagesDir": ".lake/packages"}))
    (root / "knowledge.json").write_bytes(canonical({"libraries": {}}))
    (root / "CONTRIBUTING.md").write_text("Run make check before contributing.\n")
    expressions = [
        {"tag": "sort", "level": {"tag": "zero"}},
        {"tag": "const", "name": "True", "levels": []},
        {"tag": "const", "name": "True.intro", "levels": []},
        {"tag": "bvar", "index": 0}, {"tag": "bvar", "index": 1},
        {"tag": "forall", "name": "h", "type": 3, "body": 4, "binder": "explicit"},
        {"tag": "forall", "name": "P", "type": 0, "body": 5, "binder": "explicit"},
        {"tag": "lam", "name": "h", "type": 3, "body": 3, "binder": "explicit"},
        {"tag": "lam", "name": "P", "type": 0, "body": 7, "binder": "explicit"},
        {"tag": "const", "name": "Math.Fixture.truth", "levels": []},
    ]

    def node(name, kind, type_ref, value, types, values, structural, module="Math.Fixture", line=2):
        return {"name": name, "kind": kind, "module": module, "statement": "True" if type_ref == 1 else "P → P",
                "doc": "fixture truth" if name.endswith("truth") else None, "universes": [],
                "source": {"line": line, "end_line": line, "column": 0, "end_column": 20},
                "type": type_ref, "value": value, "proof": "True.intro" if value is not None else None,
                "structure": None, "unsafe": False, "partial": False, "meta": False,
                "definition_group": [name] if value is not None else [], "reducibility": None,
                "type_dependencies": types, "value_dependencies": values, "structural_dependencies": structural,
                "dependencies": sorted(set(types + values + structural)), "axioms": [], "lean_axioms": []}

    nodes = [node("True", "inductive", 0, None, [], [], ["True", "True.intro"], "Init.Prelude"),
             node("True.intro", "constructor", 1, None, ["True"], [], ["True"], "Init.Prelude"),
             node("Math.Fixture.truth", "theorem", 1, 2, ["True"], ["True.intro"], []),
             node("Math.Fixture.alias_truth", "theorem", 1, 9, ["True"], ["Math.Fixture.truth"], [], line=3),
             node("Math.Fixture.identity", "theorem", 6, 8, [], [], [], line=4)]
    roots = [item["name"] for item in nodes if item["module"] == "Math.Fixture"]
    proof_bytes = b"fixture artifact for storage tests\n"
    proof_digest = hashlib.sha256(proof_bytes).hexdigest()
    catalog = {
        "schema_version": 3, "lean_version": "4.35.0", "lean_revision": "0" * 40,
        "declarations": nodes, "expressions": expressions, "expression_hashes": ExpressionPool(expressions).hashes,
        "declaration_hashes": {item["name"]: digest(item) for item in nodes},
        "name_data": {item["name"]: [{"str": part} for part in item["name"].split(".")] for item in nodes},
        "roots": roots, "subjects": {"mathematics": {"title": "Mathematics", "parent": None, "modules": ["Math.Fixture"]}},
        "local_modules": ["Math", "Math.Fixture"],
        "module_policy": {"Math": {"title": "Mathematics", "allowed_axioms": []},
                          "Math.Fixture": {"title": "Fixture", "allowed_axioms": []}},
        "foundation": {"id": "fixture-foundation", "rules": ["fixture rules"], "reference": "https://example.invalid"},
        "axiom_policy": {}, "axiom_audit": {"cached_summary_differences": 0},
        "sources": {"Math.Fixture": {"package": "math", "path": "Math/Fixture.lean", "sha256": hashlib.sha256(source.encode()).hexdigest()},
                    "Init.Prelude": {"package": "lean", "path": "src/Init/Prelude.lean"}},
        "provenance": {"inputs": input_hashes(root), "dependencies": {}, "proof_export_digest": proof_digest,
                       "checkers": ["fixture kernel replay", "fixture independent checker"]},
        "proof_binding": {"schema_version": 1, "method": "fixture binding for storage tests",
                          "indexed_declarations": len(nodes), "matched_declarations": len(nodes),
                          "proof_declarations": len(nodes), "indexed_expressions": len(expressions),
                          "proof_expressions": len(expressions), "logical_digest": "0" * 64,
                          "proof_export_digest": proof_digest},
    }
    catalog["provenance"]["source_digest"] = digest(catalog["provenance"]["inputs"])
    catalog["content_digest"] = digest(catalog)
    (root / "build").mkdir()
    (root / "build/knowledge.json").write_bytes(canonical(catalog) + b"\n")
    (root / "build" / f"proofs-{proof_digest}.jsonl").write_bytes(proof_bytes)
    receipt = create_store(root / "build", catalog, {"Math.Fixture": source}, file_digest(root / "build/knowledge.json"))
    (root / "build/index.json").write_bytes(canonical(receipt))
    return catalog, receipt
