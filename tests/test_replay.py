"""check exact index binding against real kernel replay artifacts and altered terms."""

from copy import deepcopy
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from repository.build import find_lake, verify
from repository.core import CHILD_FIELDS, RepositoryError, validate
from repository.replay import Hashes, bind_replay, fingerprint, name_hashes


ROOT = Path(__file__).resolve().parents[1]


class ReplayBindingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory()
        cls.root = Path(cls.temporary.name)
        (cls.root / "Math").mkdir()
        (cls.root / "tools").mkdir()
        (cls.root / "repository").mkdir()
        for path in (ROOT / "repository").glob("*.py"):
            shutil.copyfile(path, cls.root / "repository" / path.name)
        shutil.copyfile(ROOT / "tools/Export.lean", cls.root / "tools/Export.lean")
        shutil.copyfile(ROOT / "lean-toolchain", cls.root / "lean-toolchain")
        (cls.root / "Math.lean").write_text("import Math.Binding\n")
        (cls.root / "lakefile.toml").write_text('name = "math"\n[[lean_lib]]\nname = "Math"\n')
        (cls.root / "lake-manifest.json").write_text(json.dumps({
            "version": "1.3.0", "name": "math", "packages": [], "packagesDir": ".lake/packages"}))
        (cls.root / "Math/Binding.lean").write_text('''universe u
namespace Binding
theorem truth : True := True.intro
theorem alias_truth : True := True.intro
theorem identity (P : Prop) (h : P) : P := h
def zero : Nat := 0
def message : String := "logical \\"text\\" λ"
def project {α β : Type u} (p : α × β) : α := p.1
def localValue (n : Nat) : Nat := let x := n + 1; x + x
opaque hidden (n : Nat) : Nat := n
def «a.b» : Nat := 7
def «0» : Nat := 8
inductive Tree (α : Type u) where
  | leaf : α → Tree α
  | branch : List (Tree α) → Tree α
def quotient (n : Nat) : Quot (fun a b : Nat => a = b) := Quot.mk _ n
theorem quotient_eq (a b : Nat) (h : a = b) : quotient a = quotient b := Quot.sound h
end Binding
''')
        policy = json.loads((ROOT / "knowledge.json").read_text())
        cls.policy = {key: policy[key] for key in ["schema_version", "foundation", "axioms"]}
        cls.policy["modules"] = {name: {"title": name, "allowed_axioms": list(policy["axioms"])}
                                 for name in ["Math", "Math.Binding"]}
        (cls.root / "knowledge.json").write_text(json.dumps(cls.policy))
        with patch.dict(os.environ, {"MATH_LAKE": find_lake(ROOT)}):
            cls.catalog = verify(cls.root, clean=True)
        cls.proof = cls.root / "build" / f'proofs-{cls.catalog["provenance"]["proof_export_digest"]}.jsonl'
        cls.nodes = {node["name"]: node for node in cls.catalog["declarations"]}

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def altered(self, name):
        catalog = {**self.catalog, "declarations": list(self.catalog["declarations"])}
        index = next(index for index, node in enumerate(catalog["declarations"]) if node["name"] == name)
        node = deepcopy(catalog["declarations"][index])
        catalog["declarations"][index] = node
        return catalog, node

    def test_every_indexed_declaration_is_bound_to_the_checked_export(self):
        audit = self.catalog["proof_binding"]
        self.assertEqual(audit["matched_declarations"], len(self.nodes))
        self.assertEqual(audit, bind_replay(self.catalog, self.proof))
        self.assertEqual(audit["proof_export_digest"], self.catalog["provenance"]["proof_export_digest"])
        self.assertEqual({node["kind"] for node in self.nodes.values()},
                         {"axiom", "definition", "theorem", "opaque", "inductive", "constructor", "recursor", "quotient_primitive"})

    def test_ill_typed_body_that_passes_structural_audit_is_rejected(self):
        catalog, node = self.altered("Binding.truth")
        node["value"] = self.nodes["Binding.zero"]["value"]
        node["value_dependencies"] = self.nodes["Binding.zero"]["value_dependencies"]
        node["dependencies"] = sorted(set(node["type_dependencies"] + node["value_dependencies"]))
        validate(catalog, self.policy)
        with self.assertRaisesRegex(RepositoryError, "indexed declaration differs.*Binding.truth"):
            bind_replay(catalog, self.proof)

    def test_changed_types_and_universe_arguments_are_rejected(self):
        catalog, node = self.altered("Binding.identity")
        node["type"] = self.nodes["Binding.zero"]["type"]
        with self.assertRaisesRegex(RepositoryError, "indexed declaration differs.*Binding.identity"):
            bind_replay(catalog, self.proof)
        catalog = {**self.catalog, "expressions": [dict(node) for node in self.catalog["expressions"]]}
        expression = next(node for node in catalog["expressions"] if node["tag"] == "const" and node["levels"])
        expression["levels"] = []
        validate(catalog, self.policy)
        with self.assertRaisesRegex(RepositoryError, "indexed declaration differs"):
            bind_replay(catalog, self.proof)

    def test_universe_parameter_order_is_bound(self):
        name = next(name for name, node in self.nodes.items() if len(node["universes"]) > 1)
        catalog, node = self.altered(name)
        node["universes"] = list(reversed(node["universes"]))
        with self.assertRaisesRegex(RepositoryError, "indexed declaration differs"):
            bind_replay(catalog, self.proof)

    def test_changed_reduction_rules_and_structure_metadata_are_rejected(self):
        for name, key in [("Binding.Tree", "indices"), ("Binding.Tree.leaf", "fields"), ("Binding.Tree.rec", "minors")]:
            catalog, node = self.altered(name)
            node["structure"][key] += 1
            with self.subTest(name=name), self.assertRaisesRegex(RepositoryError, "indexed declaration differs"):
                bind_replay(catalog, self.proof)
        catalog, node = self.altered("Binding.Tree.rec")
        node["structure"]["rules"][0]["rhs"] = self.nodes["Binding.zero"]["value"]
        with self.assertRaisesRegex(RepositoryError, "indexed declaration differs"):
            bind_replay(catalog, self.proof)

    def test_reducibility_and_definition_groups_are_bound(self):
        for field, value in [("reducibility", "opaque"), ("definition_group", [])]:
            catalog, node = self.altered("Binding.zero")
            node[field] = value
            with self.subTest(field=field), self.assertRaisesRegex(RepositoryError, "indexed declaration differs.*Binding.zero"):
                bind_replay(catalog, self.proof)

    def test_binder_labels_and_let_optimization_hints_do_not_change_logic(self):
        catalog = {**self.catalog, "expressions": [dict(node) for node in self.catalog["expressions"]]}
        for node in catalog["expressions"]:
            if node["tag"] in {"lam", "forall", "let"}:
                node["name"] = "renamed"
                if "binder" in node:
                    node["binder"] = "implicit"
                if "nondependent" in node:
                    node["nondependent"] = not node["nondependent"]
        self.assertEqual(bind_replay(catalog, self.proof), self.catalog["proof_binding"])

    def test_expression_numbering_is_independent_of_the_checked_export(self):
        catalog = deepcopy(self.catalog)
        records = catalog["expressions"]
        position = next(index for index in range(len(records) - 1)
                        if records[index]["tag"] not in CHILD_FIELDS and records[index + 1]["tag"] not in CHILD_FIELDS)
        order = list(range(len(records)))
        order[position], order[position + 1] = order[position + 1], order[position]
        identifiers = {old: new for new, old in enumerate(order)}
        catalog["expressions"] = [records[old] for old in order]
        for record in catalog["expressions"]:
            for field in CHILD_FIELDS.get(record["tag"], ()):
                record[field] = identifiers[record[field]]
        for node in catalog["declarations"]:
            node["type"] = identifiers[node["type"]]
            if node["value"] is not None:
                node["value"] = identifiers[node["value"]]
            if node["kind"] == "recursor":
                for rule in node["structure"]["rules"]:
                    rule["rhs"] = identifiers[rule["rhs"]]
        validate(catalog, self.policy)
        self.assertEqual(bind_replay(catalog, self.proof), self.catalog["proof_binding"])

    def test_lossless_names_preserve_quoted_and_numeric_components(self):
        self.assertIn({"str": "a.b"}, self.catalog["name_data"]["Binding.«a.b»"])
        self.assertIn({"str": "0"}, self.catalog["name_data"]["Binding.«0»"])
        names = name_hashes({"string": [{"str": "0"}], "numeric": [{"num": 0}]})
        self.assertNotEqual(names["string"], names["numeric"])

    def test_missing_and_aliased_logical_names_are_rejected(self):
        catalog = {**self.catalog, "name_data": dict(self.catalog["name_data"])}
        catalog["name_data"].pop("Binding.truth")
        with self.assertRaisesRegex(RepositoryError, "missing logical name"):
            bind_replay(catalog, self.proof)
        with self.assertRaisesRegex(RepositoryError, "duplicate logical name identity"):
            name_hashes({"one": [{"str": "x"}], "two": [{"str": "x"}]})

    def test_truncated_and_mismatched_toolchain_exports_are_rejected(self):
        path = self.root / "truncated.jsonl"
        path.write_bytes(self.proof.read_bytes().splitlines(keepends=True)[0])
        with self.assertRaisesRegex(RepositoryError, "omits indexed declarations"):
            bind_replay(self.catalog, path)
        path.write_text(json.dumps({"meta": {"format": {"version": "3.1.0"},
                                            "lean": {"version": "other", "githash": "0" * 40}}}) + "\n")
        with self.assertRaisesRegex(RepositoryError, "toolchain differs"):
            bind_replay(self.catalog, path)

    def test_duplicate_fields_and_invalid_primitive_references_are_rejected(self):
        header = self.proof.read_bytes().splitlines(keepends=True)[0]
        path = self.root / "malformed.jsonl"
        for line, expected in [
            (b'{"in":1,"in":2,"str":{"pre":0,"str":"x"}}\n', "duplicate replay json field"),
            (b'{"ie":0,"app":{"fn":1,"arg":1}}\n', "undefined replay reference"),
            (b'{"in":0,"str":{"pre":0,"str":"x"}}\n', "duplicate replay index"),
            (b'{"ie":0,"unknown":0}\n', "unsupported replay expression"),
        ]:
            path.write_bytes(header + line)
            with self.subTest(line=line), self.assertRaisesRegex(RepositoryError, expected):
                bind_replay(self.catalog, path)


class PackedFingerprintTests(unittest.TestCase):
    def test_sparse_ids_duplicates_and_undefined_references(self):
        values = Hashes()
        zero, one, two = (fingerprint("test", number) for number in range(3))
        values.add(2, two)
        values.add(0, zero)
        values.add(1, one)
        self.assertEqual(len(values.data), 96)
        self.assertEqual([values.get(index) for index in range(3)], [zero, one, two])
        self.assertEqual(len(values), 3)
        with self.assertRaisesRegex(RepositoryError, "duplicate replay index"):
            values.add(2, two)
        with self.assertRaisesRegex(RepositoryError, "undefined replay reference"):
            values.get(3)


if __name__ == "__main__":
    unittest.main()
