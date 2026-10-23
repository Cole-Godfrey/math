"""check exact index binding against real kernel replay artifacts and altered terms."""

from copy import deepcopy
import http.client
from http.server import ThreadingHTTPServer
import json
import os
from pathlib import Path
import shutil
import tempfile
from threading import Thread
import unittest
from urllib.parse import urlencode
from unittest.mock import patch

from repository.build import check_replay, find_lake, read_json, verify
from repository.core import CHILD_FIELDS, RepositoryError, canonical, validate
from repository.replay import Hashes, bind_replay, fingerprint, name_hashes
from repository.server import ExplorerState, make_handler
from repository.store import open_snapshot


ROOT = Path(__file__).resolve().parents[1]


class ReplayArtifactTests(unittest.TestCase):
    """reject changed proof bytes even when a checker reports success."""

    def changed_export(self, checker):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            proof = root / "proof.jsonl"
            proof.write_bytes(b"original checked bytes\n")

            def checked_command(_root, arguments, capture=False):
                if checker in arguments and "--help" not in arguments:
                    proof.write_bytes(b"different proof bytes\n")
                return "nanoda_bin 0.4.19\n" if "--help" in arguments else ""

            with patch("repository.build.run", side_effect=checked_command):
                with self.assertRaisesRegex(RepositoryError, "proof export changed during proof replay"):
                    check_replay(root, "lake", proof, root / "checker.json", ["propext"])

    def test_export_changed_during_kernel_replay_is_rejected(self):
        self.changed_export("leanchecker")

    def test_export_changed_during_independent_replay_is_rejected(self):
        self.changed_export("nanoda_bin")

    def test_generated_partial_helpers_reject_before_proof_replay(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for name in ["Math", "tools", "repository"]:
                (root / name).mkdir()
            for path in (ROOT / "repository").glob("*.py"):
                shutil.copy2(path, root / "repository" / path.name)
            for name in ["tools/Export.lean", "lean-toolchain"]:
                shutil.copy2(ROOT / name, root / name)
            (root / "Math.lean").write_text("import Math.SafetyProbe\n")
            (root / "lakefile.toml").write_text('name = "math"\n[[lean_lib]]\nname = "Math"\n')
            (root / "lake-manifest.json").write_text(json.dumps({
                "version": "1.3.0", "name": "math", "packages": [], "packagesDir": ".lake/packages"}))
            (root / "Math/SafetyProbe.lean").write_text('''module
@[expose] public section
namespace SafetyProbe
inductive Symbol where
  | M | I | U
abbrev Word := List Symbol
open Symbol
def expansionCost : Word → Nat
  | [] => 0
  | M :: xs => expansionCost xs
  | I :: xs => 1 + expansionCost xs
  | U :: xs => 3 + expansionCost xs
end SafetyProbe
''')
            current = json.loads((ROOT / "knowledge.json").read_text())
            policy = {key: current[key] for key in ["schema_version", "foundation", "axioms"]}
            policy["modules"] = {name: {"title": name, "allowed_axioms": list(policy["axioms"])}
                                 for name in ["Math", "Math.SafetyProbe"]}
            (root / "knowledge.json").write_text(json.dumps(policy))
            with patch.dict(os.environ, {"MATH_LAKE": find_lake(ROOT)}), \
                    patch("repository.build.check_replay", side_effect=AssertionError("proof replay was reached")):
                with self.assertRaisesRegex(RepositoryError, "partial declarations are not allowed in project modules"):
                    verify(root)


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
        cls.large_natural_digits = "1" + "0" * 5000
        (cls.root / "Math/Binding.lean").write_text('''/-! fixture module reference [fixturebook]. -/
universe u
namespace Binding
theorem truth : True := True.intro
theorem alias_truth : True := True.intro
theorem identity (P : Prop) (h : P) : P := h
def zero : Nat := 0
def largeNatural : Nat := LARGE_NATURAL
theorem largeNatural_eq : largeNatural = LARGE_NATURAL := rfl
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
'''.replace("LARGE_NATURAL", cls.large_natural_digits))
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

    def assert_rejected_before_terms(self, catalog, expected, policy=None):
        """reject invalid summaries before constructing expression audit state."""
        with patch("repository.core.ExpressionPool", side_effect=AssertionError("unexpected term traversal")):
            with self.assertRaisesRegex(RepositoryError, expected):
                validate(catalog, self.policy if policy is None else policy)

    def test_invalid_declaration_metadata_is_rejected_before_terms(self):
        cases = [("value", None, "missing or unexpected body"),
                 ("value", True, "invalid expression reference"),
                 ("type", len(self.catalog["expressions"]), "invalid expression reference"),
                 ("module", "Missing", "unknown declaration module"),
                 ("universes", ["u", "u"], "universe parameters: duplicate names"),
                 ("axioms", [0], "axioms: expected names")]
        for field, value, expected in cases:
            with self.subTest(field=field, value=value):
                catalog, node = self.altered("Binding.truth")
                node[field] = value
                self.assert_rejected_before_terms(catalog, expected)

    def test_invalid_dependency_metadata_is_rejected_before_terms(self):
        catalog, node = self.altered("Binding.truth")
        node["dependencies"].remove("True.intro")
        self.assert_rejected_before_terms(catalog, "dependencies differ from declared expression roles")
        catalog, node = self.altered("Binding.truth")
        node["value_dependencies"].append("Missing")
        node["dependencies"].append("Missing")
        self.assert_rejected_before_terms(catalog, "unresolved dependency")
        catalog, node = self.altered("Binding.truth")
        node["value_dependencies"].append("True.intro")
        self.assert_rejected_before_terms(catalog, "value_dependencies: duplicate names")

    def test_axiom_summaries_are_checked_before_terms(self):
        catalog, node = self.altered("Binding.quotient_eq")
        self.assertTrue(node["axioms"])
        node["axioms"] = []
        self.assert_rejected_before_terms(catalog, "axiom closure differs from fresh Lean traversal")
        catalog, node = self.altered("Binding.truth")
        node["lean_axioms"] = ["Classical.choice"]
        self.assert_rejected_before_terms(catalog, "cached Lean axioms missing from dependency graph")
        catalog, node = self.altered("Binding.truth")
        node.update(kind="axiom", value=None, definition_group=[], value_dependencies=[],
                    dependencies=node["type_dependencies"].copy(), axioms=["Binding.truth"])
        self.assert_rejected_before_terms(catalog, "undeclared foundational axiom")

    def test_every_selecting_module_budget_is_checked_before_terms(self):
        policy = deepcopy(self.policy)
        policy["modules"]["Math.Strict"] = {"title": "strict fixture", "allowed_axioms": []}
        catalog = {**self.catalog, "modules": [*self.catalog["modules"],
                   {"name": "Math.Strict", "imports": ["Math.Binding"]}],
                   "module_declarations_by_module": {**self.catalog["module_declarations_by_module"],
                                                     "Math.Strict": ["Binding.quotient_eq"]}}
        self.assert_rejected_before_terms(catalog, "module axiom budget exceeded in Math.Strict", policy)

    def test_unreachable_declarations_are_rejected_before_terms(self):
        node = {**self.nodes["Binding.truth"], "name": "orphan", "module": "Init.Prelude",
                "definition_group": ["orphan"]}
        catalog = {**self.catalog, "declarations": [*self.catalog["declarations"], node]}
        self.assert_rejected_before_terms(catalog, "export contains unreachable declarations")

    def test_consistent_forged_summaries_still_require_actual_term_dependencies(self):
        catalog, node = self.altered("Binding.truth")
        node["value_dependencies"] = []
        node["dependencies"] = node["type_dependencies"].copy()
        with self.assertRaisesRegex(RepositoryError, "value_dependencies differs from expressions"):
            validate(catalog, self.policy)

    def test_valid_metadata_cannot_hide_invalid_or_unreachable_terms(self):
        for expression, expected in [({"tag": "mvar", "name": "hidden"}, "invalid or unresolved expression"),
                                     ({"tag": "nat", "value": 99173}, "export contains unreachable expressions")]:
            with self.subTest(expression=expression):
                catalog = {**self.catalog, "expressions": [*self.catalog["expressions"], expression]}
                with self.assertRaisesRegex(RepositoryError, expected):
                    validate(catalog, self.policy)
        catalog, node = self.altered("Binding.truth")
        node["value"] = next(index for index, expression in enumerate(catalog["expressions"])
                             if expression["tag"] == "bvar" and expression["index"] == 0)
        with self.assertRaisesRegex(RepositoryError, "unbound variable in declaration"):
            validate(catalog, self.policy)
        catalog, node = self.altered("Binding.truth")
        node["value"] = len(catalog["expressions"])
        catalog["expressions"] = [*catalog["expressions"],
                                  {"tag": "sort", "level": {"tag": "param", "name": "unbound_u"}}]
        with self.assertRaisesRegex(RepositoryError, "undeclared universe parameter"):
            validate(catalog, self.policy)

    def test_every_indexed_declaration_is_bound_to_the_checked_export(self):
        audit = self.catalog["proof_binding"]
        self.assertEqual(audit["matched_declarations"], len(self.nodes))
        self.assertEqual(audit, bind_replay(self.catalog, self.proof))
        self.assertEqual(audit["proof_export_digest"], self.catalog["provenance"]["proof_export_digest"])
        self.assertEqual({node["kind"] for node in self.nodes.values()},
                         {"axiom", "definition", "theorem", "opaque", "inductive", "constructor", "recursor", "quotient_primitive"})

    def test_module_documentation_is_extracted_from_the_lean_environment(self):
        module = next(item for item in self.catalog["modules"] if item["name"] == "Math.Binding")
        self.assertIn("fixture module reference [fixturebook]", module["docs"][0]["text"])
        self.assertEqual(module["docs"][0]["line"], 1)

    def test_large_naturals_survive_kernel_replay_storage_and_catalog_reconstruction(self):
        snapshot = open_snapshot(self.root)
        term = snapshot.term("Binding.largeNatural")
        argument = next(item for item in term["application"]["arguments"]
                        if item.get("literal") == self.large_natural_digits)
        focused = snapshot.term("Binding.largeNatural", path=argument["path"])
        self.assertEqual(focused["expression"]["tag"], "nat")
        self.assertEqual(focused["expression"]["value"], self.large_natural_digits)
        self.assertEqual(str(self.catalog["expressions"][focused["expression"]["id"]]["value"]),
                         self.large_natural_digits)
        self.assertEqual(json.loads(canonical(focused))["expression"]["value"], self.large_natural_digits)
        data = b"".join(snapshot.catalog_chunks())
        self.assertEqual(data, (self.root / "build/knowledge.json").read_bytes())
        self.assertEqual(read_json(self.root / "build/knowledge.json"), self.catalog)
        self.assertEqual(self.catalog["provenance"]["checkers"],
                         ["Lean 4.35.0 kernel replay", "nanoda_bin 0.4.19"])

    def test_large_natural_literal_changes_are_rejected_by_proof_binding(self):
        catalog = {**self.catalog, "expressions": [dict(node) for node in self.catalog["expressions"]]}
        expression = next(node for node in catalog["expressions"]
                          if node["tag"] == "nat" and node["value"] == int(self.large_natural_digits))
        expression["value"] += 1
        validate(catalog, self.policy)
        with self.assertRaisesRegex(RepositoryError, "indexed declaration differs"):
            bind_replay(catalog, self.proof)

    def test_large_naturals_remain_exact_over_http(self):
        state = ExplorerState(self.root)
        server = ThreadingHTTPServer(("127.0.0.1", 0), make_handler(state))
        thread = Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            def request(endpoint, **parameters):
                parameters["snapshot"] = self.catalog["content_digest"]
                connection = http.client.HTTPConnection("127.0.0.1", server.server_port)
                try:
                    connection.request("GET", endpoint + "?" + urlencode(parameters))
                    response = connection.getresponse()
                    self.assertEqual(response.status, 200)
                    self.assertEqual(response.getheader("X-Math-Snapshot"), self.catalog["content_digest"])
                    return response.read()
                finally:
                    connection.close()

            root = json.loads(request("/api/term", name="Binding.largeNatural"))
            argument = next(item for item in root["application"]["arguments"]
                            if item.get("literal") == self.large_natural_digits)
            term = json.loads(request("/api/term", name="Binding.largeNatural", path=argument["path"]))
            self.assertEqual(term["expression"]["value"], self.large_natural_digits)
            expressions = json.loads(request("/api/expressions", name="Binding.largeNatural"))
            self.assertIn(int(self.large_natural_digits),
                          [item["value"] for item in expressions["expressions"].values() if item["tag"] == "nat"])
            self.assertEqual(request("/api/catalog"), (self.root / "build/knowledge.json").read_bytes())
            self.assertEqual(request("/api/proof-export"), self.proof.read_bytes())
        finally:
            server.shutdown()
            server.server_close()
            thread.join()

    def test_term_inspection_retains_checked_reduction_rules_and_exact_names(self):
        snapshot = open_snapshot(self.root)
        name = "Binding.Tree.rec"
        for index, rule in enumerate(self.nodes[name]["structure"]["rules"]):
            with self.subTest(rule=index):
                result = snapshot.term(name, root="rule", rule=index)
                expected = self.catalog["expressions"][rule["rhs"]]
                self.assertEqual(result["expression"], {"id": rule["rhs"], **expected,
                                                       "digest": self.catalog["expression_hashes"][rule["rhs"]]})
                self.assertEqual(result["context"], [])
        for name in ("Binding.«a.b»", "Binding.«0»"):
            with self.subTest(name=name):
                result = snapshot.term(name)
                self.assertEqual(result["name_data"][name], self.catalog["name_data"][name])

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
