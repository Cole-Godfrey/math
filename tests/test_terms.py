"""check term occurrences, binder scope, and complete application inspection."""

from copy import deepcopy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from repository.core import RepositoryError, digest
from repository.store import open_snapshot
from repository.terms import inspect_term
from tests.store_fixture import fixture


class TermInspectionTests(unittest.TestCase):
    def setUp(self):
        self.records = [
            {"tag": "sort", "level": {"tag": "zero"}},
            {"tag": "const", "name": "True", "levels": []},
            {"tag": "const", "name": "True.intro", "levels": []},
            {"tag": "bvar", "index": 0}, {"tag": "bvar", "index": 1},
            {"tag": "forall", "name": "h", "type": 3, "body": 4, "binder": "explicit"},
            {"tag": "forall", "name": "P", "type": 0, "body": 5, "binder": "implicit"},
            {"tag": "lam", "name": "h", "type": 3, "body": 3, "binder": "explicit"},
            {"tag": "lam", "name": "P", "type": 0, "body": 7, "binder": "implicit"},
            {"tag": "const", "name": "Fixture.identity", "levels": [{"tag": "param", "name": "u"}]},
            {"tag": "let", "name": "P", "type": 0, "value": 3, "body": 3, "nondependent": False},
            {"tag": "lam", "name": "P", "type": 0, "body": 10, "binder": "explicit"},
        ]
        self.node = {"name": "Fixture.identity", "kind": "theorem", "type": 6, "value": 8,
                     "structure": None, "universes": ["u"]}

    def inspect(self, root="value", path="", rule=None):
        def read(identifier):
            record = self.records[identifier]
            return {**record, "digest": digest(record)}
        return inspect_term(self.node, read, root, path, rule)

    def test_roots_and_immediate_children_retain_exact_stored_expressions(self):
        result = self.inspect()
        self.assertEqual(result["roots"], [
            {"root": "type", "rule": None, "id": 6, "label": "Statement"},
            {"root": "value", "rule": None, "id": 8, "label": "Proof"}])
        self.assertEqual(result["expression"], {"id": 8, **self.records[8], "digest": digest(self.records[8])})
        self.assertEqual([(item["field"], item["id"], item["path"]) for item in result["children"]],
                         [("type", 0, "t"), ("body", 7, "b")])
        self.assertEqual(result["context"], [])
        self.assertEqual(result["universes"], ["u"])

    def test_shared_bound_variables_resolve_at_their_occurrence(self):
        outer, inner = self.inspect(path="bt"), self.inspect(path="bb")
        self.assertEqual(outer["expression"]["id"], inner["expression"]["id"])
        self.assertEqual(outer["binding"]["name"], "P")
        self.assertEqual(inner["binding"]["name"], "h")
        self.assertEqual(outer["binding"]["depth"], 0)
        self.assertEqual(inner["binding"]["depth"], 1)
        self.assertEqual([(item["name"], item["index"]) for item in inner["context"]], [("P", 1), ("h", 0)])
        self.assertEqual([item["field"] for item in inner["ancestors"]], ["body", "body"])

    def test_child_previews_use_the_scope_of_the_child(self):
        result = self.inspect(path="b")
        children = {item["field"]: item for item in result["children"]}
        self.assertEqual(children["type"]["binding"]["name"], "P")
        self.assertEqual(children["body"]["binding"]["name"], "h")
        self.assertEqual([item["name"] for item in result["context"]], ["P"])

    def test_dependent_statement_binders_retain_the_outer_assumption(self):
        result = self.inspect(root="type", path="bb")
        self.assertEqual(result["expression"]["index"], 1)
        self.assertEqual(result["binding"]["name"], "P")
        self.assertEqual(result["binding"]["type"], 0)
        self.assertEqual(result["binding"]["binder"], "implicit")

    def test_local_definitions_shadow_names_only_inside_the_body(self):
        self.node["kind"], self.node["value"] = "definition", 11
        outer, inner = self.inspect(path="bv"), self.inspect(path="bb")
        self.assertEqual(outer["binding"]["name"], inner["binding"]["name"])
        self.assertEqual(outer["binding"]["depth"], 0)
        self.assertEqual(inner["binding"]["depth"], 1)
        self.assertEqual(inner["binding"]["kind"], "let")
        self.assertEqual(inner["binding"]["value"], 3)
        self.assertEqual(self.inspect(path="bt")["context"], outer["context"])
        self.assertEqual(self.inspect()["roots"][1]["label"], "Definition")

    def test_application_spines_preserve_argument_order_and_every_occurrence(self):
        self.records.extend([{"tag": "app", "function": 9, "argument": 1},
                             {"tag": "app", "function": 12, "argument": 2}])
        self.node["value"] = 13
        result = self.inspect()
        self.assertEqual([(item["id"], item["path"]) for item in result["application"]["arguments"]],
                         [(1, "fa"), (2, "a")])
        function = result["application"]["function"]
        self.assertEqual((function["id"], function["path"], function["name"]), (9, "ff", "Fixture.identity"))
        self.assertEqual(function["levels"], [{"tag": "param", "name": "u"}])
        for item in [function, *result["application"]["arguments"]]:
            self.assertEqual(self.inspect(path=item["path"])["expression"]["id"], item["id"])

    def test_application_lists_have_no_browser_page_limit(self):
        for _ in range(350):
            self.records.append({"tag": "app", "function": len(self.records) - 1, "argument": 2})
        self.node["value"] = len(self.records) - 1
        result = self.inspect()
        self.assertEqual(len(result["application"]["arguments"]), 350)
        self.assertEqual(result["application"]["arguments"][0]["path"], "f" * 349 + "a")

    def test_long_term_paths_do_not_use_python_recursion(self):
        first = len(self.records) - 1
        for _ in range(2500):
            self.records.append({"tag": "proj", "name": "Fixture", "index": 0,
                                 "expression": len(self.records) - 1})
        self.node["value"] = len(self.records) - 1
        result = self.inspect(path="e" * 2500)
        self.assertEqual(result["expression"]["id"], first)
        self.assertEqual(len(result["ancestors"]), 2500)

    def test_natural_literals_keep_every_digit_for_browser_clients(self):
        value = 10 ** 5000 + 179
        self.records.append({"tag": "nat", "value": value})
        self.node["value"] = len(self.records) - 1
        result = self.inspect()
        self.assertEqual(result["expression"]["value"], str(value))
        self.assertEqual(result["expression"]["digest"], digest(self.records[-1]))
        self.records.append({"tag": "app", "function": 9, "argument": self.node["value"]})
        self.node["value"] = len(self.records) - 1
        self.assertEqual(self.inspect()["application"]["arguments"][0]["literal"], str(value))

    def test_recursor_rules_have_independent_closed_roots(self):
        self.node.update(kind="recursor", value=None,
                         structure={"rules": [{"constructor": "Fixture.leaf", "rhs": 8},
                                              {"constructor": "Fixture.branch", "rhs": 2}]})
        result = self.inspect(root="rule", rule=0, path="bb")
        self.assertEqual(result["binding"]["name"], "h")
        self.assertEqual(result["roots"][2]["label"], "Reduction for Fixture.branch")
        self.assertEqual(self.inspect(root="rule", rule=1)["expression"]["name"], "True.intro")
        self.assertEqual(self.inspect(root="type")["context"], [])

    def test_invalid_roots_paths_and_rule_indices_are_rejected(self):
        for root, path, rule in [("missing", "", None), ("type", "", 0), ("rule", "", None),
                                 ("rule", "", True), ("rule", "", -1), ("rule", "", 0),
                                 ("value", "../", None), ("value", "a", None),
                                 ("value", "tt", None)]:
            with self.subTest(root=root, path=path, rule=rule), self.assertRaises(RepositoryError):
                self.inspect(root, path, rule)
        self.node["value"] = None
        with self.assertRaisesRegex(RepositoryError, "unavailable"):
            self.inspect()

    def test_inspection_does_not_mutate_shared_declarations_or_expressions(self):
        node, records = deepcopy(self.node), deepcopy(self.records)
        for root, path in [("value", ""), ("value", "b"), ("value", "bb"), ("type", "bb")]:
            self.inspect(root, path)
        self.assertEqual(self.node, node)
        self.assertEqual(self.records, records)


class StoredTermTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.catalog, _ = fixture(self.root)
        self.snapshot = open_snapshot(self.root)

    def test_inspection_reads_only_the_requested_occurrence_and_its_neighbours(self):
        with patch.object(self.snapshot, "expressions", side_effect=AssertionError("whole proof traversal")):
            result = self.snapshot.term("Math.Fixture.identity", path="bb")
        self.assertEqual(result["expression"]["id"], 3)
        self.assertEqual(result["expression"]["digest"], self.catalog["expression_hashes"][3])
        self.assertEqual(result["binding"]["name"], "h")
        self.assertEqual(result["context"][0]["name"], "P")

    def test_constant_references_preserve_lossless_logical_name_parts(self):
        result = self.snapshot.term("Math.Fixture.alias_truth")
        self.assertEqual(result["expression"]["name"], "Math.Fixture.truth")
        self.assertEqual(result["name_data"]["Math.Fixture.truth"],
                         self.catalog["name_data"]["Math.Fixture.truth"])

    def test_unknown_declarations_and_unrelated_expression_ids_are_rejected(self):
        with self.assertRaisesRegex(RepositoryError, "unknown declaration"):
            self.snapshot.term("Missing")
        with self.assertRaisesRegex(RepositoryError, "invalid term path"):
            self.snapshot.term("Math.Fixture.truth", path="9")


if __name__ == "__main__":
    unittest.main()
