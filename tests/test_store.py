"""verify query fidelity, immutable artifacts, and complete term retrieval."""

from copy import deepcopy
import hashlib
from pathlib import Path
import sqlite3
import tempfile
import unittest

from repository.core import RepositoryError, canonical, declaration_expressions, digest
from repository.explore import KnowledgeGraph
from repository.store import Snapshot, create_store, open_snapshot
from tests.store_fixture import fixture


class StoreTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.catalog, self.receipt = fixture(self.root)
        self.snapshot = open_snapshot(self.root)

    def test_every_declaration_round_trips_with_proof(self):
        for node in self.catalog["declarations"]:
            actual = self.snapshot.declaration(node["name"], proof=True)
            for key, value in node.items():
                self.assertEqual(actual[key], value)
        self.assertNotIn("proof", self.snapshot.declaration("Math.Fixture.truth"))

    def test_complete_catalog_stream_is_byte_identical(self):
        self.assertEqual(b"".join(self.snapshot.catalog_chunks()), canonical(self.catalog) + b"\n")

    def test_catalog_stream_remains_bound_to_its_snapshot(self):
        (self.root / "build/knowledge.json").write_bytes(b"a later artifact\n")
        self.assertEqual(b"".join(self.snapshot.catalog_chunks()), canonical(self.catalog) + b"\n")
        self.assertTrue(self.snapshot.proof_path.is_file())

    def test_complete_expression_subgraphs_are_retained(self):
        for node in self.catalog["declarations"]:
            actual = self.snapshot.expressions(node["name"])
            self.assertEqual(actual["expressions"], declaration_expressions(self.catalog, node))
            for identifier, value in actual["expression_hashes"].items():
                self.assertEqual(value, self.catalog["expression_hashes"][int(identifier)])
            self.assertIn(node["name"], actual["name_data"])
            self.assertEqual(actual["definition_group"], node["definition_group"])
            self.assertEqual(actual["reducibility"], node["reducibility"])

    def test_missing_or_mismatched_proof_binding_is_rejected(self):
        for binding in [None, {**self.catalog["proof_binding"], "proof_export_digest": "0" * 64},
                        {**self.catalog["proof_binding"], "matched_declarations": 0}]:
            catalog = deepcopy(self.catalog)
            if binding is None:
                catalog.pop("proof_binding")
            else:
                catalog["proof_binding"] = binding
            catalog.pop("content_digest")
            catalog["content_digest"] = digest(catalog)
            receipt = create_store(self.root / "build", catalog, {}, hashlib.sha256(canonical(catalog) + b"\n").hexdigest())
            with self.subTest(binding=binding), self.assertRaisesRegex(RepositoryError, "proof binding"):
                Snapshot(self.root / "build" / receipt["database"], receipt)

    def test_graph_retains_every_edge_role_and_inductive_cycle(self):
        expected = KnowledgeGraph(self.catalog).hierarchy("Math.Fixture.alias_truth")
        self.assertEqual(self.snapshot.graph.hierarchy("Math.Fixture.alias_truth"), expected)

    def test_search_matches_cli_scope_order_and_literal_queries(self):
        for query in ["", "truth", "Math.Fixture.identity", "' OR 1=1 --", "%", "λ"]:
            expected = [item["name"] for item in KnowledgeGraph(self.catalog).search(query, include_dependencies=True)]
            actual = self.snapshot.search(query, include_dependencies=True)
            self.assertEqual([item["name"] for item in actual["items"]], expected)

    def test_subject_closure_and_pagination_are_complete(self):
        data = self.snapshot.search(subject="mathematics", include_dependencies=True, limit=2)
        names = []
        for offset in range(0, data["total"], 2):
            names.extend(item["name"] for item in self.snapshot.search(subject="mathematics", include_dependencies=True,
                                                                         offset=offset, limit=2)["items"])
        self.assertEqual(set(names), {node["name"] for node in self.catalog["declarations"]})
        self.assertEqual(len(names), len(set(names)))

    def test_subject_search_keeps_shared_declarations_and_canonical_origins(self):
        catalog = deepcopy(self.catalog)
        catalog["module_declarations_by_module"] = {"Math.Fixture": catalog["roots"]}
        node = next(item for item in catalog["declarations"] if item["name"] == "Math.Fixture.truth")
        node["module"] = "Init.Prelude"
        catalog["declaration_hashes"][node["name"]] = digest(node)
        catalog.pop("content_digest")
        catalog["content_digest"] = digest(catalog)
        receipt = create_store(self.root / "build", catalog, {}, hashlib.sha256(canonical(catalog) + b"\n").hexdigest())
        snapshot = Snapshot(self.root / "build" / receipt["database"], receipt)
        names = {item["name"] for item in snapshot.search(subject="mathematics")["items"]}
        self.assertEqual(names, set(catalog["roots"]))
        record = snapshot.declaration(node["name"])
        self.assertEqual(record["module"], "Init.Prelude")
        self.assertEqual(record["selected_modules"], ["Math.Fixture"])
        self.assertEqual(b"".join(snapshot.catalog_chunks()), canonical(catalog) + b"\n")

    def test_dependency_queries_handle_cycles_and_reverse_edges(self):
        direct = self.snapshot.relations("Math.Fixture.truth")
        self.assertEqual({item["name"] for item in direct["items"]}, {"True", "True.intro"})
        reverse = self.snapshot.relations("Math.Fixture.truth", reverse=True)
        self.assertEqual([item["name"] for item in reverse["items"]], ["Math.Fixture.alias_truth"])
        transitive = self.snapshot.relations("Math.Fixture.alias_truth", transitive=True)
        self.assertEqual({item["name"] for item in transitive["items"]}, {"Math.Fixture.truth", "True", "True.intro"})
        types = self.snapshot.relations("Math.Fixture.truth", role="type")
        self.assertEqual([item["name"] for item in types["items"]], ["True"])

    def test_source_is_archived_with_the_snapshot(self):
        before = self.snapshot.source("Math.Fixture.truth", full=True)
        (self.root / "Math/Fixture.lean").write_text("changed after verification\n")
        self.assertEqual(self.snapshot.source("Math.Fixture.truth", full=True), before)
        with self.assertRaisesRegex(RepositoryError, "stale"):
            open_snapshot(self.root)

    def test_corrupt_database_is_rejected(self):
        database = self.root / "build" / self.receipt["database"]
        with database.open("ab") as handle:
            handle.write(b"changed")
        with self.assertRaisesRegex(RepositoryError, "query store digest mismatch"):
            open_snapshot(self.root)

    def test_changed_proof_export_is_rejected(self):
        path = next((self.root / "build").glob("proofs-*.jsonl"))
        path.write_bytes(b"changed proof export")
        with self.assertRaisesRegex(RepositoryError, "proof export changed"):
            open_snapshot(self.root)

    def test_catalog_and_receipt_binding_are_checked(self):
        path = self.root / "build/knowledge.json"
        path.write_bytes(path.read_bytes() + b" ")
        with self.assertRaisesRegex(RepositoryError, "catalog changed"):
            open_snapshot(self.root)

    def test_snapshot_connections_cannot_write(self):
        with self.snapshot.connect() as connection:
            with self.assertRaises(sqlite3.OperationalError):
                connection.execute("DELETE FROM declarations")

    def test_query_parameters_are_validated(self):
        with self.assertRaisesRegex(RepositoryError, "invalid search page"):
            self.snapshot.search(limit=0)
        with self.assertRaisesRegex(RepositoryError, "unknown subject"):
            self.snapshot.search(subject="missing")
        with self.assertRaisesRegex(RepositoryError, "unknown dependency role"):
            self.snapshot.relations("Math.Fixture.truth", role="execute")
        with self.assertRaisesRegex(RepositoryError, "unknown declaration"):
            self.snapshot.declaration("../../private")


if __name__ == "__main__":
    unittest.main()
