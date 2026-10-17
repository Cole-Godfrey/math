"""check complete terminal queries against the verified artifact and graph."""

from contextlib import redirect_stderr, redirect_stdout
from copy import deepcopy
import hashlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from repository.__main__ import main, statistics
from repository.core import canonical, declaration_expressions, digest, expression_names
from repository.explore import KnowledgeGraph
from repository.store import create_store
from tests.store_fixture import fixture


class CliTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.catalog, self.receipt = fixture(self.root)

    def invoke(self, *arguments):
        output, error = io.StringIO(), io.StringIO()
        with redirect_stdout(output), redirect_stderr(error):
            code = main(["--root", str(self.root), *arguments])
        return code, output.getvalue(), error.getvalue()

    def successful(self, *arguments):
        code, output, error = self.invoke(*arguments)
        self.assertEqual(code, 0, error)
        self.assertEqual(error, "")
        return output

    def publish(self):
        self.catalog.pop("content_digest", None)
        self.catalog["content_digest"] = digest(self.catalog)
        data = canonical(self.catalog) + b"\n"
        (self.root / "build/knowledge.json").write_bytes(data)
        receipt = create_store(self.root / "build", self.catalog, {}, hashlib.sha256(data).hexdigest())
        (self.root / "build/index.json").write_bytes(canonical(receipt))

    def expected_search(self, query="", **options):
        return "".join(f"{node['name']} [{node['kind']}]\n  {(node['doc'] or node['statement']).strip()}\n"
                       for node in KnowledgeGraph(self.catalog).search(query, **options))

    def test_read_commands_do_not_deserialize_the_complete_catalog(self):
        read_text = Path.read_text

        def bounded_read(path, *args, **kwargs):
            self.assertNotEqual(path, self.root / "build/knowledge.json")
            return read_text(path, *args, **kwargs)

        commands = [
            ("stats",), ("search", "truth"), ("subjects", "--json"),
            ("show", "Math.Fixture.truth", "--proof"),
            ("show", "Math.Fixture.identity", "--json"),
            ("deps", "Math.Fixture.alias_truth", "--transitive"),
            ("trace", "Math.Fixture.alias_truth", "--to", "True"),
            ("hierarchy", "Math.Fixture.alias_truth", "--format", "json"),
            ("export",), ("export", "--format", "lean"), ("export", "--format", "dot"),
        ]
        with patch.object(Path, "read_text", bounded_read):
            for arguments in commands:
                with self.subTest(arguments=arguments):
                    self.successful(*arguments)

    def test_statistics_match_the_complete_catalog(self):
        self.assertEqual(self.successful("stats"), statistics(self.catalog) + "\n")

    def test_search_filters_and_order_match_the_complete_catalog(self):
        for query in ["", "truth", "Math.Fixture.identity", "' OR 1=1 --", "%", "λ"]:
            for options, arguments in [
                ({}, []), ({"include_dependencies": True}, ["--all"]),
                ({"module": "Math.Fixture"}, ["--module", "Math.Fixture"]),
                ({"subject": "mathematics", "axiom_free": True}, ["--subject", "mathematics", "--axiom-free"]),
                ({"include_dependencies": True, "module": "Init.Prelude", "kind": "constructor"},
                 ["--all", "--module", "Init.Prelude", "--kind", "constructor"]),
            ]:
                with self.subTest(query=query, options=options):
                    self.assertEqual(self.successful("search", query, *arguments),
                                     self.expected_search(query, **options))

    def test_module_filter_retains_shared_selected_declarations(self):
        self.catalog["module_declarations_by_module"] = {"Math": [], "Math.Fixture": self.catalog["roots"]}
        node = next(node for node in self.catalog["declarations"] if node["name"] == "Math.Fixture.truth")
        node["module"] = "Init.Prelude"
        self.catalog["declaration_hashes"][node["name"]] = digest(node)
        self.publish()
        self.assertEqual(self.successful("search", "", "--module", "Math.Fixture"),
                         self.expected_search(module="Math.Fixture"))
        self.assertIn(node["name"], self.successful("search", "", "--module", "Math.Fixture"))

    def test_json_statements_retain_every_field_and_reachable_expression(self):
        for node in self.catalog["declarations"]:
            expressions = declaration_expressions(self.catalog, node)
            names = expression_names(node, expressions.values())
            expected = {**node, "origin": self.catalog["sources"][node["module"]], "expressions": expressions,
                        "name_data": {name: self.catalog["name_data"][name] for name in names}}
            with self.subTest(name=node["name"]):
                self.assertEqual(json.loads(self.successful("show", node["name"], "--json")), expected)

    def test_dependency_outputs_retain_cycles_and_both_directions(self):
        graph = KnowledgeGraph(self.catalog)
        for name in graph.nodes:
            for reverse in [False, True]:
                edges = graph.edges
                if reverse:
                    edges = {target: {source for source in graph.nodes if target in graph.edges[source]}
                             for target in graph.nodes}
                for transitive in [False, True]:
                    reached, pending = set(), list(edges[name])
                    while pending:
                        child = pending.pop()
                        if child not in reached:
                            reached.add(child)
                            if transitive:
                                pending.extend(edges[child])
                    arguments = (["--reverse"] if reverse else []) + (["--transitive"] if transitive else [])
                    with self.subTest(name=name, reverse=reverse, transitive=transitive):
                        self.assertEqual(self.successful("deps", name, *arguments).splitlines(), sorted(reached - {name}))

    def test_search_and_dependency_outputs_exceed_browser_page_limits(self):
        template = next(node for node in self.catalog["declarations"] if node["name"] == "Math.Fixture.truth")
        for index in range(305):
            node = {**deepcopy(template), "name": f"Math.Fixture.entry{index:03}"}
            node["definition_group"] = [node["name"]]
            self.catalog["declarations"].append(node)
            self.catalog["roots"].append(node["name"])
            self.catalog["declaration_hashes"][node["name"]] = digest(node)
            self.catalog["name_data"][node["name"]] = [{"str": part} for part in node["name"].split(".")]
        binding = self.catalog["proof_binding"]
        for field in ["indexed_declarations", "matched_declarations", "proof_declarations"]:
            binding[field] = len(self.catalog["declarations"])
        self.publish()
        for query in ["fixture", " ".join(["fixture"] * 31), " " * 1001]:
            with self.subTest(query=query[:40]):
                actual = self.successful("search", query, "--all")
                self.assertEqual(actual, self.expected_search(query, include_dependencies=True))
                self.assertGreater(actual.count("[theorem]"), 200)
        expected = sorted(node["name"] for node in self.catalog["declarations"]
                          if node["name"] != "True" and "True" in node["dependencies"])
        self.assertGreater(len(expected), 200)
        self.assertEqual(self.successful("deps", "True", "--reverse").splitlines(), expected)

    def test_subjects_hierarchies_and_paths_match_the_complete_graph(self):
        graph = KnowledgeGraph(self.catalog)
        self.assertEqual(json.loads(self.successful("subjects", "--json")), graph.subject_coverage())
        self.assertEqual(json.loads(self.successful("hierarchy", "Math.Fixture.alias_truth", "--format", "json")),
                         graph.hierarchy("Math.Fixture.alias_truth"))
        self.assertEqual(self.successful("trace", "Math.Fixture.alias_truth", "--to", "Math.Fixture.truth"),
                         "Math.Fixture.alias_truth -> Math.Fixture.truth\n")
        self.assertIn("No additional axioms", self.successful("trace", "Math.Fixture.identity"))

    def test_exports_retain_complete_artifact_bytes_and_edges(self):
        self.assertEqual(self.successful("export").encode(), (self.root / "build/knowledge.json").read_bytes())
        proof = next((self.root / "build").glob("proofs-*.jsonl"))
        self.assertEqual(self.successful("export", "--format", "lean").encode(), proof.read_bytes())
        edges = sorted((node["name"], dependency) for node in self.catalog["declarations"]
                       for dependency in node["dependencies"])
        expected = "digraph mathematics {\n" + "".join(
            f"  {json.dumps(source)} -> {json.dumps(target)};\n" for source, target in edges) + "}\n"
        self.assertEqual(self.successful("export", "--format", "dot"), expected)

    def test_invalid_queries_fail_without_partial_results(self):
        for arguments, message in [
            (("show", "missing"), "unknown declaration"),
            (("deps", "missing"), "unknown declaration"),
            (("trace", "missing"), "unknown declaration"),
            (("trace", "True", "--to", "missing"), "unknown declaration"),
            (("trace", "True", "--to", "Math.Fixture.identity"), "is not a dependency"),
            (("search", "", "--subject", "missing"), "unknown subject"),
        ]:
            with self.subTest(arguments=arguments):
                code, output, error = self.invoke(*arguments)
                self.assertEqual(code, 1)
                self.assertEqual(output, "")
                self.assertIn(message, error)

    def test_terminal_queries_reject_changed_sources_and_artifacts(self):
        for relative, message in [("Math/Fixture.lean", "stale"), ("build/knowledge.json", "catalog changed"),
                                  ("build/" + self.receipt["database"], "digest mismatch")]:
            path = self.root / relative
            before = path.read_bytes()
            try:
                path.write_bytes(before + b" \n")
                code, output, error = self.invoke("search", "truth")
                self.assertEqual(code, 1)
                self.assertEqual(output, "")
                self.assertIn(message, error)
            finally:
                path.write_bytes(before)

    def test_complete_catalogs_remain_usable_without_query_receipts(self):
        commands = [
            ("stats",), ("search", "truth"), ("subjects", "--json"),
            ("show", "Math.Fixture.identity", "--json"),
            ("show", "Math.Fixture.truth", "--proof"),
            ("deps", "True", "--reverse", "--transitive"),
            ("trace", "Math.Fixture.truth", "--to", "True"),
            ("hierarchy", "Math.Fixture.truth", "--format", "json"),
            ("export",), ("export", "--format", "dot"), ("export", "--format", "lean"),
        ]
        expected = {arguments: self.successful(*arguments) for arguments in commands}
        (self.root / "build/index.json").unlink()
        for arguments in commands:
            with self.subTest(arguments=arguments):
                self.assertEqual(self.successful(*arguments), expected[arguments])

    def test_invalid_existing_query_receipts_are_not_ignored(self):
        (self.root / "build/index.json").write_text('{"schema_version":0}')
        code, output, error = self.invoke("show", "Math.Fixture.truth")
        self.assertEqual(code, 1)
        self.assertEqual(output, "")
        self.assertIn("unsupported query store receipt", error)


if __name__ == "__main__":
    unittest.main()
