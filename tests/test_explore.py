"""check complete dependency hierarchies and subject exploration."""

from __future__ import annotations

import unittest

from repository.core import RepositoryError, axiom_closure, subject_policy
from repository.explore import KnowledgeGraph


def node(name: str, dependencies: list[str], kind: str = "theorem", module: str = "Proofs") -> dict:
    return {
        "name": name, "module": module, "kind": kind, "dependencies": dependencies,
        "type_dependencies": dependencies[:1], "value_dependencies": dependencies[1:],
        "structural_dependencies": [], "statement": name, "doc": None, "axioms": [],
    }


class ExplorationTests(unittest.TestCase):
    def setUp(self):
        nodes = [node("A", ["A.mk"], "inductive"), node("A.mk", ["A", "axiom"], "constructor"),
                 node("lemma1", ["A"]), node("lemma2", ["A"]),
                 node("theorem", ["lemma1", "lemma2"]), node("axiom", [], "axiom", "Foundation"),
                 node("unrelated", [], module="Other")]
        closure = axiom_closure({item["name"]: item for item in nodes})
        for item in nodes:
            item["axioms"] = sorted(closure[item["name"]])
        self.catalog = {
            "declarations": nodes, "roots": ["theorem", "unrelated"],
            "foundation": {"id": "test-foundation", "rules": ["test rule"]},
            "subjects": {
                "math": {"title": "Mathematics", "parent": None, "modules": ["Other"]},
                "proofs": {"title": "Proofs", "parent": "math", "modules": ["Proofs"]},
            },
        }
        self.graph = KnowledgeGraph(self.catalog)

    def test_hierarchy_preserves_every_reachable_declaration_and_edge(self):
        result = self.graph.hierarchy("theorem")
        expected = self.graph.closure({"theorem"})
        self.assertEqual({item["name"] for item in result["declarations"]}, expected)
        self.assertEqual({(edge["from"], edge["to"]) for edge in result["edges"]},
                         {(name, dep) for name in expected for dep in self.graph.edges[name]})
        self.assertNotIn("unrelated", expected)
        self.assertTrue(all(edge["roles"] for edge in result["edges"]))

    def test_inductive_cycles_form_one_group_with_prerequisites_first(self):
        result = self.graph.hierarchy("theorem")
        groups = result["groups"]
        block = next(group for group in groups if "A" in group["members"])
        self.assertEqual(block["members"], ["A", "A.mk"])
        self.assertTrue(block["cyclic"])
        positions = {group["id"]: index for index, group in enumerate(groups)}
        by_id = {group["id"]: group for group in groups}
        for group in groups:
            for dependency in group["dependencies"]:
                self.assertLess(positions[dependency], positions[group["id"]])
                self.assertLess(by_id[dependency]["level"], group["level"])

    def test_axiom_paths_use_actual_edges(self):
        result = self.graph.hierarchy("theorem")
        self.assertEqual(result["axioms"], ["axiom"])
        for path in result["axiom_paths"].values():
            self.assertEqual(path[0], "theorem")
            self.assertEqual(path[-1], "axiom")
            for source, target in zip(path, path[1:]):
                self.assertIn(target, self.graph.edges[source])

    def test_long_derivations_do_not_depend_on_python_recursion_depth(self):
        nodes = [node(f"n{index}", [f"n{index - 1}"] if index else []) for index in range(2500)]
        graph = KnowledgeGraph({**self.catalog, "declarations": nodes, "roots": ["n2499"]})
        result = graph.hierarchy("n2499")
        self.assertEqual(len(result["declarations"]), 2500)
        self.assertEqual(max(group["level"] for group in result["groups"]), 2499)

    def test_subject_search_can_include_complete_prerequisite_closure(self):
        self.assertEqual([item["name"] for item in self.graph.search(subject="proofs")], ["theorem"])
        all_names = {item["name"] for item in self.graph.search(subject="proofs", include_dependencies=True)}
        self.assertEqual(all_names, self.graph.closure({"theorem"}))
        self.assertEqual([item["name"] for item in self.graph.search("axiom", "proofs", True)], ["axiom"])

    def test_parent_subject_includes_its_children(self):
        coverage = {item["id"]: item for item in self.graph.subject_coverage()}
        self.assertEqual(coverage["math"]["selected_declarations"], 2)
        self.assertEqual(coverage["proofs"]["selected_declarations"], 1)
        self.assertEqual(coverage["proofs"]["dependency_declarations"], 6)

    def test_unknown_subject_and_declaration_fail(self):
        with self.assertRaisesRegex(RepositoryError, "unknown subject"):
            self.graph.search(subject="absent")
        with self.assertRaisesRegex(RepositoryError, "unknown declaration"):
            self.graph.hierarchy("absent")

    def test_subject_cycles_are_rejected(self):
        self.catalog["subjects"]["math"]["parent"] = "proofs"
        with self.assertRaisesRegex(RepositoryError, "cyclic subject hierarchy"):
            subject_policy(self.catalog, {"Other", "Proofs"})

    def test_subject_modules_must_cover_registered_modules(self):
        with self.assertRaisesRegex(RepositoryError, "missing from the subject hierarchy"):
            subject_policy(self.catalog, {"Other", "Proofs", "Missing"})
        with self.assertRaisesRegex(RepositoryError, "unknown subject module"):
            subject_policy(self.catalog, {"Other"})

    def test_named_results_precede_generated_helpers_without_losing_matches(self):
        public = node("exists_deriv_eq_slope", [])
        public["doc"] = "The mean value theorem."
        helper = node("_private.Mathlib.Analysis.MeanValue.helper", [])
        graph = KnowledgeGraph({**self.catalog, "declarations": [helper, public],
                                "roots": [helper["name"], public["name"]]})
        results = graph.search("mean value")
        self.assertEqual([item["name"] for item in results], [public["name"], helper["name"]])
        self.assertEqual(graph.search(helper["name"])[0]["name"], helper["name"])

    def test_shared_declarations_remain_in_every_selecting_subject(self):
        catalog = {**self.catalog, "declarations": [dict(item) for item in self.catalog["declarations"]],
                   "module_declarations_by_module": {"Proofs": ["theorem"], "Other": ["unrelated", "theorem"]}}
        next(item for item in catalog["declarations"] if item["name"] == "theorem")["module"] = "Origin"
        graph = KnowledgeGraph(catalog)
        self.assertEqual([item["name"] for item in graph.search(subject="proofs")], ["theorem"])
        self.assertEqual([item["name"] for item in graph.search(module="Proofs")], ["theorem"])
        self.assertIn("theorem", {item["name"] for item in graph.search(module="Other")})
        coverage = {item["id"]: item for item in graph.subject_coverage()}
        self.assertEqual(coverage["proofs"]["selected_declarations"], 1)
        self.assertEqual(graph.nodes["theorem"]["module"], "Origin")


if __name__ == "__main__":
    unittest.main()
