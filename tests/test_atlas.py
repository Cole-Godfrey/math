"""check the graph atlas ordering helpers."""

from collections import Counter
import unittest

from repository.atlas import Atlas, auxiliary, components, cyclic_order, topological
from repository.explore import KnowledgeGraph


class AtlasTests(unittest.TestCase):
    def classified_atlas(self):
        nodes = [
            {"name": "choice", "kind": "axiom", "module": "Foundation", "dependencies": []},
            {"name": "Shared.basis", "kind": "theorem", "module": "Shared", "dependencies": ["choice"]},
            {"name": "Shared.solution", "kind": "theorem", "module": "Shared",
             "dependencies": ["Shared.basis", "Other.transform"]},
            {"name": "Other.transform", "kind": "theorem", "module": "Other", "dependencies": ["choice"]},
        ]
        subjects = {
            "mathematics": {"title": "Mathematics", "parent": None, "modules": []},
            "analysis": {"title": "Analysis", "parent": "mathematics", "modules": ["Shared", "Other"]},
            "harmonic": {"title": "Harmonic analysis", "parent": "analysis", "modules": ["Shared", "Other"]},
            "schwartz": {"title": "Schwartz spaces", "parent": "harmonic", "modules": ["Shared"]},
            "fourier": {"title": "Fourier analysis", "parent": "harmonic", "modules": ["Other"]},
            "pde": {"title": "Partial differential equations", "parent": "analysis", "modules": ["Shared"]},
        }
        return Atlas(KnowledgeGraph({"declarations": nodes, "subjects": subjects,
                                     "roots": [node["name"] for node in nodes if node["kind"] == "theorem"]}))

    def test_shared_modules_remain_accessible_in_every_classified_subject(self):
        atlas = self.classified_atlas()
        for subject in ("schwartz", "pde"):
            with self.subTest(subject=subject):
                view = atlas.view("s:" + subject)
                self.assertEqual(view["units"], 2)
                self.assertEqual(view["theorems"], 2)
                self.assertIn("m:Shared", {node["id"] for node in view["nodes"] if node["role"] == "child"})
        module = atlas.view("m:Shared")
        self.assertEqual(module["trail"][-2]["id"], "s:schwartz")
        self.assertEqual({node["id"] for node in module["nodes"] if node["role"] == "child"},
                         {"d:Shared.basis", "d:Shared.solution"})

    def test_overlapping_subjects_count_each_declaration_once_in_their_ancestors(self):
        atlas = self.classified_atlas()
        for subject in ("mathematics", "analysis", "harmonic"):
            with self.subTest(subject=subject):
                view = atlas.view("s:" + subject)
                self.assertEqual(view["units"], 3)
                self.assertEqual(view["theorems"], 3)
                self.assertFalse(any(node["id"].startswith("m:") for node in view["nodes"]
                                     if node["role"] == "child"))

    def test_overlapping_groups_project_only_dependencies_outside_the_source_group(self):
        atlas = self.classified_atlas()
        for subject, source, target in (("analysis", "s:pde", "s:harmonic"),
                                        ("harmonic", "s:schwartz", "s:fourier")):
            with self.subTest(subject=subject):
                view = atlas.view("s:" + subject)
                ids = [node["id"] for node in view["nodes"]]
                edges = {(ids[start], ids[end]): weight for start, end, weight, _ in view["edges"]}
                self.assertEqual(edges[source, target], 1)
                self.assertNotIn((target, source), edges)
                self.assertEqual(edges[source, "d:choice"], 1)

    def test_generated_declarations_are_hidden(self):
        for name in ["_private.Math.0.helper", "Nat.rec", "Foo.mk.injEq", "Foo.eq_1", "Foo._proof_2",
                     "definition._@.Mathlib.Foo.1._hygCtx._hyg.2", "Bar.match_3", "Baz.congr_simp"]:
            self.assertTrue(auxiliary(name), name)
        for name in ["Nat.Prime.two_le", "instAddNat", "Real.exp", "Foo.eq_iff"]:
            self.assertFalse(auxiliary(name), name)

    def test_cycles_point_their_lightest_edges_upward(self):
        weights = [Counter({1: 900}), Counter({2: 800, 0: 3}), Counter({1: 5})]
        self.assertEqual(components(range(3), [sorted(edges) for edges in weights]), [[0, 1, 2]])
        self.assertEqual(cyclic_order([0, 1, 2], weights), {(1, 0), (2, 1)})
        large = [Counter({(node + 1) % 14: 10, (node + 13) % 14: 1}) for node in range(14)]
        upward = cyclic_order(list(range(14)), large)
        self.assertEqual(sum(large[source][target] for source, target in upward), 23)

    def test_layering_rejects_cycles(self):
        self.assertEqual(topological([[1], [], [0, 1]]), [1, 0, 2])
        with self.assertRaises(ValueError):
            topological([[1], [0]])


if __name__ == "__main__":
    unittest.main()
