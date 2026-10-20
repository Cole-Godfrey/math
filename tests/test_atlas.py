"""check the graph atlas ordering helpers."""

from collections import Counter
import unittest

from repository.atlas import auxiliary, components, cyclic_order, topological


class AtlasTests(unittest.TestCase):
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
