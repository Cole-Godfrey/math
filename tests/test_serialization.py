"""check streamed artifact bytes and fingerprints against the canonical encoder."""

import random
import unittest

from repository.core import ExpressionPool, RepositoryError, canonical, canonical_chunks, digest, stream_digest


class SerializationTests(unittest.TestCase):
    def test_streams_match_canonical_bytes_for_nested_json(self):
        randomizer = random.Random(20261017)

        def value(depth):
            if not depth:
                return randomizer.choice([None, True, False, 0, -1, 10 ** 30, 1.25, "ℂ → ℝ", "\"\\\n"])
            if randomizer.randrange(2):
                return [value(depth - 1) for _ in range(randomizer.randrange(5))]
            return {key: value(depth - 1) for key in randomizer.sample(["z", "a", "λ", "\""], randomizer.randrange(5))}

        for item in [value(4) for _ in range(100)] + [[], {}, "", (1, 2), {2: "two", 1: "one"}]:
            self.assertEqual(b"".join(canonical_chunks(item, chunk_size=7)), canonical(item))
            self.assertEqual(stream_digest(item), digest(item))

    def test_large_expression_arrays_are_emitted_in_bounded_chunks(self):
        item = {"expressions": [{"tag": "const", "name": f"declaration_{index}", "levels": []}
                                for index in range(10000)], "declarations": []}
        chunks = list(canonical_chunks(item))
        self.assertGreater(len(chunks), 1)
        self.assertLess(max(map(len, chunks)), 128 * 1024)
        self.assertEqual(b"".join(chunks), canonical(item))

    def test_invalid_chunk_sizes_are_rejected(self):
        with self.assertRaisesRegex(RepositoryError, "invalid json chunk size"):
            list(canonical_chunks({}, chunk_size=0))

    def test_repeated_universe_requirements_share_immutable_storage(self):
        records = [{"tag": "const", "name": f"c{index}", "levels": [{"tag": "param", "name": "u"}]}
                   for index in range(10000)]
        pool = ExpressionPool(records)
        self.assertEqual(len({id(value) for value in pool.parameters}), 1)
        self.assertIsInstance(pool.parameters[0], frozenset)
        self.assertEqual(pool.parameters[-1], {"u"})
        self.assertEqual(pool.references(9999, {"u"}), {"c9999"})
        with self.assertRaisesRegex(RepositoryError, "undeclared universe parameter"):
            pool.references(9999, set())


if __name__ == "__main__":
    unittest.main()
