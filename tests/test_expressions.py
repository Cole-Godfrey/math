"""compare compact proof terms with the existing lossless json and term audits."""
import io
import json
import random
import unittest

from repository.core import ExpressionPool, canonical
from repository.json_reader import read_object
from repository.expressions import PackedExpressions
import repository.core as core


def read_compact(stream, chunk_size=64 * 1024):
    return read_object(stream, chunk_size, compact_expressions=True)


def packed(records):
    result = PackedExpressions()
    for record in records:
        result.append(record)
    return result.seal()


def terms():
    return [
        {'tag': 'sort', 'level': {'tag': 'zero'}},
        {'tag': 'bvar', 'index': 0},
        {'tag': 'lam', 'name': 'x', 'binder': 'implicit', 'type': 0, 'body': 1},
        {'tag': 'forall', 'name': 'x', 'binder': 'strict_implicit', 'type': 0, 'body': 1},
        {'tag': 'nat', 'value': (1 << 64) - 1},
        {'tag': 'string', 'value': '𝓞 ℚ → ℝ\n"\\'},
        {'tag': 'const', 'name': 'c', 'levels': [{'tag': 'param', 'name': 'u'}]},
        {'tag': 'app', 'function': 6, 'argument': 4},
        {'tag': 'let', 'name': 'd', 'nondependent': False, 'type': 0, 'value': 4, 'body': 1},
        {'tag': 'proj', 'name': 'Product', 'index': 0, 'expression': 7},
        {'tag': 'sort', 'level': {'tag': 'imax', 'left': {'tag': 'succ', 'of': {'tag': 'zero'}},
                                  'right': {'tag': 'max', 'left': {'tag': 'param', 'name': 'u'},
                                            'right': {'tag': 'param', 'name': 'v'}}}},
    ]


class PackedExpressionTests(unittest.TestCase):
    def test_list_equality_and_complete_canonical_encoding_remain_available(self):
        records = terms()
        result = packed(records)
        self.assertEqual(result, records)
        self.assertEqual(records, result)
        self.assertEqual(result, packed(records))
        self.assertNotEqual(result, records[:-1])
        self.assertNotEqual(result, [{'tag': 'nat', 'value': 0}, *records[1:]])
        self.assertNotEqual(result, tuple(records))
        self.assertEqual(canonical({'expressions': result}), canonical({'expressions': records}))

    def test_query_store_and_receipt_are_byte_identical_for_packed_terms(self):
        import hashlib
        from pathlib import Path
        import tempfile
        from repository.store import create_store, file_digest, open_snapshot
        from store_fixture import fixture

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            catalog, receipt = fixture(root)
            compact = {**catalog, 'expressions': packed(catalog['expressions'])}
            complete = b''.join(core.canonical_chunks(compact)) + b'\n'
            self.assertEqual(hashlib.sha256(complete).hexdigest(), receipt['catalog_file_digest'])
            current = create_store(root / 'build', compact,
                {'Math.Fixture': (root / 'Math/Fixture.lean').read_text()},
                file_digest(root / 'build/knowledge.json'))
            self.assertEqual(current, receipt)
            self.assertEqual(b''.join(open_snapshot(root).catalog_chunks()), complete)

    def test_every_expression_constructor_and_universe_annotation_round_trips(self):
        records = terms()
        result = packed(records)
        self.assertEqual(list(result), records)
        self.assertEqual(result.fallback_records, 0)
        for before, after in zip(records, result):
            self.assertEqual(canonical(before), canonical(after))

    def test_annotations_extra_fields_and_large_literals_are_retained(self):
        records = [
            {'tag': 'nat', 'value': 1 << 64}, {'tag': 'nat', 'value': 10 ** 5000},
            {'tag': 'bvar', 'index': True}, {'tag': 'app', 'function': -1, 'argument': 0},
            {'tag': 'let', 'name': 'x', 'nondependent': 1, 'type': 0, 'value': 0, 'body': 0},
            {'tag': 'nat', 'value': 1, 'annotation': {'retained': [True, None, 'λ']}},
            {'tag': 'const', 'name': 'c', 'levels': None}, {'tag': None},
            {'tag': 'future', 'payload': {'x': 'y'}}, None, False, 1.5, ['expression'],
        ]
        result = packed(records)
        self.assertGreater(result.fallback_records, 0)
        self.assertEqual(list(result), records)
        self.assertEqual(canonical(list(result)), canonical(records))

    def test_mutating_inputs_or_returned_records_cannot_change_sealed_proof_terms(self):
        records = terms()
        result = packed(records)
        expected = json.loads(canonical(records))
        records[6]['levels'][0]['name'] = 'changed'
        record = result[6]
        record['levels'][0]['name'] = 'also changed'
        record['name'] = 'new'
        self.assertEqual(list(result), expected)
        with self.assertRaises(TypeError):
            result.append({'tag': 'nat', 'value': 0})
        with self.assertRaises(TypeError):
            result[0] = {'tag': 'nat', 'value': 0}

    def test_sequence_index_and_slice_semantics_match_a_list(self):
        records = terms()
        result = packed(records)
        for index in range(-len(records), len(records)):
            self.assertEqual(result[index], records[index])
        for index in [slice(None), slice(None, None, -1), slice(-7, -2, 2), True, False]:
            self.assertEqual(result[index], records[index])
        for index in [-len(records) - 1, len(records), 10 ** 30]:
            with self.assertRaises(IndexError):
                result[index]
        with self.assertRaises(TypeError):
            result['0']

    def test_streaming_boundaries_preserve_complete_records_and_metadata(self):
        original = {'expressions': terms(), 'metadata': {'unicode': 'ℂ', 'array': [0, 1, 2]}}
        encoded = canonical(original).decode()
        for size in [1, 2, 3, 7, 31, 65536]:
            with self.subTest(size=size):
                result = read_compact(io.StringIO(encoded), size)
                self.assertIsInstance(result['expressions'], PackedExpressions)
                self.assertEqual(list(result['expressions']), original['expressions'])
                self.assertEqual(result['metadata'], original['metadata'])

    def test_duplicate_keys_and_trailing_data_still_reject(self):
        invalid = ['{"expressions":[{"tag":"nat","tag":"bvar","value":0}]}',
                   '{"expressions":[],"expressions":[]}', '{"expressions":[]}false',
                   '{"expressions":[}', '{"expressions":[0,]}']
        for encoded in invalid:
            for size in [1, 7, 65536]:
                with self.subTest(encoded=encoded, size=size):
                    with self.assertRaises(ValueError):
                        read_object(io.StringIO(encoded), size)
                    with self.assertRaises(ValueError):
                        read_compact(io.StringIO(encoded), size)

    def test_existing_term_hashes_scope_and_universe_requirements_are_identical(self):
        records = terms()
        before = ExpressionPool(records)
        after = core.ExpressionPool(packed(records))
        self.assertEqual(before.hashes, after.hashes)
        self.assertEqual(before.loose, after.loose)
        self.assertEqual(before.parameters, after.parameters)
        for root, universes in [(2, set()), (3, set()), (7, {'u'}), (8, set()), (9, {'u'}), (10, {'u', 'v'})]:
            self.assertEqual(before.references(root, universes), after.references(root, universes))
        for pool in [before, after]:
            with self.assertRaisesRegex(ValueError, 'unbound variable'):
                pool.references(1, set())
            with self.assertRaisesRegex(ValueError, 'undeclared universe parameter'):
                pool.references(7, set())

    def test_invalid_terms_produce_the_same_audit_failure(self):
        invalid = [
            {'tag': 'app', 'function': True, 'argument': 0},
            {'tag': 'app', 'function': 0, 'argument': 2},
            {'tag': 'bvar', 'index': -1}, {'tag': 'bvar', 'index': True},
            {'tag': 'const', 'name': 'c', 'levels': {}},
            {'tag': 'const', 'name': '', 'levels': []},
            {'tag': 'lam', 'name': 'x', 'binder': 'bad', 'type': 0, 'body': 0},
            {'tag': 'let', 'name': 'x', 'nondependent': 0, 'type': 0, 'value': 0, 'body': 0},
            {'tag': 'sort', 'level': {'tag': 'unresolved'}}, {'tag': 'mvar', 'name': 'x'},
        ]
        compact = core
        for record in invalid:
            errors = []
            records = [terms()[0], record]
            for pool, data in [(ExpressionPool, records), (compact.ExpressionPool, packed(records))]:
                with self.assertRaises(ValueError) as caught:
                    pool(data)
                errors.append(str(caught.exception))
            self.assertEqual(errors[0], errors[1])

    def test_canonical_catalog_streams_remain_byte_identical(self):
        original = {'expressions': terms(), 'declarations': [], 'metadata': {'a': 'λ'}}
        result = {**original, 'expressions': packed(original['expressions'])}
        compact = core
        for size in [1, 7, 65536]:
            self.assertEqual(b''.join(compact.canonical_chunks(result, chunk_size=size)), canonical(original))

    def test_random_json_extensions_never_lose_fields_or_values(self):
        rng = random.Random(20261023)
        records = []
        for index in range(1000):
            record = dict(rng.choice(terms()))
            if rng.randrange(2):
                record['extension'] = [index, 'λ', None, bool(index % 2)]
            if rng.randrange(3) == 0:
                record['value'] = rng.choice([None, True, -1, 1 << 100, 'u', -1.25e-30])
            records.append(record)
        self.assertEqual(list(packed(records)), records)


def encode(records):
    packed = PackedExpressions()
    for record in records:
        packed.append(record)
    packed.seal()
    before = (bytes(packed._tags), packed._offsets.tobytes(), packed._slots.tobytes(),
              tuple(packed._atoms))
    result = b''.join(core.canonical_chunks(packed))
    after = (bytes(packed._tags), packed._offsets.tobytes(), packed._slots.tobytes(),
             tuple(packed._atoms))
    assert after == before
    return result


class PackedEncoderTests(unittest.TestCase):
    def assert_canonical(self, records):
        expected = json.dumps(records, sort_keys=True, ensure_ascii=False,
                              separators=(',', ':')).encode('utf-8')
        self.assertEqual(encode(records), expected)

    def test_every_term_form_and_atom_kind_remains_exact(self):
        self.assert_canonical([
            {'tag': 'bvar', 'index': 0},
            {'tag': 'sort', 'level': {'tag': 'imax', 'left': {'tag': 'zero'},
                                      'right': {'tag': 'param', 'name': 'u'}}},
            {'tag': 'const', 'name': '[]', 'levels': []},
            {'tag': 'const', 'name': 'Nat.δ', 'levels': [{'tag': 'param', 'name': 'u'}]},
            {'tag': 'app', 'function': 0, 'argument': (1 << 64) - 1},
            {'tag': 'lam', 'name': '"\n\x00\\𐍈', 'binder': 'implicit', 'type': 0, 'body': 9},
            {'tag': 'forall', 'name': 'x', 'binder': 'strictImplicit', 'type': 3, 'body': 7},
            {'tag': 'let', 'name': 'x', 'nondependent': True, 'type': 1, 'value': 2, 'body': 3},
            {'tag': 'let', 'name': 'x', 'nondependent': False, 'type': 1, 'value': 2, 'body': 3},
            {'tag': 'proj', 'name': 'α.β', 'index': 1, 'expression': 23},
            {'tag': 'nat', 'value': (1 << 64) - 1},
            {'tag': 'string', 'value': '\u2028\u2029\U0010ffff\t\r\n\b\f"\\é'},
        ])

    def test_large_integers_and_unfamiliar_records_remain_exact(self):
        self.assert_canonical([
            {'tag': 'nat', 'value': 1 << 64},
            {'tag': 'nat', 'value': (1 << 2048) + 17},
            {'tag': 'nat', 'value': -1},
            {'tag': 'nat', 'value': True},
            {'tag': 'app', 'function': False, 'argument': 0},
            {'tag': 'let', 'name': 'x', 'nondependent': 1, 'type': 1, 'value': 2, 'body': 3},
            {'tag': 'app', 'function': 1, 'argument': 2, 'future_field': [False, None]},
            {'tag': 'future', 'data': {'β': [1, -0.0, True], 'a': '\x00'}},
            {'tag': ['unexpected'], 'value': 1},
            {}, [], [1, {'x': False}], None, False, 'quoted " text', -0.0,
        ])

    def test_empty_and_repeated_records_remain_exact(self):
        self.assert_canonical([])
        self.assert_canonical([{'tag': 'const', 'name': 'x', 'levels': []}] * 1024)

    def test_arbitrary_json_extensions_retain_every_field(self):
        rng = random.Random(541072)
        atoms = [None, False, True, 0, -1, (1 << 127) + 3, 1.5, -0.0,
                 '', '[]', '"', '\x00', 'λ', '𐍈', '\\']

        def value(depth):
            kind = rng.randrange(3) if depth else 0
            if kind == 0:
                return rng.choice(atoms)
            if kind == 1:
                return [value(depth - 1) for _ in range(rng.randrange(5))]
            return {str(rng.randrange(20)) + rng.choice(['', 'λ', '"']): value(depth - 1)
                    for _ in range(rng.randrange(5))}

        self.assert_canonical([value(4) for _ in range(4096)])


if __name__ == '__main__':
    unittest.main(verbosity=2)
