"""check source identities, lexical side conditions, and complete symbol relationships."""

from concurrent.futures import ThreadPoolExecutor
import copy
import json
from pathlib import Path
import sqlite3
import tempfile
import unittest

from repository.metamath_audit import ProofError
from repository.metamath_primitives import project
from repository.metamath_store import build, identity, Snapshot


FIXTURES = Path(__file__).parent / 'fixtures/metamath'


class NativePrimitiveTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.path = Path(self.directory.name)
        databases = [{'id': 'valid-' + name + '.mm', 'source': FIXTURES / ('valid-' + name + '.mm'),
                      'proof': FIXTURES / ('valid-' + name + '.jsonl')}
                     for name in ['variable_reuse', 'constant_disjoint_substitution', 'scoped_essential',
                                  'saved_subproof', 'disjoint_scopes', 'many_assertions']]
        build(self.path, databases, {'fixture': True})
        self.snapshot = Snapshot(self.path)
        self.addCleanup(self.snapshot.close)

    def name(self, fixture, label):
        return identity('valid-' + fixture + '.mm', label)

    def symbols(self, fixture, token):
        return [row for row in self.snapshot.primitives(token, 'valid-' + fixture + '.mm')['items']
                if row['token'] == token]

    def test_redeclared_variables_resolve_to_distinct_lexical_objects(self):
        symbols = self.symbols('variable_reuse', 'x')
        self.assertEqual(len(symbols), 2)
        self.assertNotEqual(symbols[0]['identifier'], symbols[1]['identifier'])
        self.assertNotEqual(symbols[0]['scope_id'], symbols[1]['scope_id'])
        first = self.snapshot.primitive(self.name('variable_reuse', 'first'))
        second = self.snapshot.primitive(self.name('variable_reuse', 'second'))
        theorem = self.snapshot.primitive(self.name('variable_reuse', 'th'))
        self.assertEqual(first['record']['tokens'][1], symbols[0]['identifier'])
        self.assertEqual(second['record']['tokens'][1], symbols[1]['identifier'])
        self.assertEqual(theorem['record']['tokens'][1], symbols[1]['identifier'])

    def test_repeated_symbol_occurrences_and_all_pages_preserve_positions(self):
        symbol = self.symbols('constant_disjoint_substitution', 'c')[0]['identifier']
        complete = self.snapshot.primitive_relations(symbol, True, 'expression_symbol')
        occurrences = [row['position'] for row in complete['items']
                       if row['source'] == self.name('constant_disjoint_substitution', 'th')]
        self.assertEqual(occurrences, [2, 3])
        pages = [self.snapshot.primitive_relations(symbol, True, 'expression_symbol', i, 1)
                 for i in range(complete['total'])]
        self.assertEqual([item for page in pages for item in page['items']], complete['items'])
        self.assertTrue(all(page['total'] == complete['total'] for page in pages))
        self.assertEqual(self.snapshot.primitive_relations(symbol, True, offset=complete['total'])['items'], [])

    def test_mandatory_and_proof_disjoint_constraints_link_original_source_clauses(self):
        rule = self.snapshot.primitive(self.name('constant_disjoint_substitution', 'mkpair'))['record']
        theorem = self.snapshot.primitive(self.name('constant_disjoint_substitution', 'th'))['record']
        self.assertEqual(theorem['mandatory_disjoint'], [])
        self.assertEqual(theorem['proof_disjoint'], rule['proof_disjoint'])
        self.assertEqual(rule['mandatory_disjoint'], rule['proof_disjoint'])
        clause = rule['mandatory_disjoint'][0]['clause']
        self.assertEqual(self.snapshot.primitive_source(clause), b' $d x y $.')
        source_variables = self.snapshot.primitive(clause)['record']['variables']
        self.assertEqual(set(source_variables), set(rule['mandatory_disjoint'][0]['variables']))
        self.assertEqual(self.snapshot.assumptions(self.name('constant_disjoint_substitution', 'th'))['disjoint'], [])

    def test_duplicate_nested_disjoint_clauses_keep_live_outer_witnesses(self):
        def binding(label):
            return self.snapshot.primitive(self.name('disjoint_scopes', label))['record']
        parent = binding('outer')['proof_disjoint']
        self.assertEqual(binding('inside')['proof_disjoint'], parent)
        self.assertEqual(binding('after')['proof_disjoint'], parent)
        first, second = binding('scoped')['mandatory_disjoint'], binding('scoped2')['mandatory_disjoint']
        self.assertNotEqual(first[0]['clause'], second[0]['clause'])
        z1 = next(name for name in first[0]['variables'] if self.snapshot.primitive(name)['token'] == 'z')
        z2 = next(name for name in second[0]['variables'] if self.snapshot.primitive(name)['token'] == 'z')
        self.assertNotEqual(z1, z2)
        self.assertNotIn(z1, binding('scoped2')['frame_variables'])
        self.assertEqual(self.snapshot.primitive_source(first[0]['clause']).strip(), b'$d x z $.')
        self.assertEqual(self.snapshot.primitive_source(second[0]['clause']).strip(), b'$d y z $.')

    def test_source_context_and_exact_scope_block_are_available(self):
        name = self.name('scoped_essential', 'nested')
        context = self.snapshot.primitive_context(name)
        self.assertEqual(len(context['scopes']), 2)
        local, global_scope = context['scopes']
        source = (FIXTURES / 'valid-scoped_essential.mm').read_bytes()
        self.assertEqual(self.snapshot.primitive_source(local['identifier']),
                         b' ${ h $e |- ph $. nested $p |- ph $= h $. $}')
        self.assertEqual(self.snapshot.primitive_source(global_scope['identifier']), source)
        self.assertEqual(self.snapshot.primitive_source(local['identifier'], full=True), source)
        self.assertEqual(context['object']['record']['scope'], local['identifier'])
        members = self.snapshot.primitive_relations(local['identifier'], True, 'source_scope')['items']
        self.assertEqual({row['source'] for row in members},
                         {self.name('scoped_essential', 'h'), self.name('scoped_essential', 'nested')})

    def test_binding_edges_retain_ordered_hypotheses_and_mandatory_variables(self):
        name = self.name('scoped_essential', 'nested')
        binding = self.snapshot.primitive(name)['record']
        node = self.snapshot.declaration(name)
        self.assertEqual(binding['hypotheses'], [self.name('scoped_essential', label)
                                                for label in node['frame']['hypotheses']])
        tokens = [self.snapshot.primitive(identifier)['token'] for identifier in binding['mandatory_variables']]
        self.assertEqual(tokens, node['frame']['mandatory_variables'])
        links = self.snapshot.primitive_relations(name, relation='mandatory_hypothesis')['items']
        self.assertEqual([row['target'] for row in links], binding['hypotheses'])
        self.assertEqual([row['position'] for row in links], list(range(len(links))))

    def test_complete_binding_search_keeps_every_assertion(self):
        results = self.snapshot.primitives(database='valid-many_assertions.mm', kind='assertion_symbols')
        self.assertEqual(results['total'], 71)
        self.assertEqual(len(results['items']), 71)
        first = self.snapshot.primitives(database='valid-many_assertions.mm', kind='assertion_symbols', limit=1)
        self.assertEqual(len(first['items']), 1)
        self.assertEqual(first['total'], 71)
        self.assertTrue(all(row['kind'] != 'assertion_symbols' for row in self.snapshot.primitives()['items']))

    def test_query_validation_and_unknown_primitive_identities_fail(self):
        name = self.name('saved_subproof', 'th')
        for options in [{'offset': -1}, {'offset': True}, {'offset': 2 ** 63}, {'limit': 0}, {'limit': True},
                        {'kind': 'axiom'}, {'database': 'missing.mm'}]:
            with self.subTest(options=options), self.assertRaises(ProofError):
                self.snapshot.primitives(**options)
        for options in [{'reverse': 1}, {'relation': 'axiom'}, {'limit': -1}]:
            with self.subTest(options=options), self.assertRaises(ProofError):
                self.snapshot.primitive_relations(name, **options)
        with self.assertRaisesRegex(ProofError, 'unknown source primitive'):
            self.snapshot.primitive('metamath-symbol:missing.mm:0:0')

    def test_primitive_rows_are_bound_to_the_content_addressed_artifact(self):
        connection = sqlite3.connect(self.snapshot.directory / 'index.sqlite')
        connection.execute("update primitive_objects set token='changed' where kind='constant'")
        connection.commit()
        connection.close()
        with self.assertRaisesRegex(ProofError, 'artifact digest differs'):
            Snapshot(self.path)

    def test_request_local_readers_do_not_share_mutable_primitive_records(self):
        name = self.name('saved_subproof', 'th')
        def read(_):
            with self.snapshot.reader() as reader:
                result = reader.primitive(name)
                result['record']['tokens'].clear()
                return reader.primitive(name)['record']['tokens']
        with ThreadPoolExecutor(max_workers=4) as pool:
            results = list(pool.map(read, range(12)))
        self.assertTrue(all(value and value == results[0] for value in results))

    def test_primitive_projection_rejects_missing_or_out_of_scope_side_conditions(self):
        path = FIXTURES / 'valid-disjoint_scopes.jsonl'
        original = [json.loads(line) for line in path.read_text().splitlines()][1:]
        for field in ['mandatory_disjoint', 'proof_disjoint']:
            rows = copy.deepcopy(original)
            row = next(row for row in rows if row.get('label') == 'after')
            row['frame'][field] = [['x', 'z']]
            with self.subTest(field=field), self.assertRaisesRegex(ProofError, 'not active'):
                project('valid-disjoint_scopes.mm', rows, lambda row: None)
        with self.assertRaisesRegex(ProofError, 'incomplete'):
            project('valid-disjoint_scopes.mm', original[:-1], lambda row: None)


if __name__ == '__main__':
    unittest.main()
