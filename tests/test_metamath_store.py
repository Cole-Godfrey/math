"""check native proof access, qualified identities, and atomic snapshot publication."""

import json
from pathlib import Path
import sqlite3
import tempfile
import unittest

from repository.metamath_audit import ProofError
from repository.metamath_store import build, identity, Snapshot


root = Path(__file__).parent / 'fixtures/metamath'


def database(name):
    return {'id': f'valid-{name}.mm', 'source': root / f'valid-{name}.mm',
            'proof': root / f'valid-{name}.jsonl'}


class NativeSnapshotTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.path = Path(self.directory.name)
        self.databases = [database('saved_subproof'), database('compressed_unused_hypothesis')]
        self.receipt = build(self.path, self.databases, {'fixture': True})
        self.snapshot = Snapshot(self.path)
        self.addCleanup(self.snapshot.close)
        self.name = identity(self.databases[0]['id'], 'th')

    def test_database_qualified_labels_do_not_collide(self):
        results = [row for row in self.snapshot.search('th') if row['label'] == 'th']
        self.assertEqual(len(results), 2)
        self.assertEqual(len({row['id'] for row in results}), 2)
        self.assertEqual(len(self.snapshot.search('th', database=self.databases[0]['id'])), 1)
        self.assertEqual(len(self.snapshot.search('', kind='Provable')), 2)

    def test_native_proof_and_source_survive_snapshot(self):
        row = self.snapshot.declaration(self.name)
        proof = self.snapshot.proof(self.name)
        self.assertEqual(proof['tokens'], ['(', 'mkpair', ')', 'AABZCB'])
        self.assertEqual(proof['dag']['nodes'][2]['arguments'], [1, 1])
        self.assertEqual(row['foundation']['database'], self.databases[0]['id'])
        source = self.databases[0]['source'].read_bytes()
        self.assertEqual(self.snapshot.source(self.name), source[row['source_start']:row['source_end']])
        self.assertIn(b'AABZCB', self.snapshot.source(self.name))

    def test_axiom_rules_and_theorem_premises_remain_distinct(self):
        prefix = self.databases[0]['id']
        assumptions = self.snapshot.assumptions(self.name)
        self.assertEqual(assumptions, {'axiom_rules': [identity(prefix, 'mkpair')],
                                       'hypotheses': ['fx'], 'disjoint': []})
        scoped = identity(self.databases[1]['id'], 'th')
        self.assertEqual(self.snapshot.assumptions(scoped)['axiom_rules'], [])
        self.assertEqual(self.snapshot.assumptions(scoped)['hypotheses'], ['wph', 'h'])
        self.assertEqual(self.snapshot.path(scoped, identity(prefix, 'mkpair')), None)

    def test_dependency_paths_include_native_hypothesis_frames(self):
        target = identity(self.databases[0]['id'], 'fy')
        self.assertEqual(self.snapshot.path(self.name, target),
                         [self.name, identity(self.databases[0]['id'], 'mkpair'), target])
        self.assertIn(target, self.snapshot.dependencies(self.name, transitive=True))
        self.assertNotIn(target, self.snapshot.dependencies(self.name))

    def test_database_is_read_only(self):
        with self.assertRaises(sqlite3.OperationalError):
            self.snapshot.connection.execute('delete from declarations')

    def test_complete_search_retains_more_than_fifty_matches(self):
        complete = self.path / 'complete'
        build(complete, [database('many_assertions')], {'fixture': True})
        snapshot = Snapshot(complete)
        try:
            self.assertEqual(len(snapshot.search('ax')), 50)
            self.assertEqual(len(list(snapshot.iter_search('ax'))), 70)
            self.assertEqual(len(list(snapshot.iter_search('ax', limit=1))), 1)
        finally:
            snapshot.close()

    def test_failed_build_retains_last_complete_pointer(self):
        before = (self.path / 'index.json').read_bytes()
        invalid = self.path / 'bad.jsonl'
        invalid.write_text('{}\n')
        with self.assertRaises((ProofError, KeyError)):
            build(self.path, [{**self.databases[0], 'proof': invalid}], {'fixture': True})
        self.assertEqual((self.path / 'index.json').read_bytes(), before)
        self.assertEqual(list(self.path.glob('staging-*')), [])

    def test_changed_verification_inputs_prevent_publication(self):
        before = (self.path / 'index.json').read_bytes()

        def changed():
            raise ProofError('verification input changed')

        with self.assertRaisesRegex(ProofError, 'verification input changed'):
            build(self.path, self.databases, {'fixture': 'changed'}, changed)
        self.assertEqual((self.path / 'index.json').read_bytes(), before)
        self.assertEqual(list(self.path.glob('staging-*')), [])

    def test_modified_archived_proof_is_rejected_on_open(self):
        directory = self.path / self.receipt['directory']
        proof = directory / (self.databases[0]['id'] + '.proof.jsonl')
        proof.write_bytes(proof.read_bytes() + b'\n')
        with self.assertRaisesRegex(ProofError, 'artifact digest differs'):
            Snapshot(self.path)

    def test_manifest_changes_are_rejected(self):
        manifest = self.path / self.receipt['directory'] / 'manifest.json'
        content = json.loads(manifest.read_text())
        content['foundation'] = 'lean'
        manifest.write_text(json.dumps(content))
        with self.assertRaisesRegex(ProofError, 'manifest digest differs'):
            Snapshot(self.path)

    def test_unsafe_identities_and_unknown_labels_are_rejected(self):
        for name in ['../bad.mm', '/tmp/bad.mm', 'x:y.mm']:
            with self.subTest(database=name):
                with self.assertRaises(ProofError):
                    identity(name, 'th')
        with self.assertRaisesRegex(ProofError, 'unknown declaration'):
            self.snapshot.declaration(identity('missing.mm', 'th'))
        with self.assertRaises(ProofError):
            self.snapshot.search('', limit=True)


if __name__ == '__main__':
    unittest.main(verbosity=2)
