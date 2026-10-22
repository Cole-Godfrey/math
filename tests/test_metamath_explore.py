"""retain native proof-system boundaries in browser search and dependency views."""

from concurrent.futures import ThreadPoolExecutor
import io
import tarfile
from pathlib import Path
import tempfile
import unittest

from repository.core import RepositoryError
from repository.metamath_explore import NativeExplorer
from repository.metamath_store import build, identity, Snapshot


FIXTURES = Path(__file__).parent / 'fixtures/metamath'


class NativeExplorerTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        databases = []
        for name in ['saved_subproof', 'compressed_unused_hypothesis', 'many_assertions']:
            databases.append({'id': f'valid-{name}.mm', 'source': FIXTURES / f'valid-{name}.mm',
                              'proof': FIXTURES / f'valid-{name}.jsonl'})
        build(self.directory.name, databases, {'fixture': True})
        self.archive = Snapshot(self.directory.name)
        self.addCleanup(self.archive.close)
        self.explorer = NativeExplorer(self.archive)
        self.database = 'valid-saved_subproof.mm'
        self.name = identity(self.database, 'th')

    def test_native_declarations_keep_exact_statements_and_local_hypotheses(self):
        node = self.explorer.declaration(self.name, proof=True)
        self.assertEqual(node['proof_system'], 'metamath')
        self.assertEqual(node['kind'], 'theorem')
        self.assertEqual(node['statement_tokens'], ['wff', 'pair', 'pair', 'x', 'x', 'pair', 'x', 'x'])
        self.assertEqual(node['proof'], '( mkpair ) AABZCB')
        self.assertEqual(node['hypotheses'], [identity(self.database, 'fx')])
        self.assertEqual(node['axioms'], [identity(self.database, 'mkpair')])
        self.assertEqual(node['foundation']['database'], self.database)
        source = (FIXTURES / self.database).read_bytes()
        span = node['source']
        self.assertEqual(source[span['byte_start']:span['byte_end']], self.archive.source(self.name))
        self.assertEqual(span['line'], 1 + source[:span['byte_start']].count(b'\n'))
        self.assertEqual(span['end_line'], 1 + source[:span['byte_end']].count(b'\n'))
        self.assertNotIn('column', span)
        hypothesis = self.explorer.declaration(identity(self.database, 'fx'))
        self.assertTrue(hypothesis['bound_assumption'])
        self.assertFalse(hypothesis['selected'])
        self.assertEqual(hypothesis['selected_modules'], [])

    def test_search_pages_retain_every_result_and_parameter_visibility(self):
        page = self.explorer.search('ax', limit=30)
        self.assertEqual(page['total'], 70)
        names = []
        for offset in [0, 30, 60]:
            names.extend(row['name'] for row in self.explorer.search('ax', offset=offset)['items'])
        self.assertEqual(len(names), len(set(names)))
        self.assertEqual(len(names), 70)
        self.assertEqual(self.explorer.search('fx')['total'], 0)
        self.assertEqual(self.explorer.search('fx', include_dependencies=True)['total'], 1)
        self.assertEqual(self.explorer.search('th', subject='metamath-db:' + self.database)['total'], 1)

    def test_dependency_roles_and_reverse_traversal_match_native_frames(self):
        floating = identity(self.database, 'fx')
        rule = identity(self.database, 'mkpair')
        self.assertEqual([node['name'] for node in self.explorer.relations(self.name, role='type')['items']], [floating])
        self.assertEqual([node['name'] for node in self.explorer.relations(self.name, role='value')['items']], [rule])
        self.assertIn(self.name, [node['name'] for node in self.explorer.relations(rule, reverse=True)['items']])
        self.assertIn(identity(self.database, 'fy'),
                      [node['name'] for node in self.explorer.relations(self.name, transitive=True)['items']])

    def test_hierarchy_keeps_each_native_axiom_path_and_scoped_hypothesis(self):
        graph = self.explorer.hierarchy(self.name)
        self.assertEqual(graph['foundation']['database'], self.database)
        self.assertEqual(graph['axiom_paths'][identity(self.database, 'mkpair')],
                         [self.name, identity(self.database, 'mkpair')])
        groups = {group['id']: group for group in graph['groups']}
        for group in groups.values():
            for child in group['dependencies']:
                self.assertLess(groups[child]['level'], group['level'])
        local = self.explorer.hierarchy(identity(self.database, 'fx'))
        self.assertEqual(len(local['declarations']), 1)
        self.assertEqual(local['axioms'], [])

    def test_source_pages_preserve_every_archived_line(self):
        page = self.explorer.source(self.name, line=1, limit=1)
        self.assertEqual(page['lines'], (FIXTURES / ('valid-saved_subproof.mm')).read_text().splitlines())
        with self.assertRaises(RepositoryError):
            self.explorer.source(self.name, full=True)
        with self.assertRaises(RepositoryError):
            self.explorer.source(self.name, line=0)

    def test_independent_requests_do_not_share_sqlite_connections(self):
        with ThreadPoolExecutor(max_workers=4) as executor:
            statements = list(executor.map(lambda _: self.explorer.declaration(self.name)['statement'], range(32)))
        self.assertEqual(len(set(statements)), 1)

    def test_foundations_distinguish_theorem_premises_from_assumed_rules(self):
        data = self.explorer.foundations(self.name)
        self.assertEqual([node['name'] for node in data['hypotheses']], [identity(self.database, 'fx')])
        self.assertEqual([node['name'] for node in data['items']], [identity(self.database, 'mkpair')])
        self.assertEqual(data['items'][0]['path'], [self.name, identity(self.database, 'mkpair')])
        local = self.explorer.foundations(identity(self.database, 'fx'))
        self.assertTrue(local['bound_assumption'])
        self.assertEqual(local['items'], [])

    def test_complete_download_reconstructs_the_native_archive(self):
        output = b''.join(self.explorer.archive_chunks())
        with tempfile.TemporaryDirectory() as directory:
            with tarfile.open(fileobj=io.BytesIO(output), mode='r:') as archive:
                for member in archive.getmembers():
                    self.assertTrue(member.isfile())
                    self.assertNotIn('..', member.name.split('/'))
                archive.extractall(directory)
            snapshot = Snapshot(directory)
            try:
                self.assertEqual(snapshot.digest, self.archive.digest)
                self.assertEqual(snapshot.proof(self.name), self.archive.proof(self.name))
            finally:
                snapshot.close()


if __name__ == '__main__':
    unittest.main()
