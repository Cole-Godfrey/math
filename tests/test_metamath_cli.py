"""exercise native statements, assumptions, proof downloads, and complete hierarchies."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from repository.metamath_store import build, identity


ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'tests/fixtures/metamath'


class NativeCliTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        name = 'valid-saved_subproof'
        build(self.directory.name, [{'id': name + '.mm', 'source': FIXTURES / (name + '.mm'),
                                    'proof': FIXTURES / (name + '.jsonl')}], {'fixture': True})
        self.name = identity(name + '.mm', 'th')

    def command(self, *arguments):
        return subprocess.run([sys.executable, '-m', 'repository.metamath', '--snapshot', self.directory.name,
                               *arguments], cwd=ROOT, capture_output=True)

    def output(self, *arguments):
        result = self.command(*arguments)
        self.assertEqual(result.returncode, 0, result.stderr)
        return json.loads(result.stdout)

    def test_stats_and_search_report_native_database_identity(self):
        self.assertEqual(self.output('stats')['counts']['Provable'], 1)
        result = self.output('search', 'th')
        self.assertEqual(result[0]['id'], self.name)
        self.assertEqual(self.output('show', self.name)['foundation']['proof_system'], 'metamath')

    def test_proof_and_source_preserve_exact_native_steps(self):
        self.assertEqual(self.output('proof', self.name)['tokens'], ['(', 'mkpair', ')', 'AABZCB'])
        result = self.command('source', self.name)
        self.assertEqual(result.returncode, 0)
        self.assertIn(b'AABZCB', result.stdout)
        self.assertNotIn(b'\n', result.stdout)
        result = self.command('source', self.name, '--full')
        self.assertEqual(result.returncode, 0)
        self.assertEqual(result.stdout, (FIXTURES / 'valid-saved_subproof.mm').read_bytes())

    def test_hierarchy_and_trace_resolve_every_native_axiom(self):
        hierarchy = self.output('hierarchy', self.name)
        declared = {node['name']: node for node in hierarchy['declarations']}
        for node in declared.values():
            for child in node['dependencies']:
                self.assertLess(declared[child]['level'], node['level'])
        axioms = self.output('assumptions', self.name)['axiom_rules']
        self.assertEqual(len(axioms), 1)
        self.assertEqual(self.output('trace', self.name, axioms[0]), [self.name, axioms[0]])
        self.assertEqual(set(self.output('deps', self.name, '--transitive')), set(declared) - {self.name})

    def test_unknown_declarations_and_invalid_search_limits_fail(self):
        self.assertNotEqual(self.command('show', self.name + '-missing').returncode, 0)
        self.assertNotEqual(self.command('search', '--limit', '0').returncode, 0)

    def test_source_primitive_queries_preserve_ordered_occurrences(self):
        result = self.output('primitives', 'x', '--kind', 'variable')
        symbol = result['items'][0]['identifier']
        self.assertEqual(self.output('primitive', symbol)['token'], 'x')
        links = self.output('primitive-relations', symbol, '--reverse', '--relation', 'expression_symbol')
        self.assertEqual([row['position'] for row in links['items'] if row['source'] == self.name], [3, 4, 6, 7])
        self.assertEqual(len(self.output('primitive-context', self.name)['scopes']), 1)

    def test_source_primitive_download_and_invalid_relations(self):
        name = self.output('primitives', 'wff', '--kind', 'constant')['items'][0]['identifier']
        source = self.command('primitive-source', name)
        self.assertEqual(source.returncode, 0, source.stderr)
        self.assertEqual(source.stdout, b'$c wff pair $.')
        full = self.command('primitive-source', name, '--full')
        self.assertEqual(full.stdout, (FIXTURES / 'valid-saved_subproof.mm').read_bytes())
        self.assertNotEqual(self.command('primitive-relations', name, '--relation', 'axiom').returncode, 0)


if __name__ == '__main__':
    unittest.main()
