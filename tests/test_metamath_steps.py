"""match displayed native substitutions to the admitted source derivation."""

import json
from pathlib import Path
import tempfile
import unittest

from repository.core import RepositoryError
from repository.metamath_steps import NativeSteps
from repository.metamath_store import build, identity, Snapshot


FIXTURES = Path(__file__).parent / 'fixtures/metamath'


class NativeStepTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        databases = [{'id': 'valid-' + name + '.mm', 'source': FIXTURES / ('valid-' + name + '.mm'),
                      'proof': FIXTURES / ('valid-' + name + '.jsonl')}
                     for name in json.loads((FIXTURES / 'valid-fixtures.json').read_text())]
        build(self.directory.name, databases, {'fixture': True})
        self.archive = Snapshot(self.directory.name)
        self.addCleanup(self.archive.close)
        self.steps = NativeSteps(self.archive)

    def name(self, fixture, label='th'):
        return identity('valid-' + fixture + '.mm', label)

    def test_every_positive_fixture_reconstructs_its_exact_conclusion(self):
        for row in self.archive.connection.execute("select id from declarations where kind='Provable'"):
            with self.subTest(name=row[0]):
                data = self.steps.inspect(row[0])
                self.assertEqual(data['focused']['expression_tokens'], self.archive.declaration(row[0])['expression'])

    def test_shared_saved_steps_preserve_ordered_argument_occurrences(self):
        data = self.steps.inspect(self.name('saved_subproof'))
        self.assertEqual(data['focused']['arguments'], [1, 1])
        self.assertEqual([step['index'] for step in data['arguments']], [1, 1])
        self.assertEqual(data['arguments'][0]['expression_tokens'], ['wff', 'pair', 'x', 'x'])
        self.assertEqual(data['focused']['reference'], self.name('saved_subproof', 'mkpair'))

    def test_unused_and_proof_local_hypotheses_keep_their_scope(self):
        data = self.steps.inspect(self.name('compressed_unused_optional_hypothesis'))
        contexts = {row['name']: row for row in data['context']}
        self.assertTrue(contexts[self.name('compressed_unused_optional_hypothesis', 'wph')]['mandatory'])
        self.assertFalse(contexts[self.name('compressed_unused_optional_hypothesis', 'wps')]['mandatory'])
        self.assertEqual(data['frame']['hypotheses'], ['wph', 'h'])

    def test_hypotheses_and_assumed_rules_are_not_displayed_as_proofs(self):
        for name in [self.name('saved_subproof', 'mkpair'), self.name('saved_subproof', 'fx')]:
            with self.subTest(name=name):
                data = self.steps.inspect(name)
                self.assertIsNone(data['root'])
                self.assertIsNone(data['focused'])
                self.assertEqual(data['step_count'], 0)

    def test_inspection_rejects_invalid_steps_and_does_not_mutate_cached_proofs(self):
        name = self.name('saved_subproof')
        for step in [-1, True, 3]:
            with self.subTest(step=step), self.assertRaises(RepositoryError):
                self.steps.inspect(name, step)
        data = self.steps.inspect(name)
        data['focused']['expression_tokens'].clear()
        data['frame']['hypotheses'].clear()
        self.assertTrue(self.steps.inspect(name)['focused']['expression_tokens'])
        self.assertEqual(self.steps.inspect(name)['frame']['hypotheses'], ['fx'])

    def test_same_statement_with_another_axiom_derivation_is_rejected(self):
        database = 'valid-distinct_derivations.mm'
        file = self.archive.directory / (database + '.proof.jsonl')
        data = file.read_bytes()
        self.assertEqual(data.count(b'"reference":"first"'), 1)
        file.write_bytes(data.replace(b'"reference":"first"', b'"reference":"second"', 1))
        with self.assertRaisesRegex(RepositoryError, 'displayed derivation differs'):
            self.steps.inspect(identity(database, 'th'))


if __name__ == '__main__':
    unittest.main()
