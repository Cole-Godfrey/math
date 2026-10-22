"""exercise source binding and reject altered derivations and scope metadata."""

import copy
import json
from pathlib import Path
import tempfile
import unittest

from repository.metamath_audit import audit, ProofError, verify_source


root = Path(__file__).parent / 'fixtures/metamath'


class ProofBindingTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.path = Path(self.directory.name) / 'export.jsonl'

    def rows(self, name='saved_subproof'):
        source = root / f'valid-{name}.mm'
        return source, [json.loads(line) for line in source.with_suffix('.jsonl').read_text().splitlines()]

    def check(self, source, rows):
        self.path.write_text(''.join(json.dumps(row) + '\n' for row in rows))
        return audit(source, self.path)

    def test_original_exports_pass(self):
        for name in json.loads((root / 'valid-fixtures.json').read_text()):
            with self.subTest(name=name):
                source, rows = self.rows(name)
                self.assertGreater(self.check(source, rows)['theorems'], 0)

    def test_source_identity_and_summary_tampering_rejected(self):
        source, original = self.rows()
        mutations = [
            lambda r: r[0].update(source_sha256='0' * 64),
            lambda r: r[0].update(database='other.mm'),
            lambda r: r[0].update(schema_version=True),
            lambda r: r[0].update(source_bytes=r[0]['source_bytes'] + 1),
            lambda r: r[0].update(retained_warnings=[{'kind': 'ignored_proof_error'}]),
            lambda r: r[-1].update(assertions=r[-1]['assertions'] - 1),
            lambda r: r[-1].update(proof_nodes=r[-1]['proof_nodes'] + 1),
            lambda r: r[-1]['counts'].update(Provable=True),
            lambda r: r.append(r[-1]),
            lambda r: r.pop(),
            lambda r: r.pop(2),
            lambda r: r[1].update(ordinal=False),
            lambda r: r[1]['source'].update(start=1),
            lambda r: r[1]['source'].update(line=27),
            lambda r: r[1]['source'].update(end_line=28),
            lambda r: r[1].update(unchecked_assumption=True),
        ]
        for index, mutate in enumerate(mutations):
            with self.subTest(case=index):
                rows = copy.deepcopy(original)
                mutate(rows)
                with self.assertRaises(ProofError):
                    self.check(source, rows)

    def test_scope_and_proof_tampering_rejected(self):
        source, original = self.rows()
        mutations = [
            lambda t: t.update(label='other'),
            lambda t: t.update(expression=['wff', 'x']),
            lambda t: t.update(proof=['fx']),
            lambda t: t['frame'].update(hypotheses=['fy']),
            lambda t: t['frame'].update(mandatory_variables=[]),
            lambda t: t['frame'].update(variables=['x', 'y']),
            lambda t: t['frame'].update(mandatory_disjoint=[['x', 'y']]),
            lambda t: t['frame'].update(proof_disjoint=[['x', 'y']]),
            lambda t: t['proof_dag'].update(root=True),
            lambda t: t['proof_dag'].update(root=0),
            lambda t: t['proof_dag']['nodes'][0].update(reference='th'),
            lambda t: t['proof_dag']['nodes'][1].update(arguments=[1, 0]),
            lambda t: t['proof_dag']['nodes'][1].update(arguments=[-1, 0]),
            lambda t: t['proof_dag']['nodes'][1].update(arguments=[True, 0]),
            lambda t: t['proof_dag']['nodes'][1].update(arguments=[0]),
            lambda t: t['proof_dag']['nodes'][1].update(expression_digest='0' * 64),
            lambda t: t['proof_dag']['nodes'].append(copy.deepcopy(t['proof_dag']['nodes'][0])),
        ]
        for index, mutate in enumerate(mutations):
            with self.subTest(case=index):
                rows = copy.deepcopy(original)
                theorem = next(row for row in rows if row.get('label') == 'th')
                mutate(theorem)
                with self.assertRaises(ProofError):
                    self.check(source, rows)

    def test_duplicate_json_fields_rejected(self):
        source, rows = self.rows()
        self.path.write_text(''.join(json.dumps(row) + '\n' for row in rows).replace(
            '"schema_version": 1', '"schema_version": 1, "schema_version": 1', 1))
        with self.assertRaisesRegex(ProofError, 'duplicate json field'):
            audit(source, self.path)

    def test_invalid_sources_rejected(self):
        for path in sorted(root.glob('negative-*.mm')):
            with self.subTest(name=path.name):
                with self.assertRaises(ProofError):
                    verify_source(path.read_bytes())

    def test_distinct_derivations_of_same_statement_rejected(self):
        source, rows = self.rows('distinct_derivations')
        theorem = next(row for row in rows if row.get('label') == 'th')
        theorem['proof_dag']['nodes'][0]['reference'] = 'second'
        with self.assertRaisesRegex(ProofError, 'different derivations'):
            self.check(source, rows)

    def test_math_symbol_and_label_collisions_rejected(self):
        fixtures = [
            '$c p $. p $a p $.',
            '$c p $. ax $a p $. $v ax $.',
            '$c p $. bad:label $a p $.',
            '$c p $. ${ $v x $. $} $c x $.',
        ]
        for text in fixtures:
            with self.subTest(source=text):
                with self.assertRaises(ProofError):
                    verify_source(text)


if __name__ == '__main__':
    unittest.main(verbosity=2)
