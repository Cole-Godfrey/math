"""reject current-worktree queries after verified inputs change."""

from pathlib import Path
import tempfile
import unittest

from repository.build import input_hashes
from repository.core import RepositoryError
from repository.metamath_build import open_snapshot
from repository.metamath_store import build
from tests.store_fixture import fixture


FIXTURES = Path(__file__).parent / 'fixtures/metamath'


class NativeQueryBindingTests(unittest.TestCase):
    def test_changed_current_verification_source_rejects_native_index(self):
        for relative in ['Math/Fixture.lean', 'knowledge.json', 'repository/checker.py']:
            with self.subTest(input=relative), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                fixture(root)
                verifier = root / 'repository/checker.py'
                verifier.parent.mkdir()
                verifier.write_text('value = 1\n')
                source = FIXTURES / 'valid-saved_subproof.mm'
                proof = FIXTURES / 'valid-saved_subproof.jsonl'
                build(root / 'build/metamath', [{'id': source.name, 'source': source, 'proof': proof}],
                      {'inputs': input_hashes(root)})
                changed = root / relative
                changed.write_bytes(changed.read_bytes() + b'\n')
                with self.assertRaisesRegex(RepositoryError, 'native index is stale'):
                    open_snapshot(root)


if __name__ == '__main__':
    unittest.main()
