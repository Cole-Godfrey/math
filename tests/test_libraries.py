"""check locked source identity and attribution using isolated git fixtures."""

from __future__ import annotations

from copy import deepcopy
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from repository.core import RepositoryError, registered_modules
from repository.libraries import package_provenance, snapshot_packages, source_origins
from repository.bibliography import archive_bibliographies


class LibraryTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.package = self.root / ".lake/packages/fixture"
        (self.package / "Fixture").mkdir(parents=True)
        self.git("init", "-q")
        self.url = "https://example.invalid/mathematics.git"
        self.git("remote", "add", "origin", self.url)
        (self.package / "LICENSE").write_text("fixture license notice\n")
        (self.package / "Fixture/Basic.lean").write_text(
            "/- authors: fixture contributors -/\ntheorem fixture : True := True.intro\n")
        (self.package / "references.bib").write_text('@book{fixturebook,title={Fixture book},year=2026}\n')
        self.git("add", ".")
        self.git("-c", "user.name=Repository tests", "-c", "user.email=tests@example.invalid",
                 "commit", "-qm", "fixture sources", "--no-gpg-sign")
        self.revision = self.git("rev-parse", "HEAD").strip()
        self.lock = {"packagesDir": ".lake/packages", "packages": [{
            "name": "fixture", "type": "git", "rev": self.revision, "url": self.url,
        }]}
        self.policy = {"libraries": {"fixture": {
            "repository": self.url, "revision": self.revision, "license": "fixture-license",
            "license_file": "LICENSE", "modules": {"Fixture.Basic": {
                "title": "Fixture", "allowed_axioms": [],
            }},
        }}}

    def git(self, *args: str) -> str:
        result = subprocess.run(["git", "-C", str(self.package), *args], text=True,
                                capture_output=True, check=True)
        return result.stdout

    def snapshot(self):
        return snapshot_packages(self.root, self.lock, self.policy)

    def test_locked_source_and_license_are_retained(self):
        packages = self.snapshot()
        provenance = package_provenance(packages)["fixture"]
        self.assertEqual(provenance["revision"], self.revision)
        self.assertEqual(provenance["licenses"]["LICENSE"]["text"], "fixture license notice\n")
        raw = {"declarations": [{"module": "Fixture.Basic"}]}
        origin = source_origins(self.root, raw, packages, self.policy)["Fixture.Basic"]
        self.assertEqual(origin["revision"], self.revision)
        self.assertIn("fixture contributors", origin["notice"])
        self.assertEqual(origin["url"], f"https://example.invalid/mathematics/blob/{self.revision}/Fixture/Basic.lean")

    def test_bibliographies_retain_pinned_bytes_and_entry_locations(self):
        self.policy["libraries"]["fixture"]["bibliography"] = "references.bib"
        bibliography = archive_bibliographies(self.snapshot(), self.policy)["fixture"]
        self.assertEqual(bibliography["text"], (self.package / "references.bib").read_text())
        self.assertEqual(bibliography["revision"], self.revision)
        self.assertIn(self.revision, bibliography["url"])
        self.assertEqual(bibliography["entries"]["fixturebook"]["line"], 1)
        self.assertEqual(bibliography["license"], "fixture-license")

    def test_untracked_or_changed_bibliographies_are_rejected(self):
        packages = self.snapshot()
        self.policy["libraries"]["fixture"]["bibliography"] = "missing.bib"
        with self.assertRaisesRegex(RepositoryError, "not a tracked source"):
            archive_bibliographies(packages, self.policy)
        self.policy["libraries"]["fixture"]["bibliography"] = "references.bib"
        (self.package / "references.bib").write_text('@book{changed,title={changed}}')
        with self.assertRaisesRegex(RepositoryError, "changed before archival"):
            archive_bibliographies(packages, self.policy)

    def test_bibliography_paths_stay_inside_the_pinned_checkout(self):
        packages = self.snapshot()
        for path in ("/tmp/source.bib", "../source.bib", "dir\\source.bib", True, ""):
            self.policy["libraries"]["fixture"]["bibliography"] = path
            with self.subTest(path=path), self.assertRaisesRegex(RepositoryError, "invalid bibliography path"):
                archive_bibliographies(packages, self.policy)

    def test_modified_source_is_rejected_even_with_preserved_timestamps(self):
        source = self.package / "Fixture/Basic.lean"
        stat = source.stat()
        source.write_text(source.read_text().replace("True.intro", "False.elim"))
        os.utime(source, ns=(stat.st_atime_ns, stat.st_mtime_ns))
        with self.assertRaisesRegex(RepositoryError, "modified dependency source"):
            self.snapshot()

    def test_wrong_checkout_commit_is_rejected(self):
        self.lock["packages"][0]["rev"] = "0" * 40
        with self.assertRaisesRegex(RepositoryError, "checkout differs from locked revision"):
            self.snapshot()

    def test_registry_and_lock_must_agree(self):
        self.policy["libraries"]["fixture"]["revision"] = "0" * 40
        with self.assertRaisesRegex(RepositoryError, "registry revision differs from lockfile"):
            self.snapshot()

    def test_repository_identity_is_checked(self):
        self.lock["packages"][0]["url"] = "https://example.invalid/other.git"
        with self.assertRaisesRegex(RepositoryError, "checkout repository differs from lockfile"):
            self.snapshot()

    def test_untracked_dependency_source_is_rejected(self):
        (self.package / "Fixture/Extra.lean").write_text("axiom extra : False\n")
        with self.assertRaisesRegex(RepositoryError, "untracked dependency sources"):
            self.snapshot()

    def test_missing_license_attribution_is_rejected(self):
        self.policy["libraries"]["fixture"]["license_file"] = "NOTICE"
        with self.assertRaisesRegex(RepositoryError, "registered license notice is missing"):
            self.snapshot()

    def test_library_registration_requires_a_commit(self):
        self.policy["libraries"]["fixture"]["revision"] = "main"
        with self.assertRaisesRegex(RepositoryError, "exact commit"):
            registered_modules(self.policy)

    def test_modules_cannot_be_owned_by_two_libraries(self):
        self.policy["libraries"]["second"] = deepcopy(self.policy["libraries"]["fixture"])
        with self.assertRaisesRegex(RepositoryError, "duplicate library module"):
            registered_modules(self.policy)

    def test_package_subdirectory_preserves_repository_source_links(self):
        (self.package / "library").mkdir()
        (self.package / "Fixture").rename(self.package / "library/Fixture")
        self.git("add", "-A")
        self.git("-c", "user.name=Repository tests", "-c", "user.email=tests@example.invalid",
                 "commit", "-qm", "move sources into package subdirectory", "--no-gpg-sign")
        revision = self.git("rev-parse", "HEAD").strip()
        self.lock["packages"][0].update(rev=revision, subDir="library")
        self.policy["libraries"]["fixture"]["revision"] = revision
        packages = self.snapshot()
        origin = source_origins(self.root, {"declarations": [{"module": "Fixture.Basic"}]},
                                packages, self.policy)["Fixture.Basic"]
        self.assertEqual(origin["path"], "library/Fixture/Basic.lean")
        self.assertIn(f"/{revision}/library/Fixture/Basic.lean", origin["url"])
        self.assertIn("LICENSE", package_provenance(packages)["fixture"]["licenses"])


if __name__ == "__main__":
    unittest.main()
