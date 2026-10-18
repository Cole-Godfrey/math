"""check bibliography fidelity and explicit documentation citation resolution."""

from copy import deepcopy
import hashlib
from pathlib import Path
import tempfile
import unittest

from repository.bibliography import BibTeX, citation_keys, resolve_citations
from repository.core import RepositoryError, canonical, digest
from repository.store import Snapshot, create_store
from tests.store_fixture import fixture


class BibTeXTests(unittest.TestCase):
    def test_nested_braces_unicode_quoted_values_and_raw_text_are_retained(self):
        text = '# source comment\n@Book{Key,\n author={Gödel, K.},\n title={A {Protected} title},\n note="A {quoted \\"word\\"} and \\{brace\\}",\n year=1931,\n}\n'
        result = BibTeX(text).entries()["Key"]
        self.assertEqual(result["kind"], "book")
        self.assertEqual(result["fields"]["author"], "Gödel, K.")
        self.assertEqual(result["fields"]["title"], "A {Protected} title")
        self.assertEqual(result["fields"]["year"], "1931")
        self.assertEqual(result["raw"], text[text.index("@Book"):].rstrip("\n"))
        self.assertEqual((result["line"], result["end_line"]), (2, 7))

    def test_macros_concatenation_comments_and_parenthesized_records(self):
        text = '@comment{ignored @book{fake, title={hidden}}}\n@string{prefix="A ",}\n@preamble{"header"}\n@article(Key, title=PREFIX # {title}, year=2026)\n'
        result = BibTeX(text).entries()
        self.assertEqual(set(result), {"Key"})
        self.assertEqual(result["Key"]["fields"], {"title": "A title", "year": "2026"})
        self.assertTrue(result["Key"]["raw"].startswith("@article("))

    def test_duplicate_keys_fields_and_macros_are_rejected(self):
        cases = ['@book{k,title={a}} @book{k,title={b}}', '@book{k,Title={a},title={b}}',
                 '@string{a="a"} @string{A="b"}']
        for text in cases:
            with self.subTest(text=text), self.assertRaisesRegex(RepositoryError, "duplicate bibliography"):
                BibTeX(text).entries()
        self.assertEqual(set(BibTeX('@book{k,title={a}} @book{K,title={b}}').entries()), {"k", "K"})

    def test_truncated_and_malformed_records_are_rejected(self):
        valid = '@book{k,title={nested {value}},year=2026}'
        cases = [valid[:index] for index in range(1, len(valid))]
        cases += ['@book{k,,title={a}}', '@book{k,title={a} year=2026}', '@book{k,title=}',
                  '@book{k,title="unterminated}', '@string{x="a",title={b}}']
        for text in cases:
            with self.subTest(text=text), self.assertRaises(RepositoryError):
                BibTeX(text).entries()

    def test_citation_keys_respect_case_and_ignore_code_and_inline_links(self):
        text = '[Author, *Book*][Key] [other] [Key] (p. 3) `f [code]`\n```lean\n[block]\n```\n[link](https://example.invalid) ![image](x) [key]'
        self.assertEqual(citation_keys(text, {"Key", "other", "code", "block", "link", "image"}), ["Key", "other"])

    def test_cross_library_keys_resolve_explicitly_or_remain_ambiguous(self):
        def bibliography(title):
            text='@book{Key,title={' + title + '}}'
            return {"entries": BibTeX(text).entries(), "url": "https://example.invalid/references.bib",
                    "sha256": hashlib.sha256(text.encode()).hexdigest()}
        records = {"first": bibliography("First"), "second": bibliography("Second")}
        ambiguous = resolve_citations(records, "[Key]")[0]
        self.assertTrue(ambiguous["ambiguous"])
        self.assertEqual({item["package"] for item in ambiguous["candidates"]}, {"first", "second"})
        self.assertEqual(resolve_citations(records, "[Key]", "second")[0]["fields"]["title"], "Second")
        self.assertEqual(resolve_citations(records, "[first:Key]", "second")[0]["fields"]["title"], "First")
        collision = BibTeX('@book{first:Key,title={Different local key}}').entries()["first:Key"]
        records["second"]["entries"]["first:Key"] = collision
        self.assertEqual(resolve_citations(records, "[first:Key]", "second")[0]["fields"]["title"], "First")
        self.assertEqual(resolve_citations(records, "[second:first:Key]", "first")[0]["fields"]["title"], "Different local key")


class StoredCitationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.catalog, _ = fixture(self.root)
        text = '@book{Direct,title={Direct reference},author={A. Author},year=2026}\n@book{Module,title={Module reference}}\n'
        self.catalog["bibliographies"] = {"fixture": {
            "package": "fixture", "path": "references.bib", "sha256": hashlib.sha256(text.encode()).hexdigest(),
            "text": text, "revision": "1" * 40, "license": "fixture-license",
            "url": "https://example.invalid/blob/" + "1" * 40 + "/references.bib", "entries": BibTeX(text).entries()}}
        self.catalog["modules"] = [{"name": "Math.Fixture", "imports": [],
                                    "docs": [{"text": "module reference [Module]", "line": 1, "end_line": 3}]}]
        node = next(item for item in self.catalog["declarations"] if item["name"] == "Math.Fixture.truth")
        node["doc"] = "declaration reference [Direct]"
        self.catalog["declaration_hashes"][node["name"]] = digest(node)
        self.catalog.pop("content_digest")
        self.catalog["content_digest"] = digest(self.catalog)
        receipt = create_store(self.root / "build", self.catalog, {}, hashlib.sha256(canonical(self.catalog) + b"\n").hexdigest())
        self.snapshot = Snapshot(self.root / "build" / receipt["database"], receipt)

    def test_declaration_citations_and_module_references_keep_distinct_scopes(self):
        result = self.snapshot.citations("Math.Fixture.truth")
        self.assertEqual([item["key"] for item in result["declaration_citations"]], ["Direct"])
        self.assertEqual([item["key"] for item in result["module_citations"]], ["Module"])
        self.assertEqual(result["module_docs"][0]["line"], 1)
        self.assertTrue(result["declaration_citations"][0]["source_url"].endswith("#L1"))
        self.assertEqual(self.snapshot.citations("Math.Fixture.alias_truth")["declaration_citations"], [])

    def test_archived_bibliography_and_catalog_round_trip_losslessly(self):
        bibliography = self.snapshot.bibliography("fixture")
        self.assertEqual(bibliography, self.catalog["bibliographies"]["fixture"])
        self.assertEqual(hashlib.sha256(bibliography["text"].encode()).hexdigest(), bibliography["sha256"])
        self.assertEqual(b"".join(self.snapshot.catalog_chunks()), canonical(self.catalog) + b"\n")
        self.assertIn("fixture:Direct", self.snapshot.summary()["bibliography_keys"])

    def test_unknown_bibliographies_and_declarations_are_rejected(self):
        with self.assertRaisesRegex(RepositoryError, "unknown bibliography"):
            self.snapshot.bibliography("missing")
        with self.assertRaisesRegex(RepositoryError, "unknown declaration"):
            self.snapshot.citations("missing")


if __name__ == "__main__":
    unittest.main()
