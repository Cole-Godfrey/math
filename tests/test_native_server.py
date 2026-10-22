"""exercise native browser requests against an admitted protocol fixture."""

from concurrent.futures import ThreadPoolExecutor
import http.client
from http.server import ThreadingHTTPServer
import io
import json
from pathlib import Path
import tarfile
import tempfile
from threading import Event, Thread
import unittest
from unittest.mock import patch
from urllib.parse import urlencode

from repository.metamath_explore import NativeExplorer
from repository.metamath_store import build, identity, Snapshot
from repository.server import ExplorerState, make_handler
from tests.store_fixture import fixture


FIXTURES = Path(__file__).parent / 'fixtures/metamath'


class NativeServerTests(unittest.TestCase):
    def request(self, path, parameters=None, method='GET', headers=None):
        connection = http.client.HTTPConnection('127.0.0.1', self.server.server_port)
        try:
            if parameters:
                path += '?' + urlencode(parameters)
            connection.request(method, path, headers=headers or {})
            response = connection.getresponse()
            return response.status, dict(response.getheaders()), response.read()
        finally:
            connection.close()

    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory()
        cls.root = Path(cls.directory.name)
        cls.catalog, _ = fixture(cls.root)
        source = FIXTURES / 'valid-saved_subproof.mm'
        build(cls.root / 'build/metamath', [{'id': source.name, 'source': source,
              'proof': FIXTURES / 'valid-saved_subproof.jsonl'}], {'fixture': True})
        cls.archive = Snapshot(cls.root / 'build/metamath')
        cls.state = ExplorerState(cls.root)
        cls.state.native = NativeExplorer(cls.archive)
        cls.server = ThreadingHTTPServer(('127.0.0.1', 0), make_handler(cls.state))
        cls.thread = Thread(target=cls.server.serve_forever, daemon=True)
        cls.thread.start()
        cls.name = identity(source.name, 'th')

    @classmethod
    def tearDownClass(cls):
        cls.server.shutdown()
        cls.server.server_close()
        cls.thread.join()
        cls.archive.close()
        cls.directory.cleanup()

    def data(self, path, parameters=None):
        code, headers, body = self.request(path, parameters)
        self.assertEqual(code, 200, body)
        self.assertEqual(headers['X-Math-Snapshot'], self.state.digest())
        return json.loads(body)

    def test_library_summaries_share_one_snapshot_pin_without_mixing_foundations(self):
        lean = self.data('/api/summary')
        native = self.data('/api/summary', {'system': 'metamath'})
        self.assertEqual(lean['declarations'], 5)
        self.assertEqual(native['declarations'], 4)
        self.assertEqual(native['selected'], 2)
        self.assertEqual(native['theorems'], 1)
        self.assertEqual(lean['catalog_digest'], native['catalog_digest'])
        self.assertNotEqual(lean['foundation']['id'], native['foundation']['id'])

    def test_native_statements_steps_and_assumptions_keep_their_exact_protocol(self):
        declaration = self.data('/api/declaration', {'name': self.name})
        self.assertEqual(declaration['proof_system'], 'metamath')
        proof = self.data('/api/native-proof', {'name': self.name})
        self.assertEqual(proof['focused']['arguments'], [1, 1])
        self.assertEqual(proof['focused']['expression_tokens'], declaration['statement_tokens'])
        foundations = self.data('/api/native-foundations', {'name': self.name})
        self.assertEqual(foundations['total'], 1)
        self.assertEqual(foundations['items'][0]['path'][0], self.name)

    def test_native_search_hierarchies_and_sources_are_complete(self):
        search = self.data('/api/search', {'system': 'metamath', 'q': 'th'})
        self.assertEqual(search['items'][0]['name'], self.name)
        graph = self.data('/api/hierarchy', {'name': self.name, 'format': 'json'})
        self.assertEqual(len(graph['declarations']), 4)
        source = self.data('/api/source', {'name': self.name})
        self.assertEqual(source['total_lines'], 1)
        code, _, raw = self.request('/api/native-source', {'name': self.name})
        self.assertEqual(code, 200)
        self.assertEqual(raw, (FIXTURES / 'valid-saved_subproof.mm').read_bytes())

    def test_native_source_primitive_queries_keep_qualified_identities_and_complete_pages(self):
        page = self.data('/api/native-primitives', {'system': 'metamath', 'kind': 'constant', 'limit': 1})
        self.assertEqual(page['total'], 2)
        second = self.data('/api/native-primitives', {'system': 'metamath', 'kind': 'constant',
                                                     'limit': 1, 'offset': 1})
        self.assertEqual(second['total'], 2)
        self.assertNotEqual(page['items'][0]['identifier'], second['items'][0]['identifier'])
        name = next(row['identifier'] for row in page['items'] + second['items'] if row['token'] == 'wff')
        node = self.data('/api/native-primitive', {'name': name})
        self.assertEqual(node['token'], 'wff')
        self.assertEqual(node['proof_system'], 'metamath')
        self.assertEqual(node['origin']['path'], 'valid-saved_subproof.mm')
        self.assertEqual(self.data('/api/summary', {'system': 'metamath'})['declarations'], 4)

    def test_native_source_primitive_context_relations_and_downloads_are_exact(self):
        binding = self.data('/api/native-primitive', {'name': self.name})['record']
        symbol = binding['tokens'][3]
        links = self.data('/api/native-primitive-relations', {'name': symbol, 'reverse': 1,
                                                            'relation': 'expression_symbol'})
        self.assertEqual([row['position'] for row in links['items'] if row['source'] == self.name], [3, 4, 6, 7])
        context = self.data('/api/native-primitive-context', {'name': self.name})
        self.assertEqual(len(context['scopes']), 1)
        scope = context['scopes'][0]['identifier']
        code, headers, source = self.request('/api/native-primitive-source', {'name': scope})
        self.assertEqual(code, 200)
        self.assertEqual(headers['X-Math-Snapshot'], self.state.digest())
        self.assertEqual(source, (FIXTURES / 'valid-saved_subproof.mm').read_bytes())
        code, _, source = self.request('/api/native-primitive-source', {'name': binding['tokens'][0]})
        self.assertEqual(code, 200)
        self.assertEqual(source, b'$c wff pair $.')

    def test_native_source_primitive_requests_reject_invalid_pages_scopes_and_libraries(self):
        for path, arguments in [
            ('/api/native-primitives', {'system': 'lean'}),
            ('/api/native-primitives', {'system': 'metamath', 'limit': 201}),
            ('/api/native-primitives', {'system': 'metamath', 'database': 'missing.mm'}),
            ('/api/native-primitive', {'name': 'metamath-scope:missing.mm:global'}),
            ('/api/native-primitive-relations', {'name': self.name, 'relation': 'axiom'}),
            ('/api/native-primitive', {'name': self.name, 'system': 'unknown'}),
        ]:
            with self.subTest(path=path, arguments=arguments):
                code, _, body = self.request(path, arguments)
                self.assertEqual(code, 400, body)

    def test_native_archive_download_retains_every_proof_and_source(self):
        code, headers, data = self.request('/api/proof-export', {'system': 'metamath'})
        self.assertEqual(code, 200)
        self.assertEqual(headers['Content-Type'], 'application/x-tar')
        with tarfile.open(fileobj=io.BytesIO(data), mode='r:') as archive:
            names = archive.getnames()
            self.assertIn('index.json', names)
            self.assertIn(self.archive.digest + '/valid-saved_subproof.mm', names)
            self.assertIn(self.archive.digest + '/valid-saved_subproof.mm.proof.jsonl', names)

    def test_source_pins_and_proof_calculus_boundaries_reject_wrong_requests(self):
        for path, parameters in [
            ('/api/declaration', {'name': self.name, 'snapshot': self.catalog['content_digest']}),
            ('/api/native-proof', {'name': self.name, 'step': '999'}),
            ('/api/term', {'name': self.name}),
            ('/api/bibliography', {'system': 'metamath', 'package': 'missing'}),
            ('/api/search', {'system': 'unknown'}),
            ('/api/declaration', {'name': self.name, 'system': 'unknown'}),
        ]:
            with self.subTest(path=path, parameters=parameters):
                self.assertEqual(self.request(path, parameters)[0], 400)

    def test_concurrent_native_requests_use_independent_readers(self):
        with ThreadPoolExecutor(max_workers=4) as executor:
            results = list(executor.map(lambda _: self.request('/api/native-proof', {'name': self.name}), range(16)))
        self.assertTrue(all(result[0] == 200 for result in results))

    def test_summary_keeps_its_selected_snapshot_when_the_available_libraries_change(self):
        native, digest = self.state.native, self.state.digest()
        selected, proceed = Event(), Event()
        original = native.summary

        def held_summary():
            selected.set()
            self.assertTrue(proceed.wait(5))
            return original()

        self.state.summary.cache_clear()
        try:
            with patch.object(native, 'summary', held_summary), ThreadPoolExecutor(max_workers=1) as executor:
                pending = executor.submit(self.state.summary, digest, 'metamath')
                try:
                    self.assertTrue(selected.wait(5))
                    with self.state.lock:
                        self.state.native = None
                finally:
                    proceed.set()
                result = pending.result(timeout=5)
            self.assertEqual(result['catalog_digest'], digest)
            self.assertEqual([library['id'] for library in result['libraries']], ['lean', 'metamath'])
        finally:
            with self.state.lock:
                self.state.native = native
            self.state.summary.cache_clear()


if __name__ == '__main__':
    unittest.main()
