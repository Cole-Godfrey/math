"""exercise the explorer http interface and snapshot boundaries."""

import http.client
from http.server import ThreadingHTTPServer
import json
from pathlib import Path
import tempfile
from threading import Thread
import unittest
from urllib.parse import urlencode

from repository.server import ExplorerState, make_handler
from tests.store_fixture import fixture


class ServerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory()
        cls.root = Path(cls.temporary.name)
        cls.catalog, cls.receipt = fixture(cls.root)
        cls.state = ExplorerState(cls.root)
        cls.server = ThreadingHTTPServer(("127.0.0.1", 0), make_handler(cls.state))
        cls.thread = Thread(target=cls.server.serve_forever, daemon=True)
        cls.thread.start()

    @classmethod
    def tearDownClass(cls):
        cls.server.shutdown()
        cls.server.server_close()
        cls.thread.join()
        cls.temporary.cleanup()

    def request(self, path, parameters=None, method="GET", headers=None):
        connection = http.client.HTTPConnection("127.0.0.1", self.server.server_port)
        try:
            if parameters:
                path += "?" + urlencode(parameters)
            connection.request(method, path, headers=headers or {})
            response = connection.getresponse()
            return response.status, dict(response.getheaders()), response.read()
        finally:
            connection.close()

    def test_static_interface_and_snapshot_summary(self):
        status, headers, body = self.request("/")
        self.assertEqual(status, 200)
        self.assertIn(b"Search mathematics", body)
        self.assertIn("script-src 'self'", headers["Content-Security-Policy"])
        status, headers, body = self.request("/api/summary")
        self.assertEqual(status, 200)
        self.assertEqual(json.loads(body)["declarations"], 5)
        self.assertEqual(headers["X-Math-Snapshot"], self.catalog["content_digest"])

    def test_all_exploration_endpoints(self):
        for path, parameters in [
            ("/api/search", {}),
            ("/api/search", {"q": "truth"}),
            ("/api/declaration", {"name": "Math.Fixture.truth", "proof": "1"}),
            ("/api/dependencies", {"name": "Math.Fixture.alias_truth", "transitive": "1"}),
            ("/api/hierarchy", {"name": "Math.Fixture.alias_truth", "format": "json"}),
            ("/api/expressions", {"name": "Math.Fixture.identity"}),
            ("/api/term", {"name": "Math.Fixture.identity", "root": "value", "path": "bb"}),
            ("/api/source", {"name": "Math.Fixture.truth"}),
            ("/api/guide", {}),
        ]:
            status, _, body = self.request(path, parameters)
            self.assertEqual(status, 200, (path, body))
            self.assertIsInstance(json.loads(body), dict)

    def test_complete_downloads_preserve_verified_artifact_bytes(self):
        for endpoint, path in [("/api/catalog", self.root / "build/knowledge.json"),
                               ("/api/proof-export", self.state.snapshot.proof_path)]:
            status, headers, body = self.request(endpoint, {"snapshot": self.catalog["content_digest"]})
            self.assertEqual(status, 200)
            self.assertEqual(body, path.read_bytes())
            self.assertIn("attachment; filename=", headers["Content-Disposition"])
            self.assertEqual(headers["X-Math-Snapshot"], self.catalog["content_digest"])
            self.assertEqual(self.request(endpoint, method="HEAD")[2], b"")

    def test_requests_cannot_silently_switch_snapshots(self):
        for endpoint in ["/api/search", "/api/catalog", "/api/proof-export", "/api/term"]:
            status, _, body = self.request(endpoint, {"snapshot": "0" * 64})
            self.assertEqual(status, 400)
            self.assertIn("snapshot changed", json.loads(body)["error"])

    def test_hierarchy_pages_and_group_links_cover_the_full_graph(self):
        name = "Math.Fixture.alias_truth"
        _, _, body = self.request("/api/hierarchy", {"name": name, "format": "json"})
        graph = json.loads(body)
        groups = set()
        for level in graph["levels"]:
            status, _, body = self.request("/api/hierarchy", {"name": name, "level": level["level"], "limit": 200})
            self.assertEqual(status, 200)
            groups.update(item["id"] for item in json.loads(body)["items"])
        self.assertEqual(groups, {group["id"] for group in graph["groups"]})
        group = graph["groups"][-1]
        status, _, body = self.request("/api/hierarchy", {"name": name, "group": group["id"]})
        self.assertEqual(status, 200)
        self.assertEqual({item["id"] for item in json.loads(body)["prerequisites"]}, set(group["dependencies"]))

    def test_invalid_queries_and_arbitrary_files_are_rejected(self):
        for path, parameters in [("/api/search", {"limit": 0}), ("/api/search", {"offset": 2 ** 100}),
                                 ("/api/declaration", {"name": "../../AGENTS.md"}),
                                 ("/api/dependencies", {"name": "Math.Fixture.truth", "role": "unsafe"}),
                                 ("/api/term", {"name": "Math.Fixture.identity", "root": "value", "path": "bbx"}),
                                 ("/api/term", {"name": "Math.Fixture.identity", "root": "rule", "rule": "-1"})]:
            status, _, _ = self.request(path, parameters)
            self.assertEqual(status, 400)
        self.assertEqual(self.request("/../AGENTS.md")[0], 404)
        self.assertEqual(self.request("/api/search?q=a&q=b")[0], 400)
        self.assertEqual(self.request("/api/term?name=Math.Fixture.identity&path=b&path=t")[0], 400)

    def test_term_occurrences_retain_binder_scope_and_snapshot_identity(self):
        status, headers, body = self.request("/api/term", {"name": "Math.Fixture.identity", "path": "bb"})
        self.assertEqual(status, 200)
        result = json.loads(body)
        self.assertEqual(result["expression"]["id"], 3)
        self.assertEqual(result["binding"]["name"], "h")
        self.assertEqual(headers["X-Math-Snapshot"], self.catalog["content_digest"])
        self.assertEqual(self.request("/api/term", {"name": "Math.Fixture.identity", "path": "bb"}, method="HEAD")[2], b"")

    def test_foreign_hosts_and_reload_origins_are_rejected(self):
        self.assertEqual(self.request("/api/summary", headers={"Host": "example.invalid"})[0], 400)
        self.assertEqual(self.request("/api/reload", method="POST", headers={"Origin": "https://example.invalid"})[0], 400)
        self.assertEqual(self.request("/api/reload", method="POST")[0], 200)


if __name__ == "__main__":
    unittest.main()
