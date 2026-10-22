"""serve immutable verified snapshots through a local browser explorer."""

from __future__ import annotations

from functools import lru_cache
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
import sqlite3
from threading import Lock, Thread
from urllib.parse import parse_qs, urlsplit

from .atlas import Atlas
from .core import RepositoryError, canonical, digest as content_digest, require
from .store import open_snapshot


WEB = Path(__file__).parent / "web"
TYPES = {".html": "text/html; charset=utf-8", ".js": "text/javascript; charset=utf-8",
         ".css": "text/css; charset=utf-8", ".svg": "image/svg+xml",
         ".json": "application/json; charset=utf-8", ".woff2": "font/woff2"}


def asset(path: str) -> Path | None:
    """resolve a static explorer file without leaving the web directory."""
    relative = "index.html" if path == "/" else path[1:]
    parts = relative.split("/")
    if not all(part and not part.startswith(".") for part in parts):
        return None
    target = WEB.joinpath(*parts)
    if target.suffix not in TYPES or not target.is_file() or target.is_symlink():
        return None
    return target if target.resolve().is_relative_to(WEB.resolve()) else None


class ExplorerState:
    def __init__(self, root: Path):
        self.root = root
        self.snapshot = open_snapshot(root)
        self.native = self.native_snapshot(self.snapshot)
        self.lock = Lock()
        self.atlas_lock = Lock()
        self.atlases = {}

    def native_snapshot(self, lean):
        binding = lean.metadata.get('provenance', {}).get('native_snapshots', {}).get('metamath')
        if binding is None:
            return None
        from .metamath_build import open_snapshot as open_native
        from .metamath_explore import NativeExplorer
        archive = open_native(self.root)
        try:
            require(archive.digest == binding['snapshot_digest'], 'native snapshot differs from the checked repository catalog')
            require(archive.manifest['provenance']['inputs'] == lean.metadata['provenance']['inputs'],
                    'proof libraries were verified against different repository inputs')
            return NativeExplorer(archive)
        finally:
            archive.close()

    def digest(self):
        lean = self.snapshot.metadata['content_digest']
        return content_digest({'lean': lean, 'metamath': self.native.snapshot.digest}) if self.native else lean

    def select(self, system='lean'):
        require(system in ['lean', 'metamath'], 'unknown proof library')
        require(system != 'metamath' or self.native is not None, 'native proofs are unavailable in this snapshot')
        return self.native if system == 'metamath' else self.snapshot

    def reload(self):
        snapshot = open_snapshot(self.root)
        native = self.native_snapshot(snapshot)
        with self.lock:
            self.snapshot = snapshot
            self.native = native
            self.hierarchy.cache_clear()
            self.atlas_view.cache_clear()
            self.summary.cache_clear()
        with self.atlas_lock:
            self.atlases.clear()
        return self.summary(self.digest(), 'lean')

    @lru_cache(maxsize=2)
    def summary(self, digest: str, system='lean'):
        with self.lock:
            require(self.digest() == digest, "snapshot changed; repeat the request")
            snapshot, native = self.select(system), self.native is not None
        result = snapshot.summary()
        if native:
            result = {**result, 'catalog_digest': digest, 'proof_system': system,
                      'libraries': [{'id': 'lean', 'title': 'Lean'}, {'id': 'metamath', 'title': 'Metamath'}]}
        return result

    def prepare(self):
        """compute the summary and graph atlas before the first pages ask for them."""
        snapshot = self.snapshot
        self.summary(self.digest(), 'lean')
        self.atlas(snapshot)

    def atlas(self, snapshot) -> Atlas:
        """build the graph atlas once per snapshot."""
        digest = snapshot.metadata["content_digest"]
        with self.atlas_lock:
            if digest not in self.atlases:
                self.atlases.clear()
                self.atlases[digest] = Atlas(snapshot.graph)
            return self.atlases[digest]

    @lru_cache(maxsize=64)
    def atlas_view(self, digest: str, node: str):
        snapshot = self.snapshot
        require(snapshot.metadata["content_digest"] == digest, "snapshot changed; repeat the request")
        return self.atlas(snapshot).view(node)

    @lru_cache(maxsize=2)
    def hierarchy(self, digest: str, name: str, system='lean'):
        with self.lock:
            require(self.digest() == digest, "snapshot changed; repeat the request")
            snapshot = self.select(system)
        return snapshot.hierarchy(name) if system == 'metamath' else snapshot.graph.hierarchy(name)


def make_handler(state: ExplorerState):
    class Handler(BaseHTTPRequestHandler):
        server_version = "MathExplorer"

        def log_message(self, format, *args):
            return

        def local_request(self):
            host = urlsplit("http://" + self.headers.get("Host", ""))
            require(host.hostname in {"127.0.0.1", "localhost", "::1"} and
                    (host.port or 80) == self.server.server_port and not host.username and
                    not host.path and not host.query and not host.fragment, "invalid local host")

        def response_headers(self, status, content_type, length=None, filename=None):
            self.send_response(status)
            self.send_header("Content-Type", content_type)
            if length is not None:
                self.send_header("Content-Length", str(length))
            if filename:
                self.send_header("Content-Disposition", f'attachment; filename="{filename}"')
            self.send_header("Cache-Control", "no-store")
            self.send_header("X-Content-Type-Options", "nosniff")
            self.send_header("Referrer-Policy", "no-referrer")
            if getattr(self, "snapshot_digest", None):
                self.send_header("X-Math-Snapshot", self.snapshot_digest)
            self.send_header("Content-Security-Policy", "default-src 'self'; script-src 'self'; style-src 'self'; "
                             "connect-src 'self'; img-src 'self' data:; frame-ancestors 'none'; base-uri 'none'")
            self.end_headers()

        def send(self, status: int, data: bytes, content_type: str = "application/json; charset=utf-8"):
            self.response_headers(status, content_type, len(data))
            if self.command != "HEAD":
                self.wfile.write(data)

        def download(self, chunks, filename, content_type, length=None):
            self.response_headers(200, content_type, length, filename)
            if self.command != "HEAD":
                for chunk in chunks:
                    self.wfile.write(chunk)

        def do_HEAD(self):
            self.do_GET()

        def do_GET(self):
            try:
                self.local_request()
                request = urlsplit(self.path)
                static = None if request.path.startswith("/api/") else asset(request.path)
                if static is not None:
                    self.send(200, static.read_bytes(), TYPES[static.suffix])
                    return
                arguments = parse_qs(request.query, keep_blank_values=True)

                def arg(name: str, default: str = "") -> str:
                    values = arguments.get(name, [default])
                    require(len(values) == 1, f"duplicate parameter: {name}")
                    return values[0]

                def number(name: str, default: int) -> int:
                    value = int(arg(name, str(default)))
                    require(0 <= value < 2 ** 63, f"invalid {name}")
                    return value

                name = arg("name")
                requested_system = arg('system', 'lean')
                require(requested_system in ['lean', 'metamath'], 'unknown proof library')
                system = 'metamath' if name.startswith(('metamath:', 'metamath-symbol:', 'metamath-scope:',
                                                        'metamath-disjoint:')) else requested_system
                with state.lock:
                    snapshot = state.select(system)
                    self.snapshot_digest = state.digest()
                require(not arg("snapshot") or arg("snapshot") == self.snapshot_digest,
                        "snapshot changed; refresh the explorer")
                if request.path == "/api/catalog":
                    self.download(snapshot.catalog_chunks(), 'metamath-manifest.json' if system == 'metamath' else "knowledge.json",
                                  "application/json; charset=utf-8")
                    return
                elif request.path == "/api/proof-export":
                    if system == 'metamath':
                        self.download(snapshot.archive_chunks(), 'metamath-' + snapshot.snapshot.digest[:12] + '.tar',
                                      'application/x-tar')
                        return
                    with snapshot.proof_path.open("rb") as handle:
                        chunks = iter(lambda: handle.read(64 * 1024), b"")
                        self.download(chunks, snapshot.proof_path.name, "application/x-ndjson", snapshot.proof_path.stat().st_size)
                    return
                elif request.path == "/api/summary":
                    result = state.summary(self.snapshot_digest, system)
                elif request.path == "/api/search":
                    result = snapshot.search(arg("q"), arg("subject") or None, arg("all") == "1",
                                             arg("kind") or None, arg("axiom_free") == "1",
                                             number("offset", 0), number("limit", 30))
                elif request.path == "/api/declaration":
                    result = snapshot.declaration(name, arg("proof") == "1")
                elif request.path == "/api/dependencies":
                    result = snapshot.relations(name, arg("reverse") == "1", arg("transitive") == "1",
                                                arg("role") or None, number("offset", 0), number("limit", 30))
                elif request.path == "/api/source":
                    result = snapshot.source(name, arg("full") == "1", number('line', 1) if arg('line') else None) \
                        if system == 'metamath' else snapshot.source(name, arg("full") == "1")
                elif request.path == '/api/native-source':
                    require(system == 'metamath', 'native source requires a native declaration')
                    node = snapshot.declaration(name)
                    database = node['foundation']['database']
                    path = snapshot.snapshot.directory / snapshot.databases[database]['source_file']
                    with path.open('rb') as handle:
                        self.download(iter(lambda: handle.read(65536), b''), database,
                                      'text/plain; charset=utf-8', path.stat().st_size)
                    return
                elif request.path == '/api/native-proof':
                    require(system == 'metamath', 'native proof inspection requires a native declaration')
                    result = snapshot.term(name, number('step', 0) if arg('step') else None)
                elif request.path == '/api/native-primitives':
                    require(system == 'metamath', 'source primitives require a native library')
                    result = snapshot.primitives(arg('q'), arg('database') or None, arg('kind') or None,
                                                 number('offset', 0), number('limit', 30))
                elif request.path == '/api/native-primitive':
                    require(system == 'metamath', 'source primitives require a native library')
                    result = snapshot.primitive(name)
                elif request.path == '/api/native-primitive-relations':
                    require(system == 'metamath', 'source primitives require a native library')
                    result = snapshot.primitive_relations(name, arg('reverse') == '1', arg('relation') or None,
                                                           number('offset', 0), number('limit', 30))
                elif request.path == '/api/native-primitive-context':
                    require(system == 'metamath', 'source primitives require a native library')
                    result = snapshot.primitive_context(name)
                elif request.path == '/api/native-primitive-source':
                    require(system == 'metamath', 'source primitives require a native library')
                    node = snapshot.primitive(name)
                    data = snapshot.primitive_source(name, arg('full') == '1')
                    self.download([data], node['database_id'] + ('' if arg('full') == '1' else '.fragment'),
                                  'text/plain; charset=utf-8', len(data))
                    return
                elif request.path == '/api/native-foundations':
                    require(system == 'metamath', 'native foundations require a native declaration')
                    result = snapshot.foundations(name, number('offset', 0), number('limit', 30))
                elif request.path == "/api/expressions":
                    result = snapshot.expressions(name)
                elif request.path == "/api/term":
                    require(system == 'lean', 'use native proof inspection for native rule applications')
                    result = snapshot.term(name, arg("root", "value"), arg("path"),
                                           number("rule", 0) if arg("rule") else None)
                elif request.path == "/api/citations":
                    result = snapshot.citations(name)
                elif request.path == "/api/bibliography":
                    bibliography = snapshot.bibliography(arg("package"))
                    data = bibliography["text"].encode("utf-8")
                    self.download([data], bibliography["package"] + "-references.bib",
                                  "application/x-bibtex; charset=utf-8", len(data))
                    return
                elif request.path == "/api/hierarchy":
                    graph = state.hierarchy(self.snapshot_digest, name, system)
                    if arg("format") == "json":
                        result = graph
                    elif arg("group"):
                        group = number("group", 0)
                        by_id = {item["id"]: item for item in graph["groups"]}
                        require(group in by_id, "unknown dependency group")
                        result = {**by_id[group], "prerequisites": [by_id[item] for item in by_id[group]["dependencies"]]}
                    else:
                        level = number("level", max(item["level"] for item in graph["groups"]))
                        offset, limit = number("offset", 0), number("limit", 30)
                        require(1 <= limit <= 200, "invalid hierarchy page")
                        groups = [item for item in graph["groups"] if item["level"] == level]
                        result = {"items": groups[offset:offset + limit], "total": len(groups), "offset": offset,
                                  "limit": limit, "levels": graph["levels"],
                                  "declarations": len(graph["declarations"]), "groups": len(graph["groups"]),
                                  "axioms": graph["axioms"], "axiom_paths": graph["axiom_paths"]}
                elif request.path == "/api/atlas":
                    require(system == 'lean', 'native dependencies are available in declaration hierarchies')
                    node = arg("node")
                    require(len(node) <= 1000 and (not node or node[:2] in {"s:", "m:", "d:"}), "invalid graph node")
                    result = state.atlas_view(snapshot.metadata["content_digest"], node)
                elif request.path == "/api/guide":
                    result = {"title": "Contribute mathematics", "text": (state.root / "CONTRIBUTING.md").read_text()}
                else:
                    self.send(404, canonical({"error": "not found"}))
                    return
                self.send(200, canonical(result))
            except (RepositoryError, ValueError) as exc:
                self.send(400, canonical({"error": str(exc)}))
            except (BrokenPipeError, ConnectionResetError):
                return
            except (OSError, sqlite3.Error):
                self.send(500, canonical({"error": "snapshot resource unavailable"}))

        def do_POST(self):
            try:
                self.local_request()
                origin = self.headers.get("Origin")
                if origin:
                    require(origin == "http://" + self.headers["Host"], "cross-origin reload is not allowed")
                require(self.path == "/api/reload", "unknown action")
                require(int(self.headers.get("Content-Length", "0")) == 0, "reload does not accept a request body")
                result = state.reload()
                self.snapshot_digest = result["catalog_digest"]
                self.send(200, canonical(result))
            except (RepositoryError, ValueError, OSError, sqlite3.Error) as exc:
                self.send(400, canonical({"error": str(exc)}))

    return Handler


def serve(root: Path, port: int = 8000):
    require(0 <= port <= 65535, "invalid server port")
    state = ExplorerState(root)
    server = ThreadingHTTPServer(("127.0.0.1", port), make_handler(state))
    Thread(target=state.prepare, daemon=True).start()
    print(f"Math explorer: http://127.0.0.1:{server.server_port}", flush=True)
    try:
        server.serve_forever(poll_interval=0.25)
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
