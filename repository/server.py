"""serve immutable verified snapshots through a local browser explorer."""

from __future__ import annotations

from functools import lru_cache
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
import sqlite3
from threading import Lock
from urllib.parse import parse_qs, urlsplit

from .core import RepositoryError, canonical, require
from .store import open_snapshot


ASSETS = {"/": ("index.html", "text/html; charset=utf-8"),
          "/app.js": ("app.js", "text/javascript; charset=utf-8"),
          "/app.css": ("app.css", "text/css; charset=utf-8"),
          "/favicon.svg": ("favicon.svg", "image/svg+xml")}


class ExplorerState:
    def __init__(self, root: Path):
        self.root = root
        self.snapshot = open_snapshot(root)
        self.lock = Lock()

    def reload(self):
        snapshot = open_snapshot(self.root)
        with self.lock:
            self.snapshot = snapshot
            self.hierarchy.cache_clear()
        return snapshot.summary()

    @lru_cache(maxsize=2)
    def hierarchy(self, digest: str, name: str):
        snapshot = self.snapshot
        require(snapshot.metadata["content_digest"] == digest, "snapshot changed; repeat the request")
        return snapshot.graph.hierarchy(name)


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
                if request.path in ASSETS:
                    filename, content_type = ASSETS[request.path]
                    self.send(200, (Path(__file__).parent / "web" / filename).read_bytes(), content_type)
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

                snapshot = state.snapshot
                self.snapshot_digest = snapshot.metadata["content_digest"]
                require(not arg("snapshot") or arg("snapshot") == self.snapshot_digest,
                        "snapshot changed; refresh the explorer")
                name = arg("name")
                if request.path == "/api/catalog":
                    self.download(snapshot.catalog_chunks(), "knowledge.json", "application/json; charset=utf-8")
                    return
                elif request.path == "/api/proof-export":
                    with snapshot.proof_path.open("rb") as handle:
                        chunks = iter(lambda: handle.read(64 * 1024), b"")
                        self.download(chunks, snapshot.proof_path.name, "application/x-ndjson", snapshot.proof_path.stat().st_size)
                    return
                elif request.path == "/api/summary":
                    result = snapshot.summary()
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
                    result = snapshot.source(name, arg("full") == "1")
                elif request.path == "/api/expressions":
                    result = snapshot.expressions(name)
                elif request.path == "/api/term":
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
                    graph = state.hierarchy(snapshot.metadata["content_digest"], name)
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
    print(f"Math explorer: http://127.0.0.1:{server.server_port}", flush=True)
    try:
        server.serve_forever(poll_interval=0.25)
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
