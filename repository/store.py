"""store and query complete verified snapshots without loading every proof term."""

from __future__ import annotations

from contextlib import contextmanager
import hashlib
import json
from pathlib import Path
import re
import sqlite3
import tempfile
from threading import Lock

from .core import CHILD_FIELDS, canonical, digest, expression_names, require, selected_module_roots
from .explore import KnowledgeGraph
from .terms import inspect_term


ROLES = {"type": 1, "value": 2, "structure": 4}
SUMMARY_COLUMNS = "d.name, d.module, d.kind, d.statement, d.doc, d.axioms, d.selected, d.meta"
LARGE_FIELDS = {"declarations", "expressions", "expression_hashes", "declaration_hashes", "sources", "name_data"}


def file_digest(path: Path) -> str:
    result = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def _text(value) -> str:
    return canonical(value).decode()


def _catalog_parts(connection, metadata):
    """reconstruct the original canonical artifact in its original array order."""
    keys = sorted((set(metadata) - {"_catalog_file_digest"}) | LARGE_FIELDS)
    yield b"{"
    for index, key in enumerate(keys):
        if index:
            yield b","
        yield canonical(key) + b":"
        if key in {"declarations", "expressions", "expression_hashes"}:
            table = "declarations" if key == "declarations" else "expressions"
            column = "digest" if key == "expression_hashes" else "record"
            yield b"["
            for position, row in enumerate(connection.execute(f"SELECT {column} FROM {table} ORDER BY id")):
                if position:
                    yield b","
                yield canonical(row[0]) if column == "digest" else row[0].encode()
            yield b"]"
        elif key in {"declaration_hashes", "sources", "name_data"}:
            query = {"declaration_hashes": "SELECT name, digest FROM declarations ORDER BY name",
                     "sources": "SELECT module, origin FROM sources ORDER BY module",
                     "name_data": "SELECT name, parts FROM names ORDER BY name"}[key]
            yield b"{"
            for position, (name, value) in enumerate(connection.execute(query)):
                if position:
                    yield b","
                yield canonical(name) + b":"
                yield canonical(value) if key == "declaration_hashes" else value.encode()
            yield b"}"
        else:
            yield canonical(metadata[key])
    yield b"}\n"


def _buffered(parts, size=64 * 1024):
    chunks, length = [], 0
    for part in parts:
        chunks.append(part)
        length += len(part)
        if length >= size:
            yield b"".join(chunks)
            chunks, length = [], 0
    if chunks:
        yield b"".join(chunks)


def archive_sources(root: Path, catalog: dict, packages: dict, prefix: Path) -> dict[str, str]:
    texts = {}
    for module, origin in catalog["sources"].items():
        package = origin["package"]
        if package == "math":
            path = root / origin["path"]
        elif package == "lean":
            path = prefix / "src/lean" / origin["path"].removeprefix("src/")
        else:
            path = packages[package].root / origin["path"]
        if not path.is_file():
            require(package == "lean", f"missing source archive input: {module}")
            continue
        content = path.read_bytes()
        require(not origin.get("sha256") or hashlib.sha256(content).hexdigest() == origin["sha256"],
                f"source changed before archival: {module}")
        texts[module] = content.decode()
    return texts


def create_store(directory: Path, catalog: dict, source_texts: dict[str, str], catalog_file_digest: str) -> dict:
    """serialize an audited catalog and check that its complete graph is retained."""
    directory.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(prefix="index-", suffix=".sqlite", dir=directory, delete=False) as handle:
        temporary = Path(handle.name)
    connection = sqlite3.connect(temporary)
    try:
        connection.executescript("""
            PRAGMA foreign_keys=ON;
            PRAGMA journal_mode=DELETE;
            CREATE TABLE metadata (key TEXT PRIMARY KEY, value TEXT NOT NULL);
            CREATE TABLE declarations (
                id INTEGER PRIMARY KEY, name TEXT UNIQUE NOT NULL, module TEXT NOT NULL,
                kind TEXT NOT NULL, selected INTEGER NOT NULL, name_fold TEXT NOT NULL,
                doc_fold TEXT NOT NULL, search_text TEXT NOT NULL, axiom_count INTEGER NOT NULL,
                statement TEXT NOT NULL, doc TEXT, axioms TEXT NOT NULL, meta INTEGER NOT NULL,
                record TEXT NOT NULL, digest TEXT NOT NULL
            );
            CREATE INDEX declaration_module ON declarations(module, selected);
            CREATE INDEX declaration_kind ON declarations(kind, selected);
            CREATE TABLE selections (
                module TEXT NOT NULL, declaration INTEGER NOT NULL REFERENCES declarations(id),
                PRIMARY KEY(module, declaration)
            ) WITHOUT ROWID;
            CREATE INDEX selection_declaration ON selections(declaration, module);
            CREATE TABLE edges (
                source INTEGER NOT NULL REFERENCES declarations(id),
                target INTEGER NOT NULL REFERENCES declarations(id), roles INTEGER NOT NULL,
                PRIMARY KEY(source, target)
            ) WITHOUT ROWID;
            CREATE INDEX reverse_edges ON edges(target, source);
            CREATE TABLE expressions (id INTEGER PRIMARY KEY, record TEXT NOT NULL, digest TEXT NOT NULL);
            CREATE TABLE sources (module TEXT PRIMARY KEY, origin TEXT NOT NULL, text TEXT);
            CREATE TABLE names (name TEXT PRIMARY KEY, parts TEXT NOT NULL);
        """)
        metadata = {key: value for key, value in catalog.items() if key not in LARGE_FIELDS}
        metadata["_catalog_file_digest"] = catalog_file_digest
        connection.executemany("INSERT INTO metadata VALUES (?, ?)",
                               ((key, _text(value)) for key, value in sorted(metadata.items())))
        roots = set(catalog["roots"])
        nodes = sorted(catalog["declarations"], key=lambda item: item["name"])
        identifiers = {node["name"]: index for index, node in enumerate(catalog["declarations"], 1)}
        connection.executemany("INSERT INTO declarations VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)", (
            (identifiers[node["name"]], node["name"], node["module"], node["kind"], node["name"] in roots,
             node["name"].casefold(), (node["doc"] or "").casefold(),
             " ".join((node["name"], node["statement"], node["doc"] or "")).casefold(),
             len(node["axioms"]), node["statement"], node["doc"], _text(node["axioms"]), node["meta"],
             _text(node), catalog["declaration_hashes"][node["name"]]) for node in nodes))
        memberships = {(module, name) for module, names in selected_module_roots(catalog).items() for name in names}
        require({name for _, name in memberships} == roots, "query store has an unassigned selection")
        connection.executemany("INSERT INTO selections VALUES (?, ?)",
                               ((module, identifiers[name]) for module, name in sorted(memberships)))
        expected_edges = hashlib.sha256()

        def edges():
            for node in nodes:
                roles = {key: set(node[field]) for key, field in (
                    ("type", "type_dependencies"), ("value", "value_dependencies"),
                    ("structure", "structural_dependencies"))}
                for dependency in sorted(node["dependencies"]):
                    mask = sum(ROLES[key] for key, names in roles.items() if dependency in names)
                    expected_edges.update(canonical([node["name"], dependency, mask]) + b"\n")
                    yield identifiers[node["name"]], identifiers[dependency], mask

        connection.executemany("INSERT INTO edges VALUES (?, ?, ?)", edges())
        expected_expressions = hashlib.sha256()

        def expressions():
            for index, record in enumerate(catalog["expressions"]):
                text = _text(record)
                value = catalog["expression_hashes"][index]
                expected_expressions.update(str(index).encode() + b"\0" + text.encode() + b"\0" + value.encode() + b"\n")
                yield index, text, value

        connection.executemany("INSERT INTO expressions VALUES (?, ?, ?)", expressions())
        connection.executemany("INSERT INTO sources VALUES (?, ?, ?)", (
            (module, _text(origin), source_texts.get(module)) for module, origin in sorted(catalog["sources"].items())))
        connection.executemany("INSERT INTO names VALUES (?, ?)",
                               ((name, _text(parts)) for name, parts in sorted(catalog["name_data"].items())))
        connection.commit()
        require(connection.execute("PRAGMA foreign_key_check").fetchone() is None, "query store has unresolved references")
        require(connection.execute("SELECT count(*) FROM expressions").fetchone()[0] == len(catalog["expressions"]),
                "query store lost expressions")
        actual_expressions = hashlib.sha256()
        for index, text, value in connection.execute("SELECT id, record, digest FROM expressions ORDER BY id"):
            actual_expressions.update(str(index).encode() + b"\0" + text.encode() + b"\0" + value.encode() + b"\n")
        require(actual_expressions.digest() == expected_expressions.digest(), "query store changed proof expressions")
        actual_edges = hashlib.sha256()
        for source, target, roles in connection.execute("""
                SELECT s.name, t.name, e.roles FROM edges e
                JOIN declarations s ON s.id=e.source JOIN declarations t ON t.id=e.target
                ORDER BY s.name, t.name"""):
            actual_edges.update(canonical([source, target, roles]) + b"\n")
        require(actual_edges.digest() == expected_edges.digest(), "query store lost dependency roles")
        require(connection.execute("SELECT count(*) FROM declarations").fetchone()[0] == len(nodes),
                "query store lost declarations")
        actual_memberships = set(connection.execute("""SELECT s.module, d.name FROM selections s
            JOIN declarations d ON d.id=s.declaration"""))
        require(actual_memberships == memberships, "query store lost selecting modules")
        reconstructed = hashlib.sha256()
        for chunk in _buffered(_catalog_parts(connection, metadata)):
            reconstructed.update(chunk)
        require(reconstructed.hexdigest() == catalog_file_digest, "query store changed the complete catalog")
        connection.close()
        value = file_digest(temporary)
        target = directory / f"index-{value}.sqlite"
        temporary.replace(target)
        return {"schema_version": 1, "database": target.name, "database_digest": value,
                "catalog_digest": catalog["content_digest"], "catalog_file_digest": catalog_file_digest,
                "provenance": catalog["provenance"]}
    finally:
        connection.close()
        temporary.unlink(missing_ok=True)


class Snapshot:
    """read an immutable, content-addressed query store through read-only connections."""

    def __init__(self, path: Path, receipt: dict):
        from .replay import validate_binding_receipt

        self.path = path
        self.receipt = receipt
        self._graph = None
        self._lock = Lock()
        with self.connect() as connection:
            self.metadata = {key: json.loads(value) for key, value in connection.execute("SELECT key, value FROM metadata")}
            declarations = connection.execute("SELECT count(*) FROM declarations").fetchone()[0]
            expressions = connection.execute("SELECT count(*) FROM expressions").fetchone()[0]
        require(self.metadata.get("schema_version") == 3, "unsupported index schema; rerun verification")
        require(self.metadata.get("content_digest") == receipt.get("catalog_digest"), "query store catalog digest mismatch")
        require(self.metadata.get("provenance") == receipt.get("provenance"), "query store provenance mismatch")
        require(self.metadata.get("_catalog_file_digest") == receipt.get("catalog_file_digest"),
                "query store artifact digest mismatch")
        validate_binding_receipt(self.metadata, declarations, expressions)

    @contextmanager
    def connect(self):
        connection = sqlite3.connect(self.path.resolve().as_uri() + "?mode=ro&immutable=1", uri=True)
        connection.row_factory = sqlite3.Row
        connection.execute("PRAGMA query_only=ON")
        try:
            yield connection
        finally:
            connection.close()

    def catalog_chunks(self):
        """stream the complete verified index without loading the expression array."""
        with self.connect() as connection:
            yield from _buffered(_catalog_parts(connection, self.metadata))

    @property
    def proof_path(self) -> Path:
        value = self.metadata["provenance"]["proof_export_digest"]
        return self.path.parent / f"proofs-{value}.jsonl"

    @property
    def graph(self) -> KnowledgeGraph:
        with self._lock:
            if self._graph is None:
                with self.connect() as connection:
                    rows = connection.execute("SELECT id, name, module, kind, axioms FROM declarations").fetchall()
                    by_id = {row["id"]: {"name": row["name"], "module": row["module"], "kind": row["kind"],
                                          "axioms": json.loads(row["axioms"]), "dependencies": [],
                                          "type_dependencies": [], "value_dependencies": [],
                                          "structural_dependencies": []} for row in rows}
                    for source, target, mask in connection.execute("SELECT source, target, roles FROM edges"):
                        node = by_id[source]
                        name = by_id[target]["name"]
                        node["dependencies"].append(name)
                        for role, field in (("type", "type_dependencies"), ("value", "value_dependencies"),
                                            ("structure", "structural_dependencies")):
                            if mask & ROLES[role]:
                                node[field].append(name)
                self._graph = KnowledgeGraph({**self.metadata, "declarations": list(by_id.values())})
        return self._graph

    def summary(self) -> dict:
        with self.connect() as connection:
            counts = connection.execute("""SELECT count(*) AS declarations, sum(selected) AS selected,
                sum(CASE WHEN kind='theorem' THEN 1 ELSE 0 END) AS theorems FROM declarations""").fetchone()
        return {**dict(counts), "catalog_digest": self.metadata["content_digest"],
                "lean_version": self.metadata["lean_version"], "foundation": self.metadata["foundation"],
                "axiom_policy": self.metadata["axiom_policy"], "axiom_audit": self.metadata["axiom_audit"],
                "proof_binding": self.metadata["proof_binding"],
                "checkers": self.metadata["provenance"]["checkers"], "subjects": self.graph.subject_coverage()}

    def statistics(self) -> dict:
        """count selected coverage without loading proof terms or the complete graph."""
        modules = sorted(self.metadata["local_modules"])
        marks = ",".join("?" for _ in modules)
        with self.connect() as connection:
            row = connection.execute(f"""SELECT count(*) AS declarations,
                count(CASE WHEN selected THEN 1 END) AS selected,
                count(CASE WHEN selected AND module IN ({marks}) THEN 1 END) AS local,
                count(CASE WHEN selected AND kind='theorem' THEN 1 END) AS theorems,
                count(CASE WHEN selected AND doc IS NOT NULL AND doc!='' THEN 1 END) AS documented,
                count(CASE WHEN selected AND axiom_count=0 THEN 1 END) AS axiom_free
                FROM declarations""", modules).fetchone()
        return {**dict(row), "lean_version": self.metadata["lean_version"],
                "subject_modules": len(self.metadata["module_policy"]) - 1}

    @staticmethod
    def _summary(row) -> dict:
        return {"name": row["name"], "module": row["module"], "kind": row["kind"],
                "statement": row["statement"], "doc": row["doc"], "axioms": json.loads(row["axioms"]),
                "selected": bool(row["selected"]), "meta": bool(row["meta"])}

    def _search_parts(self, query, subject, include_dependencies, kind, axiom_free, module):
        terms = query.casefold().split()
        prefix, parameters, where = "", [], []
        if subject:
            modules = sorted(self.graph.subject_modules(subject))
            marks = ",".join("?" for _ in modules)
            prefix = f"WITH RECURSIVE scope(id) AS (SELECT declaration FROM selections WHERE module IN ({marks})"
            if include_dependencies:
                prefix += " UNION SELECT e.target FROM edges e JOIN scope s ON s.id=e.source"
            prefix += ") "
            parameters.extend(modules)
            where.append("d.id IN (SELECT id FROM scope)")
        elif not include_dependencies:
            where.append("d.selected=1")
        for term in terms:
            where.append("instr(d.search_text, ?) > 0")
            parameters.append(term)
        if kind:
            where.append("d.kind=?")
            parameters.append(kind)
        if module:
            where.append("(d.module=? OR d.id IN (SELECT declaration FROM selections WHERE module=?))")
            parameters.extend([module, module])
        if axiom_free:
            where.append("d.axiom_count=0")
        clause = " WHERE " + " AND ".join(where) if where else ""
        score = "+".join("(instr(d.doc_fold, ?) > 0)" for _ in terms) or "CAST(0 AS INTEGER)"
        order = f" ORDER BY (d.name_fold != ?), (substr(d.name,1,9)='_private.'), -({score}), d.name"
        return prefix, clause, parameters, order, [query.strip().casefold(), *terms]

    def search(self, query: str = "", subject: str | None = None, include_dependencies: bool = False,
               kind: str | None = None, axiom_free: bool = False, offset: int = 0, limit: int = 30,
               module: str | None = None) -> dict:
        require(0 <= offset and 1 <= limit <= 200, "invalid search page")
        require(len(query) <= 1000 and len(query.split()) <= 30, "search query is too long")
        prefix, clause, parameters, order, ranking = self._search_parts(
            query, subject, include_dependencies, kind, axiom_free, module)
        with self.connect() as connection:
            total = connection.execute(prefix + "SELECT count(*) FROM declarations d" + clause, parameters).fetchone()[0]
            rows = connection.execute(prefix + f"SELECT {SUMMARY_COLUMNS} FROM declarations d" + clause + order +
                                      " LIMIT ? OFFSET ?", [*parameters, *ranking, limit, offset]).fetchall()
        return {"items": [self._summary(row) for row in rows], "total": total, "offset": offset, "limit": limit}

    def iter_search(self, query: str = "", subject: str | None = None, include_dependencies: bool = False,
                    kind: str | None = None, axiom_free: bool = False, module: str | None = None):
        """stream every matching declaration without the browser's page or query limits."""
        terms = query.casefold().split()
        if len(query) > 1000 or len(terms) > 30:
            def matches(node):
                text = " ".join((node["name"], node["statement"], node["doc"] or "")).casefold()
                return all(term in text for term in terms)

            records = (node for node in self.iter_search("", subject, include_dependencies, kind, axiom_free, module)
                       if matches(node))
            yield from sorted(records, key=lambda node: (
                node["name"].casefold() != query.strip().casefold(), node["name"].startswith("_private."),
                -sum(term in (node["doc"] or "").casefold() for term in terms), node["name"]))
            return
        prefix, clause, parameters, order, ranking = self._search_parts(
            query, subject, include_dependencies, kind, axiom_free, module)
        with self.connect() as connection:
            rows = connection.execute(prefix + f"SELECT {SUMMARY_COLUMNS} FROM declarations d" + clause + order,
                                      [*parameters, *ranking])
            for row in rows:
                yield self._summary(row)

    def declaration(self, name: str, proof: bool = False) -> dict:
        with self.connect() as connection:
            row = connection.execute("SELECT record, selected, digest FROM declarations WHERE name=?", (name,)).fetchone()
            require(row is not None, f"unknown declaration: {name}")
            record = json.loads(row["record"])
            origin = connection.execute("SELECT origin FROM sources WHERE module=?", (record["module"],)).fetchone()
            modules = [item[0] for item in connection.execute("""SELECT module FROM selections
                WHERE declaration=(SELECT id FROM declarations WHERE name=?) ORDER BY module""", (name,))]
        if not proof:
            record.pop("proof", None)
        return {**record, "selected": bool(row["selected"]), "selected_modules": modules, "digest": row["digest"],
                "origin": json.loads(origin[0]) if origin else {}}

    def _relation_parts(self, connection, name, reverse, transitive, role):
        require(role is None or role in ROLES, "unknown dependency role")
        row = connection.execute("SELECT id FROM declarations WHERE name=?", (name,)).fetchone()
        require(row is not None, f"unknown declaration: {name}")
        identifier = row[0]
        source, target = ("target", "source") if reverse else ("source", "target")
        role_clause = f" AND (e.roles & {ROLES[role]}) != 0" if role else ""
        if transitive:
            prefix = f"WITH RECURSIVE scope(id) AS (SELECT ? UNION SELECT e.{target} FROM edges e JOIN scope s ON s.id=e.{source}{role_clause}) "
            query = " FROM declarations d WHERE d.id IN (SELECT id FROM scope) AND d.id != ?"
            return prefix, query, [identifier, identifier], "0"
        query = f" FROM edges e JOIN declarations d ON d.id=e.{target} WHERE e.{source}=?{role_clause}"
        return "", query, [identifier], "e.roles"

    def relations(self, name: str, reverse: bool = False, transitive: bool = False, role: str | None = None,
                  offset: int = 0, limit: int = 30) -> dict:
        require(0 <= offset and 1 <= limit <= 200, "invalid dependency page")
        with self.connect() as connection:
            prefix, query, parameters, roles = self._relation_parts(connection, name, reverse, transitive, role)
            total = connection.execute(prefix + "SELECT count(*)" + query, parameters).fetchone()[0]
            rows = connection.execute(prefix + f"SELECT {SUMMARY_COLUMNS}, {roles} AS edge_roles" + query +
                                      " ORDER BY d.name LIMIT ? OFFSET ?",
                                      [*parameters, limit, offset]).fetchall()
        return {"items": [{**self._summary(row), "roles": [key for key, value in ROLES.items()
                                                             if row["edge_roles"] & value]} for row in rows],
                "total": total, "offset": offset, "limit": limit}

    def dependency_names(self, name: str, reverse: bool = False, transitive: bool = False):
        """stream all prerequisite or dependent names, excluding the starting declaration."""
        with self.connect() as connection:
            prefix, query, parameters, _ = self._relation_parts(connection, name, reverse, transitive, None)
            for row in connection.execute(prefix + "SELECT d.name" + query + " ORDER BY d.name", parameters):
                if row[0] != name:
                    yield row[0]

    def iter_edges(self):
        """stream the complete dependency graph in declaration name order."""
        with self.connect() as connection:
            yield from connection.execute("""SELECT s.name, t.name FROM edges e
                JOIN declarations s ON s.id=e.source JOIN declarations t ON t.id=e.target
                ORDER BY s.name, t.name""")

    def expressions(self, name: str) -> dict:
        node = self.declaration(name)
        pending = {node["type"]}
        if node["value"] is not None:
            pending.add(node["value"])
        if node["kind"] == "recursor":
            pending.update(rule["rhs"] for rule in node["structure"]["rules"])
        records, hashes = {}, {}
        with self.connect() as connection:
            while pending:
                batch = sorted(pending)[:500]
                pending.difference_update(batch)
                marks = ",".join("?" for _ in batch)
                rows = connection.execute(f"SELECT id, record, digest FROM expressions WHERE id IN ({marks})", batch).fetchall()
                require(len(rows) == len(batch), "query store has a missing proof expression")
                for identifier, record, value in rows:
                    expression = json.loads(record)
                    records[str(identifier)] = expression
                    hashes[str(identifier)] = value
                    for field in CHILD_FIELDS.get(expression["tag"], ()):
                        child = expression[field]
                        if str(child) not in records:
                            pending.add(child)
                pending.difference_update(int(key) for key in records)
        names = expression_names(node, records.values())
        identities = {}
        with self.connect() as connection:
            ordered = sorted(names)
            for offset in range(0, len(ordered), 500):
                batch = ordered[offset:offset + 500]
                marks = ",".join("?" for _ in batch)
                for key, parts in connection.execute(f"SELECT name, parts FROM names WHERE name IN ({marks})", batch):
                    identities[key] = json.loads(parts)
        require(identities.keys() == names, "query store has a missing logical name")
        return {"declaration": name, "type": node["type"], "value": node["value"],
                "structure": node["structure"], "expressions": records, "expression_hashes": hashes,
                "universes": node["universes"], "definition_group": node.get("definition_group", []),
                "reducibility": node.get("reducibility"),
                "name_data": identities}

    def term(self, name: str, root: str = "value", path: str = "", rule: int | None = None) -> dict:
        """read an exact term occurrence and preserve its local binder context."""
        node = self.declaration(name)
        records = {}
        with self.connect() as connection:
            def read(identifier):
                if identifier not in records:
                    row = connection.execute("SELECT record, digest FROM expressions WHERE id=?", (identifier,)).fetchone()
                    require(row is not None, "query store has a missing proof expression")
                    records[identifier] = {**json.loads(row[0]), "digest": row[1]}
                return records[identifier]

            result = inspect_term(node, read, root, path, rule)
            names = expression_names({"name": node["name"], "universes": node["universes"]}, records.values())
            identities = {}
            ordered = sorted(names)
            for offset in range(0, len(ordered), 500):
                batch = ordered[offset:offset + 500]
                marks = ",".join("?" for _ in batch)
                for key, parts in connection.execute(f"SELECT name, parts FROM names WHERE name IN ({marks})", batch):
                    identities[key] = json.loads(parts)
            require(identities.keys() == names, "query store has a missing logical name")
        return {**result, "name_data": identities}

    def source(self, name: str, full: bool = False) -> dict:
        node = self.declaration(name)
        with self.connect() as connection:
            row = connection.execute("SELECT text FROM sources WHERE module=?", (node["module"],)).fetchone()
        require(row is not None and row[0] is not None, "source text is unavailable in this snapshot")
        lines = row[0].splitlines()
        location = node["source"]
        start = 0 if full or not location else max(location["line"] - 5, 0)
        end = len(lines) if full or not location else min(location["end_line"] + 4, len(lines))
        return {"module": node["module"], "origin": node["origin"], "start_line": start + 1,
                "total_lines": len(lines), "lines": lines[start:end], "declaration_range": location,
                "sha256": hashlib.sha256(row[0].encode()).hexdigest()}


def open_snapshot(root: Path) -> Snapshot:
    from .build import input_hashes, read_json
    from .libraries import package_provenance, snapshot_packages

    root = root.resolve()
    receipt = read_json(root / "build/index.json")
    require(receipt.get("schema_version") == 1, "unsupported query store receipt")
    value = receipt.get("database_digest")
    require(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None, "invalid query store digest")
    require(receipt.get("database") == f"index-{value}.sqlite", "invalid query store path")
    path = root / "build" / receipt["database"]
    require(path.is_file() and not path.is_symlink(), "query store is missing; rerun verification")
    require(file_digest(path) == value, "query store digest mismatch; rerun verification")
    require(file_digest(root / "build/knowledge.json") == receipt.get("catalog_file_digest"), "query store catalog changed")
    provenance = receipt.get("provenance", {})
    require(provenance.get("inputs") == input_hashes(root), "query store is stale; rerun verification")
    require(provenance.get("source_digest") == digest(provenance["inputs"]), "query store source digest mismatch")
    policy, lock = read_json(root / "knowledge.json"), read_json(root / "lake-manifest.json")
    require(provenance.get("dependencies") == package_provenance(snapshot_packages(root, lock, policy)),
            "query store dependency sources changed")
    proof = root / "build" / f"proofs-{provenance.get('proof_export_digest')}.jsonl"
    require(isinstance(provenance.get("proof_export_digest"), str) and
            re.fullmatch(r"[0-9a-f]{64}", provenance["proof_export_digest"]) is not None, "invalid proof export digest")
    require(proof.is_file() and file_digest(proof) == provenance.get("proof_export_digest"), "query store proof export changed")
    return Snapshot(path, receipt)
