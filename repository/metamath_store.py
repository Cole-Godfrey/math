"""build and query a source-bound metamath snapshot without merging its foundations."""

from __future__ import annotations

from collections import deque
from contextlib import contextmanager
import hashlib
import json
from pathlib import Path
import re
import shutil
import sqlite3
import tempfile

from .metamath_audit import audit, encoded, object_pairs, require
from .metamath_primitives import PrimitiveReader, PrimitiveWriter


def file_digest(path):
    result = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            result.update(chunk)
    return result.hexdigest()


def identity(database, label):
    require(re.fullmatch(r'[A-Za-z0-9_.-]+', database) is not None, 'invalid database identity')
    require(re.fullmatch(r'[A-Za-z0-9_.-]+', label) is not None, 'invalid declaration label')
    return f'metamath:{database}:{label}'


def build(directory, databases, provenance, before_publish=None):
    """publish only after every database proof and source span has been audited."""
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='staging-', dir=directory) as temporary:
        staging = Path(temporary)
        connection = sqlite3.connect(staging / 'index.sqlite')
        connection.execute('pragma foreign_keys=on')
        connection.executescript('''
            create table databases (
                id text primary key, source_file text not null, proof_file text not null,
                source_sha256 text not null, proof_sha256 text not null, verification text not null
            );
            create table declarations (
                id text primary key, database_id text not null references databases(id),
                label text not null, kind text not null, ordinal integer not null,
                expression text not null, frame text, checked text,
                source_start integer not null, source_end integer not null,
                source_line integer not null, source_end_line integer not null,
                proof_offset integer not null, proof_length integer not null,
                unique (database_id, label)
            );
            create table dependencies (
                declaration_id text not null references declarations(id),
                dependency_id text not null references declarations(id),
                primary key (declaration_id, dependency_id)
            );
            create index reverse_dependencies on dependencies(dependency_id, declaration_id);
        ''')
        primitives = PrimitiveWriter(connection)
        artifacts = {}
        names = set()
        for database in databases:
            name = database['id']
            require(name not in names, 'duplicate database identity')
            names.add(name)
            identity(name, 'placeholder')
            require(name.endswith('.mm'), 'database identity must name a metamath source file')
            source_file = name
            proof_file = f'{name}.proof.jsonl'
            shutil.copyfile(database['source'], staging / source_file)
            shutil.copyfile(database['proof'], staging / proof_file)
            checked = {}
            def remember(record):
                checked[record['label']] = record

            verification = audit(staging / source_file, staging / proof_file, remember)
            connection.execute('insert into databases values (?, ?, ?, ?, ?, ?)', (
                name, source_file, proof_file, file_digest(staging / source_file),
                file_digest(staging / proof_file), encoded(verification).decode(),
            ))
            with (staging / proof_file).open('rb') as stream:
                while True:
                    offset = stream.tell()
                    line = stream.readline()
                    if not line:
                        break
                    row = json.loads(line, object_pairs_hook=object_pairs)
                    if row['record'] != 'statement' or row['label'] is None:
                        continue
                    key = identity(name, row['label'])
                    assertion = checked.get(row['label'])
                    span = row['source']
                    connection.execute('insert into declarations values (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)', (
                        key, name, row['label'], row['kind'], row['ordinal'], encoded(row['expression']).decode(),
                        encoded(row['frame']).decode(), encoded(assertion).decode() if assertion else None,
                        span['start'], span['end'], span['line'], span['end_line'], offset, len(line),
                    ))
                    references = set(row['frame']['hypotheses']) if row['frame'] else set()
                    if row['proof_dag']:
                        references.update(node['reference'] for node in row['proof_dag']['nodes'])
                    for label in sorted(references):
                        connection.execute('insert into dependencies values (?, ?)', (key, identity(name, label)))
            with (staging / proof_file).open('rb') as stream:
                header = json.loads(next(stream), object_pairs_hook=object_pairs)
                require(header['database'] == name, 'primitive database header differs')
                primitives.add_database(name, (json.loads(line, object_pairs_hook=object_pairs) for line in stream))
            for relative in [source_file, proof_file]:
                artifacts[relative] = file_digest(staging / relative)
        primitive_metadata = primitives.finish()
        connection.commit()
        require(connection.execute('pragma integrity_check').fetchall() == [('ok',)], 'snapshot database is corrupt')
        require(not connection.execute('pragma foreign_key_check').fetchall(), 'snapshot has unresolved dependencies')
        counts = {kind: count for kind, count in connection.execute(
            'select kind, count(*) from declarations group by kind')}
        connection.close()
        artifacts['index.sqlite'] = file_digest(staging / 'index.sqlite')
        manifest = {'schema_version': 1, 'proof_system': 'metamath',
                    'foundation': 'metamath-substitution-calculus',
                    'databases': sorted(names), 'counts': counts, 'artifacts': artifacts,
                    'source_primitives': primitive_metadata, 'provenance': provenance}
        manifest_bytes = encoded(manifest)
        digest = hashlib.sha256(manifest_bytes).hexdigest()
        target = directory / digest
        require(not target.exists(), 'snapshot already exists')
        (staging / 'manifest.json').write_bytes(manifest_bytes + b'\n')
        if before_publish is not None:
            before_publish()
        staging.rename(target)
        receipt = {'snapshot_digest': digest, 'directory': digest}
        pointer = directory / 'index.json.partial'
        pointer.write_bytes(encoded(receipt) + b'\n')
        pointer.replace(directory / 'index.json')
        return receipt


class Snapshot:
    """retain database-qualified labels and reconstruct each native rule application."""

    def __init__(self, directory):
        directory = Path(directory)
        pointer = json.loads((directory / 'index.json').read_text(), object_pairs_hook=object_pairs)
        digest = pointer['snapshot_digest']
        require(type(digest) is str and re.fullmatch(r'[a-f0-9]{64}', digest) is not None and
                pointer['directory'] == digest, 'invalid snapshot pointer')
        self.directory = directory / digest
        self.manifest = json.loads((self.directory / 'manifest.json').read_text(), object_pairs_hook=object_pairs)
        require(hashlib.sha256(encoded(self.manifest)).hexdigest() == digest, 'snapshot manifest digest differs')
        for name, expected in self.manifest['artifacts'].items():
            require(Path(name).name == name and not (self.directory / name).is_symlink(), 'invalid artifact path')
            require(file_digest(self.directory / name) == expected, 'snapshot artifact digest differs: ' + name)
        self.connection = sqlite3.connect((self.directory / 'index.sqlite').resolve().as_uri() + '?mode=ro', uri=True)
        self.connection.row_factory = sqlite3.Row
        self.digest = digest

    def close(self):
        self.connection.close()

    @contextmanager
    def reader(self):
        """open a request-local connection to an already validated immutable archive."""
        reader = object.__new__(type(self))
        reader.directory, reader.manifest, reader.digest = self.directory, self.manifest, self.digest
        reader.connection = sqlite3.connect((self.directory / 'index.sqlite').resolve().as_uri() +
                                           '?mode=ro&immutable=1', uri=True)
        reader.connection.row_factory = sqlite3.Row
        try:
            yield reader
        finally:
            reader.close()

    def declaration(self, name):
        row = self.connection.execute('select * from declarations where id=?', (name,)).fetchone()
        require(row is not None, 'unknown declaration: ' + name)
        result = dict(row)
        for key in ['expression', 'frame', 'checked']:
            result[key] = json.loads(result[key]) if result[key] is not None else None
        database = self.connection.execute('select * from databases where id=?', (row['database_id'],)).fetchone()
        result['foundation'] = {'proof_system': 'metamath', 'database': row['database_id'],
                                'source_sha256': database['source_sha256']}
        return result

    def primitive_reader(self):
        """require an indexed source context before querying primitive relationships."""
        metadata = self.manifest.get('source_primitives')
        require(type(metadata) is dict and type(metadata.get('schema_version')) is int and
                metadata['schema_version'] == 1, 'source primitive index is unavailable; rerun verification')
        return PrimitiveReader(self.connection)

    def primitives(self, query='', database=None, kind=None, offset=0, limit=None):
        return self.primitive_reader().search(query, database, kind, offset, limit)

    def primitive(self, name):
        return self.primitive_reader().object(name)

    def primitive_relations(self, name, reverse=False, relation=None, offset=0, limit=None):
        return self.primitive_reader().relations(name, reverse, relation, offset, limit)

    def primitive_context(self, name):
        return self.primitive_reader().context(name)

    def primitive_source(self, name, full=False):
        """read the exact declaration or complete enclosing source block."""
        node = self.primitive(name)
        database = self.connection.execute('select source_file from databases where id=?',
                                            (node['database_id'],)).fetchone()
        path = self.directory / database[0]
        record = node['record']
        if full or record['source'] is None:
            return path.read_bytes()
        start = record['source']['start']
        end = record.get('close_source', record['source'])['end']
        require(0 <= start <= end <= path.stat().st_size, 'primitive source span is invalid')
        with path.open('rb') as stream:
            stream.seek(start)
            return stream.read(end - start)

    def proof(self, name):
        row = self.declaration(name)
        database = self.connection.execute('select proof_file from databases where id=?', (row['database_id'],)).fetchone()
        with (self.directory / database['proof_file']).open('rb') as stream:
            stream.seek(row['proof_offset'])
            record = json.loads(stream.read(row['proof_length']), object_pairs_hook=object_pairs)
        require(record['label'] == row['label'], 'proof pointer differs from declaration')
        return {'tokens': record['proof'], 'dag': record['proof_dag'], 'frame': record['frame']}

    def source(self, name, full=False):
        row = self.declaration(name)
        database = self.connection.execute('select source_file from databases where id=?', (row['database_id'],)).fetchone()
        with (self.directory / database['source_file']).open('rb') as stream:
            if full:
                return stream.read()
            stream.seek(row['source_start'])
            return stream.read(row['source_end'] - row['source_start'])

    def dependencies(self, name, transitive=False):
        self.declaration(name)
        reached = set()
        pending = [name]
        while pending:
            current = pending.pop()
            for row in self.connection.execute('select dependency_id from dependencies where declaration_id=?', (current,)):
                child = row[0]
                if child not in reached:
                    reached.add(child)
                    if transitive:
                        pending.append(child)
        return sorted(reached)

    def assumptions(self, name):
        row = self.declaration(name)
        require(row['checked'] is not None, 'hypotheses have no theorem axiom closure')
        verification = json.loads(self.connection.execute(
            'select verification from databases where id=?', (row['database_id'],)).fetchone()[0])
        bits = int(row['checked']['axiom_bits'], 16)
        labels = verification['axiom_labels']
        return {'axiom_rules': [identity(row['database_id'], label) for index, label in enumerate(labels)
                                if bits & (1 << index)],
                'hypotheses': row['frame']['hypotheses'],
                'disjoint': row['frame']['mandatory_disjoint']}

    def path(self, name, target):
        self.declaration(name)
        self.declaration(target)
        pending = deque([name])
        parent = {name: None}
        while pending:
            current = pending.popleft()
            if current == target:
                route = []
                while current is not None:
                    route.append(current)
                    current = parent[current]
                return list(reversed(route))
            for child in self.dependencies(current):
                if child not in parent:
                    parent[child] = current
                    pending.append(child)
        return None

    def iter_search(self, query='', database=None, kind=None, limit=None):
        require(limit is None or type(limit) is int and limit > 0, 'invalid search limit')
        clauses = ['instr(lower(label || " " || expression), lower(?)) > 0']
        values = [query]
        for field, value in [('database_id', database), ('kind', kind)]:
            if value is not None:
                clauses.append(field + '=?')
                values.append(value)
        suffix = ''
        if limit is not None:
            suffix = ' limit ?'
            values.append(limit)
        for row in self.connection.execute(
                'select id from declarations where ' + ' and '.join(clauses) + ' order by id' + suffix, values):
            yield self.declaration(row[0])

    def search(self, query='', database=None, kind=None, limit=50):
        require(type(limit) is int and 0 < limit <= 500, 'invalid search limit')
        return list(self.iter_search(query, database, kind, limit))
