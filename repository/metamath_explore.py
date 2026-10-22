"""expose native statements without changing their proof calculus or local premises."""

from __future__ import annotations

from collections import Counter, deque
from array import array
from functools import lru_cache
import json
import re
import tarfile

from .core import require
from .metamath_store import identity
from .metamath_audit import encoded
from .metamath_steps import NativeSteps


KINDS = {'Axiom': 'axiom', 'Provable': 'theorem', 'Floating': 'parameter', 'Essential': 'hypothesis'}
FOUNDATION = {
    'id': 'metamath-substitution-calculus',
    'rules': ['ordered floating and essential hypotheses', 'simultaneous token substitution',
              'disjoint-variable restrictions', 'previously established assertions'],
    'reference': 'https://us.metamath.org/downloads/metamath.pdf',
}


class NativeExplorer:
    """serve an admitted archive through request-local database connections."""

    def __init__(self, snapshot):
        self.snapshot = snapshot
        self.steps = NativeSteps(snapshot)
        self.metadata = {'content_digest': snapshot.digest, 'foundation': FOUNDATION, 'proof_system': 'metamath'}
        with snapshot.reader() as reader:
            self.databases = {row['id']: dict(row) for row in reader.connection.execute('select * from databases')}
        for database, row in self.databases.items():
            row['verification'] = json.loads(row['verification'])
            row['axiom_names'] = tuple(identity(database, label) for label in row['verification']['axiom_labels'])
        self.subjects = {'metamath': {'title': 'Native Metamath', 'parent': 'mathematics'}}
        self.subjects.update({'metamath-db:' + database: {'title': database, 'parent': 'metamath'}
                             for database in self.databases})

    def foundation(self, database):
        return {**FOUNDATION, 'id': 'metamath:' + database, 'database': database,
                'source_sha256': self.databases[database]['source_sha256']}

    def summary(self):
        coverage = self.subject_coverage()
        counts = self.snapshot.manifest['counts']
        total = sum(counts.values())
        selected = counts.get('Axiom', 0) + counts.get('Provable', 0)
        root = {'id': 'mathematics', 'title': 'Mathematics', 'parent': None,
                'modules': coverage[0]['modules'], 'selected_declarations': selected,
                'dependency_declarations': total, 'theorems': counts.get('Provable', 0),
                'axioms': coverage[0]['axioms']}
        return {'catalog_digest': self.snapshot.digest, 'proof_system': 'metamath', 'declarations': total,
                'selected': selected, 'theorems': counts.get('Provable', 0), 'foundation': FOUNDATION,
                'axiom_policy': {}, 'bibliography_keys': [], 'subjects': [root, *coverage],
                'checkers': ['Metamath C verifier', 'metamath-knife', 'independent source replay'],
                'native_databases': [{'id': database, 'axiom_rules': len(self.databases[database]['axiom_names'])}
                                     for database in sorted(self.databases)],
                'source_primitives': self.snapshot.manifest.get('source_primitives'),
                'proof_binding': {'method': 'independent source replay and exact native proof-step digests'}}

    def primitives(self, query='', database=None, kind=None, offset=0, limit=30):
        require(type(limit) is int and 1 <= limit <= 200, 'invalid source primitive page')
        with self.snapshot.reader() as reader:
            return reader.primitives(query, database, kind, offset, limit)

    def primitive(self, name):
        with self.snapshot.reader() as reader:
            node = reader.primitive(name)
        return {**node, 'origin': self.origin(node['database_id']), 'proof_system': 'metamath'}

    def primitive_relations(self, name, reverse=False, relation=None, offset=0, limit=30):
        require(type(limit) is int and 1 <= limit <= 200, 'invalid source primitive relation page')
        with self.snapshot.reader() as reader:
            return reader.primitive_relations(name, reverse, relation, offset, limit)

    def primitive_context(self, name):
        with self.snapshot.reader() as reader:
            return reader.primitive_context(name)

    def primitive_source(self, name, full=False):
        with self.snapshot.reader() as reader:
            return reader.primitive_source(name, full)

    def expressions(self, name):
        return self.steps.reconstruct(name)

    def term(self, name, step=None):
        return self.steps.inspect(name, step)

    def foundations(self, name, offset=0, limit=30):
        require(type(offset) is int and offset >= 0 and type(limit) is int and 1 <= limit <= 200,
                'invalid foundational rule page')
        node = self.declaration(name)
        graph = self.hierarchy(name)
        frame = node['frame']
        return {'declaration': name, 'foundation': node['foundation'], 'bound_assumption': node['bound_assumption'],
                'hypotheses': [self.declaration(hypothesis) for hypothesis in node['hypotheses']],
                'disjoint': frame['mandatory_disjoint'] if frame else [],
                'items': [{**self.declaration(axiom), 'path': graph['axiom_paths'][axiom]}
                          for axiom in node['axioms'][offset:offset + limit]],
                'total': len(node['axioms']), 'offset': offset, 'limit': limit}

    def citations(self, name):
        node = self.declaration(name)
        return {'declaration': name, 'module': node['module'], 'origin': node['origin'],
                'declaration_doc': node['doc'] or '', 'module_docs': [], 'bibliographies': [],
                'declaration_citations': [], 'module_citations': [], 'proof_system': 'metamath'}

    def bibliography(self, package):
        require(False, 'native references are retained in the original source comments')

    def catalog_chunks(self):
        yield encoded(self.snapshot.manifest) + b'\n'

    def archive_chunks(self):
        """retain original member bytes in a complete, portable native snapshot archive."""
        pointer = encoded({'directory': self.snapshot.digest, 'snapshot_digest': self.snapshot.digest}) + b'\n'
        members = [('index.json', pointer)] + [(self.snapshot.digest + '/' + name, self.snapshot.directory / name)
            for name in ['manifest.json', *sorted(self.snapshot.manifest['artifacts'])]]
        for name, value in members:
            size = len(value) if isinstance(value, bytes) else value.stat().st_size
            info = tarfile.TarInfo(name)
            info.size, info.mode, info.mtime = size, 0o644, 0
            yield info.tobuf(format=tarfile.USTAR_FORMAT)
            if isinstance(value, bytes):
                yield value
            else:
                with value.open('rb') as stream:
                    yield from iter(lambda: stream.read(65536), b'')
            if size % 512:
                yield bytes(512 - size % 512)
        yield bytes(1024)

    def origin(self, database):
        package = self.snapshot.manifest['provenance'].get('lock', {}).get('set.mm', {})
        origin = {'package': 'metamath-set', 'path': database,
                  'sha256': self.databases[database]['source_sha256'], 'license': 'CC0-1.0' if package else None}
        if package:
            origin.update(repository=package['repository'], revision=package['revision'],
                          url=package['repository'].removesuffix('.git') + '/blob/' + package['revision'] + '/' + database)
        return origin

    @lru_cache(maxsize=2)
    def source_bytes(self, database):
        return (self.snapshot.directory / self.databases[database]['source_file']).read_bytes()

    @lru_cache(maxsize=2)
    def source_offsets(self, database):
        """index source lines by the newline bytes used in the retained source spans."""
        source = self.source_bytes(database)
        offsets = array('Q', [0])
        offsets.extend(match.end() for match in re.finditer(b'\n', source))
        if offsets[-1] == len(source):
            offsets.pop()
        return offsets

    def documentation(self, database, start):
        source = self.source_bytes(database)
        end = source.rfind(b'$)', 0, start)
        if end < 0 or source[end + 2:start].strip():
            return None
        begin = source.rfind(b'$(', 0, end)
        while begin >= 0 and ((begin > 0 and not source[begin - 1:begin].isspace()) or
                             not source[begin + 2:begin + 3].isspace()):
            begin = source.rfind(b'$(', 0, begin)
        return source[begin + 2:end].decode('utf-8').strip() if begin >= 0 else None

    def _node(self, row, proof=False, reader=None):
        database = row['database_id']
        expression = json.loads(row['expression'])
        frame = json.loads(row['frame']) if row['frame'] else None
        checked = json.loads(row['checked']) if row['checked'] else None
        bits = int(checked['axiom_bits'], 16) if checked else 0
        axioms = [name for index, name in enumerate(self.databases[database]['axiom_names']) if bits & (1 << index)]
        hypotheses = [identity(database, label) for label in frame['hypotheses']] if frame else []
        node = {'name': row['id'], 'kind': KINDS[row['kind']], 'native_kind': row['kind'],
                'module': 'metamath:' + database, 'statement': ' '.join(expression),
                'statement_tokens': expression, 'doc': self.documentation(database, row['source_start']),
                'source': {'line': row['source_line'], 'end_line': row['source_end_line'],
                           'byte_start': row['source_start'], 'byte_end': row['source_end']},
                'proof_system': 'metamath', 'foundation': self.foundation(database), 'origin': self.origin(database),
                'frame': frame, 'hypotheses': hypotheses, 'axioms': axioms, 'lean_axioms': [],
                'bound_assumption': row['kind'] in ['Floating', 'Essential'],
                'selected': row['kind'] in ['Axiom', 'Provable'],
                'selected_modules': ['metamath:' + database] if row['kind'] in ['Axiom', 'Provable'] else [],
                'meta': False, 'unsafe': False, 'partial': False, 'universes': [], 'type': None, 'value': None,
                'structure': None, 'definition_group': [], 'reducibility': None}
        if reader is not None:
            dependencies = [item[0] for item in reader.connection.execute(
                'select dependency_id from dependencies where declaration_id=? order by dependency_id', (row['id'],))]
            node.update(dependencies=dependencies, type_dependencies=hypotheses,
                        value_dependencies=[name for name in dependencies if name not in hypotheses], structural_dependencies=[])
            if proof:
                node['proof'] = ' '.join(reader.proof(row['id'])['tokens']) if row['kind'] == 'Provable' else None
        return node

    def declaration(self, name, proof=False):
        with self.snapshot.reader() as reader:
            row = reader.connection.execute('select * from declarations where id=?', (name,)).fetchone()
            require(row is not None, 'unknown declaration: ' + name)
            return self._node(row, proof, reader)

    @lru_cache(maxsize=1)
    def subject_coverage(self):
        result = []
        with self.snapshot.reader() as reader:
            totals = Counter()
            for database in sorted(self.databases):
                named = reader.connection.execute('select count(*) from declarations where database_id=?',
                                                  (database,)).fetchone()[0]
                verification = self.databases[database]['verification']
                counts = named, verification['assertions'], verification['theorems']
                totals.update(dict(zip(['declarations', 'selected', 'theorems'], counts)))
                result.append({'id': 'metamath-db:' + database, 'title': database, 'parent': 'metamath',
                               'modules': ['metamath:' + database], 'selected_declarations': counts[1],
                               'dependency_declarations': counts[0], 'theorems': counts[2],
                               'axioms': list(self.databases[database]['axiom_names'])})
        result.insert(0, {'id': 'metamath', 'title': 'Native Metamath', 'parent': 'mathematics',
                          'modules': ['metamath:' + database for database in sorted(self.databases)],
                          'selected_declarations': totals['selected'], 'dependency_declarations': totals['declarations'],
                          'theorems': totals['theorems'], 'axioms': [name for database in self.databases
                                                                  for name in self.databases[database]['axiom_names']]})
        return result

    def search(self, query='', subject=None, include_dependencies=False, kind=None, axiom_free=False, offset=0, limit=30):
        require(type(offset) is int and offset >= 0 and type(limit) is int and 1 <= limit <= 200, 'invalid search page')
        where, parameters = [], []
        if not include_dependencies:
            where.append("kind in ('Axiom','Provable')")
        for term in query.casefold().split():
            field = 'id' if term.startswith('metamath:') else 'label'
            where.append('instr(lower(' + field + ' || " " || expression),?) > 0')
            parameters.append(term)
        if subject and subject not in ['mathematics', 'metamath']:
            require(subject in self.subjects, 'unknown native subject')
            where.append('database_id=?')
            parameters.append(subject.removeprefix('metamath-db:'))
        if kind:
            native = next((key for key, value in KINDS.items() if value == kind), None)
            if native is None:
                return {'items': [], 'total': 0, 'offset': offset, 'limit': limit}
            where.append('kind=?')
            parameters.append(native)
        if axiom_free:
            where.append("(checked is null or json_extract(checked,'$.axiom_bits')='0x0')")
        clause = ' where ' + ' and '.join(where) if where else ''
        with self.snapshot.reader() as reader:
            total = reader.connection.execute('select count(*) from declarations' + clause, parameters).fetchone()[0]
            rows = reader.connection.execute('select * from declarations' + clause +
                ' order by (id=? or label=?) desc, id limit ? offset ?', [*parameters, query, query, limit, offset])
            items = [self._node(row) for row in rows]
        return {'items': items, 'total': total, 'offset': offset, 'limit': limit}

    def relations(self, name, reverse=False, transitive=False, role=None, offset=0, limit=30):
        require(role is None or role in ['type', 'value', 'structure'], 'unknown dependency role')
        require(type(offset) is int and offset >= 0 and type(limit) is int and 1 <= limit <= 200, 'invalid dependency page')
        self.declaration(name)
        with self.snapshot.reader() as reader:
            source, target = ('dependency_id', 'declaration_id') if reverse else ('declaration_id', 'dependency_id')
            pending, reached = [name], set()
            roles, owner_hypotheses = {}, {}
            while pending:
                current = pending.pop()
                for child, owner in reader.connection.execute(
                        'select ' + target + ', declaration_id from dependencies where ' + source + '=?', (current,)):
                    dependency = current if reverse else child
                    edge_role = None
                    if role or not transitive:
                        if owner not in owner_hypotheses:
                            frame, database = reader.connection.execute(
                                'select frame,database_id from declarations where id=?', (owner,)).fetchone()
                            frame = json.loads(frame) if frame else None
                            owner_hypotheses[owner] = {identity(database, label) for label in frame['hypotheses']} if frame else set()
                        edge_role = 'type' if dependency in owner_hypotheses[owner] else 'value'
                    if role and role != edge_role:
                        continue
                    if edge_role:
                        roles.setdefault(child, set()).add(edge_role)
                    if child not in reached:
                        reached.add(child)
                        if transitive:
                            pending.append(child)
            reached.discard(name)
            names = sorted(reached)
            items = []
            for child in names[offset:offset + limit]:
                row = reader.connection.execute('select * from declarations where id=?', (child,)).fetchone()
                items.append({**self._node(row), 'roles': sorted(roles[child]) if not transitive else []})
        return {'items': items, 'total': len(names), 'offset': offset, 'limit': limit}

    def source(self, name, full=False, line=None, limit=200):
        require(not full, 'use the native source download for a complete database')
        node = self.declaration(name)
        require(type(limit) is int and 1 <= limit <= 500, 'invalid source page')
        database = node['foundation']['database']
        offsets = self.source_offsets(database)
        start = max(0, node['source']['line'] - 5) if line is None else line - 1
        require(type(start) is int and 0 <= start < len(offsets), 'invalid source line')
        end = min(len(offsets), start + limit)
        source = self.source_bytes(database)
        page = source[offsets[start]:offsets[end] if end < len(offsets) else len(source)].decode('utf-8')
        lines = page.removesuffix('\n').split('\n')
        lines = [line.removesuffix('\r') for line in lines]
        return {'module': node['module'], 'origin': node['origin'], 'start_line': start + 1,
                'total_lines': len(offsets), 'lines': lines, 'declaration_range': node['source'],
                'sha256': node['origin']['sha256'], 'next_line': end + 1 if end < len(offsets) else None,
                'previous_line': max(1, start - limit + 1) if start else None, 'proof_system': 'metamath'}

    def hierarchy(self, name):
        with self.snapshot.reader() as reader:
            names = reader.dependencies(name, transitive=True) + [name]
            records = {key: reader.declaration(key) for key in names}
            edges = {key: reader.dependencies(key) for key in names}
        by_name = {key: index for index, key in enumerate(sorted(names))}
        levels, groups = {}, []
        for key in sorted(names, key=lambda item: records[item]['ordinal']):
            require(all(child in levels for child in edges[key]), 'native dependency order differs')
            level = 1 + max((levels[child] for child in edges[key]), default=-1)
            levels[key] = level
            groups.append({'id': by_name[key], 'members': [key], 'level': level,
                           'dependencies': sorted(by_name[child] for child in edges[key]), 'cyclic': False})
        node = self.declaration(name)
        parents = {name: None}
        pending = deque([name])
        while pending:
            current = pending.popleft()
            for child in edges[current]:
                if child not in parents:
                    parents[child] = current
                    pending.append(child)
        paths = {}
        for axiom in node['axioms']:
            route, current = [], axiom
            while current is not None:
                route.append(current)
                current = parents[current]
            paths[axiom] = list(reversed(route))
        graph_edges = []
        for source in sorted(names):
            frame = records[source]['frame']
            hyps = {identity(records[source]['database_id'], label) for label in frame['hypotheses']} if frame else set()
            graph_edges.extend({'from': source, 'to': target, 'roles': ['type' if target in hyps else 'value']}
                               for target in edges[source])
        return {'declaration': name, 'foundation': node['foundation'], 'axioms': node['axioms'], 'axiom_paths': paths,
                'groups': groups, 'edges': graph_edges,
                'declarations': [{'name': key, 'kind': KINDS[records[key]['kind']],
                                  'module': 'metamath:' + records[key]['database_id'], 'group': by_name[key]}
                                 for key in sorted(names)],
                'levels': [{'level': key, 'groups': count} for key, count in sorted(Counter(levels.values()).items())],
                'kinds': dict(Counter(KINDS[record['kind']] for record in records.values()))}
