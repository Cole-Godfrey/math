"""retain source symbols, lexical scopes, and witnesses for native side conditions."""

from __future__ import annotations

from itertools import combinations
import json

from .metamath_audit import encoded, require


COMMENTS = {'Comment', 'AdditionalInfoComment', 'TypesettingComment', 'HeadingComment(MajorPart)',
            'HeadingComment(Section)', 'HeadingComment(SubSection)', 'HeadingComment(SubSubSection)'}
NAMED = {'Floating', 'Essential', 'Axiom', 'Provable'}
KINDS = {'constant', 'variable', 'scope', 'disjoint', 'assertion_symbols'}
RELATIONS = {'parent_scope', 'source_scope', 'expression_symbol', 'frame_variable',
             'mandatory_variable', 'mandatory_hypothesis', 'disjoint_variable',
             'proof_disjoint_clause', 'mandatory_disjoint_clause'}


def project(database, records, emit):
    """resolve every token and frame constraint in its original lexical context."""
    constants, variables = {}, {}
    scopes = [{'id': f'metamath-scope:{database}:global', 'variables': [], 'disjoint': set()}]
    active_disjoint = {}
    totals = {'constants': 0, 'variables': 0, 'scopes': 1, 'disjoint_clauses': 0,
              'named': 0, 'token_occurrences': 0}
    emit({'kind': 'scope', 'id': scopes[0]['id'], 'parent': None, 'source': None, 'ordinal': None})
    ordinal, finished = 0, False
    for row in records:
        require(not finished, 'records follow the source summary')
        if row['record'] == 'summary':
            finished = True
            continue
        require(row['record'] == 'statement' and type(row['ordinal']) is int and row['ordinal'] == ordinal,
                'primitive statement order differs')
        ordinal += 1
        kind, expression = row['kind'], row['expression']
        scope = scopes[-1]
        if kind == 'OpenGroup':
            child = {'id': f'metamath-scope:{database}:{row["ordinal"]}', 'variables': [], 'disjoint': set()}
            emit({'kind': 'scope', 'id': child['id'], 'parent': scope['id'],
                  'source': row['source'], 'ordinal': row['ordinal']})
            scopes.append(child)
            totals['scopes'] += 1
        elif kind == 'CloseGroup':
            require(len(scopes) > 1, 'source scope closes the global context')
            emit({'kind': 'scope_end', 'id': scope['id'], 'source': row['source'], 'ordinal': row['ordinal']})
            for token in scope['variables']:
                del variables[token]
            for pair in scope['disjoint']:
                del active_disjoint[pair]
            scopes.pop()
        elif kind in ['Constant', 'Variable']:
            require(kind != 'Constant' or len(scopes) == 1, 'constant declared in a local source scope')
            for slot, token in enumerate(expression):
                require(token not in constants and token not in variables, 'source symbol is already active')
                identifier = f'metamath-symbol:{database}:{row["ordinal"]}:{slot}'
                emit({'kind': 'constant' if kind == 'Constant' else 'variable', 'id': identifier, 'token': token,
                      'scope': scope['id'], 'ordinal': row['ordinal'], 'slot': slot, 'source': row['source']})
                if kind == 'Constant':
                    constants[token] = identifier
                    totals['constants'] += 1
                else:
                    variables[token] = identifier
                    scope['variables'].append(token)
                    totals['variables'] += 1
        elif kind == 'Disjoint':
            require(len(expression) >= 2 and len(expression) == len(set(expression)) and
                    all(token in variables for token in expression), 'invalid source disjoint clause')
            identifiers = [variables[token] for token in expression]
            clause = f'metamath-disjoint:{database}:{row["ordinal"]}'
            for left, right in combinations(identifiers, 2):
                pair = tuple(sorted((left, right)))
                if pair not in active_disjoint:
                    active_disjoint[pair] = clause
                    scope['disjoint'].add(pair)
            emit({'kind': 'disjoint', 'id': clause, 'scope': scope['id'], 'variables': identifiers,
                  'source': row['source'], 'ordinal': row['ordinal']})
            totals['disjoint_clauses'] += 1
        elif kind in NAMED:
            require(all(token in constants or token in variables for token in expression),
                    'expression symbol is not active')
            tokens = [variables[token] if token in variables else constants[token] for token in expression]
            frame = row['frame']
            constraints = {'proof_disjoint': [], 'mandatory_disjoint': []}
            if frame:
                require(all(token in variables for token in frame['variables']), 'frame variable is not active')
                for field in constraints:
                    for left, right in frame[field]:
                        require(left in variables and right in variables, 'disjoint frame variable is not active')
                        identifiers = [variables[left], variables[right]]
                        pair = tuple(sorted(identifiers))
                        require(pair in active_disjoint, 'frame disjoint clause is not active')
                        constraints[field].append({'variables': identifiers, 'clause': active_disjoint[pair]})
                require({tuple(sorted(item['variables'])) for item in constraints['proof_disjoint']} ==
                        set(active_disjoint), 'frame omits an active source disjoint clause')
            emit({'kind': 'assertion_symbols', 'id': f'metamath:{database}:{row["label"]}',
                  'native_kind': kind, 'scope': scope['id'], 'tokens': tokens,
                  'frame_variables': [variables[token] for token in frame['variables']] if frame else [],
                  'mandatory_variables': [variables[token] for token in frame['mandatory_variables']] if frame else [],
                  'hypotheses': [f'metamath:{database}:{label}' for label in frame['hypotheses']] if frame else [],
                  **constraints, 'source': row['source'], 'ordinal': row['ordinal']})
            totals['named'] += 1
            totals['token_occurrences'] += len(tokens)
        else:
            require(kind in COMMENTS or kind == 'Eof', 'unknown source primitive kind')
    require(finished and len(scopes) == 1, 'source primitive stream is incomplete')
    return totals


class PrimitiveWriter:
    """add source relationships to the same content-addressed native database."""

    def __init__(self, connection):
        self.connection = connection
        connection.executescript('''
            create table primitive_objects (
                id integer primary key, identifier text unique not null,
                database_id text not null references databases(id), kind text not null, token text,
                scope_id integer references primitive_objects(id), ordinal integer,
                declaration_id text references declarations(id), record text not null
            );
            create table primitive_edges (
                source_id integer not null references primitive_objects(id),
                target_id integer not null references primitive_objects(id),
                relation text not null, position integer not null,
                primary key (source_id, relation, position)
            );
        ''')
        self.identifiers = {}
        self.counts = {}

    def add_database(self, database, records):
        require(database not in self.counts, 'source primitives already indexed')

        def resolve(identifier):
            require(identifier in self.identifiers, 'unresolved source primitive: ' + identifier)
            key, owner = self.identifiers[identifier]
            require(owner == database, 'source primitive belongs to another database')
            return key

        def emit(record):
            identifier, kind = record['id'], record['kind']
            if kind == 'scope_end':
                key = resolve(identifier)
                row = self.connection.execute('select record from primitive_objects where id=?', (key,)).fetchone()
                current = json.loads(row[0])
                require('close_source' not in current, 'source scope closed twice')
                current.update(close_source=record['source'], close_ordinal=record['ordinal'])
                self.connection.execute('update primitive_objects set record=? where id=?',
                                        (encoded(current).decode(), key))
                return
            require(identifier not in self.identifiers, 'duplicate source primitive identity')
            scope = record.get('scope') or record.get('parent')
            scope_key = resolve(scope) if scope is not None else None
            declaration = identifier if kind == 'assertion_symbols' else None
            cursor = self.connection.execute('''insert into primitive_objects
                (identifier,database_id,kind,token,scope_id,ordinal,declaration_id,record)
                values (?,?,?,?,?,?,?,?)''', (identifier, database, kind, record.get('token'), scope_key,
                                            record.get('ordinal'), declaration, encoded(record).decode()))
            key = cursor.lastrowid
            self.identifiers[identifier] = (key, database)
            edges = []
            if scope is not None:
                edges.append((key, scope_key, 'parent_scope' if kind == 'scope' else 'source_scope', 0))
            for field, relation in [('tokens', 'expression_symbol'), ('frame_variables', 'frame_variable'),
                                    ('mandatory_variables', 'mandatory_variable'),
                                    ('hypotheses', 'mandatory_hypothesis'), ('variables', 'disjoint_variable')]:
                for position, target in enumerate(record.get(field, [])):
                    edges.append((key, resolve(target), relation, position))
            for field in ['proof_disjoint', 'mandatory_disjoint']:
                for position, restriction in enumerate(record.get(field, [])):
                    edges.append((key, resolve(restriction['clause']), field + '_clause', position))
            require(all(target < key for _, target, _, _ in edges), 'cyclic source primitive relationship')
            self.connection.executemany('insert into primitive_edges values (?,?,?,?)', edges)

        self.counts[database] = project(database, records, emit)

    def finish(self):
        self.connection.executescript('''
            create index reverse_primitive_edges on primitive_edges(target_id,relation,source_id,position);
            create index primitive_tokens on primitive_objects(token,database_id,kind);
            create index primitive_kinds on primitive_objects(database_id,kind,id);
            create index primitive_scopes on primitive_objects(scope_id,id);
        ''')
        return {'schema_version': 1, 'databases': self.counts}


class PrimitiveReader:
    """query lexical source relationships independently of mathematical proof edges."""

    def __init__(self, connection):
        self.connection = connection

    @staticmethod
    def page(offset, limit):
        require(type(offset) is int and 0 <= offset < 2 ** 63, 'invalid primitive offset')
        require(limit is None or type(limit) is int and 0 < limit < 2 ** 63, 'invalid primitive limit')

    @staticmethod
    def decode(row):
        return {**dict(row), 'record': json.loads(row['record'])}

    def object(self, identifier):
        row = self.connection.execute('select * from primitive_objects where identifier=?', (identifier,)).fetchone()
        require(row is not None, 'unknown source primitive: ' + identifier)
        return self.decode(row)

    def search(self, query='', database=None, kind=None, offset=0, limit=None):
        self.page(offset, limit)
        require(type(query) is str, 'invalid primitive query')
        require(kind is None or kind in KINDS, 'unknown source primitive kind')
        clauses, parameters = [], []
        if kind is None:
            clauses.append("kind!='assertion_symbols'")
        else:
            clauses.append('kind=?')
            parameters.append(kind)
        if database is not None:
            require(self.connection.execute('select 1 from databases where id=?', (database,)).fetchone() is not None,
                    'unknown source primitive database')
            clauses.append('database_id=?')
            parameters.append(database)
        for token in query.casefold().split():
            clauses.append("instr(lower(identifier || ' ' || coalesce(token,'')),?)>0")
            parameters.append(token)
        where = ' where ' + ' and '.join(clauses)
        total = self.connection.execute('select count(*) from primitive_objects' + where, parameters).fetchone()[0]
        rows = self.connection.execute('select * from primitive_objects' + where +
            ' order by (token=? or identifier=?) desc,identifier limit ? offset ?',
            [*parameters, query, query, limit if limit is not None else -1, offset])
        return {'items': [self.decode(row) for row in rows], 'total': total, 'offset': offset, 'limit': limit}

    def relations(self, identifier, reverse=False, relation=None, offset=0, limit=None):
        self.page(offset, limit)
        require(type(reverse) is bool, 'invalid primitive relation direction')
        require(relation is None or relation in RELATIONS, 'unknown source primitive relation')
        key = self.object(identifier)['id']
        where = ' where e.' + ('target_id' if reverse else 'source_id') + '=?'
        parameters = [key]
        if relation:
            where += ' and e.relation=?'
            parameters.append(relation)
        total = self.connection.execute('select count(*) from primitive_edges e' + where, parameters).fetchone()[0]
        rows = self.connection.execute('''select s.identifier,t.identifier,e.relation,e.position from primitive_edges e
            join primitive_objects s on s.id=e.source_id join primitive_objects t on t.id=e.target_id''' +
            where + ' order by e.source_id,e.relation,e.position limit ? offset ?',
            [*parameters, limit if limit is not None else -1, offset])
        return {'items': [{'source': row[0], 'target': row[1], 'relation': row[2], 'position': row[3]} for row in rows],
                'total': total, 'offset': offset, 'limit': limit}

    def context(self, identifier):
        node = self.object(identifier)
        key = node['id'] if node['kind'] == 'scope' else node['scope_id']
        scopes, seen = [], set()
        while key is not None:
            require(key not in seen, 'cyclic primitive source context')
            seen.add(key)
            row = self.connection.execute('select * from primitive_objects where id=?', (key,)).fetchone()
            require(row is not None and row['kind'] == 'scope', 'missing primitive source scope')
            scopes.append(self.decode(row))
            key = row['scope_id']
        return {'object': node, 'scopes': scopes}
