"""inspect native metamath proofs and their database-qualified dependencies."""

import argparse
import json
from pathlib import Path
import sys

from .metamath_audit import ProofError, require
from .metamath_store import Snapshot


def parser():
    result = argparse.ArgumentParser(description='Explore verified native Metamath statements.')
    result.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    result.add_argument('--snapshot', type=Path)
    commands = result.add_subparsers(dest='command', required=True)
    commands.add_parser('stats')
    commands.add_parser('fetch')
    commands.add_parser('verify')
    search = commands.add_parser('search')
    search.add_argument('query', nargs='?', default='')
    search.add_argument('--database')
    search.add_argument('--kind', choices=['Axiom', 'Provable', 'Floating', 'Essential'])
    search.add_argument('--limit', type=int)
    primitives = commands.add_parser('primitives')
    primitives.add_argument('query', nargs='?', default='')
    primitives.add_argument('--database')
    primitives.add_argument('--kind', choices=['constant', 'variable', 'scope', 'disjoint', 'assertion_symbols'])
    primitives.add_argument('--offset', type=int, default=0)
    primitives.add_argument('--limit', type=int)
    for name in ['primitive', 'primitive-context', 'primitive-source']:
        command = commands.add_parser(name)
        command.add_argument('name')
        if name == 'primitive-source':
            command.add_argument('--full', action='store_true')
    relations = commands.add_parser('primitive-relations')
    relations.add_argument('name')
    relations.add_argument('--reverse', action='store_true')
    relations.add_argument('--relation')
    relations.add_argument('--offset', type=int, default=0)
    relations.add_argument('--limit', type=int)
    for name in ['show', 'proof', 'source', 'assumptions', 'hierarchy']:
        command = commands.add_parser(name)
        command.add_argument('name')
        if name == 'source':
            command.add_argument('--full', action='store_true')
    dependencies = commands.add_parser('deps')
    dependencies.add_argument('name')
    dependencies.add_argument('--transitive', action='store_true')
    trace = commands.add_parser('trace')
    trace.add_argument('name')
    trace.add_argument('target')
    return result


def hierarchy(snapshot, name):
    names = snapshot.dependencies(name, transitive=True) + [name]
    nodes = {key: snapshot.declaration(key) for key in names}
    ordered = sorted(names, key=lambda key: nodes[key]['ordinal'])
    levels = {}
    groups = []
    for key in ordered:
        dependencies = snapshot.dependencies(key)
        require(all(child in levels for child in dependencies), 'native dependency order is invalid')
        levels[key] = 1 + max((levels[child] for child in dependencies), default=-1)
        groups.append({'name': key, 'level': levels[key], 'dependencies': dependencies})
    return {'name': name, 'foundation': nodes[name]['foundation'],
            'assumptions': snapshot.assumptions(name), 'declarations': groups}


def main(arguments=None):
    options = parser().parse_args(arguments)
    snapshot = None
    try:
        if options.command == 'fetch':
            from .metamath_build import fetch
            fetch(options.root)
            return 0
        if options.command == 'verify':
            from .metamath_build import verify
            print(json.dumps(verify(options.root)))
            return 0
        if options.snapshot is not None:
            snapshot = Snapshot(options.snapshot)
        else:
            from .metamath_build import open_snapshot
            snapshot = open_snapshot(options.root)
        if options.command == 'stats':
            output = {'snapshot_digest': snapshot.digest,
                      'proof_system': snapshot.manifest['proof_system'],
                      'databases': snapshot.manifest['databases'], 'counts': snapshot.manifest['counts'],
                      'source_primitives': snapshot.manifest.get('source_primitives')}
        elif options.command == 'search':
            output = list(snapshot.iter_search(options.query, options.database, options.kind, options.limit))
        elif options.command == 'show':
            output = snapshot.declaration(options.name)
        elif options.command == 'primitives':
            output = snapshot.primitives(options.query, options.database, options.kind, options.offset, options.limit)
        elif options.command == 'primitive':
            output = snapshot.primitive(options.name)
        elif options.command == 'primitive-context':
            output = snapshot.primitive_context(options.name)
        elif options.command == 'primitive-relations':
            output = snapshot.primitive_relations(options.name, options.reverse, options.relation,
                                                   options.offset, options.limit)
        elif options.command == 'primitive-source':
            sys.stdout.buffer.write(snapshot.primitive_source(options.name, options.full))
            return 0
        elif options.command == 'proof':
            output = snapshot.proof(options.name)
        elif options.command == 'source':
            sys.stdout.buffer.write(snapshot.source(options.name, options.full))
            return 0
        elif options.command == 'assumptions':
            output = snapshot.assumptions(options.name)
        elif options.command == 'deps':
            output = snapshot.dependencies(options.name, options.transitive)
        elif options.command == 'trace':
            output = snapshot.path(options.name, options.target)
        else:
            output = hierarchy(snapshot, options.name)
        print(json.dumps(output, ensure_ascii=False, indent=2))
        return 0
    except (ProofError, OSError, ValueError, KeyError) as error:
        print(f'error: {error}', file=sys.stderr)
        return 1
    finally:
        if snapshot is not None:
            snapshot.close()


if __name__ == '__main__':
    raise SystemExit(main())
