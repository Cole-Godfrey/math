"""fetch pinned native sources and verify their proofs before snapshot publication."""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from .core import require
from .libraries import package_provenance, snapshot_packages
from .metamath_audit import object_pairs
from .metamath_store import build, file_digest, Snapshot


PACKAGES = {'set.mm': 'set_mm', 'metamath-exe': 'exe', 'metamath-knife': 'knife'}
RUST = '1.94.1'


def run(root, arguments, environment=None):
    result = subprocess.run(arguments, cwd=root, env=environment, capture_output=True,
                            text=True, stdin=subprocess.DEVNULL)
    require(result.returncode == 0, 'command failed: ' + ' '.join(map(str, arguments)) + '\n' + result.stderr)
    return result.stdout


def read_lock(root):
    lock = json.loads((root / 'metamath-lock.json').read_text(), object_pairs_hook=object_pairs)
    require(set(lock) == set(PACKAGES), 'unsupported native package registry')
    for name, package in lock.items():
        require(type(package) is dict and re.fullmatch(r'[a-f0-9]{40}', package.get('revision', '')) is not None,
                'native package revision must be an exact commit')
        require(package.get('repository', '').startswith('https://github.com/metamath/'),
                'native package repository differs from the pinned source registry')
        filename = package.get('license_file', '')
        require(Path(filename).name == filename and bool(filename), 'invalid native license path')
        require(re.fullmatch(r'[a-f0-9]{64}', package.get('license_sha256', '')) is not None,
                'invalid native license digest')
    for filename, source in lock['set.mm']['databases'].items():
        require(re.fullmatch(r'[A-Za-z0-9_.-]+\.mm', filename) is not None, 'invalid native database filename')
        require(re.fullmatch(r'[a-f0-9]{64}', source.get('sha256', '')) is not None,
                'invalid native database source digest')
        require(type(source.get('bytes')) is int and source['bytes'] > 0, 'invalid native source length')
    return lock


def package_lock(lock):
    return {'packagesDir': '.tools/metamath', 'packages': [
        {'name': PACKAGES[name], 'type': 'git', 'rev': package['revision'], 'url': package['repository']}
        for name, package in lock.items()
    ]}


def sources(root, lock):
    packages = snapshot_packages(root, package_lock(lock), {})
    for name, package in lock.items():
        checkout = packages[PACKAGES[name]].root
        require(file_digest(checkout / package['license_file']) == package['license_sha256'],
                name + ': license differs from the pinned source')
    checkout = packages['set_mm'].root
    for name, expected in lock['set.mm']['databases'].items():
        path = checkout / name
        require(path.stat().st_size == expected['bytes'] and file_digest(path) == expected['sha256'],
                name + ': native database differs from the pinned source')
    require(file_digest(packages['knife'].root / 'Cargo.lock') == lock['metamath-knife']['cargo_lock_sha256'],
            'native verifier dependency lock differs')
    return packages


def fetch(root):
    """materialize exact commits without changing an existing checkout."""
    root = Path(root).resolve()
    lock = read_lock(root)
    for name, package in lock.items():
        checkout = root / '.tools/metamath' / PACKAGES[name]
        require(not checkout.is_symlink(), 'native checkout is a symlink')
        if checkout.exists():
            continue
        checkout.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix=PACKAGES[name] + '-', dir=checkout.parent) as temporary:
            staging = Path(temporary) / 'source'
            run(root, ['git', 'init', str(staging)])
            run(root, ['git', '-C', str(staging), 'remote', 'add', 'origin', package['repository']])
            run(root, ['git', '-C', str(staging), 'fetch', '--depth', '1', 'origin', package['revision']])
            run(root, ['git', '-C', str(staging), 'checkout', '--detach', package['revision']])
            staging.rename(checkout)
    sources(root, lock)


def native_inputs(root):
    paths = [root / 'metamath-lock.json']
    paths.extend((root / 'tools/metamath-export').rglob('*.rs'))
    paths.extend(root / 'tools/metamath-export' / filename for filename in ['Cargo.toml', 'Cargo.lock'])
    paths.extend((root / 'tests/fixtures/metamath').glob('*'))
    result = {}
    for path in sorted(paths):
        require(path.is_file() and not path.is_symlink(), 'invalid native verification input: ' + str(path))
        result[path.relative_to(root).as_posix()] = file_digest(path)
    return result


def compile_tools(root, packages):
    """build the two independent checkers and the instrumented proof exporter."""
    installed = run(root, ['rustup', 'toolchain', 'list'])
    require(any(line.split()[0].split('-')[0] == RUST for line in installed.splitlines()),
            'install the pinned Rust toolchain with: rustup toolchain install ' + RUST + ' --profile minimal')
    directory = root / '.tools/metamath'
    c = directory / 'metamath'
    run(root, ['cc', '-O2', *map(str, sorted((packages['exe'].root / 'src').glob('m*.c'))), '-lm', '-o', str(c)])
    cargo = ['rustup', 'run', RUST, 'cargo', 'build', '--release', '--locked', '--jobs', '2', '--manifest-path']
    paths = []
    for manifest, target, binary in [
        (packages['knife'].root / 'Cargo.toml', directory / 'knife-target', 'metamath-knife'),
        (root / 'tools/metamath-export/Cargo.toml', directory / 'export-target', 'math-metamath-export'),
    ]:
        environment = {**os.environ, 'CARGO_TARGET_DIR': str(target)}
        run(root, [*cargo, str(manifest)], environment)
        paths.append(target / 'release' / binary)
    versions = {'c': run(root, ['cc', '--version']),
                'rust': run(root, ['rustup', 'run', RUST, 'rustc', '-Vv'])}
    return c, *paths, versions


def check_native(root, source, c, rust, expected):
    """require positive proof verification; the c checker returns zero for some errors."""
    output = run(root, [str(c), f'read "{source}"', 'verify proof *', 'exit'])
    require('All proofs in the database were verified in ' in output and
            not any(line.lstrip().startswith('?') for line in output.splitlines()),
            source.name + ': the original checker rejected the database')
    result = subprocess.run([str(rust), '--time', '--jobs', '2', '--split', '--verify', str(source)],
                            cwd=root, capture_output=True, text=True, stdin=subprocess.DEVNULL)
    plain = re.sub(r'\x1b\[[0-9;]*m', '', result.stdout + result.stderr)
    if source.name == 'big-unifier.mm':
        require(expected == '664669725ff42cb35a4b4c10823b5a7664d8f404eab94385de0ace79e6aa501e' and
                result.returncode == 1 and '1 diagnostics issued.' in plain and
                'big-unifier.mm:345:5' in plain and
                re.findall(r'^(warning|error): (.+)$', plain, re.M) == [('warning', 'Wrong comment marker')],
                'the reviewed documentation warning differs')
    else:
        require(result.returncode == 0 and '0 diagnostics issued.' in plain,
                source.name + ': the independent checker rejected the database')
    return {'c': output, 'rust': plain}


def verify(root):
    """publish a native snapshot only after both checkers and exact source replay pass."""
    root = Path(root).resolve()
    from .build import input_hashes

    before = input_hashes(root)
    lock = read_lock(root)
    packages = sources(root, lock)
    dependency_hashes = package_provenance(packages)
    c, rust, exporter, versions = compile_tools(root, packages)
    provenance = {'lock': lock, 'inputs': before, 'dependencies': dependency_hashes,
                  'compiler_versions': versions, 'tools': {path.name: file_digest(path) for path in [c, rust, exporter]},
                  'checkers': ['metamath-exe', 'metamath-knife', 'independent source and proof-dag replay'], 'checks': {}}
    parent = root / 'build/metamath'
    parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='extract-', dir=parent) as temporary:
        directory = Path(temporary)
        databases = []
        for name, expected in lock['set.mm']['databases'].items():
            source = packages['set_mm'].root / name
            provenance['checks'][name] = check_native(root, source, c, rust, expected['sha256'])
            proof = directory / (name + '.jsonl')
            run(root, [str(exporter), str(source), str(proof)])
            databases.append({'id': name, 'source': source, 'proof': proof})
        require(input_hashes(root) == before, 'native verification inputs changed')
        require(package_provenance(sources(root, lock)) == dependency_hashes, 'native dependency sources changed')
        def before_publish():
            require(input_hashes(root) == before, 'native verification inputs changed before publication')
            require(package_provenance(sources(root, lock)) == dependency_hashes,
                    'native dependency sources changed before publication')

        receipt = build(parent, databases, provenance, before_publish)
        require(input_hashes(root) == before, 'native verification inputs changed while publishing')
        require(package_provenance(sources(root, lock)) == dependency_hashes, 'native dependency sources changed while publishing')
    return receipt


def open_snapshot(root):
    """bind default native queries to current repository and upstream source bytes."""
    from .build import input_hashes

    root = Path(root).resolve()
    snapshot = Snapshot(root / 'build/metamath')
    try:
        provenance = snapshot.manifest['provenance']
        require(provenance.get('inputs') == input_hashes(root), 'native index is stale; rerun verification')
        lock = read_lock(root)
        require(provenance.get('lock') == lock, 'native snapshot lock differs from current sources')
        require(provenance.get('dependencies') == package_provenance(sources(root, lock)),
                'native dependency source provenance differs')
        require(provenance.get('checkers') == ['metamath-exe', 'metamath-knife', 'independent source and proof-dag replay'],
                'native snapshot has incomplete proof verification provenance')
        require(set(snapshot.manifest['databases']) == set(lock['set.mm']['databases']),
                'native snapshot omits a registered database')
    except BaseException:
        snapshot.close()
        raise
    return snapshot
