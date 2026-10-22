"""build Lean sources and publish an audited, source-bound index."""

from __future__ import annotations

import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from .core import RepositoryError, canonical, canonical_chunks, digest, registered_modules, require, stream_digest, subject_policy, validate
from .json_reader import read_object
from .libraries import package_provenance, snapshot_packages, source_origins
from .bibliography import archive_bibliographies


def read_json(path: Path) -> dict:
    try:
        with path.open(encoding="utf-8") as handle:
            result = read_object(handle)
    except (OSError, ValueError) as exc:
        raise RepositoryError(f"cannot read {path}: {exc}") from exc
    require(isinstance(result, dict), f"{path}: expected a json object")
    return result


def proof_export_path(root: Path, catalog: dict) -> Path:
    from .store import file_digest

    value = catalog.get("provenance", {}).get("proof_export_digest")
    require(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None,
            "missing proof export digest")
    path = root / "build" / f"proofs-{value}.jsonl"
    require(path.is_file(), "proof export is missing; rerun verification")
    require(file_digest(path) == value, "proof export digest mismatch")
    return path


def lean_sources(root: Path) -> list[Path]:
    paths = []
    for directory, subdirectories, files in os.walk(root):
        subdirectories[:] = sorted(name for name in subdirectories
                                   if name not in {".git", ".lake", ".tools", "build", "__pycache__"})
        paths.extend(Path(directory) / name for name in files if name.endswith(".lean"))
    return sorted(paths)


def input_hashes(root: Path) -> dict[str, str]:
    paths = [root / name for name in (
        "lean-toolchain", "lakefile.toml", "lake-manifest.json", "Math.lean", "knowledge.json",
    )]
    paths.extend(lean_sources(root))
    paths.extend((root / "repository").glob("*.py"))
    paths.extend((root / "tests").rglob("*.py"))
    result = {}
    for path in sorted(paths):
        require(path.is_file(), f"missing verification input: {path}")
        require(not path.is_symlink(), f"verification input is a symlink: {path}")
        result[path.relative_to(root).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    if (root / "metamath-lock.json").is_file():
        from .metamath_build import native_inputs
        result.update(native_inputs(root))
    return result


def find_lake(root: Path) -> str:
    override = os.environ.get("MATH_LAKE")
    if override:
        path = Path(override).expanduser().absolute()
        require(path.is_file(), f"MATH_LAKE does not exist: {path}")
        return str(path)
    version = (root / "lean-toolchain").read_text().strip().split(":")[-1].removeprefix("v")
    local = sorted((root / ".tools").glob(f"lean-{version}-*/bin/lake"))
    if local:
        return str(local[0].resolve())
    lake = shutil.which("lake")
    if lake:
        return lake
    elan_lake = Path.home() / ".elan/bin/lake"
    require(elan_lake.is_file(), "lake is unavailable; install the pinned Lean toolchain")
    return str(elan_lake)


def run(root: Path, command: list[str], capture: bool = False) -> str:
    environment = {**os.environ, "MATHLIB_NO_CACHE_ON_UPDATE": "1"}
    result = subprocess.run(command, cwd=root, text=True, capture_output=capture, check=False, env=environment)
    if result.returncode:
        detail = (result.stderr or result.stdout or "").strip() if capture else ""
        raise RepositoryError(f"command failed ({result.returncode}): {' '.join(command)}"
                              + (f"\n{detail}" if detail else ""))
    return result.stdout if capture else ""


def fetch(root: Path) -> None:
    """materialize locked packages and fetch only registered mathlib module caches."""
    root = root.resolve()
    policy = read_json(root / "knowledge.json")
    registered_modules(policy)
    lock = read_json(root / "lake-manifest.json")
    lake = find_lake(root)
    modules = policy.get("libraries", {}).get("mathlib", {}).get("modules", {})
    if modules:
        run(root, [lake, "exe", "cache", "get", *sorted(modules)])
    else:
        run(root, [lake, "env", "lean", "--version"])
    require(lock == read_json(root / "lake-manifest.json"), "dependency lock changed while fetching")
    snapshot_packages(root, lock, policy)
    if (root / "metamath-lock.json").is_file():
        from .metamath_build import fetch as fetch_native
        fetch_native(root)


def check_replay(root: Path, lake: str, path: Path, configuration: Path,
                 permitted_axioms: list[str]) -> tuple[str, str]:
    """check immutable proof bytes before loading the mathematical catalog."""
    from .store import file_digest

    checked_digest = file_digest(path)
    run(root, [lake, "env", "leanchecker", "--from-export", str(path)], capture=True)
    configuration.write_bytes(canonical({
        "export_file_path": str(path),
        "permitted_axioms": sorted(permitted_axioms),
        "unpermitted_axiom_hard_error": True,
        "nat_extension": True,
        "string_extension": True,
        "print_success_message": False,
    }))
    run(root, [lake, "env", "nanoda_bin", str(configuration)], capture=True)
    checker_version = run(root, [lake, "env", "nanoda_bin", "--help"], capture=True).splitlines()[0]
    require(file_digest(path) == checked_digest, "proof export changed during proof replay")
    return checked_digest, checker_version


def verify(root: Path, clean: bool = False) -> dict:
    from .replay import bind_replay
    from .store import archive_sources, create_store, file_digest

    root = root.resolve()
    policy = read_json(root / "knowledge.json")
    for path in lean_sources(root):
        relative = path.relative_to(root)
        require(relative.as_posix() == "Math.lean" or relative.parts[0] in {"Math", "tools", "tests"},
                f"mathematical sources must be inside Math/: {relative}")
    sources = {"Math"} | {".".join(path.relative_to(root).with_suffix("").parts)
                          for path in (root / "Math").rglob("*.lean")}
    require(sources == policy.get("modules", {}).keys(), "Lean sources differ from module policy")
    subject_policy(policy, sources | registered_modules(policy).keys())
    lock = read_json(root / "lake-manifest.json")
    packages = snapshot_packages(root, lock, policy)
    dependencies = package_provenance(packages)
    lake = find_lake(root)
    expected = (root / "lean-toolchain").read_text().strip().split(":")[-1].removeprefix("v")
    actual = run(root, [lake, "env", "lean", "--version"], capture=True)
    match = re.search(r"version ([0-9.]+)[, )]", actual)
    require(match is not None and match[1] == expected, "Lean version differs from lean-toolchain")
    before = input_hashes(root)
    native = None
    if (root / "metamath-lock.json").is_file():
        from .metamath_build import verify as verify_native
        native = verify_native(root)
        require(before == input_hashes(root), "verification inputs changed during native proof replay")
    if clean:
        run(root, [lake, "clean", lock["name"]])
    run(root, [lake, "build", "Math", *["+" + name for name in sorted(registered_modules(policy))]])
    directory = root / "build"
    directory.mkdir(exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix="extract-", suffix=".json", dir=directory)
    os.close(fd)
    raw_path = Path(temporary)
    replay_path = raw_path.with_suffix(".jsonl")
    checker_path = raw_path.with_suffix(".checker.json")
    receipt_path = raw_path.with_suffix(".index.json")
    try:
        run(root, [lake, "env", "lean", "--run", "tools/Export.lean", str(raw_path), str(replay_path)])
        checked_digest, checker_version = check_replay(root, lake, replay_path, checker_path,
                                                      sorted(policy["axioms"]))
        raw = read_json(raw_path)
        require(raw.get("lean_version") == expected, "exported Lean version differs from toolchain")
        catalog = validate(raw, policy)
        catalog["proof_binding"] = bind_replay(catalog, replay_path)
        require(catalog["proof_binding"]["proof_export_digest"] == checked_digest,
                "indexed proof export differs from checked proof bytes")
        catalog["sources"] = source_origins(root, catalog, packages, policy)
        catalog["bibliographies"] = archive_bibliographies(packages, policy)
        prefix = Path(run(root, [lake, "env", "lean", "--print-prefix"], capture=True).strip())
        license_text = (prefix / "LICENSE").read_text()
        require(file_digest(replay_path) == catalog["proof_binding"]["proof_export_digest"],
                "proof export changed after index binding")
        require(before == input_hashes(root), "verification inputs changed during the build")
        require(dependencies == package_provenance(snapshot_packages(root, lock, policy)),
                "dependency sources changed during the build")
        catalog["provenance"] = {
            "inputs": before, "source_digest": digest(before),
            "dependencies": dependencies,
            "toolchain": {
                "repository": "https://github.com/leanprover/lean4",
                "revision": raw["lean_revision"], "license": "Apache-2.0",
                "licenses": {"LICENSE": {"text": license_text,
                                            "sha256": hashlib.sha256(license_text.encode()).hexdigest()}},
            },
            "proof_export_digest": file_digest(replay_path),
            "checkers": [f"Lean {expected} kernel replay", checker_version],
        }
        if native is not None:
            catalog["provenance"]["native_snapshots"] = {"metamath": native}
        catalog["content_digest"] = stream_digest(catalog)
        proof_path = directory / f"proofs-{catalog['provenance']['proof_export_digest']}.jsonl"
        replay_path.replace(proof_path)
        with raw_path.open("wb") as handle:
            for chunk in canonical_chunks(catalog):
                handle.write(chunk)
            handle.write(b"\n")
        receipt = create_store(directory, catalog, archive_sources(root, catalog, packages, prefix), file_digest(raw_path))
        receipt_path.write_bytes(canonical(receipt) + b"\n")
        require(before == input_hashes(root), "verification inputs changed while publishing the query store")
        require(dependencies == package_provenance(snapshot_packages(root, lock, policy)),
                "dependency sources changed while publishing the query store")
        raw_path.replace(directory / "knowledge.json")
        receipt_path.replace(directory / "index.json")
        return catalog
    finally:
        raw_path.unlink(missing_ok=True)
        Path(str(raw_path) + ".expressions").unlink(missing_ok=True)
        replay_path.unlink(missing_ok=True)
        checker_path.unlink(missing_ok=True)
        receipt_path.unlink(missing_ok=True)


def load_catalog(root: Path) -> dict:
    from .replay import validate_binding_receipt

    path = root / "build/knowledge.json"
    require(path.is_file(), "no verified index; run python3 -m repository verify")
    catalog = read_json(path)
    require(catalog.get("schema_version") == 3, "unsupported index schema; rerun verification")
    provenance = catalog.get("provenance", {})
    require(provenance.get("inputs") == input_hashes(root),
            "index is stale; run python3 -m repository verify")
    policy = read_json(root / "knowledge.json")
    lock = read_json(root / "lake-manifest.json")
    dependencies = package_provenance(snapshot_packages(root, lock, policy))
    require(provenance.get("dependencies", {}) == dependencies,
            "dependency sources differ from verified index; rerun verification")
    require(provenance.get("source_digest") == digest(provenance["inputs"]), "invalid source digest")
    validate_binding_receipt(catalog, len(catalog["declarations"]), len(catalog["expressions"]))
    proof_export_path(root, catalog)
    expected = catalog.pop("content_digest", None)
    require(expected == stream_digest(catalog), "index content digest mismatch; rerun verification")
    catalog["content_digest"] = expected
    return catalog
