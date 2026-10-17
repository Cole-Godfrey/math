"""bind imported mathematical libraries to locked sources and attribution."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import os
from pathlib import Path
import re
import subprocess

from .core import digest, registered_modules, require


def _git(directory: Path, *args: str) -> str:
    result = subprocess.run(["git", "-C", str(directory), *args], capture_output=True, text=True)
    require(result.returncode == 0, f"cannot inspect dependency {directory.name}: " + result.stderr.strip())
    return result.stdout


def _repository_identity(url: str) -> str:
    return url.rstrip("/").removesuffix(".git")


@dataclass
class PackageSnapshot:
    name: str
    root: Path
    repository: str
    revision: str
    files: dict[str, str]
    licenses: dict[str, dict]
    license_id: str | None
    source_prefix: str = ""

    def module_path(self, relative: str) -> str:
        return self.source_prefix + relative

    def provenance(self) -> dict:
        return {
            "repository": self.repository,
            "revision": self.revision,
            "source_digest": digest(self.files),
            "source_prefix": self.source_prefix,
            "license": self.license_id,
            "licenses": self.licenses,
        }


def snapshot_packages(root: Path, lock: dict, policy: dict) -> dict[str, PackageSnapshot]:
    """check actual tracked bytes against each dependency's committed git objects."""
    registered_modules(policy)
    entries = lock.get("packages")
    require(isinstance(entries, list), "missing locked dependency list")
    directory = Path(lock.get("packagesDir", ".lake/packages"))
    require(not directory.is_absolute() and ".." not in directory.parts, "invalid dependency directory")
    snapshots = {}
    for entry in entries:
        require(isinstance(entry, dict) and entry.get("type") == "git", "dependencies must use pinned git sources")
        name, revision, repository = entry.get("name"), entry.get("rev"), entry.get("url")
        require(isinstance(name, str) and re.fullmatch(r"[A-Za-z0-9_-]+", name) is not None,
                "invalid dependency name")
        require(name not in snapshots, f"duplicate locked dependency: {name}")
        require(isinstance(revision, str) and re.fullmatch(r"[0-9a-f]{40}", revision) is not None,
                f"{name}: lockfile revision must be an exact commit")
        require(isinstance(repository, str) and bool(repository), f"{name}: missing repository")
        checkout = root / directory / name
        require(checkout.is_dir(), f"dependency {name} is missing; run python3 -m repository fetch")
        require(_git(checkout, "rev-parse", "HEAD").strip() == revision,
                f"{name}: checkout differs from locked revision")
        remote = _git(checkout, "remote", "get-url", "origin").strip()
        require(_repository_identity(remote) == _repository_identity(repository),
                f"{name}: checkout repository differs from lockfile")
        registration = policy.get("libraries", {}).get(name)
        if registration:
            require(registration["revision"] == revision, f"{name}: registry revision differs from lockfile")
            require(_repository_identity(registration["repository"]) == _repository_identity(repository),
                    f"{name}: registry repository differs from lockfile")
        files = {}
        for item in _git(checkout, "ls-tree", "-r", "-z", "HEAD").split("\0"):
            if not item:
                continue
            metadata, path = item.split("\t", 1)
            mode, kind, object_id = metadata.split()
            require(kind == "blob", f"{name}: unsupported nested git dependency: {path}")
            source = checkout / path
            require(source.exists() or source.is_symlink(), f"{name}: missing tracked source: {path}")
            content = os.readlink(source).encode() if mode == "120000" else source.read_bytes()
            blob = b"blob " + str(len(content)).encode() + b"\0" + content
            require(hashlib.sha1(blob).hexdigest() == object_id, f"{name}: modified dependency source: {path}")
            files[path] = hashlib.sha256(content).hexdigest()
        extra = _git(checkout, "ls-files", "--others", "--exclude-standard", "-z")
        require(not extra, f"{name}: untracked dependency sources")
        subdirectory = Path(entry.get("subDir") or ".")
        require(not subdirectory.is_absolute() and ".." not in subdirectory.parts, "invalid package subdirectory")
        licenses = {}
        for path in files:
            filename = Path(path)
            if (filename.parent in {Path("."), subdirectory}
                    and filename.name.casefold().startswith(("license", "copying", "notice"))):
                licenses[path] = {"sha256": files[path], "text": (checkout / path).read_text()}
        require(bool(licenses), f"{name}: dependency has no retained license notice")
        if registration:
            require(registration["license_file"] in licenses, f"{name}: registered license notice is missing")
        prefix = subdirectory.as_posix() + "/" if subdirectory != Path(".") else ""
        snapshots[name] = PackageSnapshot(name, checkout, repository, revision, files, licenses,
                                          registration["license"] if registration else None, prefix)
    require(policy.get("libraries", {}).keys() <= snapshots.keys(), "registered library is not locked")
    return snapshots


def package_provenance(packages: dict[str, PackageSnapshot]) -> dict:
    return {name: package.provenance() for name, package in sorted(packages.items())}


def source_origins(root: Path, catalog: dict, packages: dict[str, PackageSnapshot], policy: dict) -> dict:
    """retain module attribution without changing upstream declaration names."""
    result = {}
    owners = {module: name for name, library in policy.get("libraries", {}).items()
              for module in library["modules"]}
    used = {node["module"] for node in catalog["declarations"]} | owners.keys()
    for module in sorted(used):
        relative = module.replace(".", "/") + ".lean"
        if module == "Math" or module.startswith("Math."):
            source = root / relative
            require(source.is_file(), f"missing project source: {relative}")
            result[module] = {"package": "math", "path": relative,
                              "sha256": hashlib.sha256(source.read_bytes()).hexdigest()}
            continue
        candidates = [package for package in packages.values() if package.module_path(relative) in package.files]
        require(len(candidates) <= 1, f"ambiguous library source: {module}")
        if not candidates:
            require(module not in owners, f"registered library module has no tracked source: {module}")
            require(module.split(".", 1)[0] in {"Init", "Lean", "Std", "Lake", "LeanExport"},
                    f"imported module has no locked source: {module}")
            path = ("src/lake/" if module.split(".", 1)[0] == "Lake" else "src/") + relative
            revision = catalog["lean_revision"]
            result[module] = {
                "package": "lean", "repository": "https://github.com/leanprover/lean4",
                "revision": revision, "license": "Apache-2.0", "path": path,
                "url": f"https://github.com/leanprover/lean4/blob/{revision}/{path}",
            }
            continue
        package = candidates[0]
        require(module not in owners or owners[module] == package.name,
                f"{module}: source belongs to the wrong library")
        repository_path = package.module_path(relative)
        text = (package.root / repository_path).read_text()
        notice = re.match(r"\s*(/\-.*?\-/)", text, flags=re.DOTALL)
        result[module] = {
            "package": package.name, "repository": package.repository, "revision": package.revision,
            "path": repository_path, "sha256": package.files[repository_path], "license": package.license_id,
            "license_files": sorted(package.licenses),
            "url": f"{package.repository.removesuffix('.git')}/blob/{package.revision}/{repository_path}",
            "notice": notice[1] if notice else None,
        }
    return result
