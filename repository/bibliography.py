"""retain pinned bibliographies and resolve explicit documentation citations."""

from __future__ import annotations

from bisect import bisect_right
import hashlib
from pathlib import PurePosixPath
import re

from .core import require


class BibTeX:
    """parse balanced bibtex records while preserving their complete original text."""

    def __init__(self, text: str):
        self.text = text
        self.position = 0
        self.macros = {}
        self.lines = [match.end() for match in re.finditer("\n", text)]

    def space(self):
        while self.position < len(self.text):
            if self.text[self.position].isspace():
                self.position += 1
            elif self.text[self.position] == "%":
                self.position = self.text.find("\n", self.position)
                if self.position < 0:
                    self.position = len(self.text)
            else:
                break

    def take(self, character):
        self.space()
        require(self.text[self.position:self.position + 1] == character,
                f"invalid bibliography near character {self.position}: expected {character!r}")
        self.position += 1

    def token(self):
        self.space()
        match = re.match(r"[A-Za-z0-9_:-]+", self.text[self.position:])
        require(match is not None, f"invalid bibliography token near character {self.position}")
        self.position += len(match[0])
        return match[0]

    def balanced(self, quoted=False):
        opening = '"' if quoted else "{"
        self.take(opening)
        start, depth = self.position, 0 if quoted else 1
        while self.position < len(self.text):
            character = self.text[self.position]
            if character == "\\":
                self.position += 2
                continue
            if character == "{":
                depth += 1
            elif character == "}":
                depth -= 1
                require(depth >= 0, "unbalanced bibliography braces")
                if not quoted and depth == 0:
                    value = self.text[start:self.position]
                    self.position += 1
                    return value
            elif character == '"' and quoted and depth == 0:
                value = self.text[start:self.position]
                self.position += 1
                return value
            self.position += 1
        require(False, "unterminated bibliography value")

    def value(self):
        parts = []
        while True:
            self.space()
            character = self.text[self.position:self.position + 1]
            if character in {"{", '"'}:
                parts.append(self.balanced(character == '"'))
            else:
                token = self.token()
                parts.append(self.macros.get(token.casefold(), token))
            self.space()
            if self.text[self.position:self.position + 1] != "#":
                return "".join(parts)
            self.position += 1

    def entries(self):
        result = {}
        while True:
            self.space()
            if self.position == len(self.text):
                return result
            if self.text[self.position] == "#":
                end = self.text.find("\n", self.position)
                self.position = len(self.text) if end < 0 else end + 1
                continue
            start = self.position
            self.take("@")
            kind = self.token().casefold()
            self.space()
            if kind == "comment":
                self.balanced()
                continue
            opening = self.text[self.position:self.position + 1]
            require(opening in {"{", "("}, "invalid bibliography record delimiter")
            closing = "}" if opening == "{" else ")"
            self.position += 1
            if kind == "preamble":
                self.value()
                self.take(closing)
                continue
            key = self.token()
            if kind == "string":
                self.take("=")
                require(key.casefold() not in self.macros, f"duplicate bibliography macro: {key}")
                self.macros[key.casefold()] = self.value()
                self.space()
                if self.text[self.position:self.position + 1] == ",":
                    self.position += 1
                self.take(closing)
                continue
            else:
                require(key not in result, f"duplicate bibliography key: {key}")
                self.take(",")
            fields = {}
            while True:
                self.space()
                if self.text[self.position:self.position + 1] == closing:
                    self.position += 1
                    break
                field = self.token().casefold()
                require(field not in fields, f"duplicate bibliography field: {field}")
                self.take("=")
                fields[field] = self.value()
                self.space()
                require(self.text[self.position:self.position + 1] in {",", closing},
                        "missing bibliography field delimiter")
                if self.text[self.position:self.position + 1] == ",":
                    self.position += 1
            result[key] = {"key": key, "kind": kind, "fields": fields,
                           "raw": self.text[start:self.position],
                           "line": bisect_right(self.lines, start) + 1,
                           "end_line": bisect_right(self.lines, self.position - 1) + 1}


def citation_aliases(bibliography: dict) -> dict[str, str]:
    """validate reviewed aliases without changing canonical bibliography records."""
    aliases = bibliography.get("citation_aliases", {})
    entries = bibliography["entries"]
    require(isinstance(aliases, dict), "bibliography citation aliases must be a mapping")
    for alias, target in aliases.items():
        require(isinstance(alias, str) and re.fullmatch(r"[A-Za-z0-9_:-]+", alias) is not None,
                "invalid bibliography citation alias")
        require(alias not in entries, "bibliography citation alias shadows a canonical key")
        require(isinstance(target, str) and target in entries, "bibliography citation alias has no canonical target")
    return aliases


def bibliography_keys(bibliographies: dict) -> list[str]:
    """include original citation spellings and their package-qualified forms."""
    return sorted({key for owner, bibliography in bibliographies.items()
                   for name in set(bibliography["entries"]) | set(citation_aliases(bibliography))
                   for key in (name, owner + ":" + name)})


def archive_bibliographies(packages: dict, policy: dict) -> dict:
    """archive configured, tracked bibliography bytes from the locked dependencies."""
    result = {}
    for name, library in sorted(policy.get("libraries", {}).items()):
        relative = library.get("bibliography")
        if relative is None:
            require("citation_aliases" not in library, f"{name}: citation aliases require a pinned bibliography")
            continue
        require(isinstance(relative, str) and bool(relative), f"{name}: invalid bibliography path")
        path = PurePosixPath(relative)
        require(not path.is_absolute() and ".." not in path.parts and "\\" not in relative,
                f"{name}: invalid bibliography path")
        package = packages[name]
        require(relative in package.files, f"{name}: bibliography is not a tracked source")
        data = (package.root / relative).read_bytes()
        value = hashlib.sha256(data).hexdigest()
        require(value == package.files[relative], f"{name}: bibliography changed before archival")
        text = data.decode("utf-8")
        result[name] = {"package": name, "path": relative, "sha256": value, "text": text,
                        "revision": package.revision, "license": package.license_id,
                        "url": f"{package.repository.removesuffix('.git')}/blob/{package.revision}/{relative}",
                        "entries": BibTeX(text).entries()}
        if "citation_aliases" in library:
            require(isinstance(library["citation_aliases"], dict), "bibliography citation aliases must be a mapping")
            result[name]["citation_aliases"] = dict(library["citation_aliases"])
            citation_aliases(result[name])
    return result


def citation_keys(text: str, available: set[str]) -> list[str]:
    """recognize explicit bibliography keys outside markdown code spans and blocks."""
    text = re.sub(r"(`+).*?\1", "", text, flags=re.DOTALL)
    return sorted({match[1] for match in re.finditer(r"(?<!!)\[([A-Za-z0-9_:-]+)\](?!\()", text)
                   if match[1] in available})


def resolve_citations(bibliographies: dict, text: str, package: str | None = None) -> list[dict]:
    """prefer the source library's keys and expose ambiguous cross-library matches."""
    available, qualified = {}, {}
    for owner, bibliography in bibliographies.items():
        canonical_records = {}
        for key, entry in bibliography["entries"].items():
            record = {**entry, "package": owner, "id": owner + ":" + key,
                      "source_url": bibliography["url"] + "#L" + str(entry["line"]),
                      "bibliography_digest": bibliography["sha256"]}
            available.setdefault(key, []).append(record)
            qualified[owner + ":" + key] = record
            canonical_records[key] = record
        for alias, target in citation_aliases(bibliography).items():
            record = {**canonical_records[target], "alias": alias}
            available.setdefault(alias, []).append(record)
            qualified[owner + ":" + alias] = record
    result = []
    for key in citation_keys(text, set(available) | set(qualified)):
        candidates = available.get(key, [])
        local = [item for item in candidates if item["package"] == package]
        if key in qualified:
            candidates = [qualified[key]]
        elif len(local) == 1:
            candidates = local
        if len(candidates) == 1:
            result.append({**candidates[0], "citation_key": key, "ambiguous": False})
        else:
            result.append({"citation_key": key, "ambiguous": True,
                           "candidates": [{"package": item["package"], "key": item["key"]}
                                          for item in candidates]})
    return result
