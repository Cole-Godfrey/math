"""read catalog objects without retaining a second copy of their complete json text."""

from __future__ import annotations

import json
import re
from functools import partial
from typing import TextIO

from .core import PackedHexDigests, RepositoryError, require
from .expressions import PackedExpressions


_SHA256 = re.compile(r"[0-9a-f]{64}\Z")
_MAX_SHARED_STRINGS = 1000000
_MAX_SHARED_LENGTH = 256
_TEXT_FIELDS = frozenset({"statement", "proof", "doc", "text", "value", "url"})


_SYNTAX_TAGS = {tag: tag for tag in (
    "app", "lam", "forall", "let", "proj", "bvar", "sort", "const", "nat", "string",
    "zero", "succ", "max", "imax", "param",
)}


class _StringPool:
    """share repeated immutable identifiers within one catalog read."""

    def __init__(self):
        self.values = {}

    def share(self, value: str) -> str:
        if len(value) > _MAX_SHARED_LENGTH:
            return value
        previous = self.values.get(value)
        if previous is not None:
            return previous
        if len(self.values) < _MAX_SHARED_STRINGS:
            self.values[value] = value
        return value


def _unique_object(pairs: list[tuple], *, keys: dict[str, str], strings: _StringPool) -> dict:
    result = {}
    for name, value in pairs:
        name = keys.setdefault(name, name)
        require(name not in result, f"duplicate json field: {name}")
        if name == "tag" and isinstance(value, str):
            value = _SYNTAX_TAGS.get(value, value)
        if name not in _TEXT_FIELDS:
            if isinstance(value, str):
                value = strings.share(value)
            elif isinstance(value, list):
                for index, item in enumerate(value):
                    if isinstance(item, str):
                        value[index] = strings.share(item)
        result[name] = value
    return result


class _Reader:
    """decode complete records while streaming the outer catalog containers."""

    def __init__(self, stream: TextIO, chunk_size: int, compact_expressions: bool = False):
        require(type(chunk_size) is int and chunk_size > 0, "invalid json chunk size")
        require(type(compact_expressions) is bool, "invalid compact expression option")
        self.compact_expressions = compact_expressions
        self.stream = stream
        self.chunk_size = chunk_size
        self.buffer = ""
        self.position = 0
        self.offset = 0
        self.eof = False
        self.keys = {}
        self.strings = _StringPool()
        self.decoder = json.JSONDecoder(object_pairs_hook=partial(
            _unique_object, keys=self.keys, strings=self.strings))

    def fill(self):
        self.offset += self.position
        self.buffer = self.buffer[self.position:]
        self.position = 0
        chunk = self.stream.read(self.chunk_size)
        self.buffer += chunk
        self.eof = not chunk

    def peek(self):
        while True:
            while self.position < len(self.buffer) and self.buffer[self.position] in " \t\r\n":
                self.position += 1
            if self.position < len(self.buffer):
                return self.buffer[self.position]
            if self.eof:
                return ""
            self.fill()

    def expect(self, character):
        require(self.peek() == character,
                f"invalid json near character {self.offset + self.position}: expected {character!r}")
        self.position += 1

    def incomplete(self, error):
        if error.pos == len(self.buffer) or error.msg.startswith("Unterminated string"):
            return True
        suffix = self.buffer[error.pos:]
        if error.msg == "Invalid \\uXXXX escape":
            return len(suffix) < 6
        if error.msg == "Expecting value":
            return suffix == "-" or any(token.startswith(suffix) for token in
                ("true", "false", "null", "NaN", "Infinity", "-Infinity"))
        return error.msg == "Expecting ',' delimiter" and suffix in {".", "e", "E", "e+", "e-", "E+", "E-"}

    def value(self):
        self.peek()
        while True:
            try:
                value, end = self.decoder.raw_decode(self.buffer, self.position)
            except json.JSONDecodeError as exc:
                if self.eof or not self.incomplete(exc):
                    raise RepositoryError(
                        f"invalid json near character {self.offset + exc.pos}: {exc.msg}") from exc
                self.fill()
                continue
            # a number can continue across the next input chunk.
            suffix_length = len(self.buffer) - end
            if (not self.eof and type(value) in {int, float}
                    and (suffix_length == 0 or suffix_length <= 2 and
                         self.buffer[end:] in {".", "e", "E", "e+", "e-", "E+", "E-"})):
                self.fill()
                continue
            self.position = end
            return value

    def array(self, compact_hashes=False, compact_expressions=False):
        self.expect("[")
        result = PackedExpressions() if compact_expressions else PackedHexDigests() if compact_hashes else []
        if self.peek() != "]":
            while True:
                value = self.value()
                if isinstance(value, str) and not compact_hashes:
                    value = self.strings.share(value)
                if isinstance(result, PackedHexDigests) and not (
                        isinstance(value, str) and _SHA256.fullmatch(value)):
                    result = list(result)
                result.append(value)
                if self.peek() != ",":
                    break
                self.position += 1
        self.expect("]")
        return result.seal() if isinstance(result, PackedExpressions) else result

    def object(self, split_values=False):
        self.expect("{")
        result = {}
        if self.peek() != "}":
            while True:
                require(self.peek() == '"', "invalid json object key")
                key = self.value()
                key = self.keys.setdefault(key, key)
                require(key not in result, f"duplicate json field: {key}")
                self.expect(":")
                result[key] = self.container(key) if split_values else self.value()
                if self.peek() != ",":
                    break
                self.position += 1
        self.expect("}")
        return result

    def container(self, key=None):
        character = self.peek()
        if character == "[":
            return self.array(compact_hashes=key == "expression_hashes",
                              compact_expressions=self.compact_expressions and key == "expressions")
        if character == "{":
            return self.object()
        return self.value()


def read_object(stream: TextIO, chunk_size: int = 64 * 1024, *, compact_expressions: bool = False) -> dict:
    """retain every field and record while rejecting duplicate fields and trailing data."""
    reader = _Reader(stream, chunk_size, compact_expressions=compact_expressions)
    require(reader.peek() == "{", "expected a json object")
    result = reader.object(split_values=True)
    require(not reader.peek(), "unexpected trailing json data")
    return result
