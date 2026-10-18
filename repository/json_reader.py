"""read catalog objects without retaining a second copy of their complete json text."""

from __future__ import annotations

import json
from functools import partial
from typing import TextIO

from .core import RepositoryError, require


def _unique_object(pairs: list[tuple], *, keys: dict[str, str]) -> dict:
    result = {}
    for name, value in pairs:
        name = keys.setdefault(name, name)
        require(name not in result, f"duplicate json field: {name}")
        result[name] = value
    return result


class _Reader:
    """decode complete records while streaming the outer catalog containers."""

    def __init__(self, stream: TextIO, chunk_size: int):
        require(type(chunk_size) is int and chunk_size > 0, "invalid json chunk size")
        self.stream = stream
        self.chunk_size = chunk_size
        self.buffer = ""
        self.position = 0
        self.offset = 0
        self.eof = False
        self.keys = {}
        self.decoder = json.JSONDecoder(object_pairs_hook=partial(_unique_object, keys=self.keys))

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

    def array(self):
        self.expect("[")
        result = []
        if self.peek() != "]":
            while True:
                result.append(self.value())
                if self.peek() != ",":
                    break
                self.position += 1
        self.expect("]")
        return result

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
                result[key] = self.container() if split_values else self.value()
                if self.peek() != ",":
                    break
                self.position += 1
        self.expect("}")
        return result

    def container(self):
        character = self.peek()
        if character == "[":
            return self.array()
        if character == "{":
            return self.object()
        return self.value()


def read_object(stream: TextIO, chunk_size: int = 64 * 1024) -> dict:
    """retain every field and record while rejecting duplicate fields and trailing data."""
    reader = _Reader(stream, chunk_size)
    require(reader.peek() == "{", "expected a json object")
    result = reader.object(split_values=True)
    require(not reader.peek(), "unexpected trailing json data")
    return result
