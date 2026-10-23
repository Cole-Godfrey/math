"""lossless, read-only storage for complete proof expressions."""

from array import array
from collections.abc import Sequence
import json
import operator


_SCHEMAS = (
    ('bvar', (('index', 'integer'),)),
    ('sort', (('level', 'json'),)),
    ('const', (('name', 'string'), ('levels', 'json'))),
    ('app', (('function', 'integer'), ('argument', 'integer'))),
    ('lam', (('name', 'string'), ('binder', 'string'), ('type', 'integer'), ('body', 'integer'))),
    ('forall', (('name', 'string'), ('binder', 'string'), ('type', 'integer'), ('body', 'integer'))),
    ('let', (('name', 'string'), ('nondependent', 'boolean'), ('type', 'integer'),
             ('value', 'integer'), ('body', 'integer'))),
    ('proj', (('name', 'string'), ('index', 'integer'), ('expression', 'integer'))),
    ('nat', (('value', 'integer'),)),
    ('string', (('value', 'string'),)),
)
_TAGS = {name: index for index, (name, _) in enumerate(_SCHEMAS)}
_FIELDS = {name: {'tag', *(field for field, _ in fields)} for name, fields in _SCHEMAS}
_LAYOUTS = tuple(tuple(sorted([('tag', -1, 'tag'),
                             *((field, index, kind) for index, (field, kind) in enumerate(fields))]))
                 for _, fields in _SCHEMAS)
_FALLBACK = 255
_LIMIT = 1 << 64


def _json(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':'))


class PackedExpressions(Sequence):
    """retain every json field while exposing fresh records from sealed packed arrays."""

    def __init__(self):
        assert array('Q').itemsize == 8
        self._tags = bytearray()
        self._offsets = array('Q')
        self._slots = array('Q')
        self._atoms = []
        self._atom_ids = {}
        self._sealed = False
        self.fallback_records = 0

    def _atom(self, kind, value):
        key = (kind, value)
        identifier = self._atom_ids.get(key)
        if identifier is None:
            identifier = len(self._atoms)
            self._atoms.append(value)
            self._atom_ids[key] = identifier
        return identifier

    def _pack(self, record):
        if not isinstance(record, dict):
            return None
        tag = record.get('tag')
        if not isinstance(tag, str) or tag not in _TAGS or set(record) != _FIELDS[tag]:
            return None
        fields = _SCHEMAS[_TAGS[tag]][1]
        for name, kind in fields:
            value = record[name]
            if kind == 'integer' and not (type(value) is int and 0 <= value < _LIMIT):
                return None
            if kind == 'boolean' and type(value) is not bool:
                return None
            if kind == 'string' and not isinstance(value, str):
                return None
        result = []
        for name, kind in fields:
            value = record[name]
            if kind == 'integer':
                result.append(value)
            elif kind == 'boolean':
                result.append(int(value))
            elif kind == 'string':
                result.append(self._atom(kind, value))
            else:
                result.append(self._atom(kind, _json(value)))
        return _TAGS[tag], result

    def append(self, record):
        if self._sealed:
            raise TypeError('packed expressions are sealed')
        packed = self._pack(record)
        if packed is None:
            packed = _FALLBACK, [self._atom('json', _json(record))]
            self.fallback_records += 1
        tag, slots = packed
        self._offsets.append(len(self._slots))
        self._tags.append(tag)
        self._slots.extend(slots)

    def seal(self):
        self._sealed = True
        self._atom_ids.clear()
        return self

    def __len__(self):
        return len(self._tags)

    def __getitem__(self, index):
        if isinstance(index, slice):
            return [self[position] for position in range(*index.indices(len(self)))]
        index = operator.index(index)
        if index < 0:
            index += len(self)
        if not 0 <= index < len(self):
            raise IndexError(index)
        tag = self._tags[index]
        start = self._offsets[index]
        if tag == _FALLBACK:
            return json.loads(self._atoms[self._slots[start]])
        name = _SCHEMAS[tag][0]
        result = {}
        for field, offset, kind in _LAYOUTS[tag]:
            if kind == 'tag':
                result[field] = name
                continue
            value = self._slots[start + offset]
            if kind == 'boolean':
                value = bool(value)
            elif kind == 'string':
                value = self._atoms[value]
            elif kind == 'json':
                value = json.loads(self._atoms[value])
            result[field] = value
        return result

    def __iter__(self):
        for index in range(len(self)):
            yield self[index]

    def __eq__(self, other):
        if not isinstance(other, (list, PackedExpressions)):
            return NotImplemented
        return len(self) == len(other) and all(left == right for left, right in zip(self, other))

    def storage_bytes(self):
        return len(self._tags) + self._offsets.buffer_info()[1] * self._offsets.itemsize + \
            self._slots.buffer_info()[1] * self._slots.itemsize

    def canonical_parts(self):
        """stream complete canonical records without decoding their packed fields."""
        yield from _PackedEncoder(self).array()


class _PackedEncoder:
    """retain canonical bytes for every packed field and lossless fallback record."""

    def __init__(self, expressions):
        self.expressions = expressions
        self.raw_atoms = [value.encode('utf-8') for value in expressions._atoms]
        self.string_atoms = [_json(value).encode('utf-8') for value in expressions._atoms]
        self.templates = [(_json(name).encode('utf-8'),
                           [(('"' + key + '":').encode(), offset, kind)
                            for key, offset, kind in layout])
                          for (name, _), layout in zip(_SCHEMAS, _LAYOUTS)]

    def records(self):
        packed = self.expressions
        slots, offsets = packed._slots, packed._offsets
        for index, tag in enumerate(packed._tags):
            start = offsets[index]
            if tag == _FALLBACK:
                yield self.raw_atoms[slots[start]]
                continue
            name, template = self.templates[tag]
            fields = []
            for key, offset, kind in template:
                if kind == 'tag':
                    value = name
                else:
                    value = slots[start + offset]
                    if kind == 'integer':
                        value = str(value).encode()
                    elif kind == 'boolean':
                        value = b'true' if value else b'false'
                    elif kind == 'string':
                        value = self.string_atoms[value]
                    else:
                        value = self.raw_atoms[value]
                fields.append(key + value)
            yield b'{' + b','.join(fields) + b'}'

    def array(self):
        yield b'['
        for index, record in enumerate(self.records()):
            if index:
                yield b','
            yield record
        yield b']'
