"""check complete json decoding, chunk boundaries, and bounded text reads."""

import io
import json
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from repository.build import read_json
from repository.core import RepositoryError, canonical
from repository.json_reader import read_object


class JsonReaderTests(unittest.TestCase):
    def test_large_integer_tokens_preserve_every_digit_across_chunks(self):
        value = 10 ** 5000 + 179
        original = {"expressions": [{"tag": "nat", "value": value}],
                    "metadata": {"positive": value, "negative": -value}}
        encoded = canonical(original).decode()
        for size in (1, 31, 257, 65536):
            with self.subTest(size=size):
                self.assertEqual(read_object(io.StringIO(encoded), size), original)
        self.assertEqual(json.loads(encoded), original)

    def test_package_import_allows_large_literals_under_a_restrictive_python_setting(self):
        source = '''import json
import sys
digits = "1" + "0" * 5000
if hasattr(sys, "get_int_max_str_digits"):
    assert sys.get_int_max_str_digits() == 640
    try:
        int(digits)
    except ValueError:
        pass
    else:
        raise AssertionError("expected the initial conversion limit")
from repository.core import canonical
value = 10 ** 5000
assert int(digits) == value
assert str(value) == digits
assert canonical({"value": value}) == ("{\\"value\\":" + digits + "}").encode()
assert json.loads("{\\"value\\":" + digits + "}")["value"] == value
'''
        result = subprocess.run([sys.executable, "-X", "int_max_str_digits=640", "-c", source],
                                cwd=Path(__file__).resolve().parents[1], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_objects_match_the_standard_decoder_across_chunk_sizes(self):
        randomizer = random.Random(20261017)

        def value(depth):
            if not depth:
                return randomizer.choice([None, True, False, 0, -12, 10 ** 30, 1.25e-30,
                                          -3e20, "ℚ → 𝓞 K", '\\"\n\t', ""])
            if randomizer.randrange(2):
                return [value(depth - 1) for _ in range(randomizer.randrange(4))]
            return {key: value(depth - 1) for key in
                    randomizer.sample(["a", "z", "λ", "𝓞", '\\"'], randomizer.randrange(5))}

        for index in range(60):
            original = {"records": [value(3) for _ in range(3)], "metadata": value(3)}
            encoded = json.dumps(original, ensure_ascii=bool(index % 2))
            for size in (1, 2, 3, 7, 31, 65536):
                with self.subTest(index=index, size=size):
                    self.assertEqual(read_object(io.StringIO(encoded), size), json.loads(encoded))

    def test_numeric_and_escape_boundaries_preserve_complete_tokens(self):
        encoded = (' {"values":[-1.25e-30,1e+15,1234567890123456789012345,true,false,null,'
                   '"\\uD835\\uDD46\\u00e9\\\\\\\""],"after":42} \n')
        expected = json.loads(encoded)
        for size in range(1, len(encoded) + 1):
            with self.subTest(size=size):
                self.assertEqual(read_object(io.StringIO(encoded), size), expected)

    def test_duplicate_fields_are_rejected_at_every_depth(self):
        examples = ['{"a":1,"a":2}', '{"a":0,"\\u0061":1}',
                    '{"records":[{"a":1,"a":2}]}',
                    '{"metadata":{"name":{"str":"a","str":"b"}}}']
        for encoded in examples:
            for size in (1, 2, 7, 65536):
                with self.subTest(encoded=encoded, size=size):
                    with self.assertRaisesRegex(RepositoryError, "duplicate json field"):
                        read_object(io.StringIO(encoded), size)

    def test_malformed_truncated_and_trailing_data_are_rejected(self):
        complete = '{"records":[{"value":-1.25e-3},null,"\\u00e9"]}'
        examples = [complete[:index] for index in range(len(complete))]
        examples += ['[]', 'null', '"object"', '{}{}', '{} true', '{"a":[1,]}',
                     '{"a":1,}', '{a:1}', '{"a":01}', '{"a":1.e2}',
                     '{"a":"\\uZZZZ"}', '{"a":"\\x"}', '{"a":truth}', '{"a":1 "b":2}']
        for encoded in examples:
            for size in (1, 3, 7, 65536):
                with self.subTest(encoded=encoded, size=size):
                    with self.assertRaises(RepositoryError):
                        read_object(io.StringIO(encoded), size)

    def test_large_record_arrays_use_bounded_reads_and_retain_every_item(self):
        class BoundedStream(io.StringIO):
            def read(self, size=-1):
                if not 0 < size <= 257:
                    raise AssertionError(f"unbounded read: {size}")
                return super().read(size)

        original = {"expressions": [{"tag": "const", "name": f"declaration_{index}", "levels": []}
                                     for index in range(10000)],
                    "name_data": {f"n{index}": [{"str": str(index)}] for index in range(1000)}}
        self.assertEqual(read_object(BoundedStream(json.dumps(original)), 257), original)

    def test_record_keys_share_storage_across_input_chunks(self):
        original = {"expressions": [{"tag": "const", "name": "ℚ", "levels": []}] * 1000}
        actual = read_object(io.StringIO(json.dumps(original)), 17)
        for field in ("tag", "name", "levels"):
            self.assertEqual(len({id(next(key for key in row if key == field))
                                  for row in actual["expressions"]}), 1)

    def test_records_larger_than_one_chunk_are_not_truncated(self):
        original = {"declarations": [{"proof": "λ 𝓞 K \\\n" * 10000}], "after": {"complete": True}}
        self.assertEqual(read_object(io.StringIO(json.dumps(original)), 65536), original)

    def test_file_reader_avoids_read_text_and_preserves_error_context(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "catalog.json"
            path.write_text('{"name":"ℚ","records":[1,2,3]}', encoding="utf-8")
            with patch.object(Path, "read_text", side_effect=AssertionError("whole file read")):
                self.assertEqual(read_json(path), {"name": "ℚ", "records": [1, 2, 3]})
            path.write_text('{"a":1,"a":2}', encoding="utf-8")
            with self.assertRaisesRegex(RepositoryError, "cannot read .*catalog.json: duplicate json field"):
                read_json(path)
            path.unlink()
            with self.assertRaisesRegex(RepositoryError, "cannot read .*catalog.json"):
                read_json(path)

    def test_invalid_chunk_sizes_are_rejected(self):
        for size in (0, -1, True, 1.5):
            with self.subTest(size=size), self.assertRaisesRegex(RepositoryError, "invalid json chunk size"):
                read_object(io.StringIO("{}"), size)


if __name__ == "__main__":
    unittest.main()
