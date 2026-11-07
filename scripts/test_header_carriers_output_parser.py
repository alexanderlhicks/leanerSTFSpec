#!/usr/bin/env -S uv run --no-project --python 3.12 python
"""Complete-value, scalar-type and actual CLI controls for raw header observations."""
import argparse
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import unittest
import uuid

ROOT = Path(__file__).resolve().parents[1]
READER = ROOT / "STFSpec/Conformance/Block/header_carriers_differential.py"
spec = importlib.util.spec_from_file_location("header_reader", READER)
reader = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reader)
OUTPUT = None


def encode(rows):
    return ("\n".join(json.dumps(row, separators=(",", ":")) for row in rows) + "\n").encode()


def changed(value):
    return value + 1 if type(value) is int else ("ff" if not value else
           ("80" if value[:2] == "00" else "00") + value[2:])


class HeaderOutput(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.frames = reader.expected_frames()
        cls.good = encode(cls.frames)

    def test_complete_catalogue(self):
        self.assertEqual(reader.check_bytes(self.good), 2798)
        rows = self.frames[1:-1]
        self.assertEqual(sum(len(row["fields"]) for row in rows), 61638)
        self.assertEqual(sum(len(row["commonAccessors"]) for row in rows), 12591)
        self.assertEqual({(row["family"], row["variant"]) for row in rows},
                         {("Header", "amsterdam"), ("PrevHeader", "bpo5"),
                          ("ParentHeader", "amsterdam"), ("ParentHeader", "bpo5")})

    def test_every_field_and_accessor_position(self):
        # All four families, including both same-common-field parent variants.
        for expected in (row for row in self.frames[1:-1]
                         if row["caseId"].endswith("/marker")):
            for group in ("fields", "commonAccessors"):
                for index, field in enumerate(expected[group]):
                    for key in field:
                        actual = copy.deepcopy(expected)
                        value = field[key]
                        actual[group][index][key] = changed(value)
                        with self.assertRaises(ValueError):
                            reader.exact(actual, expected)
                    for bad in (True, False, None, [], {}, 0.0):
                        actual = copy.deepcopy(expected)
                        actual[group][index]["value"] = bad
                        with self.assertRaises(ValueError):
                            reader.exact(actual, expected)

    def test_parser_scalars(self):
        for raw in ("0.0", "1e0", "1e309", "NaN", "Infinity", "-Infinity", "-1", "-0"):
            with self.assertRaises(ValueError):
                reader.decode(raw)
        for actual, expected in ((False, 0), (True, 1), (0, False), (1, True)):
            with self.assertRaises(ValueError):
                reader.exact({"value": [actual]}, {"value": [expected]})
        for raw in ('{"value":0,"value":0}', '{"field":{"value":1,"value":1}}'):
            with self.assertRaises(ValueError):
                reader.decode(raw)

    def test_actual_cli(self):
        out = OUTPUT or ROOT / ".lake" / ("header-parser-" + uuid.uuid4().hex)
        out.mkdir(parents=True, exist_ok=False)
        cases = {"positive": (self.good, True)}

        def mutation(label, change):
            rows = copy.deepcopy(self.frames)
            change(rows)
            cases[label] = (encode(rows), False)

        mutation("bool-count", lambda r: r[0].__setitem__("count", True))
        mutation("wrong-catalog", lambda r: r[0].__setitem__("catalog", "0" * 64))
        mutation("wrong-schema", lambda r: r[0].__setitem__("schema", 1))
        mutation("wrong-variant", lambda r: r[1].__setitem__("variant", "bpo5"))
        mutation("wrong-family", lambda r: r[1].__setitem__("family", "ParentHeader"))
        mutation("wrong-case", lambda r: r[1].__setitem__("caseId", "other"))
        mutation("missing-field", lambda r: r[1]["fields"].pop())
        mutation("extra-field", lambda r: r[1]["fields"].append(r[1]["fields"][0]))
        mutation("swapped-fields", lambda r: r[1]["fields"].__setitem__(
            slice(0, 2), [r[1]["fields"][1], r[1]["fields"][0]]))
        mutation("wrong-label", lambda r: r[1]["fields"][3].__setitem__("type", "Bytes32"))
        mutation("interior-byte", lambda r: r[1]["fields"][6].__setitem__(
            "value", "00" * 128 + "01" + "00" * 127))
        mutation("bool-nat", lambda r: r[1]["fields"][7].__setitem__("value", False))
        mutation("float-nat", lambda r: r[1]["fields"][7].__setitem__("value", 0.0))
        mutation("overflow-u64", lambda r: r[1]["fields"][17].__setitem__("value", 2 ** 64))
        mutation("overflow-u256", lambda r: r[1]["fields"][11].__setitem__("value", 2 ** 256))
        mutation("string-nat", lambda r: r[1]["fields"][8].__setitem__("value", "0"))
        mutation("wrong-value", lambda r: r[1]["fields"][9].__setitem__("value", 1))
        mutation("lost-leading-zero", lambda r: r[1]["fields"][0].__setitem__("value", "00" * 31))
        mutation("wrong-position", lambda r: r[1]["fields"][0].__setitem__("position", False))
        mutation("missing-row", lambda r: r.pop(1))
        mutation("extra-row", lambda r: r.insert(1, r[1]))
        mutation("wrong-order", lambda r: r.__setitem__(slice(1, 3), [r[2], r[1]]))
        mutation("wrong-trailer", lambda r: r[-1].__setitem__("complete", False))
        mutation("bool-trailer", lambda r: r[-1].__setitem__("complete", 1))
        parent = next(i for i, row in enumerate(self.frames)
                      if row.get("family") == "ParentHeader")
        mutation("missing-accessor", lambda r: r[parent]["commonAccessors"].pop())
        mutation("wrong-accessor", lambda r: r[parent]["commonAccessors"][0].__setitem__(
            "value", 1))
        mutation("extra-accessor", lambda r: r[parent]["commonAccessors"].append(
            r[parent]["commonAccessors"][0]))
        mutation("swapped-accessors", lambda r: r[parent]["commonAccessors"].__setitem__(
            slice(0, 2), [r[parent]["commonAccessors"][1], r[parent]["commonAccessors"][0]]))
        long_data = next(i for i, row in enumerate(self.frames)
                         if row.get("fields") and len(str(row["fields"][12]["value"])) == 2050)
        mutation("truncated-long-data", lambda r: r[long_data]["fields"][12].__setitem__(
            "value", r[long_data]["fields"][12]["value"][:-2]))
        for label, raw in {
            "empty": b"", "missing-lf": self.good[:-1], "crlf": self.good.replace(b"\n", b"\r\n"),
            "blank": b"\n" + self.good, "bom": b"\xef\xbb\xbf" + self.good,
            "extra-json": self.good + b"{}\n", "array": b"[]\n",
            "invalid-utf8": b"\xff" + self.good,
            "duplicate-key": self.good.replace(b'"count":2798', b'"count":2798,"count":2798', 1),
            "duplicate-nested-key": self.good.replace(
                b'"position":0', b'"position":0,"position":0', 1),
            "negative-zero": self.good.replace(b'"value":0', b'"value":-0', 1),
            "nonfinite": self.good.replace(b'"value":0', b'"value":NaN', 1),
        }.items():
            self.assertNotEqual(raw, self.good)
            cases[label] = (raw, False)
        results = []
        for label, (raw, success) in cases.items():
            path = out / (label + ".jsonl")
            path.write_bytes(raw)
            cmd = [sys.executable, "-B"] + (["-O"] if sys.flags.optimize else [])
            cmd += [str(READER), "--check-target", str(path)]
            proc = subprocess.Popen(cmd, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            stdout, stderr = proc.communicate(timeout=30)
            (out / (label + ".stdout")).write_bytes(stdout)
            (out / (label + ".stderr")).write_bytes(stderr)
            self.assertEqual(proc.returncode, 0 if success else 1, label)
            self.assertTrue((stdout.startswith(b"PASS:") and not stderr) if success else
                            (not stdout and stderr.startswith(b"FAIL:")), label)
            results.append({"label": label, "argv": cmd, "pid": proc.pid,
                            "returncode": proc.returncode, "terminalKnown": True})
        (out / "results.json").write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    args, rest = parser.parse_known_args()
    OUTPUT = args.output_dir
    unittest.main(argv=[sys.argv[0], *rest])
