#!/usr/bin/env python3
"""Positive and malformed-stream CLI controls for reference division, including -O."""
from pathlib import Path
import argparse
import importlib.util
import json
import os
import subprocess
import sys
import uuid

ROOT = Path(__file__).resolve().parents[1]
READER = ROOT / "STFSpec/Conformance/Field/reference_division_differential.py"
spec = importlib.util.spec_from_file_location("division_reader", READER)
reader = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reader)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    out = args.output_dir or ROOT / ".lake" / ("division-parser-" + uuid.uuid4().hex)
    out.mkdir(parents=True, exist_ok=False)
    expected = reader.expected_records()
    def encode(rows):
        return ("\n".join(json.dumps(row, separators=(",", ":")) for row in rows) + "\n").encode()
    good = encode(expected)
    cases = {"positive": (good, True)}
    def mutation(label, change):
        rows = json.loads(json.dumps(expected))
        change(rows)
        cases[label] = (encode(rows), False)
    for field in ("p", "raw_a", "raw_b", "metadata", "canonical_a", "canonical_b",
                  "inverse", "named", "operator"):
        mutation("bool-" + field, lambda rows, field=field: rows[1].__setitem__(field, False if rows[1][field] == 0 else True))
    mutation("metadata-bool-zero", lambda r: r[2].__setitem__("metadata", False))
    mutation("float", lambda r: r[1].__setitem__("named", 0.0))
    mutation("negative-natural", lambda r: r[1].__setitem__("raw_a", -1))
    mutation("string-natural", lambda r: r[1].__setitem__("named", "0"))
    mutation("null-natural", lambda r: r[1].__setitem__("inverse", None))
    mutation("integer-range", lambda r: r[1].__setitem__("in_range", 1))
    mutation("false-range", lambda r: r[1].__setitem__("in_range", False))
    mutation("wrong-value", lambda r: r[1].__setitem__("named", 1))
    mutation("wrong-operator", lambda r: r[1].__setitem__("operator", 1))
    mutation("wrong-inverse", lambda r: r[1].__setitem__("inverse", 1))
    mutation("wrong-canonical", lambda r: r[1].__setitem__("canonical_b", 1))
    mutation("wrong-context", lambda r: r[1].__setitem__("context", "fabricated-native-scalar"))
    mutation("wrong-id", lambda r: r[1].__setitem__("id", "other"))
    mutation("wrong-order", lambda r: r.__setitem__(slice(1, 3), [r[2], r[1]]))
    mutation("missing-field", lambda r: r[1].pop("inverse"))
    mutation("extra-field", lambda r: r[1].__setitem__("source_metadata", None))
    mutation("missing-row", lambda r: r.pop(1))
    mutation("extra-row", lambda r: r.insert(1, r[1]))
    mutation("wrong-provenance", lambda r: r[0].__setitem__("catalog", "0" * 64))
    mutation("wrong-schema", lambda r: r[0].__setitem__("schema", 1))
    mutation("bool-count", lambda r: r[0].__setitem__("count", True))
    mutation("wrong-trailer", lambda r: r[-1].__setitem__("complete", False))
    mutation("missing-trailer", lambda r: r.pop())
    for name, data in {"empty": b"", "missing-lf": good[:-1], "bom": b"\xef\xbb\xbf" + good,
                       "crlf": good.replace(b"\n", b"\r\n"), "blank": b"\n" + good,
                       "leading-space": b" " + good, "trailing-object": good + b"{}\n",
                       "array": b"[]\n", "duplicate-key": good.replace(b'"count":2787',
                       b'"count":2787,"count":2787', 1),
                       "nan": good.replace(b'"named":0', b'"named":NaN', 1),
                       "infinity": good.replace(b'"named":0', b'"named":Infinity', 1),
                       "overflow-float": good.replace(b'"named":0', b'"named":1e309', 1),
                       "two-objects": b'{}{}\n' + good}.items():
        reader.require(data != good, "negative must change stream")
        cases[name] = (data, False)
    results = []
    for label, (data, success) in cases.items():
        fixture = out / (label + ".jsonl")
        fixture.write_bytes(data)
        for optimized in (False, True):
            cmd = [sys.executable, "-B"] + (["-O"] if optimized else []) + [str(READER),
                   "--check-target", str(fixture)]
            proc = subprocess.Popen(cmd, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            stdout, stderr = proc.communicate(timeout=30)
            prefix = out / (label + ("-optimized" if optimized else "-normal"))
            prefix.with_suffix(".stdout").write_bytes(stdout)
            prefix.with_suffix(".stderr").write_bytes(stderr)
            reader.require((proc.returncode == 0) is success, label + ": wrong CLI outcome")
            reader.require((not stderr and stdout.startswith(b"PASS")) if success else
                           ((b"ValueError" in stderr or b"JSONDecodeError" in stderr) and not stdout), label + ": wrong rejection")
            results.append(dict(label=label, optimized=optimized, pid=proc.pid, argv=cmd,
                                exit=proc.returncode, expected_success=success))
    (out / "results.json").write_text(json.dumps(dict(status="PASS", cases=len(cases),
        negatives=len(cases)-1, invocations=results), indent=2) + "\n")
    print(f"PASS {len(cases)-1} meaningful malformed streams and positive CLI, both modes")


if __name__ == "__main__":
    main()
