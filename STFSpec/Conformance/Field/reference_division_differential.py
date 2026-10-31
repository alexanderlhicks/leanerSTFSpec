#!/usr/bin/env python3
"""Check complete reference division observations against the frozen source baseline.

The baseline was frozen from original py-ecc 8.0.0 optimized FQ / on 929 natural
pairs, with both actual BN254/BLS12-381 base classes and 15 synthetic parameter
classes; those source runs and the generator are out of tree (not committed).
The target expands each input over three metadata choices; source has no metadata.
Spec guidance: STFSpec/informal/modules/EthField.md §§3–7.
"""
from pathlib import Path
import argparse
import hashlib
import json

DIRECTORY = Path(__file__).resolve().parent
# Opaque fixed catalogue label shared with the producer; it is not a digest of any
# committed file. INPUT_SHA and EXPECTED_SHA pin the committed inputs and baseline.
CATALOG = "19119c6a0f1960ee3fae319250af7ba1e399ceec40afe14bb0b48df29a5be9d2"
EXPECTED_SHA = "3b1a4b54c3a1c52be36488003d849e5496775cd203e95fcb3ff2c6e8b7ec023f"
INPUT_SHA = "5f40afa6ec04d266d83c956768477d7183c88d21e3b5c8ca7ad7b0898cd8bfd8"
METADATA = (None, 0, 2**4096 + 17)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def object_pairs(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate key")
        result[key] = value
    return result


def forbidden(value):
    raise ValueError("floats/nonfinite numbers are forbidden: " + value)


def records(data):
    require(data and data.endswith(b"\n"), "missing terminal LF")
    require(not data.startswith(b"\xef\xbb\xbf") and b"\r" not in data, "noncanonical framing")
    rows = []
    for line in data[:-1].split(b"\n"):
        require(line and line.startswith(b"{") and line.endswith(b"}"), "one object per line")
        row = json.loads(line.decode("utf-8"), object_pairs_hook=object_pairs,
                         parse_float=forbidden, parse_constant=forbidden)
        require(type(row) is dict, "object required")
        rows.append(row)
    return rows


def exact(actual, expected, path="root"):
    require(type(actual) is type(expected), path + ": exact type mismatch")
    if type(expected) is dict:
        require(actual.keys() == expected.keys(), path + ": fields mismatch")
        for key in expected:
            exact(actual[key], expected[key], path + "." + key)
    elif type(expected) is list:
        require(len(actual) == len(expected), path + ": list length mismatch")
        for index, (a, b) in enumerate(zip(actual, expected, strict=True)):
            exact(a, b, path + f"[{index}]")
    else:
        require(actual == expected, path + ": value mismatch")


def baseline():
    source = (DIRECTORY / "reference_division_expected.jsonl").read_bytes()
    raw = (DIRECTORY / "reference_division_inputs.tsv").read_bytes()
    require(hashlib.sha256(source).hexdigest() == EXPECTED_SHA, "baseline provenance")
    require(hashlib.sha256(raw).hexdigest() == INPUT_SHA, "input provenance")
    rows = records(source)
    inputs = [line.split("\t") for line in raw.decode().splitlines()]
    require(len(rows) == len(inputs) == 929, "input count")
    result = []
    for index, (row, inp) in enumerate(zip(rows, inputs, strict=True)):
        require(inp[0] == row["id"] == f"div-input-{index:04}", "id/order")
        exact([row[k] for k in ("id", "context", "p", "raw_a", "raw_b")],
              inp[:2] + [int(v) for v in inp[2:]], "input bridge")
        for metadata in METADATA:
            result.append(dict(row, metadata=metadata))
    return result


def expected_records():
    return [dict(schema="reference-division-v1", catalog=CATALOG, count=2787),
            *baseline(), dict(complete=True, count=2787)]


def check(data):
    actual = records(data)
    expected = expected_records()
    exact(actual, expected)
    return 2787


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-target", required=True, type=Path)
    args = parser.parse_args()
    count = check(args.check_target.read_bytes())
    print(f"PASS complete reference division: {count} rows, "
          "all values/types/metadata/order/provenance")


if __name__ == "__main__":
    main()
