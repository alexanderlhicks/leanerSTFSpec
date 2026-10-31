#!/usr/bin/env python3
"""Strict complete ancestor output reader; no EELS loader or suffix oracle.

The literal catalog was independently frozen before Lean construction. This
reader validates finite target values only; source/runtime authentication is a
separate gate, and the source packet is never imported by this module.
"""

import argparse
import hashlib
import json
from pathlib import Path

CATALOG_SHA256 = "b150be91f95506119cb221a908dc7b090f73f50d96be3bd79346a8e90acc0a1b"


class AdmissionError(ValueError):
    """The complete observation is outside the frozen wire contract."""


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise AdmissionError("duplicate JSON key: " + key)
        result[key] = value
    return result


def reject_number(value):
    raise AdmissionError("noninteger JSON number: " + value)


def decode(data):
    try:
        return json.loads(data, object_pairs_hook=unique_object,
                          parse_float=reject_number, parse_constant=reject_number)
    except (UnicodeError, ValueError) as error:
        raise AdmissionError(str(error)) from error


def strict_equal(actual, expected, path="frame"):
    # Exact types are essential: False == 0 and True == 1 in Python.
    if type(actual) is not type(expected):
        raise AdmissionError(path + ": wrong type")
    if type(expected) is dict:
        if actual.keys() != expected.keys():
            raise AdmissionError(path + ": missing or extra keys")
        for key in expected:
            strict_equal(actual[key], expected[key], path + "." + key)
    elif type(expected) is list:
        if len(actual) != len(expected):
            raise AdmissionError(path + ": wrong length")
        for index, (left, right) in enumerate(zip(actual, expected, strict=True)):
            strict_equal(left, right, path + "[" + str(index) + "]")
    elif actual != expected:
        raise AdmissionError(path + ": complete value mismatch")


def expected_frames():
    data = Path(__file__).with_name("witness_ancestors_cases.json").read_bytes()
    if hashlib.sha256(data).hexdigest() != CATALOG_SHA256:
        raise AdmissionError("frozen catalog identity mismatch")
    rows = decode(data)
    if type(rows) is not list or len(rows) != 48:
        raise AdmissionError("frozen catalog count mismatch")
    return [{"id": row["id"], "headers": row["headers"], "offset": row["offset"],
             "result": row["expected"]} for row in rows]


def parse_target(data):
    if type(data) is not bytes or len(data) > 1048576:
        raise AdmissionError("invalid or oversized byte stream")
    lines = data.splitlines()
    if len(lines) != 48:
        raise AdmissionError("missing, duplicate or extra observations")
    frames = [decode(line) for line in lines]
    strict_equal(frames, expected_frames())
    return frames


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-target", required=True, type=Path)
    args = parser.parse_args()
    frames = parse_target(args.check_target.read_bytes())
    print(f"PASS ancestors: {len(frames)} complete target observations; source imports/calls 0")


if __name__ == "__main__":
    main()
