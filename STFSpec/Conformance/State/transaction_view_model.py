#!/usr/bin/env python3
"""Strict complete mathematical transaction-view controls.

The 118 complete expected raw maps were independently derived and frozen before
candidate target execution. These are finite model-agreement controls: the pinned
Python source has no standalone mathematical block/transaction-view operation.
"""

import argparse
import hashlib
import json
from pathlib import Path

INPUT_SHA256 = "635b516926026b9c19ece1316b86630c195f812cf9730a68734c9e5058446986"
EXPECTED_SHA256 = "ed4a32b2d685615a6065176b8ed83ccd155b675d0bc6dc429a3bcee846cffb41"


class AdmissionError(ValueError):
    """The complete stream differs from its frozen finite contract."""


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
    root = Path(__file__).parent
    for name, digest in [("transaction_view_inputs.json", INPUT_SHA256),
                         ("transaction_view_expected.json", EXPECTED_SHA256)]:
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
            raise AdmissionError("frozen catalogue identity mismatch: " + name)
    rows = decode((root / "transaction_view_expected.json").read_bytes())
    if type(rows) is not list or len(rows) != 118:
        raise AdmissionError("frozen catalogue count mismatch")
    return rows


def parse_target(data):
    if type(data) is not bytes or len(data) > 2097152:
        raise AdmissionError("invalid or oversized byte stream")
    if not data.endswith(b"\n") or b"\r" in data:
        raise AdmissionError("expected newline-terminated JSON lines")
    lines = data.split(b"\n")[:-1]
    if len(lines) != 118:
        raise AdmissionError("missing, duplicate or extra observations")
    frames = [decode(line) for line in lines]
    strict_equal(frames, expected_frames())
    return frames


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-target", required=True, type=Path)
    args = parser.parse_args()
    frames = parse_target(args.check_target.read_bytes())
    print(f"PASS transaction views: {len(frames)} complete raw model observations; no source execution")


if __name__ == "__main__":
    main()
