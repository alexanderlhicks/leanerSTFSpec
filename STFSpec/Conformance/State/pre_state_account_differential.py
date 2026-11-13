#!/usr/bin/env python3
"""Strict complete optional-account output reader; no source loader or lookup oracle.

The input-only catalogue and independent integer/list expectations are frozen beside
this file. Source execution/authentication remains separate: instrumented exceptions
are not a selected production WitnessError adapter. Every failed target state is null.
The companion `pre_state_account_source.py` reproduces the separately authenticated
normal/-O source comparison from a supplied pinned clone.
"""

import argparse
import hashlib
import json
from pathlib import Path

INPUT_SHA256 = "4dbbecfb0e575e655694f1aad624bde5317cf66889117d027ecc0014bfb3cd4e"
EXPECTED_SHA256 = "7d92dee8ee6feebad33eb16c3c355dbd081da84a5021a7e6eb977d8345eed35a"


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
    for name, digest in [("pre_state_account_inputs.json", INPUT_SHA256),
                         ("pre_state_account_expected.json", EXPECTED_SHA256)]:
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
            raise AdmissionError("frozen catalogue identity mismatch: " + name)
    rows = decode((root / "pre_state_account_expected.json").read_bytes())
    if type(rows) is not list or len(rows) != 66:
        raise AdmissionError("frozen catalogue count mismatch")
    return rows


def parse_target(data):
    if type(data) is not bytes or len(data) > 1048576:
        raise AdmissionError("invalid or oversized byte stream")
    lines = data.splitlines()
    if len(lines) != 66:
        raise AdmissionError("missing, duplicate or extra observations")
    frames = [decode(line) for line in lines]
    strict_equal(frames, expected_frames())
    return frames


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-target", required=True, type=Path)
    args = parser.parse_args()
    frames = parse_target(args.check_target.read_bytes())
    print(f"PASS optional accounts: {len(frames)} complete observations; source imports/calls 0")


if __name__ == "__main__":
    main()
