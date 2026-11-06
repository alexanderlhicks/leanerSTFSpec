#!/usr/bin/env -S uv run --no-project --python 3.12 python
"""Check complete raw header observations against frozen identity/projection expectations.

The catalogue is independent of both the Lean implementation and the pinned EELS
classes. Source coupling is finite raw-constructor evidence, separate from this
reader. This check establishes no codec, admission, hash or execution result.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

RECIPE = Path(__file__).with_name("header_carrier_cases.py")
spec = importlib.util.spec_from_file_location("header_cases", RECIPE)
cases = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cases)

CATALOG = "4639932a31950e19686713ce32266d01ba172dc64417b66d0c922a3cb2152d63"
COUNT = 2798
MAX_BYTES = 24_000_000
MAX_LINE = 32_000


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def integer(token):
    require(not token.startswith("-"), "unsigned integer required")
    return int(token)


def no_float(token):
    raise ValueError("floating or nonfinite token: " + token)


def decode(raw):
    return json.loads(raw, object_pairs_hook=unique_object, parse_int=integer,
                      parse_float=no_float, parse_constant=no_float)


def exact(actual, expected, context="$"):
    # Exact recursive types keep Python's False == 0 and True == 1 out of evidence.
    require(type(actual) is type(expected), context + ": JSON type differs")
    if type(expected) is dict:
        require(actual.keys() == expected.keys(), context + ": object keys differ")
        for key in expected:
            exact(actual[key], expected[key], context + "/" + key)
    elif type(expected) is list:
        require(len(actual) == len(expected), context + ": array length differs")
        for index, (left, right) in enumerate(zip(actual, expected, strict=True)):
            exact(left, right, context + "/" + str(index))
    else:
        require(actual == expected, context + ": value differs")


def expected_frames():
    require(hashlib.sha256(cases.input_bytes()).hexdigest() == CATALOG,
            "frozen input recipe differs")
    rows = list(cases.expected_rows())
    require(len(rows) == COUNT, "catalogue count differs")
    return [{"schema": "header-carriers-v1", "catalog": CATALOG, "count": COUNT},
            *rows, {"complete": True, "count": COUNT}]


def check_bytes(raw):
    require(type(raw) is bytes and len(raw) <= MAX_BYTES, "target byte bound differs")
    require(raw.endswith(b"\n") and b"\r" not in raw, "LF framing required")
    lines = raw[:-1].split(b"\n")
    require(len(lines) == COUNT + 2, "complete ordered frame count required")
    wanted = expected_frames()
    for index, (line, expected) in enumerate(zip(lines, wanted, strict=True)):
        require(line and len(line) <= MAX_LINE, "frame size differs")
        require(line.startswith(b"{") and line.endswith(b"}"), "object framing required")
        exact(decode(line.decode("utf-8")), expected, "frame " + str(index))
    return COUNT


def check_target(path):
    with Path(path).open("rb") as stream:
        raw = stream.read(MAX_BYTES + 1)
    return check_bytes(raw)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-target", required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        count = check_target(args.check_target)
    except (ValueError, OSError, UnicodeError, RecursionError) as error:
        print("FAIL:", error, file=sys.stderr)
        return 1
    print("PASS:", count, "complete raw header rows, every field and parent getter")
    return 0


if __name__ == "__main__":
    sys.exit(main())
