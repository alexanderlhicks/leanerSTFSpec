#!/usr/bin/env python3
"""Strict complete-value reader for the independently frozen Amsterdam VM catalogue.

No EELS import or source recomputation. Every expected stored value, including both
full ordered tables, is literal data authenticated by CATALOGUE_SHA256. Provenance
in that file binds its rows to the independent preimplementation packet.
"""

import argparse
import hashlib
import json
from pathlib import Path
import sys

CATALOGUE = Path(__file__).with_name("amsterdam_vm_catalogue.json")
CATALOGUE_SHA256 = "e814a7640f23a14a98d58282f6f649d459cdd5d874d37b498fdfc772dd51f426"
MAX_BYTES = 65536


class AdmissionError(ValueError):
    """A malformed or nonmatching complete observation."""


def require(condition, message):
    if not condition:
        raise AdmissionError(message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate field: " + key)
        result[key] = value
    return result


def reject_number(value):
    raise AdmissionError("noninteger JSON number: " + value)


def load_json(data):
    require(type(data) is bytes and len(data) <= MAX_BYTES, "input size/type")
    try:
        return json.loads(
            data.decode("utf-8"),
            object_pairs_hook=unique_object,
            parse_float=reject_number,
            parse_constant=reject_number,
        )
    except (UnicodeError, ValueError, RecursionError) as error:
        raise AdmissionError("invalid JSON: " + str(error)) from error


def frozen_values():
    data = CATALOGUE.read_bytes()
    require(hashlib.sha256(data).hexdigest() == CATALOGUE_SHA256, "catalogue digest")
    catalogue = load_json(data)
    values = {}
    for group in ("gasCosts", "stateGasCosts", "vmLimits"):
        values[group] = {row["lean_field"]: row["value"] for row in catalogue[group]}
    values["vmConfig"] = {
        "costs": values["gasCosts"],
        "stateCosts": values["stateGasCosts"],
        "limits": values["vmLimits"],
    }
    return values


def compare_exact(actual, expected, path="root"):
    # Python equality identifies True with 1; admission must precede equality.
    require(type(actual) is type(expected), path + ": exact JSON type")
    if type(expected) is dict:
        require(actual.keys() == expected.keys(), path + ": complete field set")
        for key, value in expected.items():
            compare_exact(actual[key], value, path + "." + key)
    elif type(expected) is list:
        require(len(actual) == len(expected), path + ": complete array length")
        for index, (value, wanted) in enumerate(zip(actual, expected, strict=True)):
            compare_exact(value, wanted, path + "[" + str(index) + "]")
    else:
        require(type(expected) is int and actual == expected, path + ": stored value")


def parse_target(data):
    value = load_json(data)
    compare_exact(value, frozen_values())
    return value


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-target", required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        with args.check_target.open("rb") as stream:
            parse_target(stream.read(MAX_BYTES + 1))
        print("PASS Amsterdam VM: all 151 stored values and complete VmConfig; source imports 0")
        return 0
    except (AdmissionError, OSError) as error:
        print("FAIL Amsterdam VM: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
