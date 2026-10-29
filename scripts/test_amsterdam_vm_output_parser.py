#!/usr/bin/env python3
"""Complete native-value admission regressions; run with ordinary Python and -O."""

import copy
import importlib.util
import json
from pathlib import Path
import sys

PATH = Path(__file__).resolve().parents[1] / "STFSpec/Conformance/Fork/amsterdam_vm_values.py"
SPEC = importlib.util.spec_from_file_location("amsterdam_vm_values", PATH)
READER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(READER)


def encoded(value):
    return json.dumps(value, separators=(",", ":")).encode()


def rejected(data, label):
    try:
        READER.parse_target(data)
    except READER.AdmissionError:
        return
    raise RuntimeError("accepted " + label)


def main():
    expected = READER.frozen_values()
    READER.parse_target(encoded(expected))
    count = 0
    # Exercise every scalar and every array entry, through both direct and grouped
    # record paths. Each one must independently affect complete comparison.
    def visit(node, path):
        nonlocal count
        if type(node) is dict:
            for key, value in node.items():
                visit(value, path + [key])
        elif type(node) is list:
            for index, value in enumerate(node):
                visit(value, path + [index])
        else:
            for replacement in (node + 1, bool(node), str(node), None, float(node)):
                mutated = copy.deepcopy(expected)
                parent = mutated
                for key in path[:-1]:
                    parent = parent[key]
                parent[path[-1]] = replacement
                rejected(encoded(mutated), str(path))
                count += 1
    visit(expected, [])
    for group, rows in expected.items():
        mutated = copy.deepcopy(expected)
        del mutated[group]
        rejected(encoded(mutated), "missing top group")
        mutated = copy.deepcopy(expected)
        mutated[group]["extra"] = 0
        rejected(encoded(mutated), "extra field")
        for key in rows:
            mutated = copy.deepcopy(expected)
            del mutated[group][key]
            rejected(encoded(mutated), "missing field")
            count += 1
    for path in (["gasCosts"], ["vmConfig", "costs"]):
        for table in ("blsG1KDiscount", "blsG2KDiscount"):
            for operation in ("short", "extra", "reverse", "swap", "duplicate"):
                mutated = copy.deepcopy(expected)
                parent = mutated
                for key in path:
                    parent = parent[key]
                array = parent[table]
                if operation == "short":
                    array.pop()
                elif operation == "extra":
                    array.append(0)
                elif operation == "reverse":
                    array.reverse()
                elif operation == "swap":
                    array[2], array[3] = array[3], array[2]
                else:
                    array[3] = array[2]
                rejected(encoded(mutated), operation + " table")
                count += 1
    valid = encoded(expected)
    for bad in (
        b"", b"{", valid[:-1], valid + b"{}", b"[]", b"null",
        b'{"gasCosts":{},"gasCosts":{}}',
        valid.replace(b'"base":2', b'"base":2,"base":2', 1),
        valid.replace(b'"base":2', b'"base":NaN', 1),
        valid.replace(b'"base":2', b'"base":Infinity', 1),
        b"\xff", b"[" * 2000 + b"]" * 2000, b" " * (READER.MAX_BYTES + 1),
    ):
        rejected(bad, "malformed/duplicate/frame")
        count += 1
    if any(name == "ethereum" or name.startswith(("ethereum.", "ethereum_types"))
           for name in sys.modules):
        raise RuntimeError("unexpected EELS import")
    print(f"PASS Amsterdam VM parser: {count} rejection controls; complete literal positive")


if __name__ == "__main__":
    main()
