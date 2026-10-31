#!/usr/bin/env python3
"""Independent mathematical budget controls; no original Python budget operation exists.

Finite processing limits bound this test reader only, never the Lean policy domain.
"""

import argparse
import json
from pathlib import Path
import sys

FIELDS = ("gasLeft", "stateGasLeft", "stateGasBaseline", "refundCounter",
          "stateGasSpilled", "stateGasCommittedSpill")


def controls():
    """Input-only controls, independently varying all six raw meter fields."""
    large = 2 ** 4096
    meters = [
        (0, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0),
        (0, 0, 0, 0, 1, 0), (0, 0, 0, 0, 0, 1),
        (2, 0, 0, 0, 3, 5), (2, 1, 0, 0, 3, 5),
        (2, 0, 1, 0, 3, 5), (2, 0, 0, -1, 3, 5),
        (2, large, 0, -large, 3, 5), (2, 0, large, large, 3, 5),
        (large, 0, 0, 0, 0, 0), (0, 0, 0, 0, large, 0),
        (0, 0, 0, 0, 0, large), (large, large + 7, 1, -large - 3, large + 1, large + 2),
        (large, 1, large + 9, large + 5, large + 1, large + 2),
        (2 ** 64 + 1, 2 ** 256 + 2, 3, -(2 ** 256 + 4), 5, 2 ** 256 + 6),
    ]
    return [(f"B{i:02d}C{j}", meter, constant)
            for i, meter in enumerate(meters)
            for j, constant in enumerate((0, 1, 17, large + 11))]


def input_text():
    return "".join("\t".join(map(str, (id_, *meter, constant))) + "\n"
                   for id_, meter, constant in controls())


def expected():
    result = [{"schema": "budget-policy-v1", "count": len(controls())}]
    for id_, meter, constant in controls():
        potential = meter[0] + meter[4] + meter[5]
        result.append({"id": id_, "meter": dict(zip(FIELDS, meter)), "constant": constant,
                       "phi": potential, "phiBudget": potential + 1, "constBudget": constant})
    return result + [{"end": True, "count": len(controls())}]


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate key: {key}")
        result[key] = value
    return result


def reject_constant(value):
    raise ValueError(f"nonfinite number: {value}")


def exact(value, model, path="frame"):
    if type(value) is not type(model):
        raise ValueError(f"{path}: exact type mismatch")
    if isinstance(model, dict):
        if value.keys() != model.keys():
            raise ValueError(f"{path}: missing or extra keys")
        for key in model:
            exact(value[key], model[key], f"{path}.{key}")
    elif isinstance(model, list):
        if len(value) != len(model):
            raise ValueError(f"{path}: count mismatch")
        for index, (item, wanted) in enumerate(zip(value, model)):
            exact(item, wanted, f"{path}[{index}]")
    elif value != model:
        raise ValueError(f"{path}: value mismatch")


def check_text(raw):
    if len(raw.encode("utf-8")) > 4000000:
        raise ValueError("output exceeds reader bound")
    lines = raw.splitlines()
    if len(lines) != len(controls()) + 2 or not raw.endswith("\n"):
        raise ValueError("framing/count mismatch")
    frames = [json.loads(line, object_pairs_hook=unique_object,
                         parse_constant=reject_constant) for line in lines]
    exact(frames, expected())
    return len(controls())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write-input", type=Path)
    group.add_argument("--check-target", type=Path)
    args = parser.parse_args()
    try:
        if args.write_input is not None:
            args.write_input.write_text(input_text(), encoding="utf-8")
            print(f"wrote {len(controls())} input-only controls")
        else:
            count = check_text(args.check_target.read_text(encoding="utf-8"))
            print(f"PASS {count} complete mathematical budget observations")
    except (OSError, ValueError, RecursionError) as error:
        print(f"FAIL {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
