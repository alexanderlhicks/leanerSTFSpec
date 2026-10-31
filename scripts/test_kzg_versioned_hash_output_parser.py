# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Strict parser controls, including real CLI rejection, in normal and -O Python."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PATH = ROOT / "STFSpec/Conformance/Precompiles/kzg_versioned_hash_differential.py"
spec = importlib.util.spec_from_file_location("kzg_reader", PATH)
reader = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reader)


def encode(values):
    return b"".join(reader.canonical(v) for v in values)


def main():
    base = [{"schema": reader.SCHEMA, "count": reader.COUNT}, *reader.expected_rows(),
            {"end": True, "count": reader.COUNT}]
    total = 0
    with tempfile.TemporaryDirectory(prefix="kzg-parser-") as temp:
        output = Path(temp) / "observations.jsonl"
        flags = [sys.executable, "-B"] + (["-O"] if sys.flags.optimize else [])

        def check(name, data, accepted=False):
            nonlocal total
            try:
                reader.parse_target(data)
            except reader.AdmissionError:
                if accepted:
                    raise RuntimeError("rejected valid " + name)
            else:
                if not accepted:
                    raise RuntimeError("accepted invalid " + name)
            output.write_bytes(data)
            result = subprocess.run([*flags, str(PATH), "--check-target", str(output)],
                                    capture_output=True)
            if (result.returncode == 0) != accepted:
                raise RuntimeError("CLI admission disagrees " + name)
            total += 1

        check("valid", encode(base), True)
        for name, data in [("empty", b""), ("invalid-utf8", b"\xff"),
                           ("truncated-json", b"{\n"), ("missing-footer", encode(base[:-1])),
                           ("extra-row", encode(base + [base[-1]])),
                           ("no-newline", encode(base)[:-1]),
                           ("blank-line", encode(base) + b"\n"),
                           ("duplicate-key", b'{"count":926,"count":926}\n'),
                           ("nonfinite", b'{"count":NaN}\n'),
                           ("oversize", b" " * (reader.MAX_BYTES + 1))]:
            check(name, data)

        def mutate(name, path, value=None, delete=False):
            changed = copy.deepcopy(base)
            obj = changed
            for key in path[:-1]:
                obj = obj[key]
            if delete:
                del obj[path[-1]]
            else:
                obj[path[-1]] = value
            check(name, encode(changed))

        for row in (0, len(base) - 1):
            for value in (True, False, None, "926", 926.0, [], {}, -1, 925, 927):
                mutate("typed/count", [row, "count"], value)
        for value in (False, 1, None, "true"):
            mutate("footer-bool", [len(base) - 1, "end"], value)
        for key in ("id", "input_hex", "length", "actual_hex"):
            mutate("missing-field", [2, key], delete=True)
        mutate("extra-field", [2, "extra"], None)
        for value in (True, False, 1.0, "1", None, [], {}, -1, 0, 2):
            mutate("row-length", [2, "length"], value)
        for value in (True, 1, None, "", "c0000", "c0002", " c0001"):
            mutate("row-id", [2, "id"], value)
        for key in ("input_hex", "actual_hex"):
            for value in (True, None, 1, [], {}, "0", "GG", "AA", " 00", "00 ",
                          "0x00", "００", "00\n", "", "00" * 31, "00" * 33):
                mutate("malformed-hex", [2, key], value)
        good = base[2]["actual_hex"]
        for i in range(32):
            changed = good[:2*i] + ("ff" if good[2*i:2*i+2] != "ff" else "00") + good[2*i+2:]
            mutate("each-output-byte", [2, "actual_hex"], changed)
        mutate("wrong-input-byte", [2, "input_hex"], "01")
        swapped = copy.deepcopy(base)
        swapped[2], swapped[3] = swapped[3], swapped[2]
        check("row-order", encode(swapped))
        duplicate = copy.deepcopy(base)
        duplicate[3] = duplicate[2]
        check("duplicate-id", encode(duplicate))
        # CLI requires both source modes together and exact two-path options.
        output.write_bytes(encode(base))
        result = subprocess.run([*flags, str(PATH), "--check-target", str(output),
                                 "--check-source-normal", str(output), str(output)], capture_output=True)
        if result.returncode == 0:
            raise RuntimeError("CLI accepted one source mode")
        total += 1
    print(f"PASS KZG parser: {total} actual CLI/library controls")


if __name__ == "__main__":
    main()
