# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Positive and negative controls for complete byte/error admission, normal and -O."""
import copy
import importlib.util
import json
from pathlib import Path
import sys

PATH = Path(__file__).resolve().parents[1] / "STFSpec/Conformance/Block/deposit_data_differential.py"
spec = importlib.util.spec_from_file_location("deposit_reader", PATH)
reader = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reader)


def encode(frame):
    return ("\n".join(json.dumps(x, separators=(",", ":")) for x in frame) + "\n").encode()


def main():
    cases = reader.catalog()
    rows = [{"id": x["id"], "hex": x["hex"], "actual": reader.projection(x["expected"])} for x in cases]
    target = [{"schema": reader.SCHEMA, "count": reader.COUNT}, *rows,
              {"end": True, "count": reader.COUNT}]
    source_rows = []
    for row in cases:
        success = "ok" in row["expected"]
        source_rows.append({**row, "actual": row["expected"], "input_type": "builtins.bytes",
                            "input_bytes": len(row["hex"]) // 2,
                            "return_type": "builtins.bytes" if success else None,
                            "exception_type": None if success else "ethereum.exceptions.InvalidBlock",
                            "exception_args": None if success else [row["expected"]["message"]],
                            **({"return_bytes": 192} if success else {})})
    source = {"head": reader.PIN, "status": "all 142 source cases passed",
              "case_file_before_sha256": reader.CATALOG_SHA256,
              "case_file_after_sha256": reader.CATALOG_SHA256,
              "runtime": {"isolated": 1, "dont_write_bytecode": True, "optimize": 0,
                          "cache_prefix_empty_at_start_and_end": True},
              "function": {"module": "ethereum.forks.amsterdam.requests",
                           "qualname": "extract_deposit_data", "firstlineno": 170},
              "rows": source_rows}
    count = 0

    def check(mode, name, value, valid=False, raw=False):
        nonlocal count
        data = value if raw else encode(value) if mode == "target" else json.dumps(value).encode()
        parser = reader.parse_target if mode == "target" else reader.parse_source
        try:
            parser(data)
        except reader.AdmissionError:
            if valid:
                raise RuntimeError("rejected valid " + mode + ":" + name)
        else:
            if not valid:
                raise RuntimeError("accepted invalid " + mode + ":" + name)
        count += 1

    check("target", "valid", target, True)
    check("target", "no-final-newline", encode(target)[:-1], True, True)
    check("source", "valid", source, True)
    for mode, base in (("target", target), ("source", source)):
        for name, data in (("empty", b""), ("truncated", b'{"schema":'),
                           ("oversize", b" " * (8388608 + 1)), ("garbage", b"nope"),
                           ("nonfinite", b'{"value":NaN}'), ("duplicate-key", b'{"a":1,"a":1}')):
            check(mode, name, data, raw=True)

        def mutate(name, path, value=None, delete=False):
            changed = copy.deepcopy(base)
            obj = changed
            for key in path[:-1]:
                obj = obj[key]
            if delete:
                del obj[path[-1]]
            else:
                obj[path[-1]] = value
            check(mode, name, changed)

        prefix = [1] if mode == "target" else ["rows", 0]
        for field in ("id", "hex", "actual"):
            mutate("missing-" + field, prefix + [field], delete=True)
        mutate("extra-row-key", prefix + ["extra"], 0)
        for bad in (True, False, 0, 0.0, "0", None, [], {}):
            mutate("result-type", prefix + ["actual"], bad)
        for bad in ("0", "0x00", "gg", "00 ", "AA", "٠٠", True, 0, None):
            mutate("hex", prefix + ["hex"], bad)
        for bad in (True, 0, None, "other"):
            mutate("id", prefix + ["id"], bad)
        for bad in ("00" * 191, "00" * 193, "GG" * 192, True, 0, None):
            mutate("ok-bytes", prefix + ["actual", "ok"], bad)
        mutate("ok-extra-key", prefix + ["actual", "error"], "length")
        collection = base[1:-1] if mode == "target" else base["rows"]
        for name, altered in (("missing", collection[:-1]), ("extra", collection + [collection[-1]]),
                              ("duplicate", [collection[0], *collection[:-1]]),
                              ("swapped", [collection[1], collection[0], *collection[2:]])):
            changed = copy.deepcopy(base)
            if mode == "target":
                changed = [changed[0], *altered, changed[-1]]
            else:
                changed["rows"] = altered
            check(mode, name, changed)
        # Every successful byte position must matter, including leading/trailing zeros.
        original = bytes.fromhex(cases[0]["expected"]["ok"])
        for index in range(192):
            changed = bytearray(original)
            changed[index] ^= 1
            mutate("changed-success-byte", prefix + ["actual", "ok"], changed.hex())
        for index, case in enumerate(cases):
            if "error" not in case["expected"]:
                continue
            at = [index + 1] if mode == "target" else ["rows", index]
            for bad in ("unknown", "", True, None):
                mutate("error-identity", at + ["actual", "error"], bad)
            other = "wcOffset" if case["expected"]["error"] == "length" else "length"
            mutate("other-known-error", at + ["actual", "error"], other)
        if mode == "target":
            for at in (0, -1):
                for bad in (True, 142.0, "142", 141, 143):
                    mutate("count", [at, "count"], bad)
            mutate("end-int", [-1, "end"], 1)
            mutate("header-extra", [0, "extra"], 0)
            mutate("footer-extra", [-1, "extra"], 0)
            mutate("schema", [0, "schema"], "other")
            check(mode, "after-footer", encode(base) + b"{}\n", raw=True)
            check(mode, "blank-line", encode(base) + b"\n", raw=True)
            check(mode, "nested-duplicate", encode(base).replace(b'"ok":', b'"ok":"", "ok":', 1), raw=True)
        else:
            for path, bad in ((["head"], "bad"), (["case_file_after_sha256"], "bad"),
                              (["runtime", "isolated"], True), (["runtime", "dont_write_bytecode"], 1),
                              (["runtime", "optimize"], False), (["runtime", "optimize"], 0.0),
                              (["runtime", "optimize"], 2), (["function", "firstlineno"], 170.0),
                              (["function", "qualname"], "other"), (["runtime"], None)):
                mutate("binding", path, bad)
            for index, case in enumerate(cases):
                if "error" not in case["expected"]:
                    continue
                at = ["rows", index]
                mutate("wrong-message", at + ["actual", "message"], "Unknown failure")
                mutate("exception-class", at + ["exception_type"], "builtins.Exception")
                mutate("exception-args", at + ["exception_args"], ["Unknown failure"])
            mutate("input-bool", ["rows", 0, "input_bytes"], True)
            mutate("return-float", ["rows", 0, "return_bytes"], 192.0)
    if any(name == "ethereum" or name.startswith(("ethereum.", "ethereum_types")) for name in sys.modules):
        raise RuntimeError("local reader imported original source")
    print(f"PASS deposit parser: {count} controls; original imports/calls 0")


if __name__ == "__main__":
    main()
