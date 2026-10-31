# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Complete request/digest parser controls in normal and optimized Python.

Synthetic source rows test admission only; actual original-source comparisons and
packet authentication are separate work-item gates.
"""
import copy
import importlib.util
import json
from pathlib import Path

PATH = Path(__file__).resolve().parents[1] / "STFSpec/Conformance/Block/requests_hash_differential.py"
spec = importlib.util.spec_from_file_location("requests_hash_reader", PATH)
reader = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reader)


def encode(frame):
    return ("\n".join(json.dumps(x, separators=(",", ":")) for x in frame) + "\n").encode()


def main():
    cases = reader.catalog()
    rows = [{"id": x["id"], "requests_hex": x["requests_hex"], "actual_hex": x["expected_hex"]}
            for x in cases]
    target = [{"schema": reader.SCHEMA, "count": reader.COUNT}, *rows,
              {"end": True, "count": reader.COUNT}]
    source_rows = [{**x, "actual_hex": x["expected_hex"], "input_type": "builtins.list",
                    "request_types": ["builtins.bytes"] * len(x["requests_hex"]),
                    "request_bytes": [len(text) // 2 for text in x["requests_hex"]],
                    "return_type": "builtins.bytes", "return_bytes": 32} for x in cases]
    source = {"head": reader.PIN, "status": "all 298 source cases passed",
              "case_file_before_sha256": reader.CATALOG_SHA256,
              "case_file_after_sha256": reader.CATALOG_SHA256,
              "runtime": {"isolated": 1, "dont_write_bytecode": True, "optimize": 0,
                          "cache_prefix_empty_at_start_and_end": True},
              "function": {"module": "ethereum.forks.amsterdam.requests",
                           "qualname": "compute_requests_hash", "firstlineno": 307},
              "rows": source_rows}
    count = 0

    def check(mode, name, value, valid=False, raw=False):
        nonlocal count
        data = value if raw else encode(value) if mode == "target" else json.dumps(value).encode()
        parser = reader.parse_target if mode == "target" else lambda data: reader.parse_source(data, 0)
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
    optimized = copy.deepcopy(source)
    optimized["runtime"]["optimize"] = 1
    reader.parse_source(json.dumps(optimized).encode(), 1)
    count += 1
    for mode, base in (("target", target), ("source", source)):
        for name, data in (("empty", b""), ("truncated", b'{"schema":'),
                           ("oversize", b" " * (reader.MAX_BYTES + 1)), ("garbage", b"nope"),
                           ("nonfinite", b'{"value":NaN}'), ("duplicate-key", b'{"a":1,"a":1}'),
                           ("not-object", b"null"), ("invalid-utf8", b"\xff")):
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

        prefix = [5] if mode == "target" else ["rows", 4]  # one abc request
        empty_prefix = [1] if mode == "target" else ["rows", 0]
        for field in ("id", "requests_hex", "actual_hex"):
            mutate("missing-" + field, prefix + [field], delete=True)
        mutate("extra-row-key", prefix + ["extra"], 0)
        for value in (None, True, 1, 1.0, [], {}):
            mutate("wrong-id-type", prefix + ["id"], value)
            mutate("wrong-digest-type", prefix + ["actual_hex"], value)
        for value in (None, True, 1, 1.0, "616263", {}):
            mutate("wrong-requests-type", prefix + ["requests_hex"], value)
        for value in (None, True, 1, 1.0, [], {}):
            mutate("wrong-request-type", prefix + ["requests_hex", 0], value)
        for value in ("", "0", "gg", "AB", " 61", "61 ", "0x61", "６１", "61\n"):
            mutate("malformed-request-hex", prefix + ["requests_hex", 0], value)
        for value in ("", "00", "0" * 63, "0" * 65, "gg" * 32, "AA" * 32,
                      "0x" + "00" * 32, "00" * 32 + "\n"):
            mutate("malformed-digest", prefix + ["actual_hex"], value)
        actual = rows[4]["actual_hex"]
        for i in range(32):
            byte = int(actual[2 * i:2 * i + 2], 16) ^ 1
            mutate("digest-byte-" + str(i), prefix + ["actual_hex"],
                   actual[:2 * i] + f"{byte:02x}" + actual[2 * i + 2:])
        for i in range(3):
            text = "616263"
            mutate("request-byte-" + str(i), prefix + ["requests_hex", 0],
                   text[:2 * i] + "00" + text[2 * i + 2:])
        mutate("short-request", prefix + ["requests_hex", 0], "6162")
        mutate("long-request", prefix + ["requests_hex", 0], "61626300")
        mutate("missing-request", prefix + ["requests_hex"], [])
        mutate("extra-request", prefix + ["requests_hex"], ["616263", ""])
        mutate("empty-list-vs-empty-request", empty_prefix + ["requests_hex"], [""])
        order_prefix = [6] if mode == "target" else ["rows", 5]
        mutate("request-order", order_prefix + ["requests_hex"], ["616263", ""])
        mutate("missing-empty-request", order_prefix + ["requests_hex"], ["616263"])
        duplicate_prefix = [9] if mode == "target" else ["rows", 8]
        mutate("deduplicated-request", duplicate_prefix + ["requests_hex"], ["616263"])
        if mode == "target":
            for position in (0, -1):
                for value in (True, False, 298.0, "298", None, -1, 297, 299):
                    mutate("bad-frame-count", [position, "count"], value)
            for value in (1, 1.0, "true", False, None):
                mutate("bad-end", [-1, "end"], value)
            mutate("wrong-schema", [0, "schema"], "wrong")
            mutate("extra-header-key", [0, "extra"], 0)
            mutate("extra-footer-key", [-1, "extra"], 0)
            for value in (target[:-1], target[1:], target[:4] + target[5:],
                          target[:-1] + [target[2], target[-1]],
                          target[:2] + [target[1]] + target[3:],
                          target[:1] + [target[2], target[1]] + target[3:]):
                check(mode, "frame/row-count/order", value)
            for data in (b"\n" + encode(target), encode(target) + b"\n",
                         encode(target) + b"garbage\n"):
                check(mode, "extra-frame-lines", data, raw=True)
        else:
            for field in ("head", "status", "case_file_before_sha256", "case_file_after_sha256"):
                mutate("wrong-" + field, [field], "wrong")
            for field in ("runtime", "function", "rows"):
                mutate("missing-" + field, [field], delete=True)
                mutate("wrong-" + field + "-type", [field], None)
            for value in (True, 0.0, "0", None, -1, 1, 2):
                mutate("wrong-source-mode", ["runtime", "optimize"], value)
            for value in (True, 1.0, "1", 0, None):
                mutate("wrong-isolated", ["runtime", "isolated"], value)
            for field in ("dont_write_bytecode", "cache_prefix_empty_at_start_and_end"):
                for value in (1, "true", False, None):
                    mutate("wrong-source-boolean", ["runtime", field], value)
            mutate("wrong-function", ["function", "qualname"], "other")
            mutate("wrong-module", ["function", "module"], "other")
            for value in (True, 307.0, "307", None, 306):
                mutate("wrong-line", ["function", "firstlineno"], value)
            for field in ("input_type", "return_type"):
                mutate("wrong-source-type", prefix + [field], "builtins.str")
            for field in ("return_bytes",):
                for value in (True, 32.0, "32", None, 31, 33):
                    mutate("wrong-source-size", prefix + [field], value)
            for value in (True, 3.0, "3", None, 2, 4):
                mutate("wrong-request-size", prefix + ["request_bytes", 0], value)
            for field in ("request_bytes", "request_types", "inner_expected_hex"):
                for value in (None, True, {}, [], [0, 0]):
                    mutate("wrong-source-list", prefix + [field], value)
            mutate("wrong-request-type", prefix + ["request_types", 0], "builtins.bytearray")
            mutate("wrong-inner", prefix + ["inner_expected_hex", 0], "00" * 32)
            mutate("wrong-outer", prefix + ["outer_input_hex"], "00" * 32)
            mutate("wrong-expected", prefix + ["expected_hex"], "00" * 32)
            mutate("wrong-coverage", prefix + ["coverage"], "other")
            for value in (source_rows[:-1], source_rows + [source_rows[0]],
                          [source_rows[1], source_rows[0]] + source_rows[2:],
                          source_rows[:1] + [source_rows[0]] + source_rows[2:]):
                mutate("source-row-count/order", ["rows"], value)
    print(f"PASS requests hash parser: {count} complete positive/negative controls")


if __name__ == "__main__":
    main()
