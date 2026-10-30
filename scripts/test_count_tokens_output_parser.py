# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Strict-reader negative controls, effective with and without Python optimization."""
import copy
import importlib.util
import json
from pathlib import Path
import sys

PATH = Path(__file__).resolve().parents[1] / "STFSpec/Conformance/Block/count_tokens_differential.py"
spec = importlib.util.spec_from_file_location("count_tokens_reader", PATH)
reader = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reader)


def encode(frame):
    return ("\n".join(json.dumps(x, separators=(",", ":")) for x in frame) + "\n").encode()


def main():
    rows = [{"id": x["id"], "hex": x["hex"], "actual": x["expected"]} for x in reader.catalog()]
    target = [{"schema": reader.SCHEMA, "count": 266}, *rows, {"end": True, "count": 266}]
    source = {"schema": reader.SCHEMA, "metadata": {
        "head": reader.PIN, "python": "fixture", "executable": "/fixture/python", "isolated": True,
        "dont_write_bytecode": True, "optimize": 0, "openssl": "fixture", "ethereum_types": "0.4.1",
        "function_file": "/fixture/transactions.py", "function_firstlineno": 804,
        "files": [{"path": "/fixture/transactions.py", "sha256": "0" * 64}]}, "rows": rows}
    fixtures = []

    def add(mode, name, value, valid=False, raw=False):
        data = value if raw else (encode(value) if mode == "target" else json.dumps(value).encode())
        fixtures.append((mode, name, data, valid))

    add("target", "valid", target, True)
    add("target", "valid-no-final-newline", encode(target)[:-1], True, True)
    add("source", "valid", source, True)
    for mode, base in (("target", target), ("source", source)):
        for name, data in (("empty", b""), ("truncated", b'{"schema":'), ("oversize", b" " * (4194304 + 1)),
                           ("garbage", b"nope"), ("nonfinite", b'{"value":NaN}'),
                           ("duplicate-key", b'{"schema":1,"schema":1}')):
            add(mode, name, data, raw=True)

        def mutate(name, path, value=None, delete=False):
            changed = copy.deepcopy(base)
            obj = changed
            for key in path[:-1]:
                obj = obj[key]
            if delete:
                del obj[path[-1]]
            else:
                obj[path[-1]] = value
            add(mode, name, changed)

        prefix = [1] if mode == "target" else ["rows", 0]
        for field in ("id", "hex", "actual"):
            mutate("missing-" + field, prefix + [field], delete=True)
        mutate("extra-key", prefix + ["extra"], 0)
        for bad in (True, False, 0.0, "0", -1, None, [], {}):
            mutate("result-type-" + repr(bad), prefix + ["actual"], bad)
        mutate("unexpected-result", prefix + ["actual"], 1)
        for bad in ("0", "0x00", "gg", "00 ", "AA", "٠٠", True, 0, None):
            mutate("hex-" + repr(bad), prefix + ["hex"], bad)
        for bad in (True, 0, None, "other"):
            mutate("id-" + repr(bad), prefix + ["id"], bad)
        collection = base[1:-1] if mode == "target" else base["rows"]
        for name, altered in (("missing-row", collection[:-1]), ("extra-row", collection + [collection[-1]]),
                              ("duplicate-row", [collection[0], *collection[:-1]]),
                              ("swapped-row", [collection[1], collection[0], *collection[2:]])):
            changed = copy.deepcopy(base)
            if mode == "target":
                changed = [changed[0], *altered, changed[-1]]
            else:
                changed["rows"] = altered
            add(mode, name, changed)
        # These exact values compare equal to small JSON integers in Python.
        one = 11 if mode == "target" else 10
        path = [one] if mode == "target" else ["rows", one]
        mutate("bool-as-one", path + ["actual"], True)
        mutate("float-as-one", path + ["actual"], 1.0)
        if mode == "target":
            for at, key in ((0, "count"), (-1, "count")):
                for bad in (True, 266.0, "266", 265, 267):
                    mutate("count-" + str(at) + repr(bad), [at, key], bad)
            mutate("end-int", [-1, "end"], 1)
            mutate("header-extra", [0, "extra"], 0)
            mutate("footer-extra", [-1, "extra"], 0)
            mutate("bad-schema", [0, "schema"], "other")
            add(mode, "after-footer", encode(base) + b"{}\n", raw=True)
            add(mode, "blank-line", encode(base) + b"\n", raw=True)
            add(mode, "duplicate-result-key", encode(base).replace(b'"actual":0', b'"actual":0,"actual":0', 1), raw=True)
        else:
            for field, bad in (("head", "bad"), ("ethereum_types", "0"), ("isolated", 1),
                               ("dont_write_bytecode", 1), ("optimize", False), ("optimize", 0.0),
                               ("optimize", 2), ("function_firstlineno", 804.0), ("files", []),
                               ("python", None)):
                mutate("metadata-" + field + repr(bad), ["metadata", field], bad)
            mutate("source-extra", ["extra"], 0)
            mutate("source-missing", ["metadata"], delete=True)
            mutate("file-hash", ["metadata", "files", 0, "sha256"], "bad")
    for mode, name, data, valid in fixtures:
        parser = reader.parse_target if mode == "target" else reader.parse_source
        try:
            parser(data)
        except reader.AdmissionError:
            if valid:
                raise RuntimeError("rejected valid fixture " + mode + ":" + name)
        else:
            if not valid:
                raise RuntimeError("accepted invalid fixture " + mode + ":" + name)
    if any(name == "ethereum" or name.startswith(("ethereum.", "ethereum_types")) for name in sys.modules):
        raise RuntimeError("local reader imported original source")
    print(f"PASS calldata-token parser: {len(fixtures)} controls; original imports/calls 0")


if __name__ == "__main__":
    main()
