# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Strict complete finite observations; original source execution is opt-in.

The catalog predates the implementation. Source mode calls the original pinned
function using an explicitly supplied locked interpreter. Recorded module hashes
identify files used in that process, not a universal runtime authentication proof.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

PIN = "e1a316a06fc3d3e0a5da36fdc78580811e9d8a36"
SCHEMA = "calldata-tokens-v1"
CATALOG_SHA256 = "356620fcec4a2a6ed80b77c0e2bac0f02f523fc077486255ec57ab6cf028ee2c"
CATALOG = Path(__file__).with_name("count_tokens_cases.json")


class AdmissionError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise AdmissionError(message)


def object_pairs(pairs):
    value = {}
    for key, item in pairs:
        require(key not in value, "duplicate JSON key")
        value[key] = item
    return value


def decode(data):
    require(len(data) <= 4 * 1024 * 1024, "oversize output")
    try:
        return json.loads(data, object_pairs_hook=object_pairs,
                          parse_constant=lambda _: (_ for _ in ()).throw(AdmissionError("nonfinite JSON")))
    except (ValueError, UnicodeError) as error:
        raise AdmissionError(str(error)) from error


def keys(value, expected):
    require(type(value) is dict and set(value) == set(expected), "unexpected object keys")


def natural(value):
    require(type(value) is int and value >= 0, "expected JSON natural, excluding bool")


def catalog():
    data = CATALOG.read_bytes()
    require(hashlib.sha256(data).hexdigest() == CATALOG_SHA256, "catalog identity")
    rows = decode(data)
    require(type(rows) is list and len(rows) == 266, "catalog count")
    seen = set()
    for row in rows:
        keys(row, ("id", "hex", "expected"))
        require(type(row["id"]) is str and row["id"] not in seen, "catalog id")
        seen.add(row["id"])
        require(type(row["hex"]) is str and re.fullmatch(r"(?:[0-9a-f]{2})*", row["hex"]) is not None,
                "catalog hex")
        natural(row["expected"])
    return rows


def check_rows(rows):
    expected = catalog()
    require(type(rows) is list and len(rows) == len(expected), "row count")
    for row, case in zip(rows, expected):
        keys(row, ("id", "hex", "actual"))
        require(type(row["id"]) is str and row["id"] == case["id"], "row id/order")
        require(type(row["hex"]) is str and row["hex"] == case["hex"], "complete input hex")
        natural(row["actual"])
        require(row["actual"] == case["expected"], "complete result")
    return rows


def parse_target(data):
    require(len(data) <= 4 * 1024 * 1024, "oversize output")
    lines = data.splitlines()
    require(len(lines) == 268, "frame length")
    frame = [decode(line) for line in lines]
    keys(frame[0], ("schema", "count"))
    require(frame[0]["schema"] == SCHEMA, "schema")
    natural(frame[0]["count"])
    require(frame[0]["count"] == 266, "header count")
    keys(frame[-1], ("end", "count"))
    require(frame[-1]["end"] is True, "footer end")
    natural(frame[-1]["count"])
    require(frame[-1]["count"] == 266, "footer count")
    return check_rows(frame[1:-1])


def parse_source(data):
    value = decode(data)
    keys(value, ("schema", "metadata", "rows"))
    require(value["schema"] == SCHEMA, "source schema")
    meta = value["metadata"]
    keys(meta, ("head", "python", "executable", "isolated", "dont_write_bytecode", "optimize",
                "openssl", "ethereum_types", "function_file", "function_firstlineno", "files"))
    require(meta["head"] == PIN and meta["ethereum_types"] == "0.4.1", "source pin/types")
    require(meta["isolated"] is True and meta["dont_write_bytecode"] is True, "source isolation")
    natural(meta["optimize"])
    require(meta["optimize"] in (0, 1), "source optimization")
    natural(meta["function_firstlineno"])
    require(meta["function_firstlineno"] == 804, "source function line")
    for key in ("python", "executable", "openssl", "function_file"):
        require(type(meta[key]) is str and bool(meta[key]), "source provenance string")
    require(type(meta["files"]) is list and len(meta["files"]) > 0, "source file provenance")
    seen = set()
    for file in meta["files"]:
        keys(file, ("path", "sha256"))
        require(type(file["path"]) is str and file["path"] not in seen, "source file path")
        seen.add(file["path"])
        require(type(file["sha256"]) is str and re.fullmatch(r"[0-9a-f]{64}", file["sha256"]) is not None,
                "source file hash")
    return check_rows(value["rows"])


def source_worker(root):
    import importlib.metadata
    import inspect
    import ssl
    root = root.resolve()
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    require(head == PIN, "source HEAD")
    require(subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"], cwd=root) == b"",
            "modified tracked source")
    require(sys.flags.isolated == 1 and sys.dont_write_bytecode, "use -I -B")
    sys.path.insert(0, str(root / "src"))
    from ethereum.forks.amsterdam import transactions
    from ethereum_types.numeric import Uint
    fn = transactions.count_tokens_in_data
    source_file = Path(inspect.getsourcefile(fn)).resolve()
    require(source_file == root / "src/ethereum/forks/amsterdam/transactions.py", "function path")
    require(fn.__globals__["Uint"] is Uint and fn.__code__.co_firstlineno == 804, "function binding")
    require(importlib.metadata.version("ethereum-types") == "0.4.1", "locked types")
    rows = []
    for case in catalog():
        data = bytes.fromhex(case["hex"])
        value = fn(data)
        require(type(value) is Uint, "source result type")
        rows.append({"id": case["id"], "hex": data.hex(), "actual": int(value)})
    check_rows(rows)
    paths = {root / "uv.lock", source_file, Path(sys.executable).resolve()}
    for module in tuple(sys.modules.values()):
        path = getattr(module, "__file__", None)
        if path and Path(path).is_file():
            paths.add(Path(path).resolve())
    files = [{"path": str(p), "sha256": hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(paths)]
    metadata = {"head": head, "python": sys.version, "executable": sys.executable,
                "isolated": bool(sys.flags.isolated), "dont_write_bytecode": sys.dont_write_bytecode,
                "optimize": sys.flags.optimize, "openssl": ssl.OPENSSL_VERSION, "ethereum_types": "0.4.1",
                "function_file": str(source_file), "function_firstlineno": fn.__code__.co_firstlineno,
                "files": files}
    print(json.dumps({"schema": SCHEMA, "metadata": metadata, "rows": rows}, indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-target", type=Path)
    parser.add_argument("--check-source", type=Path)
    parser.add_argument("--source-worker", type=Path)
    args = parser.parse_args()
    if args.source_worker:
        require(not args.check_target and not args.check_source, "exclusive worker mode")
        source_worker(args.source_worker)
        return
    require(args.check_target is not None, "--check-target required")
    target = parse_target(args.check_target.read_bytes())
    if args.check_source:
        source = parse_source(args.check_source.read_bytes())
        require(target == source, "target/source complete rows")
    print("PASS calldata tokens: 266 complete finite rows" + (" coupled to original source" if args.check_source else " against frozen catalog"))


if __name__ == "__main__":
    main()
