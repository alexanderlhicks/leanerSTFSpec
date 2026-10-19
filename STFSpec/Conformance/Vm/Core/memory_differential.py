#!/usr/bin/env python3
"""Complete Memory literals, strict frames and a source-independent Lean producer.

The emitted main must run with lake env lean --run; see EthVmCore section 3.
Optional --source-frames compares caller-supplied evidence; it authenticates nothing.
Default checks compare 33 target/literal frames and no external source frames.
"""

# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys

PIN = "e1a316a06fc3d3e0a5da36fdc78580811e9d8a36"
CONTROL_SHA256 = "96fb056ccac988b2729a041575eb0f3f05149f4e235a772736baba7d36b7e644"
LEAN_ONLY = {"31-lean-only-empty-read-2p4096", "32-lean-only-empty-write-2p4096"}
ROW_FIELDS = {
    "id",
    "op",
    "before",
    "input",
    "after",
    "reads",
    "savedMemories",
    "savedBytes",
    "returnClass",
}


class FrameError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise FrameError(message)


def pairs(items):
    result = {}
    for key, value in items:
        require(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def bad_constant(value):
    raise FrameError("non-JSON numeric constant: " + value)


def load(text):
    return json.loads(text, object_pairs_hook=pairs, parse_constant=bad_constant)


def whole_hex(value):
    return (
        type(value) is str and len(value) % 2 == 0 and all(c in "0123456789abcdef" for c in value)
    )


def decimal(value):
    return (
        type(value) is str
        and bool(value)
        and value.isascii()
        and value.isdecimal()
        and (value == "0" or not value.startswith("0"))
    )


def byte_object(value):
    require(type(value) is dict and set(value) == {"size", "hex"}, "byte-object keys")
    require(type(value["size"]) is int and value["size"] >= 0, "byte-object size")
    require(
        whole_hex(value["hex"]) and len(value["hex"]) == 2 * value["size"],
        "byte-object full hex/size",
    )


def catalog(path=None):
    raw = (
        path.read_bytes() if path is not None else (json.dumps(CATALOG, indent=2) + "\n").encode()
    )
    require(hashlib.sha256(raw).hexdigest() == CONTROL_SHA256, "changed frozen catalog")
    obj = load(raw.decode("utf-8"))
    require(
        type(obj) is dict and set(obj) == {"status", "version", "frameCount", "models", "frames"},
        "catalog keys",
    )
    require(
        type(obj["version"]) is int
        and obj["version"] == 1
        and type(obj["frameCount"]) is int
        and obj["frameCount"] == 33,
        "catalog version/count",
    )
    require(type(obj["models"]) is dict and len(obj["models"]) == 17, "literal models")
    for value in obj["models"].values():
        byte_object(value)
    require(type(obj["frames"]) is list and len(obj["frames"]) == 33, "literal frames")
    ids = set()
    for row in obj["frames"]:
        require(type(row) is dict and set(row) == ROW_FIELDS, "literal frame keys")
        require(type(row["id"]) is str and row["id"] not in ids, "literal id")
        ids.add(row["id"])
        require(row["op"] in {"observe", "expand", "read", "write"}, "literal operation")
        require(row["before"] in obj["models"] and row["after"] in obj["models"], "memory refs")
        require(type(row["input"]) is dict, "input object")
        for key, value in row["input"].items():
            if key == "payload":
                require(value in obj["models"], "payload ref")
            elif key == "startExpression":
                require(row["id"] in LEAN_ONLY and value == "2^4096", "Lean-only expression")
            else:
                require(key in {"start", "length", "increment"} and decimal(value), "Nat literal")
        for key in ["reads", "savedMemories", "savedBytes"]:
            require(type(row[key]) is dict, "named observation object")
            require(
                all(
                    type(name) is str and value in obj["models"]
                    for name, value in row[key].items()
                ),
                "named observation reference",
            )
    require(LEAN_ONLY <= ids, "Lean-only rows absent")
    return obj


def expanded_literals(obj, source=False):
    """Expand static references only; never simulate Memory or EELS operations."""
    result = []
    for literal in obj["frames"]:
        if source and literal["id"] in LEAN_ONLY:
            continue
        row = copy.deepcopy(literal)
        for key in ["before", "after"]:
            row[key] = copy.deepcopy(obj["models"][row[key]])
        if "payload" in row["input"]:
            row["input"]["payload"] = copy.deepcopy(obj["models"][row["input"]["payload"]])
        for key in ["reads", "savedMemories", "savedBytes"]:
            row[key] = {name: copy.deepcopy(obj["models"][ref]) for name, ref in row[key].items()}
        result.append(row)
    return result


def marked(rows):
    return (
        [{"kind": "begin", "version": 1, "count": len(rows)}]
        + rows
        + [{"kind": "end", "version": 1, "count": len(rows)}]
    )


def stream(rows):
    return "".join(json.dumps(row, separators=(",", ":")) + "\n" for row in rows)


def exact(actual, expected, path="frame"):
    require(type(actual) is type(expected), "exact type: " + path)
    if type(expected) is dict:
        require(set(actual) == set(expected), "exact keys: " + path)
        if set(expected) == {"size", "hex"}:
            byte_object(actual)
        for key in expected:
            exact(actual[key], expected[key], path + "." + key)
    elif type(expected) is list:
        require(len(actual) == len(expected), "exact list size: " + path)
        for index, value in enumerate(expected):
            exact(actual[index], value, path + "." + str(index))
    else:
        require(actual == expected, "complete value differs: " + path)


def parse_frames(text, expected):
    require(type(text) is str and text.endswith("\n"), "missing final newline")
    lines = text.split("\n")
    require(
        lines[-1] == "" and len(lines) == len(expected) + 3, "whole-stream count/trailing data"
    )
    rows = [load(line) for line in lines[:-1]]
    exact(rows, marked(expected))
    return rows


def self_test(obj):
    expected = expanded_literals(obj)
    rows = marked(expected)
    good = stream(rows)
    parse_frames(good, expected)
    bad = [
        "",
        good[:-1],
        good[:-2],
        good + "\n",
        good + good,
        good + "{}\n",
        good.replace('"version":1', '"version":1,"version":1', 1),
        good.replace('"size":0', '"size":0,"size":0', 1),
        good.replace('"size":0', '"size":NaN', 1),
        good.replace('"size":0', '"size":Infinity', 1),
        good.replace('"size":0', '"size":-Infinity', 1),
    ]

    def mutate(index, path, value=None, remove=False):
        changed = copy.deepcopy(rows)
        node = changed[index]
        for key in path[:-1]:
            node = node[key]
        if remove:
            del node[path[-1]]
        else:
            node[path[-1]] = value
        bad.append(stream(changed))

    for index in [0, len(rows) - 1]:
        for field in ["version", "count"]:
            for value in [True, False, 1.0, -1, "1", None]:
                mutate(index, [field], value)
        mutate(index, ["extra"], 0)
        mutate(index, ["kind"], "wrong")
        mutate(index, ["kind"], remove=True)
    for field in ROW_FIELDS:
        mutate(1, [field], remove=True)
    mutate(1, ["extra"], 0)
    mutate(1, ["id"], rows[2]["id"])
    mutate(1, ["op"], "wrong")
    mutate(1, ["returnClass"], "bytes")
    for value in [True, False, 0.0, -1, "0", None]:
        mutate(1, ["before", "size"], value)
    for value in ["0", "gg", "AA", " 00", "0x00", [], False]:
        mutate(1, ["before", "hex"], value)
    mutate(1, ["before", "extra"], 0)
    mutate(1, ["before", "hex"], remove=True)
    for value in [True, 0, 0.0, "00", "-1", "1.0", "1e0", None]:
        mutate(3, ["input", "increment"], value)
        mutate(8, ["input", "start"], value)
    mutate(6, ["input", "payload", "size"], True)
    mutate(6, ["input", "payload", "hex"], "00")
    mutate(10, ["after", "hex"], rows[6]["after"]["hex"])
    mutate(10, ["savedMemories", "base", "size"], True)
    mutate(10, ["savedMemories", "base", "extra"], 0)
    mutate(10, ["savedBytes", "window", "hex"], remove=True)
    for index, path in [
        (10, ["after", "hex"]),
        (17, ["savedMemories", "base", "hex"]),
        (17, ["savedBytes", "window", "hex"]),
        (11, ["reads", "result", "hex"]),
    ]:
        node = rows[index]
        for key in path:
            node = node[key]
        middle = (len(node) // 4) * 2
        replacement = "ff" if node[middle : middle + 2] != "ff" else "00"
        mutate(index, path, node[:middle] + replacement + node[middle + 2 :])
    changed = copy.deepcopy(rows)
    changed[1], changed[2] = changed[2], changed[1]
    bad.extend(
        [
            stream(changed),
            stream(rows[:1] + rows[2:]),
            stream(rows[:1] + [rows[1]] + rows[1:]),
            good.replace("\n", "\nnoise\n", 1),
        ]
    )
    for index, text in enumerate(bad):
        try:
            parse_frames(text, expected)
        except (FrameError, json.JSONDecodeError, UnicodeError):
            pass
        else:
            raise FrameError("parser accepted adversary " + str(index))
    print(
        json.dumps(
            {
                "status": "strict parser controls passed",
                "rejected": len(bad),
                "optimize": sys.flags.optimize,
                "literal_cases": len(expected),
            }
        )
    )


CATALOG = {
    "status": "FROZEN EXPECTATIONS ONLY; NO TARGET RESULTS",
    "version": 1,
    "frameCount": 33,
    "models": {
        "E": {"size": 0, "hex": ""},
        "Z32": {
            "size": 32,
            "hex": "0000000000000000000000000000000000000000000000000000000000000000",
        },
        "Z64": {
            "size": 64,
            (
                'hex'
            ): (
                '000000000000000000000000000000000000000000000000000000000000'
                '000000000000000000000000000000000000000000000000000000000000'
                '00000000'
            ),
        },
        "B64": {
            "size": 64,
            (
                'hex'
            ): (
                '000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d'
                '1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b'
                '3c3d3e3f'
            ),
        },
        "H32": {
            "size": 32,
            "hex": "0080ff01007f55aa0080ff01007f55aa0080ff01007f55aa0080ff01007f55aa",
        },
        "P8": {"size": 8, "hex": "fe0080ff01007f55"},
        "S8": {"size": 8, "hex": "1c1d1e1f20212223"},
        "F4": {"size": 4, "hex": "0080ff00"},
        "C64": {
            "size": 64,
            (
                'hex'
            ): (
                '000102030405060708090a0b0c0d0e0f101112131415161718191a1bfe00'
                '80ff01007f552425262728292a2b2c2d2e2f303132333435363738393a3b'
                '3c3d3e3f'
            ),
        },
        "L64": {
            "size": 64,
            (
                'hex'
            ): (
                '000102030405060708090a0b0c0d0e0f101112131415161718191c1d1e1f'
                '2021222322232425262728292a2b2c2d2e2f303132333435363738393a3b'
                '3c3d3e3f'
            ),
        },
        "R64": {
            "size": 64,
            (
                'hex'
            ): (
                '000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d'
                '1c1d1e1f20212223262728292a2b2c2d2e2f303132333435363738393a3b'
                '3c3d3e3f'
            ),
        },
        "END64": {
            "size": 64,
            (
                'hex'
            ): (
                '000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d'
                '1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b'
                '0080ff00'
            ),
        },
        "C96": {
            "size": 96,
            (
                'hex'
            ): (
                '000102030405060708090a0b0c0d0e0f101112131415161718191a1bfe00'
                '80ff01007f552425262728292a2b2c2d2e2f303132333435363738393a3b'
                '3c3d3e3f0000000000000000000000000000000000000000000000000000'
                '000000000000'
            ),
        },
        "PRE28": {"size": 28, "hex": "000102030405060708090a0b0c0d0e0f101112131415161718191a1b"},
        "SUF28": {"size": 28, "hex": "2425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f"},
        "READ4": {"size": 4, "hex": "18191a1b"},
        "READ4B": {"size": 4, "hex": "24252627"},
    },
    "frames": [
        {
            "id": "01-empty",
            "op": "observe",
            "before": "E",
            "input": {},
            "after": "E",
            "reads": {},
            "savedMemories": {},
            "savedBytes": {},
            "returnClass": "observation",
        },
        {
            "id": "02-empty-expand-zero",
            "op": "expand",
            "before": "E",
            "input": {"increment": "0"},
            "after": "E",
            "reads": {},
            "savedMemories": {"old": "E"},
            "savedBytes": {},
            "returnClass": "NoneType",
        },
        {
            "id": "03-expand32",
            "op": "expand",
            "before": "E",
            "input": {"increment": "32"},
            "after": "Z32",
            "reads": {},
            "savedMemories": {"old": "E"},
            "savedBytes": {},
            "returnClass": "NoneType",
        },
        {
            "id": "04-expand-zero32",
            "op": "expand",
            "before": "Z32",
            "input": {"increment": "0"},
            "after": "Z32",
            "reads": {},
            "savedMemories": {"old": "Z32"},
            "savedBytes": {},
            "returnClass": "NoneType",
        },
        {
            "id": "05-expand32-again",
            "op": "expand",
            "before": "Z32",
            "input": {"increment": "32"},
            "after": "Z64",
            "reads": {},
            "savedMemories": {"old": "Z32"},
            "savedBytes": {},
            "returnClass": "NoneType",
        },
        {
            "id": "06-full-write",
            "op": "write",
            "before": "Z64",
            "input": {"start": "0", "payload": "B64"},
            "after": "B64",
            "reads": {},
            "savedMemories": {"old": "Z64"},
            "savedBytes": {},
            "returnClass": "NoneType",
        },
        {
            "id": "07-high-interior-zero-full-write",
            "op": "write",
            "before": "Z32",
            "input": {"start": "0", "payload": "H32"},
            "after": "H32",
            "reads": {},
            "savedMemories": {"old": "Z32"},
            "savedBytes": {},
            "returnClass": "NoneType",
        },
        {
            "id": "08-read-all",
            "op": "read",
            "before": "B64",
            "input": {"start": "0", "length": "64"},
            "after": "B64",
            "reads": {"result": "B64"},
            "savedMemories": {},
            "savedBytes": {},
            "returnClass": "bytes",
        },
        {
            "id": "09-save-cross-window",
            "op": "read",
            "before": "B64",
            "input": {"start": "28", "length": "8"},
            "after": "B64",
            "reads": {"result": "S8"},
            "savedMemories": {"base": "B64"},
            "savedBytes": {"window": "S8"},
            "returnClass": "bytes",
        },
        {
            "id": "10-cross-word-write",
            "op": "write",
            "before": "B64",
            "input": {"start": "28", "payload": "P8"},
            "after": "C64",
            "reads": {},
            "savedMemories": {"base": "B64"},
            "savedBytes": {"window": "S8"},
            "returnClass": "NoneType",
        },
        {
            "id": "11-cross-word-read",
            "op": "read",
            "before": "C64",
            "input": {"start": "28", "length": "8"},
            "after": "C64",
            "reads": {"result": "P8"},
            "savedMemories": {"base": "B64"},
            "savedBytes": {"window": "S8"},
            "returnClass": "bytes",
        },
        {
            "id": "12-whole-prefix",
            "op": "read",
            "before": "C64",
            "input": {"start": "0", "length": "28"},
            "after": "C64",
            "reads": {"result": "PRE28"},
            "savedMemories": {"base": "B64"},
            "savedBytes": {"window": "S8"},
            "returnClass": "bytes",
        },
        {
            "id": "13-whole-suffix",
            "op": "read",
            "before": "C64",
            "input": {"start": "36", "length": "28"},
            "after": "C64",
            "reads": {"result": "SUF28"},
            "savedMemories": {"base": "B64"},
            "savedBytes": {"window": "S8"},
            "returnClass": "bytes",
        },
        {
            "id": "14-left-overlap",
            "op": "write",
            "before": "B64",
            "input": {"start": "26", "payload": "S8"},
            "after": "L64",
            "reads": {},
            "savedMemories": {"base": "B64"},
            "savedBytes": {"window": "S8"},
            "returnClass": "NoneType",
        },
        {
            "id": "15-right-overlap",
            "op": "write",
            "before": "B64",
            "input": {"start": "30", "payload": "S8"},
            "after": "R64",
            "reads": {},
            "savedMemories": {"base": "B64"},
            "savedBytes": {"window": "S8"},
            "returnClass": "NoneType",
        },
        {
            "id": "16-self-copy",
            "op": "write",
            "before": "B64",
            "input": {"start": "28", "payload": "S8"},
            "after": "B64",
            "reads": {},
            "savedMemories": {"base": "B64"},
            "savedBytes": {"window": "S8"},
            "returnClass": "NoneType",
        },
        {
            "id": "17-retained-original-and-read",
            "op": "observe",
            "before": "C64",
            "input": {},
            "after": "C64",
            "reads": {},
            "savedMemories": {"base": "B64"},
            "savedBytes": {"window": "S8"},
            "returnClass": "observation",
        },
        {
            "id": "18-expand-written32",
            "op": "expand",
            "before": "C64",
            "input": {"increment": "32"},
            "after": "C96",
            "reads": {},
            "savedMemories": {"old": "C64", "base": "B64"},
            "savedBytes": {"window": "S8"},
            "returnClass": "NoneType",
        },
        {
            "id": "19-exact-end-write",
            "op": "write",
            "before": "B64",
            "input": {"start": "60", "payload": "F4"},
            "after": "END64",
            "reads": {},
            "savedMemories": {"base": "B64"},
            "savedBytes": {"window": "S8"},
            "returnClass": "NoneType",
        },
        {
            "id": "20-exact-end-read",
            "op": "read",
            "before": "END64",
            "input": {"start": "60", "length": "4"},
            "after": "END64",
            "reads": {"result": "F4"},
            "savedMemories": {"base": "B64"},
            "savedBytes": {"window": "S8"},
            "returnClass": "bytes",
        },
        {
            "id": "21-empty-end-read",
            "op": "read",
            "before": "B64",
            "input": {"start": "64", "length": "0"},
            "after": "B64",
            "reads": {"result": "E"},
            "savedMemories": {},
            "savedBytes": {},
            "returnClass": "bytes",
        },
        {
            "id": "22-empty-read-inside-write",
            "op": "read",
            "before": "C64",
            "input": {"start": "30", "length": "0"},
            "after": "C64",
            "reads": {"result": "E"},
            "savedMemories": {"base": "B64"},
            "savedBytes": {"window": "S8"},
            "returnClass": "bytes",
        },
        {
            "id": "23-empty-write-inside-read",
            "op": "write",
            "before": "B64",
            "input": {"start": "30", "payload": "E"},
            "after": "B64",
            "reads": {"preserved-window": "S8"},
            "savedMemories": {"base": "B64"},
            "savedBytes": {"window": "S8"},
            "returnClass": "NoneType",
        },
        {
            "id": "24-adjacent-prefix",
            "op": "read",
            "before": "C64",
            "input": {"start": "28", "length": "0"},
            "after": "C64",
            "reads": {"result": "E"},
            "savedMemories": {},
            "savedBytes": {},
            "returnClass": "bytes",
        },
        {
            "id": "25-adjacent-left",
            "op": "read",
            "before": "C64",
            "input": {"start": "24", "length": "4"},
            "after": "C64",
            "reads": {"result": "READ4"},
            "savedMemories": {},
            "savedBytes": {},
            "returnClass": "bytes",
        },
        {
            "id": "26-adjacent-right",
            "op": "read",
            "before": "C64",
            "input": {"start": "36", "length": "4"},
            "after": "C64",
            "reads": {"result": "READ4B"},
            "savedMemories": {},
            "savedBytes": {},
            "returnClass": "bytes",
        },
        {
            "id": "27-empty-read-2p64",
            "op": "read",
            "before": "B64",
            "input": {"start": "18446744073709551616", "length": "0"},
            "after": "B64",
            "reads": {"result": "E"},
            "savedMemories": {"base": "B64"},
            "savedBytes": {"window": "S8"},
            "returnClass": "bytes",
        },
        {
            "id": "28-empty-write-2p64",
            "op": "write",
            "before": "B64",
            "input": {"start": "18446744073709551616", "payload": "E"},
            "after": "B64",
            "reads": {},
            "savedMemories": {"base": "B64"},
            "savedBytes": {"window": "S8"},
            "returnClass": "NoneType",
        },
        {
            "id": "29-empty-read-u256max",
            "op": "read",
            "before": "B64",
            "input": {
                (
                    'start'
                ): (
                    '115792089237316195423570985008687907853269984665640564039457'
                    '584007913129639935'
                ),
                "length": "0",
            },
            "after": "B64",
            "reads": {"result": "E"},
            "savedMemories": {"base": "B64"},
            "savedBytes": {"window": "S8"},
            "returnClass": "bytes",
        },
        {
            "id": "30-empty-write-u256max",
            "op": "write",
            "before": "B64",
            "input": {
                (
                    'start'
                ): (
                    '115792089237316195423570985008687907853269984665640564039457'
                    '584007913129639935'
                ),
                "payload": "E",
            },
            "after": "B64",
            "reads": {},
            "savedMemories": {"base": "B64"},
            "savedBytes": {"window": "S8"},
            "returnClass": "NoneType",
        },
        {
            "id": "31-lean-only-empty-read-2p4096",
            "op": "read",
            "before": "B64",
            "input": {"startExpression": "2^4096", "length": "0"},
            "after": "B64",
            "reads": {"result": "E"},
            "savedMemories": {"base": "B64"},
            "savedBytes": {"window": "S8"},
            "returnClass": "observation",
        },
        {
            "id": "32-lean-only-empty-write-2p4096",
            "op": "write",
            "before": "B64",
            "input": {"startExpression": "2^4096", "payload": "E"},
            "after": "B64",
            "reads": {},
            "savedMemories": {"base": "B64"},
            "savedBytes": {"window": "S8"},
            "returnClass": "observation",
        },
        {
            "id": "33-both-empty",
            "op": "write",
            "before": "E",
            "input": {"start": "18446744073709551616", "payload": "E"},
            "after": "E",
            "reads": {"empty-read-inside": "E"},
            "savedMemories": {"old": "E"},
            "savedBytes": {"empty": "E"},
            "returnClass": "NoneType",
        },
    ],
}

LEAN_PROGRAM = r"""/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Vm.Core
import Lean
/-!
# Complete Memory observations
Library `EthConformance`. Public construction and complete actual memories, immutable
reads and retained snapshots for thirty-three frozen controls.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/7.
-/
open STFSpec.Vm.Core STFSpec.Base Lean
private def byteHex (b : UInt8) : String :=
  let digit := fun n ↦ if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  String.ofList [digit (b.toNat / 16), digit (b.toNat % 16)]
private def fullBytes (size : Nat) (xs : List UInt8) : Json :=
  Json.mkObj [("size", toJson size), ("hex", toJson (String.join (xs.map byteHex)))]
private def memoryJson (m : Memory) : Json := fullBytes m.size m.toBytes
private def bytesJson (b : Bytes) : Json := fullBytes b.size b.toList
-- 01-empty
private def m01 : Memory := Memory.empty
-- 02-empty-expand-zero
private def m02 : Memory := m01.expand 0 (by decide)
-- 03-expand32
private def m03 : Memory := m01.expand 32 (by decide)
-- 04-expand-zero32
private def m04 : Memory := m03.expand 0 (by decide)
-- 05-expand32-again
private def m05 : Memory := m03.expand 32 (by decide)
-- 06-full-write
private def v06 : Bytes := Bytes.ofList [0 , 1 , 2 , 3 , 4 , 5 , 6 , 7 , 8 , 9 , 10 , 11 , 12 , 13
  , 14 , 15 , 16 , 17 , 18 , 19 , 20 , 21 , 22 , 23 , 24 , 25 , 26 , 27 , 28 , 29 , 30 , 31 , 32 ,
  33 , 34 , 35 , 36 , 37 , 38 , 39 , 40 , 41 , 42 , 43 , 44 , 45 , 46 , 47 , 48 , 49 , 50 , 51 , 52
  , 53 , 54 , 55 , 56 , 57 , 58 , 59 , 60 , 61 , 62 , 63]
private def m06 : Memory := m05.write 0 v06 (by right; decide)
-- 07-high-interior-zero-full-write
private def v07 : Bytes := Bytes.ofList [0 , 128 , 255 , 1 , 0 , 127 , 85 , 170 , 0 , 128 , 255 , 1
  , 0 , 127 , 85 , 170 , 0 , 128 , 255 , 1 , 0 , 127 , 85 , 170 , 0 , 128 , 255 , 1 , 0 , 127 , 85
  , 170]
private def m07 : Memory := m03.write 0 v07 (by right; decide)
-- 08-read-all
private def m08 : Memory := m06
private def r08 : Bytes := m08.readBytes 0 64 (by right; decide)
-- 09-save-cross-window
private def m09 : Memory := m06
private def r09 : Bytes := m09.readBytes 28 8 (by right; decide)
-- 10-cross-word-write
private def v10 : Bytes := Bytes.ofList [254, 0, 128, 255, 1, 0, 127, 85]
private def m10 : Memory := m06.write 28 v10 (by right; decide)
-- 11-cross-word-read
private def m11 : Memory := m10
private def r11 : Bytes := m11.readBytes 28 8 (by right; decide)
-- 12-whole-prefix
private def m12 : Memory := m10
private def r12 : Bytes := m12.readBytes 0 28 (by right; decide)
-- 13-whole-suffix
private def m13 : Memory := m10
private def r13 : Bytes := m13.readBytes 36 28 (by right; decide)
-- 14-left-overlap
private def v14 : Bytes := r09
private def m14 : Memory := m06.write 26 v14 (by right; decide)
-- 15-right-overlap
private def v15 : Bytes := r09
private def m15 : Memory := m06.write 30 v15 (by right; decide)
-- 16-self-copy
private def v16 : Bytes := r09
private def m16 : Memory := m06.write 28 v16 (by right; decide)
-- 17-retained-original-and-read
private def m17 : Memory := m10
-- 18-expand-written32
private def m18 : Memory := m10.expand 32 (by decide)
-- 19-exact-end-write
private def v19 : Bytes := Bytes.ofList [0, 128, 255, 0]
private def m19 : Memory := m06.write 60 v19 (by right; decide)
-- 20-exact-end-read
private def m20 : Memory := m19
private def r20 : Bytes := m20.readBytes 60 4 (by right; decide)
-- 21-empty-end-read
private def m21 : Memory := m06
private def r21 : Bytes := m21.readBytes 64 0 (Or.inl rfl)
-- 22-empty-read-inside-write
private def m22 : Memory := m10
private def r22 : Bytes := m22.readBytes 30 0 (Or.inl rfl)
-- 23-empty-write-inside-read
private def v23 : Bytes := Bytes.ofList []
private def m23 : Memory := m06.write 30 v23 (Or.inl (by decide))
private def r23 : Bytes := m23.readBytes 28 8 (by right; decide)
-- 24-adjacent-prefix
private def m24 : Memory := m10
private def r24 : Bytes := m24.readBytes 28 0 (Or.inl rfl)
-- 25-adjacent-left
private def m25 : Memory := m10
private def r25 : Bytes := m25.readBytes 24 4 (by right; decide)
-- 26-adjacent-right
private def m26 : Memory := m10
private def r26 : Bytes := m26.readBytes 36 4 (by right; decide)
-- 27-empty-read-2p64
private def m27 : Memory := m06
private def r27 : Bytes := m27.readBytes 18446744073709551616 0 (Or.inl rfl)
-- 28-empty-write-2p64
private def v28 : Bytes := Bytes.ofList []
private def m28 : Memory := m06.write 18446744073709551616 v28 (Or.inl (by decide))
-- 29-empty-read-u256max
private def m29 : Memory := m06
private def r29 : Bytes := m29.readBytes
  115792089237316195423570985008687907853269984665640564039457584007913129639935 0 (Or.inl rfl)
-- 30-empty-write-u256max
private def v30 : Bytes := Bytes.ofList []
private def m30 : Memory := m06.write
  115792089237316195423570985008687907853269984665640564039457584007913129639935 v30 (Or.inl (by
  decide))
-- 31-lean-only-empty-read-2p4096
private def m31 : Memory := m06
private def r31 : Bytes := m31.readBytes (2^4096) 0 (Or.inl rfl)
-- 32-lean-only-empty-write-2p4096
private def v32 : Bytes := Bytes.ofList []
private def m32 : Memory := m06.write (2^4096) v32 (Or.inl (by decide))
-- 33-both-empty
private def v33 : Bytes := Bytes.ofList []
private def m33 : Memory := m01.write 18446744073709551616 v33 (Or.inl (by decide))
private def r33 : Bytes := m33.readBytes 0 0 (Or.inl rfl)
private def observations : List Json := [
  Json.mkObj [( "id" , toJson "01-empty" ) , ( "op" , toJson "observe" ) , ( "before" , memoryJson
    Memory.empty) , ( "input" , Json.mkObj []) , ( "after" , memoryJson m01) , ( "reads" ,
    Json.mkObj []) , ( "savedMemories" , Json.mkObj []) , ( "savedBytes" , Json.mkObj []) , (
    "returnClass" , toJson "observation" )] ,
  Json.mkObj [( "id" , toJson "02-empty-expand-zero" ) , ( "op" , toJson "expand" ) , ( "before" ,
    memoryJson m01) , ( "input" , Json.mkObj [( "increment" , toJson (toString (0 : Nat)))]) , (
    "after" , memoryJson m02) , ( "reads" , Json.mkObj []) , ( "savedMemories" , Json.mkObj [(
    "old" , memoryJson m01)]) , ( "savedBytes" , Json.mkObj []) , ( "returnClass" , toJson
    "NoneType" )] ,
  Json.mkObj [( "id" , toJson "03-expand32" ) , ( "op" , toJson "expand" ) , ( "before" ,
    memoryJson m01) , ( "input" , Json.mkObj [( "increment" , toJson (toString (32 : Nat)))]) , (
    "after" , memoryJson m03) , ( "reads" , Json.mkObj []) , ( "savedMemories" , Json.mkObj [(
    "old" , memoryJson m01)]) , ( "savedBytes" , Json.mkObj []) , ( "returnClass" , toJson
    "NoneType" )] ,
  Json.mkObj [( "id" , toJson "04-expand-zero32" ) , ( "op" , toJson "expand" ) , ( "before" ,
    memoryJson m03) , ( "input" , Json.mkObj [( "increment" , toJson (toString (0 : Nat)))]) , (
    "after" , memoryJson m04) , ( "reads" , Json.mkObj []) , ( "savedMemories" , Json.mkObj [(
    "old" , memoryJson m03)]) , ( "savedBytes" , Json.mkObj []) , ( "returnClass" , toJson
    "NoneType" )] ,
  Json.mkObj [( "id" , toJson "05-expand32-again" ) , ( "op" , toJson "expand" ) , ( "before" ,
    memoryJson m03) , ( "input" , Json.mkObj [( "increment" , toJson (toString (32 : Nat)))]) , (
    "after" , memoryJson m05) , ( "reads" , Json.mkObj []) , ( "savedMemories" , Json.mkObj [(
    "old" , memoryJson m03)]) , ( "savedBytes" , Json.mkObj []) , ( "returnClass" , toJson
    "NoneType" )] ,
  Json.mkObj [( "id" , toJson "06-full-write" ) , ( "op" , toJson "write" ) , ( "before" ,
    memoryJson m05) , ( "input" , Json.mkObj [( "start" , toJson (toString (0 : Nat))) , (
    "payload" , bytesJson v06)]) , ( "after" , memoryJson m06) , ( "reads" , Json.mkObj []) , (
    "savedMemories" , Json.mkObj [( "old" , memoryJson m05)]) , ( "savedBytes" , Json.mkObj []) , (
    "returnClass" , toJson "NoneType" )] ,
  Json.mkObj [( "id" , toJson "07-high-interior-zero-full-write" ) , ( "op" , toJson "write" ) , (
    "before" , memoryJson m03) , ( "input" , Json.mkObj [( "start" , toJson (toString (0 : Nat))) ,
    ( "payload" , bytesJson v07)]) , ( "after" , memoryJson m07) , ( "reads" , Json.mkObj []) , (
    "savedMemories" , Json.mkObj [( "old" , memoryJson m03)]) , ( "savedBytes" , Json.mkObj []) , (
    "returnClass" , toJson "NoneType" )] ,
  Json.mkObj [( "id" , toJson "08-read-all" ) , ( "op" , toJson "read" ) , ( "before" , memoryJson
    m06) , ( "input" , Json.mkObj [( "start" , toJson (toString (0 : Nat))) , ( "length" , toJson
    (toString (64 : Nat)))]) , ( "after" , memoryJson m08) , ( "reads" , Json.mkObj [( "result" ,
    bytesJson r08)]) , ( "savedMemories" , Json.mkObj []) , ( "savedBytes" , Json.mkObj []) , (
    "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "09-save-cross-window" ) , ( "op" , toJson "read" ) , ( "before" ,
    memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString (28 : Nat))) , (
    "length" , toJson (toString (8 : Nat)))]) , ( "after" , memoryJson m09) , ( "reads" ,
    Json.mkObj [( "result" , bytesJson r09)]) , ( "savedMemories" , Json.mkObj [( "base" ,
    memoryJson m06)]) , ( "savedBytes" , Json.mkObj [( "window" , bytesJson r09)]) , (
    "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "10-cross-word-write" ) , ( "op" , toJson "write" ) , ( "before" ,
    memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString (28 : Nat))) , (
    "payload" , bytesJson v10)]) , ( "after" , memoryJson m10) , ( "reads" , Json.mkObj []) , (
    "savedMemories" , Json.mkObj [( "base" , memoryJson m06)]) , ( "savedBytes" , Json.mkObj [(
    "window" , bytesJson r09)]) , ( "returnClass" , toJson "NoneType" )] ,
  Json.mkObj [( "id" , toJson "11-cross-word-read" ) , ( "op" , toJson "read" ) , ( "before" ,
    memoryJson m10) , ( "input" , Json.mkObj [( "start" , toJson (toString (28 : Nat))) , (
    "length" , toJson (toString (8 : Nat)))]) , ( "after" , memoryJson m11) , ( "reads" ,
    Json.mkObj [( "result" , bytesJson r11)]) , ( "savedMemories" , Json.mkObj [( "base" ,
    memoryJson m06)]) , ( "savedBytes" , Json.mkObj [( "window" , bytesJson r09)]) , (
    "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "12-whole-prefix" ) , ( "op" , toJson "read" ) , ( "before" ,
    memoryJson m10) , ( "input" , Json.mkObj [( "start" , toJson (toString (0 : Nat))) , ( "length"
    , toJson (toString (28 : Nat)))]) , ( "after" , memoryJson m12) , ( "reads" , Json.mkObj [(
    "result" , bytesJson r12)]) , ( "savedMemories" , Json.mkObj [( "base" , memoryJson m06)]) , (
    "savedBytes" , Json.mkObj [( "window" , bytesJson r09)]) , ( "returnClass" , toJson "bytes" )]
    ,
  Json.mkObj [( "id" , toJson "13-whole-suffix" ) , ( "op" , toJson "read" ) , ( "before" ,
    memoryJson m10) , ( "input" , Json.mkObj [( "start" , toJson (toString (36 : Nat))) , (
    "length" , toJson (toString (28 : Nat)))]) , ( "after" , memoryJson m13) , ( "reads" ,
    Json.mkObj [( "result" , bytesJson r13)]) , ( "savedMemories" , Json.mkObj [( "base" ,
    memoryJson m06)]) , ( "savedBytes" , Json.mkObj [( "window" , bytesJson r09)]) , (
    "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "14-left-overlap" ) , ( "op" , toJson "write" ) , ( "before" ,
    memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString (26 : Nat))) , (
    "payload" , bytesJson v14)]) , ( "after" , memoryJson m14) , ( "reads" , Json.mkObj []) , (
    "savedMemories" , Json.mkObj [( "base" , memoryJson m06)]) , ( "savedBytes" , Json.mkObj [(
    "window" , bytesJson r09)]) , ( "returnClass" , toJson "NoneType" )] ,
  Json.mkObj [( "id" , toJson "15-right-overlap" ) , ( "op" , toJson "write" ) , ( "before" ,
    memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString (30 : Nat))) , (
    "payload" , bytesJson v15)]) , ( "after" , memoryJson m15) , ( "reads" , Json.mkObj []) , (
    "savedMemories" , Json.mkObj [( "base" , memoryJson m06)]) , ( "savedBytes" , Json.mkObj [(
    "window" , bytesJson r09)]) , ( "returnClass" , toJson "NoneType" )] ,
  Json.mkObj [( "id" , toJson "16-self-copy" ) , ( "op" , toJson "write" ) , ( "before" ,
    memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString (28 : Nat))) , (
    "payload" , bytesJson v16)]) , ( "after" , memoryJson m16) , ( "reads" , Json.mkObj []) , (
    "savedMemories" , Json.mkObj [( "base" , memoryJson m06)]) , ( "savedBytes" , Json.mkObj [(
    "window" , bytesJson r09)]) , ( "returnClass" , toJson "NoneType" )] ,
  Json.mkObj [( "id" , toJson "17-retained-original-and-read" ) , ( "op" , toJson "observe" ) , (
    "before" , memoryJson m10) , ( "input" , Json.mkObj []) , ( "after" , memoryJson m17) , (
    "reads" , Json.mkObj []) , ( "savedMemories" , Json.mkObj [( "base" , memoryJson m06)]) , (
    "savedBytes" , Json.mkObj [( "window" , bytesJson r09)]) , ( "returnClass" , toJson
    "observation" )] ,
  Json.mkObj [( "id" , toJson "18-expand-written32" ) , ( "op" , toJson "expand" ) , ( "before" ,
    memoryJson m10) , ( "input" , Json.mkObj [( "increment" , toJson (toString (32 : Nat)))]) , (
    "after" , memoryJson m18) , ( "reads" , Json.mkObj []) , ( "savedMemories" , Json.mkObj [(
    "old" , memoryJson m10) , ( "base" , memoryJson m06)]) , ( "savedBytes" , Json.mkObj [(
    "window" , bytesJson r09)]) , ( "returnClass" , toJson "NoneType" )] ,
  Json.mkObj [( "id" , toJson "19-exact-end-write" ) , ( "op" , toJson "write" ) , ( "before" ,
    memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString (60 : Nat))) , (
    "payload" , bytesJson v19)]) , ( "after" , memoryJson m19) , ( "reads" , Json.mkObj []) , (
    "savedMemories" , Json.mkObj [( "base" , memoryJson m06)]) , ( "savedBytes" , Json.mkObj [(
    "window" , bytesJson r09)]) , ( "returnClass" , toJson "NoneType" )] ,
  Json.mkObj [( "id" , toJson "20-exact-end-read" ) , ( "op" , toJson "read" ) , ( "before" ,
    memoryJson m19) , ( "input" , Json.mkObj [( "start" , toJson (toString (60 : Nat))) , (
    "length" , toJson (toString (4 : Nat)))]) , ( "after" , memoryJson m20) , ( "reads" ,
    Json.mkObj [( "result" , bytesJson r20)]) , ( "savedMemories" , Json.mkObj [( "base" ,
    memoryJson m06)]) , ( "savedBytes" , Json.mkObj [( "window" , bytesJson r09)]) , (
    "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "21-empty-end-read" ) , ( "op" , toJson "read" ) , ( "before" ,
    memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString (64 : Nat))) , (
    "length" , toJson (toString (0 : Nat)))]) , ( "after" , memoryJson m21) , ( "reads" ,
    Json.mkObj [( "result" , bytesJson r21)]) , ( "savedMemories" , Json.mkObj []) , ( "savedBytes"
    , Json.mkObj []) , ( "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "22-empty-read-inside-write" ) , ( "op" , toJson "read" ) , (
    "before" , memoryJson m10) , ( "input" , Json.mkObj [( "start" , toJson (toString (30 : Nat)))
    , ( "length" , toJson (toString (0 : Nat)))]) , ( "after" , memoryJson m22) , ( "reads" ,
    Json.mkObj [( "result" , bytesJson r22)]) , ( "savedMemories" , Json.mkObj [( "base" ,
    memoryJson m06)]) , ( "savedBytes" , Json.mkObj [( "window" , bytesJson r09)]) , (
    "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "23-empty-write-inside-read" ) , ( "op" , toJson "write" ) , (
    "before" , memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString (30 : Nat)))
    , ( "payload" , bytesJson v23)]) , ( "after" , memoryJson m23) , ( "reads" , Json.mkObj [(
    "preserved-window" , bytesJson r23)]) , ( "savedMemories" , Json.mkObj [( "base" , memoryJson
    m06)]) , ( "savedBytes" , Json.mkObj [( "window" , bytesJson r09)]) , ( "returnClass" , toJson
    "NoneType" )] ,
  Json.mkObj [( "id" , toJson "24-adjacent-prefix" ) , ( "op" , toJson "read" ) , ( "before" ,
    memoryJson m10) , ( "input" , Json.mkObj [( "start" , toJson (toString (28 : Nat))) , (
    "length" , toJson (toString (0 : Nat)))]) , ( "after" , memoryJson m24) , ( "reads" ,
    Json.mkObj [( "result" , bytesJson r24)]) , ( "savedMemories" , Json.mkObj []) , ( "savedBytes"
    , Json.mkObj []) , ( "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "25-adjacent-left" ) , ( "op" , toJson "read" ) , ( "before" ,
    memoryJson m10) , ( "input" , Json.mkObj [( "start" , toJson (toString (24 : Nat))) , (
    "length" , toJson (toString (4 : Nat)))]) , ( "after" , memoryJson m25) , ( "reads" ,
    Json.mkObj [( "result" , bytesJson r25)]) , ( "savedMemories" , Json.mkObj []) , ( "savedBytes"
    , Json.mkObj []) , ( "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "26-adjacent-right" ) , ( "op" , toJson "read" ) , ( "before" ,
    memoryJson m10) , ( "input" , Json.mkObj [( "start" , toJson (toString (36 : Nat))) , (
    "length" , toJson (toString (4 : Nat)))]) , ( "after" , memoryJson m26) , ( "reads" ,
    Json.mkObj [( "result" , bytesJson r26)]) , ( "savedMemories" , Json.mkObj []) , ( "savedBytes"
    , Json.mkObj []) , ( "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "27-empty-read-2p64" ) , ( "op" , toJson "read" ) , ( "before" ,
    memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString (18446744073709551616 :
    Nat))) , ( "length" , toJson (toString (0 : Nat)))]) , ( "after" , memoryJson m27) , ( "reads"
    , Json.mkObj [( "result" , bytesJson r27)]) , ( "savedMemories" , Json.mkObj [( "base" ,
    memoryJson m06)]) , ( "savedBytes" , Json.mkObj [( "window" , bytesJson r09)]) , (
    "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "28-empty-write-2p64" ) , ( "op" , toJson "write" ) , ( "before" ,
    memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString (18446744073709551616 :
    Nat))) , ( "payload" , bytesJson v28)]) , ( "after" , memoryJson m28) , ( "reads" , Json.mkObj
    []) , ( "savedMemories" , Json.mkObj [( "base" , memoryJson m06)]) , ( "savedBytes" ,
    Json.mkObj [( "window" , bytesJson r09)]) , ( "returnClass" , toJson "NoneType" )] ,
  Json.mkObj [( "id" , toJson "29-empty-read-u256max" ) , ( "op" , toJson "read" ) , ( "before" ,
    memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString
    (115792089237316195423570985008687907853269984665640564039457584007913129639935 : Nat))) , (
    "length" , toJson (toString (0 : Nat)))]) , ( "after" , memoryJson m29) , ( "reads" ,
    Json.mkObj [( "result" , bytesJson r29)]) , ( "savedMemories" , Json.mkObj [( "base" ,
    memoryJson m06)]) , ( "savedBytes" , Json.mkObj [( "window" , bytesJson r09)]) , (
    "returnClass" , toJson "bytes" )] ,
  Json.mkObj [( "id" , toJson "30-empty-write-u256max" ) , ( "op" , toJson "write" ) , ( "before" ,
    memoryJson m06) , ( "input" , Json.mkObj [( "start" , toJson (toString
    (115792089237316195423570985008687907853269984665640564039457584007913129639935 : Nat))) , (
    "payload" , bytesJson v30)]) , ( "after" , memoryJson m30) , ( "reads" , Json.mkObj []) , (
    "savedMemories" , Json.mkObj [( "base" , memoryJson m06)]) , ( "savedBytes" , Json.mkObj [(
    "window" , bytesJson r09)]) , ( "returnClass" , toJson "NoneType" )] ,
  Json.mkObj [( "id" , toJson "31-lean-only-empty-read-2p4096" ) , ( "op" , toJson "read" ) , (
    "before" , memoryJson m06) , ( "input" , Json.mkObj [( "startExpression" , toJson "2^4096" ) ,
    ( "length" , toJson (toString (0 : Nat)))]) , ( "after" , memoryJson m31) , ( "reads" ,
    Json.mkObj [( "result" , bytesJson r31)]) , ( "savedMemories" , Json.mkObj [( "base" ,
    memoryJson m06)]) , ( "savedBytes" , Json.mkObj [( "window" , bytesJson r09)]) , (
    "returnClass" , toJson "observation" )] ,
  Json.mkObj [( "id" , toJson "32-lean-only-empty-write-2p4096" ) , ( "op" , toJson "write" ) , (
    "before" , memoryJson m06) , ( "input" , Json.mkObj [( "startExpression" , toJson "2^4096" ) ,
    ( "payload" , bytesJson v32)]) , ( "after" , memoryJson m32) , ( "reads" , Json.mkObj []) , (
    "savedMemories" , Json.mkObj [( "base" , memoryJson m06)]) , ( "savedBytes" , Json.mkObj [(
    "window" , bytesJson r09)]) , ( "returnClass" , toJson "observation" )] ,
  Json.mkObj [( "id" , toJson "33-both-empty" ) , ( "op" , toJson "write" ) , ( "before" ,
    memoryJson m01) , ( "input" , Json.mkObj [( "start" , toJson (toString (18446744073709551616 :
    Nat))) , ( "payload" , bytesJson v33)]) , ( "after" , memoryJson m33) , ( "reads" , Json.mkObj
    [( "empty-read-inside" , bytesJson r33)]) , ( "savedMemories" , Json.mkObj [( "old" ,
    memoryJson m01)]) , ( "savedBytes" , Json.mkObj [( "empty" , bytesJson r33)]) , ( "returnClass"
    , toJson "NoneType" )]
]
def main : IO Unit := do
  IO.println "{\"kind\":\"begin\",\"version\":1,\"count\":33}"
  for row in observations do IO.println row.compress
  IO.println "{\"kind\":\"end\",\"version\":1,\"count\":33}"
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--controls", type=Path, help="optional exact frozen catalog override")
    parser.add_argument(
        "--source-frames",
        type=Path,
        help="caller-supplied baseline; not authenticated here; never replays source",
    )
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--self-test", action="store_true")
    modes.add_argument("--emit-lean", action="store_true")
    modes.add_argument("--check-frames", type=Path)
    args = parser.parse_args()
    obj = catalog(args.controls)
    if args.self_test:
        self_test(obj)
    elif args.emit_lean:
        print(LEAN_PROGRAM, end="")
    else:
        actual = parse_frames(args.check_frames.read_text(), expanded_literals(obj))
        if args.source_frames is not None:
            source = parse_frames(
                args.source_frames.read_text(), expanded_literals(obj, source=True)
            )
            mapped = [row for row in actual[1:-1] if row["id"] not in LEAN_ONLY]
            exact(mapped, source[1:-1])
        print(
            json.dumps(
                {
                    "status": "complete literal frames agree",
                    "frames": 33,
                    "source_frames_compared": 31 if args.source_frames else 0,
                    "optimize": sys.flags.optimize,
                }
            )
        )


if __name__ == "__main__":
    main()
