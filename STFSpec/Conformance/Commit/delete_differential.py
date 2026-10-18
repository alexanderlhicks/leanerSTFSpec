#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Bounded original deletion, separate strict completion, and full nominal frames.

Freeze --write-catalog, --write-premises and --preflight artifacts before original execution. Use
EELS/.venv/bin/python -I -B, --eels EELS, --output EXTERNAL.lean, --catalog JSON,
--rlp-wheel WHEEL and --types-wheel WHEEL. --self-test also supports Python -O.
Concrete full-value comparison has local retained-cache/embedding/finite-host
premises. Original dirty-cache writes and query histories remain observations.
"""

import argparse
import base64
import datetime
import hashlib
import importlib.metadata
import json
import marshal
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import traceback
import types
import zipfile

ROOT = Path(__file__).resolve().parents[3]
DEFAULT_SEED = 191


def require(condition, message):
    if not condition:
        raise ValueError(message)


def natural(value):
    require(type(value) is int and value >= 0, "non-natural field")
    return value


def object_pairs(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON field")
        result[key] = value
    return result


def reject_constant(value):
    raise ValueError("nonfinite JSON constant: " + value)


def load_json(text):
    return json.loads(text, object_pairs_hook=object_pairs, parse_constant=reject_constant)


class Reader:
    def __init__(self, values):
        require(type(values) is list, "wire must be list")
        self.values, self.offset = values, 0

    def take(self):
        require(self.offset < len(self.values), "truncated field")
        value = natural(self.values[self.offset])
        self.offset += 1
        return value

    def octets(self, count, bound=256):
        require(count <= len(self.values) - self.offset, "truncated bytes")
        values = [self.take() for _ in range(count)]
        require(all(x < bound for x in values), "out of range field")
        return values

    def array(self, bound=256):
        return self.octets(self.take(), bound)

    def cache(self):
        raw, tag = self.array(), self.take()
        require(tag in (0, 1), "hash option tag")
        return raw, None if tag == 0 else self.octets(32)

    def ref(self):
        tag = self.take()
        require(tag in range(5), "Ref tag")
        if tag == 0:
            return (0,)
        if tag == 1:
            return (1, self.octets(32))
        if tag == 2:
            return (2, self.array(16), self.array(), self.cache())
        if tag == 3:
            path, child = self.array(16), self.ref()
            require(child[0] != 0, "absent extension child")
            return (3, path, child, self.cache())
        count = self.take()
        require(count <= len(self.values) - self.offset, "truncated children")
        children = [self.ref() for _ in range(count)]
        return (4, children, self.array(), self.cache())

    def result(self):
        tag = self.take()
        require(tag in (0, 1, 2, 3), "result tag")
        if tag == 0:
            value = self.ref()
            return (0, value)
        if tag in (1, 3):
            return (tag, self.octets(32))
        reason = self.take()
        require(reason in range(13), "malformed tag")
        fields = 2 if reason == 11 else 1 if reason in (6, 7, 9, 12) else 0
        return (2, reason, [self.take() for _ in range(fields)])

    def finish(self):
        require(self.offset == len(self.values), "trailing fields")


def parse_records(text, count):
    lines = text.splitlines()
    require(len(lines) == count, "missing/trailing records")
    rows = []
    for index, line in enumerate(lines):
        row = load_json(line)
        fields = {"case", "input", "key", "result", "stateResult", "queries", "answers", "counter"}
        require(type(row) is dict and set(row) == fields, "reply fields")
        require(natural(row["case"]) == index, "case order")
        for key, bound in (("key", 16),):
            require(
                type(row[key]) is list and all(natural(x) < bound for x in row[key]),
                "key/value digits",
            )
        reader = Reader(row["input"])
        reader.ref()
        reader.finish()
        for key in ("result", "stateResult"):
            reader = Reader(row[key])
            reader.result()
            reader.finish()
        require(type(row["queries"]) is type(row["answers"]) is list, "query/answer list")
        require(len(row["queries"]) == len(row["answers"]), "query/answer arity")
        for preimage, answer in zip(row["queries"], row["answers"]):
            reader = Reader(preimage)
            reader.array()
            reader.finish()
            reader = Reader(answer)
            reader.octets(32)
            reader.finish()
        natural(row["counter"])
        rows.append(row)
    return rows


def reject_resume(arguments):
    """Reject unsupported prior-phase reuse before reading or creating artifacts."""
    require(
        not any(arg.split("=", 1)[0].startswith("--resume") for arg in arguments),
        "resume is unsupported; use fresh output artifacts",
    )


def resume_cli_tests():
    """The real CLI must reject reuse before touching any candidate artifacts."""
    with tempfile.TemporaryDirectory(prefix="delete-resume-control-") as folder:
        root = Path(folder)
        journal = root / "prior.jsonl"
        journal.write_text('{"phase":"complete","driver_sha256":"stale"}\n')
        output, catalog_path = root / "result.lean", root / "catalog.json"
        original = journal.read_bytes()
        controls = [
            ["--resume-journal", str(journal)],
            ["--resume-journal=" + str(journal)],
            ["--resume", str(journal)],
            ["--resume-journal"],
            ["--write-catalog", str(catalog_path), "--resume-journal", str(journal)],
            ["--self-test", "--resume-journal", str(journal)],
        ]
        for options in controls:
            argv = [sys.executable, "-I", "-B"]
            if sys.flags.optimize:
                argv.append("-O")
            result = subprocess.run(
                [*argv, str(Path(__file__).resolve()), *options, "--output", str(output)],
                capture_output=True,
            )
            require(
                result.returncode != 0 and b"resume is unsupported" in result.stderr,
                "unsupported resume CLI accepted",
            )
            require(
                set(root.iterdir()) == {journal} and journal.read_bytes() == original,
                "resume rejection touched artifacts",
            )
    return len(controls)


def parser_tests():
    h = list(range(32))
    leaf = [2, 1, 15, 2, 0, 255, 2, 193, 128, 1, *h]
    tree = [3, 0, 4, 3, 0, 1, *h, *leaf, 2, 0, 255, 0, 0, 0, 0]
    good = dict(
        case=0,
        input=tree,
        key=[15, 0],
        result=[0, *leaf],
        stateResult=[2, 11, 15, 1],
        queries=[[0], [2, 0, 255]],
        answers=[h, h],
        counter=8,
    )
    positive = [
        good,
        dict(good, input=[0], result=[3, *h], stateResult=[1, *h], queries=[], answers=[]),
    ]
    positive.append(dict(good, result=[0, 0], stateResult=[0, 0]))
    for reason in range(13):
        payload = [65537, 257] if reason == 11 else [65537] if reason in (6, 7, 9, 12) else []
        positive.append(dict(good, result=[2, reason, *payload]))
    for row in positive:
        require(parse_records(json.dumps(row), 1) == [row], "valid complete frame")
    bad = [
        "",
        json.dumps(good) + "\n" + json.dumps(good),
        json.dumps(dict(good, extra=0)),
        '{"case":0,"case":0}',
        json.dumps({k: v for k, v in good.items() if k != "counter"}),
    ]
    for key in ("case", "counter"):
        for value in (True, False, -1, 0.0, None, float("nan"), float("inf")):
            bad.append(json.dumps(dict(good, **{key: value})))
    for key in ("input", "result", "stateResult"):
        for cut in range(len(good[key])):
            bad.append(json.dumps(dict(good, **{key: good[key][:cut]})))
        bad.append(json.dumps(dict(good, **{key: good[key] + [0]})))
        for pos in range(len(good[key])):
            for value in (True, False, -1, 0.0, None, float("nan"), float("inf")):
                values = good[key].copy()
                values[pos] = value
                bad.append(json.dumps(dict(good, **{key: values})))
    for key, invalid in (
        ("key", [16]),
        ("key", [True]),
        ("input", [3, 0, 0, 0, 0]),
        ("result", [2, 13]),
        ("result", [2, 11, 15]),
        ("result", [3, *h, 0]),
        ("queries", [[1, 256]]),
        ("queries", [[0, 0]]),
        ("answers", [h]),
        ("answers", [h, h[:-1]]),
    ):
        bad.append(json.dumps(dict(good, **{key: invalid})))
    for key in ("queries", "answers"):
        for index, original in enumerate(good[key]):
            for cut in range(len(original)):
                frames = [x.copy() for x in good[key]]
                frames[index] = original[:cut]
                bad.append(json.dumps(dict(good, **{key: frames})))
            frames = [x.copy() for x in good[key]]
            frames[index] = original + [0]
            bad.append(json.dumps(dict(good, **{key: frames})))
            for pos in range(len(original)):
                for value in (True, False, -1, 0.0, None, float("nan"), float("inf")):
                    frames = [x.copy() for x in good[key]]
                    frames[index][pos] = value
                    bad.append(json.dumps(dict(good, **{key: frames})))
    for text in bad:
        try:
            parse_records(text, 1)
        except (ValueError, TypeError, json.JSONDecodeError):
            continue
        raise RuntimeError("invalid complete delete frame accepted: " + text)
    resume_cli_tests()
    print(
        json.dumps(dict(accepted=len(positive), rejected=len(bad), optimized=sys.flags.optimize))
    )


def rlp_bytes(item):
    """Independent finite standard-domain wire model used to freeze exact payloads."""

    def prefix(length, short, long):
        if length < 56:
            return bytes([short + length])
        width = (length.bit_length() + 7) // 8
        require(width <= 8, "catalog Encodable bound")
        return bytes([long + width]) + length.to_bytes(width, "big")

    if type(item) is bytes:
        return item if len(item) == 1 and item[0] < 128 else prefix(len(item), 128, 183) + item
    require(type(item) is list, "model item type")
    payload = b"".join(rlp_bytes(child) for child in item)
    return prefix(len(payload), 192, 247) + payload


def compact(path, leaf):
    require(all(type(x) is int and 0 <= x < 16 for x in path), "catalog nibble")
    odd = len(path) % 2
    digits = [(2 if leaf else 0) + odd, *([] if odd else [0]), *path]
    return bytes(16 * digits[i] + digits[i + 1] for i in range(0, len(digits), 2))


def child_item(node):
    if node["tag"] == 0:
        return b""
    if node["tag"] == 1 or node["hash"] is not None:
        return bytes(node["hash"])
    return current_item(node)


def current_item(node):
    if node["tag"] == 2:
        return [compact(node["path"], True), bytes(node["value"])]
    if node["tag"] == 3:
        return [compact(node["path"], False), child_item(node["child"])]
    require(node["tag"] == 4, "resolved current item")
    return [*[child_item(child) for child in node["children"]], bytes(node["value"])]


def catalog():
    import copy

    def h(n):
        return list(n.to_bytes(32, "big"))

    def leaf(path=(), value=(), cache="arbitrary", dirty=False):
        n = dict(tag=2, path=list(path), value=list(value), raw=[255, 0], hash=h(91), dirty=dirty)
        if cache == "inline":
            n.update(raw=list(rlp_bytes(current_item(dict(n, hash=None)))), hash=None)
        return n

    def ext(path, child, dirty=False):
        return dict(
            tag=3, path=list(path), child=copy.deepcopy(child), raw=[255], hash=h(42), dirty=dirty
        )

    def branch(children, value=(), dirty=False):
        return dict(
            tag=4,
            children=copy.deepcopy(children),
            value=list(value),
            raw=[0, 255],
            hash=h(61),
            dirty=dirty,
        )

    none, stub = dict(tag=0), dict(tag=1, hash=h(17))
    rows = []

    def add(family, root, key=(), boundary=None, helper=None):
        row = dict(
            case=len(rows),
            family=family,
            root=copy.deepcopy(root),
            key=list(key),
            boundary=boundary,
            helper=helper,
            stages=["A", "B1", "B2", "B3", "B4", "C", "D"],
        )
        if boundary:
            row["stages"].append("E")
        if helper in ("leaf", "ext", "branch"):
            row["expected_own_raw"] = list(rlp_bytes(current_item(root)))
            require(len(row["expected_own_raw"]) in (31, 32, 33), "constructed raw width")
        rows.append(row)

    for key in ([], [0], [15, 0]):
        add("D01", none, key)
        add("D01", stub, key)
        for p in ([], [0], [15, 0]):
            for size in (0, 1, 40):
                add("D02" if p == key else "D03", leaf(p, [0] * size), key)
    for size in (0, 31, 32, 33):
        for cached in (False, True):
            n = leaf([], [])
            n.update(raw=[255] * size, hash=h(63) if cached else None)
            add("D04", n, [0])
    variants = [
        leaf([1], [170], "inline"),
        ext([2], leaf([3], [], "inline")),
        branch([none, stub, leaf([])], [0, 255]),
        stub,
    ]
    for c in variants:
        for p, k in (([0], []), ([0], [15]), ([0, 15], [0, 1])):
            add("D05", ext(p, c), k)
    add("D06", ext([0], leaf([1], [170])), [0, 1])
    add("D07", ext([0], leaf([1], [170])), [0, 2])
    add("D08", ext([0], ext([1], leaf([2]))), [0, 3])
    add("D09", ext([0], branch([none, leaf([1], [170], "inline")], [255])), [0, 0])
    add("D09", ext([0], branch([leaf([]), leaf([1], [], "inline")], [255])), [0, 0])
    for c in variants:
        add("D10", ext([], c), [0, 15])
        add("D10", ext([], ext([], c)), [0, 15])
    for arity in (0, 1, 15, 16, 17, 257):
        for c in (none, stub, leaf([], [], "inline")):
            add("D11", branch([c] * arity), [])
        for digit in (0, 14, 15):
            for selected in (none, leaf([1], [170], "inline"), stub):
                xs = [none] * arity
                if digit < arity:
                    xs[digit] = selected
                family = (
                    "D14"
                    if digit >= arity
                    else "D15"
                    if arity < 16
                    else "D16"
                    if arity == 16
                    else "D17"
                )
                add(family, branch(xs, [0, 255]), [digit, 0])
    for size in (0, 31, 32, 33):
        n = branch([], [255])
        n.update(raw=[255] * size, hash=h(63) if size % 2 else None)
        add("D12", n)
    add("D13", branch([none]), [0])
    for i in (15, 16, 255, 256):
        xs = [none] * (i + 1)
        xs[i] = stub
        add("D13", branch(xs), [0])
    add("D18", branch([leaf([1], [170], "inline"), stub]), [0, 2])
    for i in (1, 15):
        for sibling in variants[:3]:
            xs = [none] * (i + 1)
            xs[0] = leaf([])
            xs[i] = sibling
            add("D19", branch(xs), [0])
    for i in (1, 15, 16, 255, 256):
        xs = [none] * (i + 1)
        xs[0] = leaf([])
        xs[i] = stub
        add("D20", branch(xs), [0])
    for i in (16, 255, 256):
        for cache in ("arbitrary", "inline", "long"):
            sibling = leaf([1], [170], "inline")
            if cache == "arbitrary":
                sibling.update(hash=h(53), raw=[255])
            if cache == "long":
                sibling.update(raw=[255] * 33, hash=None)
            xs = [none] * (i + 1)
            xs[0] = leaf([])
            xs[i] = sibling
            add("D21", branch(xs), [0], boundary="high-survivor-" + str(i) + "-" + cache)
    add("D22", branch([leaf([])]), [0])
    add("D23", branch([leaf([])], [255]), [0])
    add("D23", branch([leaf([]), stub, leaf([])]), [0])
    add("D23", branch([leaf([]), stub], [255]), [0])
    add("D24", branch([branch([leaf([]), leaf([1], [170], "inline")]), stub]), [0, 0])
    add("D25", branch([ext([], leaf([1], [170])), none]), [0, 2])
    add("D25", branch([ext([], branch([none, stub])), stub]), [0, 0])
    for size in (28, 29, 30):
        add("D26", leaf([], [0] * size), [0], helper="leaf")
    for size in (50, 52, 54):
        add("D26", ext([0] * size, leaf([], [], "inline")), [15], helper="ext")
    for arity in (29, 30, 31):
        add("D26", branch([none] * arity), [], helper="branch")
    for plen in (0, 1, 2, 49, 50, 51, 110, 111, 510, 511):
        for size in (52, 53, 54, 253, 254, 255, 256):
            add("D26", ext([0] * plen, leaf([1], [0] * size)), [0] * plen + [2], helper="joined")
    for cache in ("arbitrary", "inline", "hashless-long"):
        s = leaf([1], [170], "inline")
        if cache == "arbitrary":
            s.update(hash=h(73), raw=[255, 0])
        if cache == "hashless-long":
            s.update(raw=[255] * 33, hash=None)
        add("D27", branch([leaf([]), s]), [0])
    add("D28", ext([], branch([none, stub, leaf([0])], [255])), [0])
    chain = ext([0, 15], ext([], leaf([0, 1], [0] * 40)))
    # These four repeated source shapes exercise D08, not Lean-only effect families.
    for _ in range(4):
        add("D08", chain, [0, 15, 0, 2])
    add("D10", ext([], branch([])), [15])
    add("D27", branch([leaf([]), leaf([1], [0] * 40, "inline")]), [0])
    # E1: the same nominal child has two different source dirty flags. Only
    # the clean guarded return satisfies Option A; the dirty outcome is recorded.
    for dirty in (False, True):
        add(
            "D18",
            branch([leaf([1], [170], "inline", dirty)]),
            [0, 2],
            boundary="observed-dirty-return" if dirty else None,
        )
    add("D03", leaf([1], [170], dirty=True), [2])
    add("D07", ext([0], leaf([1], [170], dirty=True)), [0, 2])
    off = leaf([], [], "inline", True)
    add("D13", branch([none, dict(tag=1, hash=h(17)), off]), [0])
    for name in ("dirty-cached-hash", "hashless-long", "missing-inline-raw", "stale-inline-raw"):
        c = leaf([], [0, 255], "inline")
        if name == "dirty-cached-hash":
            c.update(dirty=True, hash=h(83))
        if name == "hashless-long":
            c.update(value=[0] * 40, raw=[255] * 33)
        if name == "missing-inline-raw":
            c["raw"] = None
        if name == "stale-inline-raw":
            c["raw"] = [255]
        add("D13", branch([none, c]), [0], boundary=name)
    add("D10", ext([], none), [0], boundary="extension-None")
    add("D11", branch([leaf([], [], "inline")] * 2), [], boundary="alias")
    # A changed branch survivor must be witnessed before its outer branch collapses.
    inner = branch([leaf([], [1], "inline") for _ in range(3)] + [none] * 13)
    add("D24", branch([inner] + [none] * 15), [0, 0])
    result = dict(
        schema=1,
        pin="e1a316a06fc3d3e0a5da36fdc78580811e9d8a36",
        cases=rows,
        families=[f"D{i:02d}" for i in range(1, 29)],
        stages=["A", "B1", "B2", "B3", "B4", "C", "D", "E"],
        lean_only=[
            "D29: arbitrary-distinct/repeated-answer",
            "D30: each-first-query-error",
            "D31: both-transformer-failure-retention",
            "D32: nonlawful-count-and-negative-association",
        ],
        relation=(
            "finite acyclic nonaliasing represented trees; clean same-origin returns only "
            "where a parent actually inspects dirty; precise consulted embedding/raw cache; "
            "complete Encodable; actual Id Keccak and finite host"
        ),
    )
    require({r["family"] for r in rows} == set(result["families"]), "complete family catalog")
    return result


def deletion_model(root, key, hash_fn, recording=False):
    """Independent lawful finite model; all query bytes and control sites retained."""
    import copy

    queries, counter, guards, retained, witnesses = [], 7, [], [], []

    def query(raw):
        nonlocal counter
        answer = counter.to_bytes(32, "big") if recording else bytes(hash_fn(bytes(raw)))
        queries.append(dict(preimage=list(raw), answer=list(answer), ordinal=counter))
        counter += 1
        return list(answer)

    def consult(n):
        if n["tag"] in (0, 1):
            return
        if "_input_path" in n:
            retained.append(dict(path=n["_input_path"], node=copy.deepcopy(n)))
        if n["hash"] is None:
            if n["tag"] == 3:
                consult(n["child"])
            elif n["tag"] == 4:
                for c in n["children"]:
                    consult(c)

    def fresh(n):
        n = copy.deepcopy(n)
        if n["tag"] == 3:
            consult(n["child"])
        elif n["tag"] == 4:
            for c in n["children"]:
                consult(c)
        raw = list(rlp_bytes(current_item(n)))
        n.update(raw=raw, hash=query(raw) if len(raw) >= 32 else None, dirty=False)
        return n

    def witness(n):
        n = copy.deepcopy(n)
        witnesses.append(copy.deepcopy(n))
        if n["tag"] == 1:
            return n, [3, *n["hash"]]
        if n["hash"] is not None:
            return n, None
        if n["raw"] is not None and len(n["raw"]) >= 32:
            query(n["raw"])
            return n, None
        return fresh(n), None

    def merge(p, n):
        if n["tag"] == 2:
            return fresh(dict(tag=2, path=p + n["path"], value=n["value"]))
        if n["tag"] == 3:
            return fresh(dict(tag=3, path=p + n["path"], child=n["child"]))
        return fresh(dict(tag=3, path=p, child=n))

    def collapse(xs, v):
        nonempty = [(i, n) for i, n in enumerate(xs) if n["tag"] != 0]
        if not nonempty and not v:
            return None, False, False, [2, 9, 0]
        if len(nonempty) == 1 and not v:
            i, n = nonempty[0]
            n, e = witness(n)
            if e:
                return None, False, False, e
            if i >= 16:
                return None, False, False, [2, 12, i]
            return merge([i], n), False, True, None
        if not nonempty:
            return fresh(dict(tag=2, path=[], value=v)), False, True, None
        return fresh(dict(tag=4, children=xs, value=v)), True, True, None

    def visit(n, k, path):
        tag = n["tag"]
        if tag == 0:
            return n, True, False, None
        if tag == 1:
            return None, False, False, [3, *n["hash"]]
        if tag == 2:
            if n["path"] == k:
                return dict(tag=0), False, False, None
            return fresh(dict(tag=2, path=n["path"], value=n["value"])), True, False, None
        if tag == 3:
            p = n["path"]
            if p != k[: len(p)]:
                return fresh(dict(tag=3, path=p, child=n["child"])), True, False, None
            c, same, dirty, e = visit(n["child"], k[len(p) :], path + ["child"])
            if e:
                return None, False, False, e
            if c["tag"] == 0:
                return c, False, False, None
            if c["tag"] in (2, 3):
                return merge(p, c), False, True, None
            guards.append(
                dict(
                    parent=path,
                    kind="extension",
                    child=path + ["child"],
                    sameOrigin=same,
                    liftedDirty=dirty,
                    inputDirty=n["child"].get("dirty"),
                    requiresCleanReturn=same and not dirty and c["tag"] != 0,
                )
            )
            return fresh(dict(tag=3, path=p, child=c)), True, (not same or dirty), None
        if not k:
            if not n["value"]:
                return fresh(dict(tag=4, children=n["children"], value=[])), True, False, None
            return collapse(n["children"], [])
        i = k[0]
        if i >= len(n["children"]):
            return None, False, False, [2, 11, i, len(n["children"])]
        c, same, dirty, e = visit(n["children"][i], k[1:], path + ["children", i])
        if e:
            return None, False, False, e
        guards.append(
            dict(
                parent=path,
                kind="branch",
                child=path + ["children", i],
                sameOrigin=same,
                liftedDirty=dirty,
                inputDirty=n["children"][i].get("dirty"),
                requiresCleanReturn=same and not dirty and c["tag"] != 0,
            )
        )
        xs = n["children"].copy()
        xs[i] = c
        if same and not dirty:
            return fresh(dict(tag=4, children=xs, value=n["value"])), True, False, None
        return collapse(xs, n["value"])

    def tagged(n, p):
        n = copy.deepcopy(n)
        n["_input_path"] = p
        if n["tag"] == 3:
            n["child"] = tagged(n["child"], p + ["child"])
        elif n["tag"] == 4:
            n["children"] = [tagged(c, p + ["children", i]) for i, c in enumerate(n["children"])]
        return n

    n, same, dirty, error = visit(tagged(root, []), key, [])
    return dict(
        node=n,
        error=error,
        queries=queries,
        counter=counter,
        guards=guards,
        retained=retained,
        witnesses=witnesses,
        sameOrigin=same,
        dirty=dirty,
    )


def embedding_compatible(node):
    if node["tag"] in (0, 1):
        return True
    if node["raw"] is None:
        return False
    if node["hash"] is not None:
        return not node["dirty"]
    raw = rlp_bytes(current_item(node))
    if len(raw) >= 32 or list(raw) != node["raw"]:
        return False
    if node["tag"] == 3:
        return embedding_compatible(node["child"])
    if node["tag"] == 4:
        return all(embedding_compatible(c) for c in node["children"])
    return True


def premise_map(descriptors):
    rows = []
    for row in descriptors:
        source_only = row["boundary"] in ("extension-None", "alias")
        if source_only:
            rows.append(dict(case=row["case"], source_only=True, boundary=row["boundary"]))
            continue
        m = deletion_model(row["root"], row["key"], lambda _: bytes(32), True)
        guards = [
            dict(g, eligible=(not g["requiresCleanReturn"] or g["inputDirty"] is False))
            for g in m["guards"]
        ]
        retained = [
            dict(
                path=c["path"],
                embedding=embedding_compatible(c["node"]),
                full_cache_present=c["node"]["raw"] is not None,
                node=c["node"],
            )
            for c in m["retained"]
        ]
        rows.append(
            dict(
                case=row["case"],
                source_only=False,
                boundary=row["boundary"],
                nominal_error=m["error"],
                guard_reads=guards,
                retained_consultations=retained,
                reached_witnesses=m["witnesses"],
                local_guard_eligible=all(g["eligible"] for g in guards),
                embedding_eligible=all(
                    c["embedding"] and c["full_cache_present"] for c in retained
                ),
                completed_assembly_encodable=True,
                caveat=(
                    "failed nominal rows have prospective model consultations; "
                    "actual original trace determines reached source history"
                ),
            )
        )
    return dict(
        schema=1,
        cases=rows,
        scope=(
            "typed finite catalog local source guard/retained embedding stages; "
            "no blanket WF or initial-clean admission"
        ),
    )


def main():
    reject_resume(sys.argv[1:])
    if sys.argv[1:] == ["--self-test"]:
        parser_tests()
        return 0
    if len(sys.argv) == 3 and sys.argv[1] == "--write-premises":
        destination = Path(sys.argv[2])
        require(not destination.exists(), "fresh premise path")
        destination.write_text(json.dumps(premise_map(catalog()["cases"]), indent=2) + "\n")
        print(
            json.dumps(
                dict(
                    cases=len(catalog()["cases"]),
                    sha256=hashlib.sha256(destination.read_bytes()).hexdigest(),
                )
            )
        )
        return 0
    if len(sys.argv) == 3 and sys.argv[1] == "--write-catalog":
        destination = Path(sys.argv[2])
        require(not destination.exists(), "fresh catalog path")
        destination.write_text(json.dumps(catalog(), indent=2) + "\n")
        print(
            json.dumps(
                dict(
                    cases=len(catalog()["cases"]),
                    sha256=hashlib.sha256(destination.read_bytes()).hexdigest(),
                )
            )
        )
        return 0
    require(
        sys.flags.isolated and sys.flags.dont_write_bytecode and not sys.flags.optimize,
        "pinned unoptimized -I -B",
    )
    extra = argparse.ArgumentParser(add_help=False)
    extra.add_argument("--rlp-wheel", type=Path, required=True)
    extra.add_argument("--types-wheel", type=Path, required=True)
    extra.add_argument("--catalog", type=Path, required=True)
    extra.add_argument("--preflight", action="store_true")
    own, remainder = extra.parse_known_args()
    sys.argv = [sys.argv[0]] + remainder
    dst = argparse.ArgumentParser(add_help=False)
    dst.add_argument("--output", type=Path, required=True)
    args, _ = dst.parse_known_args(remainder)
    out = args.output.resolve()
    log = out.parent / (out.stem + "-commands")
    log.mkdir(exist_ok=False)
    counter = 0

    def command(argv, cwd, stdin=None, env=None):
        nonlocal counter
        counter += 1
        d = log / f"{counter:04d}"
        d.mkdir()
        start = datetime.datetime.now(datetime.timezone.utc).isoformat()
        p = subprocess.run(argv, cwd=cwd, input=stdin, env=env, capture_output=True)
        for name, b in [("stdin", stdin or b""), ("stdout", p.stdout), ("stderr", p.stderr)]:
            (d / name).write_bytes(b)
        (d / "record.json").write_text(
            json.dumps(
                dict(
                    argv=[str(x) for x in argv],
                    cwd=str(cwd),
                    start_utc=start,
                    end_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                    exit=p.returncode,
                ),
                indent=2,
            )
            + "\n"
        )
        return p

    sys.path.insert(0, str(ROOT / "scripts"))
    sys.path.insert(0, str(ROOT / "STFSpec/Conformance/Codec"))
    from differential import Driver
    from rlp_typed_differential import RlpSourceAuth, RlpFreshFinder

    git_env = {
        **{k: v for k, v in os.environ.items() if not k.startswith("GIT_")},
        "GIT_NO_LAZY_FETCH": "1",
        "GIT_TERMINAL_PROMPT": "0",
    }

    class CapturedDriver(Driver):
        def git(self, *argv, input=None, text=False):
            p = command(
                ["git", "--no-replace-objects", "--no-optional-locks", *argv],
                self.eels,
                input,
                git_env,
            )
            require(p.returncode == 0, "reference Git read")
            return p.stdout.decode() if text else p.stdout

    context = CapturedDriver(__doc__, Path(__file__), DEFAULT_SEED)
    auth = RlpSourceAuth(context)
    sys.meta_path.insert(0, RlpFreshFinder(auth))
    dependency = []
    for pkg, wheel, digest in [
        (
            "ethereum_rlp",
            own.rlp_wheel,
            "f4144caa96b975720c62b967bbfd6c98601e95ee3c36457ece11ef4ce0cffa04",
        ),
        (
            "ethereum_types",
            own.types_wheel,
            "33de3e2a0c0e57ea1b67802485de556b92d557aae7c8c640070800f2b4f639e3",
        ),
    ]:
        require(hashlib.sha256(wheel.read_bytes()).hexdigest() == digest, "raw wheel identity")
        dist = importlib.metadata.distribution(pkg.replace("_", "-"))
        with zipfile.ZipFile(wheel) as z:
            raw = {
                n: z.read(n) for n in z.namelist() if n.startswith(pkg + "/") and n.endswith(".py")
            }
        require(
            set(Path(dist.locate_file(pkg)).rglob("*.py"))
            == {Path(dist.locate_file(n)) for n in raw},
            "installed .py inventory",
        )
        for n, b in raw.items():
            require(Path(dist.locate_file(n)).read_bytes() == b, "installed actual source bytes")
        dependency.append(
            dict(
                package=pkg,
                wheel=str(wheel),
                sha256=digest,
                installed={
                    n: dict(
                        path=str(dist.locate_file(n)),
                        sha256=hashlib.sha256(b).hexdigest(),
                        mode=oct(Path(dist.locate_file(n)).stat().st_mode & 0o777),
                    )
                    for n, b in raw.items()
                },
            )
        )
    from ethereum.forks.amsterdam import incremental_mpt as inc
    from ethereum import merkle_patricia_trie as mpt
    from ethereum.crypto import hash as hash_module
    from ethereum_rlp import rlp
    from ethereum_types.bytes import Bytes, Bytes32

    for mod, rel in [
        (inc, "ethereum/forks/amsterdam/incremental_mpt.py"),
        (mpt, "ethereum/merkle_patricia_trie.py"),
        (hash_module, "ethereum/crypto/hash.py"),
    ]:
        context.check_source(mod, rel)
    context.check_source(rlp, "ethereum_rlp/rlp.py", dependency=True)
    classes = (
        inc.MutableLeafNode,
        inc.MutableExtensionNode,
        inc.MutableBranchNode,
        inc.HashedNode,
    )
    functions = (
        inc._mpt_delete_node,
        inc._delete_from_extension,
        inc._delete_from_branch,
        inc._collapse_branch,
        inc._record_witness,
        inc._compute_node_hash_and_rlp,
        inc._encode_mutable_node,
        inc._encode_mutable_node_to_extended,
        mpt.nibble_list_to_compact,
        hash_module.keccak256,
        rlp.encode,
        inc._invalidate_hash,
    )
    held = [(id(f), id(f.__code__)) for f in functions]

    def code_data(c):
        def const(x):
            if isinstance(x, types.CodeType):
                return code_data(x)
            if isinstance(x, bytes):
                return dict(bytes=list(x))
            if isinstance(x, tuple):
                return [const(y) for y in x]
            return dict(type=type(x).__name__, repr=repr(x))

        return dict(
            bytecode=list(c.co_code),
            names=list(c.co_names),
            varnames=list(c.co_varnames),
            freevars=list(c.co_freevars),
            cellvars=list(c.co_cellvars),
            constants=[const(x) for x in c.co_consts],
            argcount=c.co_argcount,
            posonlyargcount=c.co_posonlyargcount,
            kwonlyargcount=c.co_kwonlyargcount,
            flags=c.co_flags,
            exceptiontable=list(c.co_exceptiontable),
        )

    def identity():
        context.check_clean()
        context.check_dependency()
        auth.check()
        require(
            classes
            == (
                inc.MutableLeafNode,
                inc.MutableExtensionNode,
                inc.MutableBranchNode,
                inc.HashedNode,
            ),
            "class replaced",
        )
        require(
            functions
            == (
                inc._mpt_delete_node,
                inc._delete_from_extension,
                inc._delete_from_branch,
                inc._collapse_branch,
                inc._record_witness,
                inc._compute_node_hash_and_rlp,
                inc._encode_mutable_node,
                inc._encode_mutable_node_to_extended,
                inc.nibble_list_to_compact,
                inc.keccak256,
                inc.rlp.encode,
                inc._invalidate_hash,
            ),
            "callable/global replaced",
        )
        require(held == [(id(f), id(f.__code__)) for f in functions], "held code replaced")
        require(Bytes is bytes and hash_module.Hash32 is Bytes32, "Bytes/Hash32 actual class")
        return dict(
            pin=context.head,
            original_index=context.git("ls-files", "--stage", "-z").decode(),
            original_status=context.git("status", "--porcelain", "--untracked-files=all").decode(),
            original_tree=context.git("ls-tree", "-rz", context.head).decode(),
            executable=sys.executable,
            version=sys.version,
            dependencies=dependency,
            classes=[
                dict(
                    module=c.__module__,
                    name=c.__qualname__,
                    id=id(c),
                    methods={
                        n: dict(
                            function_id=id(f),
                            code_id=id(f.__code__),
                            code_identity_v2=hashlib.sha256(
                                marshal.dumps(f.__code__, 2)
                            ).hexdigest(),
                            semantic_code=code_data(f.__code__),
                        )
                        for n, f in c.__dict__.items()
                        if type(f) is types.FunctionType
                    },
                )
                for c in classes
            ],
            functions=[
                dict(
                    module=f.__module__,
                    name=f.__qualname__,
                    function_id=id(f),
                    code_id=id(f.__code__),
                    filename=f.__code__.co_filename,
                    firstline=f.__code__.co_firstlineno,
                    code_identity_v2=hashlib.sha256(marshal.dumps(f.__code__, 2)).hexdigest(),
                    semantic_code=code_data(f.__code__),
                )
                for f in functions
            ],
        )

    def inputs(tag):
        dest = out.parent / (out.stem + "-inputs-" + tag)
        dest.mkdir()
        rows = []
        for name in [
            "src/ethereum/forks/amsterdam/incremental_mpt.py",
            "src/ethereum/merkle_patricia_trie.py",
            "src/ethereum/crypto/hash.py",
            "uv.lock",
        ]:
            p = context.eels / name
            b = p.read_bytes()
            oid = context.oracle_blobs[name]
            actual = command(
                ["git", "--no-replace-objects", "--no-optional-locks", "cat-file", "blob", oid],
                context.eels,
                env=git_env,
            )
            mode = command(
                [
                    "git",
                    "--no-replace-objects",
                    "--no-optional-locks",
                    "ls-files",
                    "--stage",
                    name,
                ],
                context.eels,
                env=git_env,
            )
            require(
                actual.returncode == mode.returncode == 0 and actual.stdout == b,
                "actual original blob bytes",
            )
            q = dest / name
            q.parent.mkdir(parents=True, exist_ok=True)
            q.write_bytes(b)
            rows.append(
                dict(
                    path=name,
                    blob=oid,
                    size=len(b),
                    sha256=hashlib.sha256(b).hexdigest(),
                    fs_mode=oct(p.stat().st_mode & 0o777),
                    git_index=mode.stdout.decode(),
                )
            )
        for entry in dependency:
            p = Path(entry["wheel"])
            b = p.read_bytes()
            require(hashlib.sha256(b).hexdigest() == entry["sha256"], "raw wheel changed")
            (dest / p.name).write_bytes(b)
            rows.append(
                dict(
                    path=p.name,
                    size=len(b),
                    sha256=hashlib.sha256(b).hexdigest(),
                    fs_mode=oct(p.stat().st_mode & 0o777),
                )
            )
            with zipfile.ZipFile(p) as z:
                for info in z.infolist():
                    if info.is_dir():
                        continue
                    data = z.read(info)
                    q = dest / p.stem / info.filename
                    q.parent.mkdir(parents=True, exist_ok=True)
                    q.write_bytes(data)
                    rows.append(
                        dict(
                            path=p.stem + "/" + info.filename,
                            size=len(data),
                            sha256=hashlib.sha256(data).hexdigest(),
                            zip_external_attr=info.external_attr,
                        )
                    )
            for name, meta in entry["installed"].items():
                data = Path(meta["path"]).read_bytes()
                require(
                    hashlib.sha256(data).hexdigest() == meta["sha256"], "installed code changed"
                )
                q = dest / "installed" / name
                q.parent.mkdir(parents=True, exist_ok=True)
                q.write_bytes(data)
                rows.append(
                    dict(
                        path="installed/" + name,
                        source_path=meta["path"],
                        size=len(data),
                        sha256=hashlib.sha256(data).hexdigest(),
                        fs_mode=oct(Path(meta["path"]).stat().st_mode & 0o777),
                    )
                )
        (dest / "manifest.json").write_text(json.dumps(rows, indent=2) + "\n")
        return rows

    payload = own.catalog.read_bytes()
    frozen = load_json(payload)
    require(frozen == catalog(), "catalog must equal the complete frozen generator")
    catalog_sha = hashlib.sha256(payload).hexdigest()

    def file_identity(path):
        p = Path(path)
        data = p.read_bytes()
        return dict(
            path=str(p),
            resolved=str(p.resolve()),
            size=len(data),
            sha256=hashlib.sha256(data).hexdigest(),
            mode=oct(p.stat().st_mode & 0o777),
        )

    def runtime_identity():
        crypto = importlib.metadata.distribution("pycryptodome")
        require(crypto.version == "3.23.0", "pinned crypto distribution")
        crypto_entries = {}
        records = []
        for entry in crypto.files or []:
            p = Path(crypto.locate_file(entry)).absolute()
            if entry.name == "RECORD":
                records.append(file_identity(p))
            if entry.parts and entry.parts[0] == "Crypto" and entry.hash is not None:
                data = p.read_bytes()
                require(
                    entry.hash.mode == "sha256" and entry.size == len(data), "crypto RECORD width"
                )
                digest = (
                    base64.urlsafe_b64encode(hashlib.sha256(data).digest()).decode().rstrip("=")
                )
                require(digest == entry.hash.value, "actual crypto RECORD bytes")
                crypto_entries[str(p)] = file_identity(p)
        require(len(records) == 1 and crypto_entries, "crypto RECORD/package inventory")
        loaded = []
        for name, module in sorted(sys.modules.items()):
            origin = getattr(module, "__file__", None)
            if origin is None or not Path(origin).is_file():
                continue
            p = Path(origin).absolute()
            if name.split(".", 1)[0] in ("ethereum", "ethereum_types", "ethereum_rlp", "Crypto"):
                require(p.resolve() == p, "loaded source alias")
                if name.startswith("ethereum.") or name == "ethereum":
                    relative = p.relative_to(context.eels).as_posix()
                    require(relative in context.oracle_blobs, "loaded original source inventory")
                    require(
                        context.git("hash-object", "--stdin", "--no-filters", input=p.read_bytes())
                        .decode()
                        .strip()
                        == context.oracle_blobs[relative],
                        "loaded original current bytes",
                    )
                loaded.append(dict(module=name, **file_identity(p)))
        mapped = []
        for line in Path("/proc/self/maps").read_text().splitlines():
            path = line.split()[-1]
            if path.startswith("/") and (
                "Crypto/" in path or "_hashlib" in path or "libcrypto" in path
            ):
                require(Path(path).is_file(), "actual mapped crypto file")
                entry = file_identity(path)
                if "Crypto/" in path:
                    require(
                        path in crypto_entries and entry == crypto_entries[path],
                        "mapped crypto authenticated RECORD",
                    )
                if entry not in mapped:
                    mapped.append(entry)
        require(mapped, "actual crypto backend map")
        startup = [file_identity(context.eels / ".venv/pyvenv.cfg")]
        import site

        for folder in site.getsitepackages():
            for p in sorted(Path(folder).glob("*.pth")):
                startup.append(file_identity(p))
        for name in ("sitecustomize", "usercustomize", "site", "_hashlib", "ssl"):
            module = sys.modules.get(name)
            p = getattr(module, "__file__", None)
            if p and Path(p).is_file():
                startup.append(file_identity(p))
        return dict(
            executable=file_identity(sys.executable),
            resolved_executable=file_identity(Path(sys.executable).resolve()),
            version=sys.version,
            prefix=sys.prefix,
            base_prefix=sys.base_prefix,
            flags=repr(sys.flags),
            startup=startup,
            sys_path=list(sys.path),
            loaded=loaded,
            crypto_version=crypto.version,
            crypto_RECORD=records,
            crypto_files=crypto_entries,
            mapped_crypto=mapped,
            use_hashlib=hash_module._USE_HASHLIB,
            actual_digest=dict(
                id=id(hash_module._keccak256_digest),
                code_identity_v2=hashlib.sha256(
                    marshal.dumps(hash_module._keccak256_digest.__code__, 2)
                ).hexdigest(),
                code=code_data(hash_module._keccak256_digest.__code__),
            ),
        )

    before = identity()
    before["runtime"] = runtime_identity()
    before["catalog_sha256"] = catalog_sha
    before["candidate_inputs"] = [
        file_identity(ROOT / name)
        for name in (
            "reference.toml",
            "STFSpec/Commit/Delete.lean",
            "STFSpec/Conformance/Commit/DeleteGuards.lean",
            "STFSpec/Conformance/Commit/DeleteCallerProofs.lean",
            "STFSpec/Conformance/Commit/delete_differential.py",
            "scripts/differential.py",
            "STFSpec/Conformance/Codec/rlp_typed_differential.py",
        )
    ]
    before_inputs = inputs("before")
    out.with_suffix(".before-identity.json").write_text(json.dumps(before, indent=2) + "\n")
    if own.preflight:
        after = identity()
        after["runtime"] = runtime_identity()
        require(before["runtime"] == after["runtime"], "preflight runtime identity changed")
        out.with_suffix(".preflight.json").write_text(
            json.dumps(
                dict(
                    schema=1,
                    catalog_sha256=catalog_sha,
                    cases=len(frozen["cases"]),
                    families=frozen["families"],
                    stages=frozen["stages"],
                    candidate_inputs=before["candidate_inputs"],
                    before=before,
                    after=after,
                    source_inputs=before_inputs,
                    original_protocol_executed=False,
                ),
                indent=2,
            )
            + "\n"
        )
        print(
            json.dumps(
                dict(
                    preflight=True,
                    cases=len(frozen["cases"]),
                    catalog_sha256=catalog_sha,
                    path=str(out.with_suffix(".preflight.json")),
                )
            )
        )
        return 0

    origin_labels = {}

    def label(node):
        if node is None:
            return None
        origin_labels.setdefault(id(node), len(origin_labels))
        return origin_labels[id(node)]

    def view(node):
        if node is None:
            return dict(tag=0)
        if type(node) is classes[3]:
            return dict(tag=1, hash=list(node._hash), origin=label(node))
        require(type(node) in classes[:3], "actual resolved class")
        require(type(node._dirty) is bool, "actual dirty Bool")
        common = dict(
            raw=None if node._rlp is None else list(node._rlp),
            hash=None if node._hash is None else list(node._hash),
            dirty=node._dirty,
            origin=label(node),
        )
        if type(node) is classes[0]:
            return dict(tag=2, path=list(node.rest_of_key), value=list(node.value), **common)
        if type(node) is classes[1]:
            return dict(tag=3, path=list(node.key_segment), child=view(node.child), **common)
        return dict(
            tag=4, children=[view(x) for x in node.children], value=list(node.value), **common
        )

    def build(node):
        tag = node["tag"]
        if tag == 0:
            return None
        if tag == 1:
            return inc.HashedNode(Bytes32(bytes(node["hash"])))
        common = dict(
            _rlp=None if node["raw"] is None else Bytes(node["raw"]),
            _hash=None if node["hash"] is None else Bytes32(bytes(node["hash"])),
            _dirty=node["dirty"],
        )
        if tag == 2:
            return inc.MutableLeafNode(Bytes(node["path"]), Bytes(node["value"]), **common)
        if tag == 3:
            return inc.MutableExtensionNode(Bytes(node["path"]), build(node["child"]), **common)
        return inc.MutableBranchNode(
            [build(x) for x in node["children"]], Bytes(node["value"]), **common
        )

    def arr(values):
        return [len(values), *values]

    def wire(node):
        tag = node["tag"]
        if tag == 0:
            return [0]
        if tag == 1:
            return [1, *node["hash"]]
        cache = [*arr(node["raw"] or []), *([0] if node["hash"] is None else [1, *node["hash"]])]
        if tag == 2:
            return [2, *arr(node["path"]), *arr(node["value"]), *cache]
        if tag == 3:
            return [3, *arr(node["path"]), *wire(node["child"]), *cache]
        return [
            4,
            len(node["children"]),
            *[n for child in node["children"] for n in wire(child)],
            *arr(node["value"]),
            *cache,
        ]

    def expression(node):
        def bs(values):
            return "(bytes [" + ",".join(map(str, values)) + "])"

        def hs(value):
            return (
                "(Hash32.ofBytes32 (FixedBytes.ofNat "
                + str(int.from_bytes(bytes(value), "big"))
                + "))"
            )

        tag = node["tag"]
        if tag == 0:
            return "none"
        if tag == 1:
            return "some (.hashed " + hs(node["hash"]) + ")"
        cache = (
            "(Enc.mk "
            + bs(node["raw"] or [])
            + " "
            + ("none" if node["hash"] is None else "(some " + hs(node["hash"]) + ")")
            + ")"
        )
        path = "(path [" + ",".join(map(str, node.get("path", []))) + "])"
        if tag == 2:
            return "some (.leaf " + path + " " + bs(node["value"]) + " " + cache + ")"
        if tag == 3:
            require(node["child"]["tag"] != 0, "represented extension child")
            return "some (.ext " + path + " (" + expression(node["child"])[5:] + ") " + cache + ")"
        return (
            "some (.branch #["
            + ",".join(expression(c) for c in node["children"])
            + "] "
            + bs(node["value"])
            + " "
            + cache
            + ")"
        )

    def model(root, key, recording=False):
        result = deletion_model(root, key, hash_module.keccak256, recording)
        return result["error"] or [0, *wire(result["node"])], result["queries"], result["counter"]

    journal = out.with_suffix(".source-journal.jsonl")
    with journal.open("x"):
        pass

    def record(row):
        row = dict(
            row,
            catalog_sha256=catalog_sha,
            driver_sha256=next(
                x["sha256"]
                for x in before["candidate_inputs"]
                if x["path"] == str(Path(__file__).resolve())
            ),
        )
        with journal.open("a") as stream:
            stream.write(json.dumps(row) + "\n")
            stream.flush()
            os.fsync(stream.fileno())

    guards = (ROOT / "STFSpec/Conformance/Commit/DeleteGuards.lean").read_text()
    observer = guards[
        guards.index("private def wireBytes") : guards.index("private def branchItemReference")
    ]
    recording_support = guards[
        guards.index("private abbrev Trace") : guards.index("private def expected")
    ]
    emit = guards[
        guards.index("private def emit") : guards.index(
            "\nend STFSpec.Conformance.Commit.DeleteGuards"
        )
    ]
    lean_header = (
        "import STFSpec.Commit.Delete\n"
        "open STFSpec.Base STFSpec.Codec STFSpec.Hash STFSpec.Commit\n"
        + "private def bytes (xs : List UInt8) : ByteArray := xs.toByteArray\n"
        + "private def path (xs : List (Fin 16)) : Nibbles := Nibbles.ofList xs\n"
        + "private def answer (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)\n"
        + observer
        + recording_support
        + emit
    )
    observations = []
    for descriptor in frozen["cases"]:
        index = descriptor["case"]
        origin_labels.clear()
        root = build(descriptor["root"])
        if descriptor["boundary"] == "alias":
            root.children[1] = root.children[0]
        source_before = view(root)
        state = inc.IncrementalMPT(secured=False, default=Bytes(b""), root_node=root)
        calls, events, throws, stages, visited_returns = [], [], [], [], []
        stage, result, immediate, error = "immediate-deletion", None, None, None
        codes = {f.__code__: f.__qualname__ for f in functions}

        def trace(frame, event, arg):
            if frame.f_code is hash_module.keccak256.__code__:
                if event == "call":
                    calls.append(
                        dict(
                            stage=stage,
                            ordinal=len(calls),
                            preimage=list(frame.f_locals["buffer"]),
                            answer=None,
                        )
                    )
                elif event == "return":
                    calls[-1]["answer"] = None if arg is None else list(arg)
            if frame.f_code in codes and event in ("call", "return", "exception"):
                item = dict(
                    stage=stage,
                    function=codes[frame.f_code],
                    event=event,
                    file=frame.f_code.co_filename,
                    line=frame.f_lineno,
                )
                if "node" in frame.f_locals:
                    item["node"] = view(frame.f_locals["node"])
                if event == "return" and frame.f_code in (
                    inc._mpt_delete_node.__code__,
                    inc._delete_from_extension.__code__,
                    inc._delete_from_branch.__code__,
                    inc._collapse_branch.__code__,
                ):
                    item["returned"] = view(arg)
                    if frame.f_code is inc._mpt_delete_node.__code__ and arg is not None:
                        visited_returns.append(arg)
                if event == "exception":
                    exception = dict(
                        stage=stage,
                        function=codes[frame.f_code],
                        file=frame.f_code.co_filename,
                        line=frame.f_lineno,
                        module=arg[0].__module__,
                        name=arg[0].__qualname__,
                        args=[dict(type=type(a).__name__, repr=repr(a)) for a in arg[1].args],
                        message=str(arg[1]),
                    )
                    throws.append(exception)
                    item["exception"] = exception
                events.append(item)
            return trace

        record(dict(phase="before", case=index, descriptor=descriptor, input=source_before))
        previous = sys.gettrace()
        sys.settrace(trace)
        try:
            try:
                from ethereum_types.numeric import Uint

                result = inc._mpt_delete_node(state, root, Bytes(descriptor["key"]), Uint(0))
                immediate = view(result)
                # Each surviving entered original deletion return, including
                # detached returns later spliced into a fresh parent, is
                # materialized bottom-up after the immediate protocol stage.
                # Applicable immediate witnessing queries remain separately
                # recorded; this is not original/nominal history equivalence.
                schedule = visited_returns
                for ordinal, node in enumerate(schedule):
                    stage = "separate-own-completion-" + str(ordinal)
                    item = dict(
                        stage=stage,
                        origin=label(node),
                        before=view(node),
                        root_before=view(root),
                        result_before=view(result),
                    )
                    answer_hash, answer_raw = inc._compute_node_hash_and_rlp(node)
                    item.update(
                        after=view(node),
                        returned_raw=list(answer_raw),
                        returned_hash=None if answer_hash is None else list(answer_hash),
                        root_after=view(root),
                        result_after=view(result),
                    )
                    stages.append(item)
            except Exception as exception:
                error = dict(
                    stage=stage,
                    module=type(exception).__module__,
                    name=type(exception).__qualname__,
                    message=str(exception),
                    args=[dict(type=type(a).__name__, repr=repr(a)) for a in exception.args],
                    traceback=traceback.format_exc(),
                )
        finally:
            sys.settrace(previous)
        row = dict(
            phase="original-returned",
            case=index,
            descriptor=descriptor,
            input=source_before,
            immediate=immediate,
            input_after=view(root),
            source_after=view(result),
            error=error,
            materializations=stages,
            queries=calls,
            events=events,
            throws=throws,
            witness=[
                dict(hash=list(h), raw=list(raw))
                for h, raw in state.witness.accessed_nodes.items()
            ],
        )
        record(row)
        # Extension-None and aliases have no admitted equality image. Keep complete
        # original boundary stages without inventing a nominal input or replay.
        if descriptor["boundary"] in ("extension-None", "alias"):
            row = dict(
                row,
                phase="complete",
                source_bridge=False,
                expected=None,
                actual=None,
                scope="source boundary only; outside selected nominal relation",
            )
            record(row)
            observations.append(row)
            continue
        expected_id, id_queries, _ = model(row["input"], descriptor["key"])
        expected_state, state_queries, number = model(row["input"], descriptor["key"], True)
        expected_error = (
            "AssertionError"
            if expected_id[0] == 3 or expected_id[:2] == [2, 9]
            else "IndexError"
            if expected_id[:2] == [2, 11]
            else None
        )
        high_boundary = str(descriptor["boundary"]).startswith("high-survivor-")
        if not high_boundary:
            require(
                (row["error"] is None) == (expected_error is None),
                "original success/error dispatch",
            )
            if expected_error:
                require(
                    row["error"]["stage"] == "immediate-deletion"
                    and row["error"]["name"] == expected_error,
                    "actual first exception class/stage",
                )
        elif expected_id[:2] != [2, 12]:
            raise ValueError("high survivor must retain exact nominal collapseIndex")
        premise = premise_map([descriptor])["cases"][0]
        bridge = (
            descriptor["boundary"] is None
            and expected_error is None
            and premise["local_guard_eligible"]
            and premise["embedding_eligible"]
        )
        if bridge:
            require(
                expected_id == [0, *wire(row["source_after"])],
                "full completed original value/cache image",
            )
        if descriptor["helper"] in ("leaf", "ext", "branch"):
            require(
                row["source_after"]["raw"] == descriptor["expected_own_raw"],
                "actual helper raw boundary",
            )
        case_expression = (
            "("
            + expression(row["input"])
            + ",(path ["
            + ",".join(map(str, descriptor["key"]))
            + "]))"
        )
        case_module = out.parent / (out.stem + "-case" + str(index).zfill(4) + ".lean")
        require(not case_module.exists(), "fresh failed/unstarted Lean phase destination")
        case_module.write_text(lean_header + "\n#eval emit [" + case_expression + "]\n")
        execution = command(["lake", "env", "lean", str(case_module)], ROOT)
        require(execution.returncode == 0, "full public deletion observer at " + str(index))
        got = parse_records(execution.stdout.decode(), 1)[0]
        expected = dict(
            case=0,
            input=wire(row["input"]),
            key=descriptor["key"],
            result=expected_id,
            stateResult=expected_state,
            queries=[arr([0, 255, 66])] + [arr(q["preimage"]) for q in state_queries],
            answers=[list((199).to_bytes(32, "big"))] + [q["answer"] for q in state_queries],
            counter=number,
        )
        require(got == expected, "complete Id/State frame differs at " + str(index))
        row = dict(
            row,
            phase="complete",
            source_bridge=bridge,
            expected=expected,
            actual=got,
            expression=case_expression,
            id_model_queries=id_queries,
            state_model_queries=state_queries,
            generated_module=file_identity(case_module),
        )
        record(row)
        observations.append(row)

    after = identity()
    after["runtime"] = runtime_identity()
    require(before["runtime"] == after["runtime"], "actual runtime/source/crypto identity changed")
    after_inputs = inputs("after")
    require(before_inputs == after_inputs, "original focused sources/wheels changed")
    require(
        before["candidate_inputs"]
        == [
            file_identity(ROOT / name)
            for name in (
                "reference.toml",
                "STFSpec/Commit/Delete.lean",
                "STFSpec/Conformance/Commit/DeleteGuards.lean",
                "STFSpec/Conformance/Commit/DeleteCallerProofs.lean",
                "STFSpec/Conformance/Commit/delete_differential.py",
                "scripts/differential.py",
                "STFSpec/Conformance/Codec/rlp_typed_differential.py",
            )
        ],
        "frozen candidate phase inputs changed",
    )
    out.with_suffix(".after-identity.json").write_text(json.dumps(after, indent=2) + "\n")
    out.with_suffix(".observations.json").write_text(
        json.dumps(
            dict(schema=1, cases=observations, before_identity=before, after_identity=after),
            indent=2,
        )
        + "\n"
    )
    out.write_text(
        "-- Complete per-case deletion observers are retained beside this summary.\n"
        + "-- Every case executes freshly; its journal retains actual original phases.\n"
    )
    print(
        json.dumps(
            dict(
                cases=len(observations),
                source_bridges=sum(r["source_bridge"] for r in observations),
                original_queries=sum(len(r["queries"]) for r in observations),
                catalog_sha256=catalog_sha,
                pin=context.head,
            )
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
