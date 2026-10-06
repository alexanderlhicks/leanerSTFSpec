#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Bounded original insertion, separate strict completion, and full nominal frames.

Freeze --write-catalog and --preflight artifacts before original execution. Use
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
            require(value[0] != 0, "absent insertion success")
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
        fields = {
            "case",
            "input",
            "key",
            "value",
            "result",
            "stateResult",
            "queries",
            "answers",
            "counter",
        }
        require(type(row) is dict and set(row) == fields, "reply fields")
        require(natural(row["case"]) == index, "case order")
        for key, bound in (("key", 16), ("value", 256)):
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
    with tempfile.TemporaryDirectory(prefix="update-resume-control-") as folder:
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


def validate_source_error(row, expected):
    """Cross-check typed payloads against the first actual originating source throw."""
    require(row["throws"], "missing originating exception frame")
    first = row["throws"][0]
    function = "_invalidate_hash" if expected[0] == 3 else "_insert_into_branch"
    require(
        first["stage"] == "immediate-insertion" and first["function"] == function,
        "unexpected originating error frame",
    )
    require(first.get("error_payload") == expected, "actual source error payload differs")


def source_error_tests():
    """Bounded snapshot controls; actual EELS frames are checked in a fresh run."""
    controls = 0
    for function, expected in (
        ("_invalidate_hash", [3, *range(32)]),
        ("_insert_into_branch", [2, 11, 15, 1]),
    ):
        good = dict(stage="immediate-insertion", function=function, error_payload=expected)
        validate_source_error(dict(throws=[good]), expected)
        bad_payloads = [[], expected[:-1], [*expected, 0]]
        for index in range(1 if expected[0] == 3 else 2, len(expected)):
            changed = expected.copy()
            changed[index] += 1
            bad_payloads.append(changed)
        bad = [dict(good, error_payload=payload) for payload in bad_payloads]
        bad += [
            dict(good, stage="separate-own-completion-0"),
            dict(good, function="_mpt_insert_node"),
            {key: value for key, value in good.items() if key != "error_payload"},
        ]
        for first in bad:
            try:
                validate_source_error(dict(throws=[first, good]), expected)
            except ValueError:
                controls += 1
                continue
            raise RuntimeError("wrong first source error payload accepted")
        try:
            validate_source_error(dict(throws=[]), expected)
        except ValueError:
            controls += 1
        else:
            raise RuntimeError("missing source error frame accepted")
    return controls


def parser_tests():
    h = list(range(32))
    leaf = [2, 1, 15, 2, 0, 255, 2, 193, 128, 1, *h]
    tree = [3, 0, 4, 3, 0, 1, *h, *leaf, 2, 0, 255, 0, 0, 0, 0]
    good = dict(
        case=0,
        input=tree,
        key=[15, 0],
        value=[0, 255],
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
        ("value", [256]),
        ("value", [False]),
        ("input", [3, 0, 0, 0, 0]),
        ("result", [0, 0]),
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
        raise RuntimeError("invalid complete update frame accepted: " + text)
    resume_cli_tests()
    source_error_tests()
    print(json.dumps(dict(accepted=len(positive), rejected=len(bad), optimized=sys.flags.optimize)))


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
    def h(n):
        return list(n.to_bytes(32, "big"))

    def leaf(path=(), value=(), cache="arbitrary"):
        node = dict(
            tag=2, path=list(path), value=list(value), raw=[255, 0], hash=h(91), dirty=False
        )
        if cache == "inline":
            node.update(raw=list(rlp_bytes(current_item(dict(node, hash=None)))), hash=None)
        return node

    def ext(path, child):
        return dict(tag=3, path=list(path), child=child, raw=[255], hash=h(42), dirty=False)

    def branch(children, value=()):
        return dict(
            tag=4, children=children, value=list(value), raw=[0, 255], hash=h(61), dirty=False
        )

    none, stub = dict(tag=0), dict(tag=1, hash=h(17))
    rows = []

    def add(family, root, key=(), value=(), boundary=None, helper=None):
        row = dict(
            case=len(rows),
            family=family,
            root=root,
            key=list(key),
            value=list(value),
            boundary=boundary,
            helper=helper,
            stages=["O-A", "O-B", "O-C", "O-D", "O-E"],
        )
        if boundary:
            row["stages"].append("O-F")
        if helper:
            row["stages"].append("O-G")
        if helper == "leaf":
            row["expected_own_raw"] = list(rlp_bytes([compact(key, True), bytes(value)]))
        elif helper == "ext":
            row["expected_own_raw"] = list(
                rlp_bytes([compact(root["path"], False), [compact([], True), bytes(value)]])
            )
        elif helper == "branch":
            row["expected_own_raw"] = list(rlp_bytes([bytes(value)]))
        if "expected_own_raw" in row:
            require(
                len(row["expected_own_raw"]) in (31, 32, 33), "constructed catalog raw boundary"
            )
        rows.append(row)

    for key in ([], [0], [15, 0]):
        for size in (0, 1, 40):
            add("U01", none, key, [255] * size)
        add("U02", stub, key)
        for size in (0, 1, 40):
            add("U03", leaf(key, [0, 255]), key, [0] * size)
    pairs = [
        ([0], [15]),
        ([0, 15, 0], [0, 15, 1]),
        ([], [0]),
        ([0], []),
        ([0, 15, 0, 15, 1], [0, 15, 0, 15, 2]),
    ]
    for family, (old, key) in zip(range(4, 9), pairs):
        for old_size in (0, 2, 40):
            for new_size in (0, 1, 40):
                add(f"U{family:02d}", leaf(old, [0] * old_size), key, [255] * new_size)
    variants = [leaf([0, 15]), ext([], leaf([0])), branch([none, stub, leaf([])], [0, 255]), stub]
    for child in variants:
        for family, prefix in ((9, [0, 15]), (10, [])):
            add(f"U{family:02d}", ext(prefix, child), prefix + [0, 15])
        for family in (11, 12):
            add(f"U{family:02d}", ext([], ext([], child)), [0, 15], [0, 255])
        for family, (old, key) in zip(
            (13, 14, 15, 16, 17, 17),
            [
                ([0], [15]),
                ([0, 1], [15]),
                ([0, 15], [0, 1]),
                ([0, 15, 0], [0, 1]),
                ([0, 15], []),
                ([0, 15], [0]),
            ],
        ):
            for value in ([], [0, 255]):
                add(f"U{family:02d}", ext(old, child), key, value)
    for arity in (0, 1, 15, 16, 17, 257):
        for family, child in ((18, none), (19, leaf([], [], "inline")), (20, stub)):
            for old in ([], [0, 255]):
                for new in ([], old, [1]):
                    add(f"U{family:02d}", branch([child] * arity, old), [], new)
        for digit in (0, 14, 15):
            for family, child in ((21, none), (22, leaf([])), (23, stub)):
                children = [none] * arity
                if digit < arity:
                    children[digit] = child
                add(f"U{family:02d}", branch(children, [0, 255]), [digit], [0, 255])
            if digit >= arity:
                add("U24", branch([none] * arity), [digit])
    for arity in (1, 15, 16, 17, 257):
        for child in variants:
            children = [child] * arity
            children[0] = none
            add("U25", branch(children, [255]), [0, 15], [0, 255])
    add("U26", branch([]), [0])
    add("U26", ext([0], branch([])), [0, 15])
    add("U26", ext([0], stub), [15])
    for size in (28, 29, 30):
        add("U27", none, [], [0] * size, helper="leaf")
    for size in (50, 52, 54):
        add("U27", ext([0] * size, leaf([], [], "inline")), [0] * size, helper="ext")
    for size in (29, 30, 31):
        add("U27", branch([]), [], [0] * size, helper="branch")
    for shared in (1, 2, 49, 50, 51, 110, 111, 510, 511):
        for size in (52, 53, 54, 253, 254, 255, 256):
            add(
                "U28",
                leaf([0] * shared + [1], [0] * size),
                [0] * shared + [15],
                [255] * size,
                helper="joined-prefix",
            )
    # U29–31 are also observed concretely; arbitrary/repeated/failing queries and
    # the syntax-sensitive carrier are additionally Lean-only controls.
    chain = ext([0, 15], ext([], leaf([0, 1], [0] * 40)))
    for family in ("U29", "U30", "U31"):
        add(family, chain, [0, 15, 0, 2], [255] * 40)
    for name in ("dirty-cached-hash", "hashless-long", "missing-inline-raw", "stale-inline-raw"):
        child = leaf([], [0, 255], "inline")
        if name == "dirty-cached-hash":
            child.update(dirty=True, hash=h(83))
        if name == "hashless-long":
            child.update(value=[0] * 40, raw=[255] * 33)
        if name == "missing-inline-raw":
            child["raw"] = None
        if name == "stale-inline-raw":
            child["raw"] = [255]
        add("U25", branch([none, child]), [0], [0, 255], boundary=name)
    add("U09", ext([], none), [0], boundary="extension-None")
    add("U20", branch([leaf([], [], "inline")] * 2), [], [0], boundary="alias")
    result = dict(
        schema=1,
        pin="e1a316a06fc3d3e0a5da36fdc78580811e9d8a36",
        cases=rows,
        families=[f"U{i:02d}" for i in range(1, 32)],
        stages=[f"O-{c}" for c in "ABCDEFG"],
        lean_only=[
            "arbitrary-distinct/repeated-answer",
            "each-first-query-error-both-transformers",
            "nonlawful-count-carrier-and-negative-association",
        ],
        relation=(
            "finite acyclic nonaliasing represented trees; local consulted clean hashes or "
            "coherent short inline; present equal retained raw/hash for full cache comparison; "
            "complete Encodable; actual Id Keccak and finite host"
        ),
    )
    require({r["family"] for r in rows} == set(result["families"]), "complete family catalog")
    return result


def main():
    reject_resume(sys.argv[1:])
    if sys.argv[1:] == ["--self-test"]:
        parser_tests()
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

    context = CapturedDriver(__doc__, Path(__file__), 184)
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
    classes = (inc.MutableLeafNode, inc.MutableExtensionNode, inc.MutableBranchNode, inc.HashedNode)
    functions = (
        inc._mpt_insert_node,
        inc._insert_into_leaf,
        inc._create_branch_from_two_leaves,
        inc._insert_into_extension,
        inc._split_extension,
        inc._insert_into_branch,
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
                inc._mpt_insert_node,
                inc._insert_into_leaf,
                inc._create_branch_from_two_leaves,
                inc._insert_into_extension,
                inc._split_extension,
                inc._insert_into_branch,
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
                ["git", "--no-replace-objects", "--no-optional-locks", "ls-files", "--stage", name],
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
            "STFSpec/Commit/Update.lean",
            "STFSpec/Conformance/Commit/UpdateGuards.lean",
            "STFSpec/Conformance/Commit/update_differential.py",
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

    def lcp(left, right):
        size = 0
        while size < min(len(left), len(right)) and left[size] == right[size]:
            size += 1
        return size

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

    def model(root, key, value, recording=False):
        queries, counter = [], 7

        def fresh(node):
            nonlocal counter
            raw = rlp_bytes(current_item(node))
            node.update(raw=list(raw), hash=None, dirty=False)
            if len(raw) >= 32:
                answer = counter.to_bytes(32, "big") if recording else hash_module.keccak256(raw)
                queries.append(dict(preimage=list(raw), answer=list(answer), ordinal=counter))
                node["hash"] = list(answer)
                counter += 1
            return node

        def insert(node, key):
            tag = node["tag"]
            if tag == 0:
                return fresh(dict(tag=2, path=key, value=value)), None
            if tag == 1:
                return None, [3, *node["hash"]]
            if tag == 2 and node["path"] == key:
                return fresh(dict(tag=2, path=node["path"], value=value)), None
            if tag in (2, 3):
                shared = lcp(node["path"], key)
                if tag == 3 and shared == len(node["path"]):
                    child, error = insert(node["child"], key[shared:])
                    if error:
                        return None, error
                    return fresh(dict(tag=3, path=node["path"], child=child)), None
                old_tail, new_tail = node["path"][shared:], key[shared:]
                children, terminal = [dict(tag=0) for _ in range(16)], []
                if tag == 2:
                    if old_tail:
                        children[old_tail[0]] = fresh(
                            dict(tag=2, path=old_tail[1:], value=node["value"])
                        )
                    else:
                        terminal = node["value"]
                else:
                    require(old_tail, "extension suffix nonempty")
                    children[old_tail[0]] = (
                        node["child"]
                        if len(old_tail) == 1
                        else fresh(dict(tag=3, path=old_tail[1:], child=node["child"]))
                    )
                if new_tail:
                    if old_tail:
                        require(old_tail[0] != new_tail[0], "maximal-prefix slot distinction")
                    children[new_tail[0]] = fresh(dict(tag=2, path=new_tail[1:], value=value))
                else:
                    terminal = value
                result = fresh(dict(tag=4, children=children, value=terminal))
                if shared:
                    result = fresh(dict(tag=3, path=node["path"][:shared], child=result))
                return result, None
            if not key:
                return fresh(dict(tag=4, children=node["children"], value=value)), None
            digit = key[0]
            if digit >= len(node["children"]):
                return None, [2, 11, digit, len(node["children"])]
            child, error = insert(node["children"][digit], key[1:])
            if error:
                return None, error
            children = node["children"].copy()
            children[digit] = child
            return fresh(dict(tag=4, children=children, value=node["value"])), None

        result, error = insert(load_json(json.dumps(root)), key)
        return error or [0, *wire(result)], queries, counter

    def completion_schedule(before_node, key, result):
        tag = before_node["tag"]
        if tag in (0, 2) and (tag == 0 or before_node["path"] == key):
            return [result]
        if tag in (2, 3):
            shared = lcp(before_node["path"], key)
            if tag == 3 and shared == len(before_node["path"]):
                return completion_schedule(before_node["child"], key[shared:], result.child) + [
                    result
                ]
            branch_node = result.child if shared else result
            old_tail, new_tail = before_node["path"][shared:], key[shared:]
            schedule = []
            if old_tail and (tag == 2 or len(old_tail) > 1):
                schedule.append(branch_node.children[old_tail[0]])
            if new_tail:
                schedule.append(branch_node.children[new_tail[0]])
            schedule.append(branch_node)
            if shared:
                schedule.append(result)
            return schedule
        require(tag == 4, "successful source completion node")
        if not key:
            return [result]
        return completion_schedule(
            before_node["children"][key[0]], key[1:], result.children[key[0]]
        ) + [result]

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

    guards = (ROOT / "STFSpec/Conformance/Commit/UpdateGuards.lean").read_text()
    observer = guards[guards.index("private def wireBytes") : guards.index("private def complete")]
    recording_support = guards[
        guards.index("private abbrev Trace") : guards.index("private def expected")
    ]
    emit = guards[
        guards.index("private def emit") : guards.index(
            "\nend STFSpec.Conformance.Commit.UpdateGuards"
        )
    ]
    lean_header = (
        "import STFSpec.Commit.Update\n"
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
        calls, events, throws, stages = [], [], [], []
        stage, result, immediate, error = "immediate-insertion", None, None, None
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
                    inc._mpt_insert_node.__code__,
                    inc._insert_into_leaf.__code__,
                    inc._insert_into_extension.__code__,
                    inc._split_extension.__code__,
                    inc._create_branch_from_two_leaves.__code__,
                    inc._insert_into_branch.__code__,
                ):
                    item["returned"] = view(arg)
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
                    if frame.f_code is inc._invalidate_hash.__code__ and arg[0] is AssertionError:
                        exception["error_payload"] = [3, *frame.f_locals["node"]._hash]
                    elif frame.f_code is inc._insert_into_branch.__code__ and arg[0] is IndexError:
                        exception["error_payload"] = [
                            2,
                            11,
                            int(frame.f_locals["child_idx"]),
                            len(frame.f_locals["node"].children),
                        ]
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

                result = inc._mpt_insert_node(
                    state, root, Bytes(descriptor["key"]), Bytes(descriptor["value"]), Uint(0)
                )
                immediate = view(result)
                require(not calls, "immediate insertion must make no original Keccak query")
                schedule = completion_schedule(source_before, descriptor["key"], result)
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
            source_after=None if result is None else view(result),
            error=error,
            materializations=stages,
            queries=calls,
            events=events,
            throws=throws,
            witness=[
                dict(hash=list(h), raw=list(raw)) for h, raw in state.witness.accessed_nodes.items()
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
        expected_id, id_queries, _ = model(row["input"], descriptor["key"], descriptor["value"])
        expected_state, state_queries, number = model(
            row["input"], descriptor["key"], descriptor["value"], True
        )
        expected_error = (
            "AssertionError"
            if expected_id[0] == 3
            else "IndexError"
            if expected_id[:2] == [2, 11]
            else None
        )
        require(
            (row["error"] is None) == (expected_error is None), "original success/error dispatch"
        )
        if expected_error:
            require(
                row["error"]["stage"] == "immediate-insertion"
                and row["error"]["name"] == expected_error,
                "actual first exception class/stage",
            )
            require(not row["queries"], "typed adaptation original query prefix")
            validate_source_error(row, expected_id)
        bridge = descriptor["boundary"] is None and expected_error is None
        if bridge:
            require(
                expected_id == [0, *wire(row["source_after"])],
                "full completed original value/cache image",
            )
            # Python may rehash a dirty child in later embedding. Its complete
            # query history is recorded, never equated to the strict Lean history.
        if descriptor["helper"] in ("leaf", "ext", "branch"):
            require(
                row["source_after"] is not None
                and row["source_after"]["raw"] == descriptor["expected_own_raw"],
                "actual helper raw boundary",
            )
        case_expression = (
            "("
            + expression(row["input"])
            + ",(path ["
            + ",".join(map(str, descriptor["key"]))
            + "]),"
            + "(bytes ["
            + ",".join(map(str, descriptor["value"]))
            + "]))"
        )
        case_module = out.parent / (out.stem + "-case" + str(index).zfill(4) + ".lean")
        require(not case_module.exists(), "fresh failed/unstarted Lean phase destination")
        case_module.write_text(lean_header + "\n#eval emit [" + case_expression + "]\n")
        execution = command(["lake", "env", "lean", str(case_module)], ROOT)
        require(execution.returncode == 0, "full public insertion observer at " + str(index))
        got = parse_records(execution.stdout.decode(), 1)[0]
        expected = dict(
            case=0,
            input=wire(row["input"]),
            key=descriptor["key"],
            value=descriptor["value"],
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
                "STFSpec/Commit/Update.lean",
                "STFSpec/Conformance/Commit/UpdateGuards.lean",
                "STFSpec/Conformance/Commit/update_differential.py",
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
        "-- Complete per-case insertion observers are retained beside this summary.\n"
        + "-- Every case executes freshly; the journal retains actual original phases.\n"
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
