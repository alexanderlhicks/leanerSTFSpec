#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Original-source child references with complete recursive-item comparisons.

Use frozen EELS/.venv/bin/python -I -B, --eels, --output EXTERNAL.lean,
--rlp-wheel and --types-wheel. Actual source classes/helpers/hash are authenticated
and observed, never replaced. Conditional source-value cases are separate from
dirty/cache and query boundary controls; no pure action/cache refinement is claimed.
--self-test runs strict complete recursive input/item framing tests, also with -O.
"""

import argparse
import datetime
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import tomllib
import traceback
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


class Reader:
    def __init__(self, values):
        require(type(values) is list, "wire must be a list")
        self.values, self.offset = values, 0

    def take(self):
        require(self.offset < len(self.values), "truncated field")
        x = natural(self.values[self.offset])
        self.offset += 1
        return x

    def octets(self, count, bound=256):
        require(count <= len(self.values) - self.offset, "truncated bytes")
        xs = [self.take() for _ in range(count)]
        require(all(x < bound for x in xs), "out of range field")
        return xs

    def array(self, bound=256):
        return self.octets(self.take(), bound)

    def item(self):
        tag = self.take()
        require(tag in (0, 1), "unknown item tag")
        if tag == 0:
            return (0, self.array())
        n = self.take()
        require(n <= len(self.values) - self.offset, "truncated list")
        return (1, [self.item() for _ in range(n)])

    def cache(self):
        raw = self.array()
        tag = self.take()
        require(tag in (0, 1), "unknown hash option")
        return raw, None if tag == 0 else self.octets(32)

    def ref(self):
        tag = self.take()
        require(tag in range(5), "unknown Ref tag")
        if tag == 0:
            return (0,)
        if tag == 1:
            return (1, self.octets(32))
        if tag == 2:
            return (2, self.array(16), self.array(), self.cache())
        if tag == 3:
            path, child = self.array(16), self.ref()
            require(child[0] != 0, "extension child cannot be absent")
            return (3, path, child, self.cache())
        n = self.take()
        require(n <= len(self.values) - self.offset, "truncated children")
        children = [self.ref() for _ in range(n)]
        return (4, children, self.array(), self.cache())

    def finish(self):
        require(self.offset == len(self.values), "trailing wire fields")


def parse_records(text, count):
    lines = text.splitlines()
    require(len(lines) == count, "missing/trailing records")
    rows = []
    for i, line in enumerate(lines):
        row = json.loads(line, object_pairs_hook=object_pairs)
        require(
            type(row) is dict and set(row) == {"case", "input", "result"},
            "unknown/missing reply field",
        )
        require(natural(row["case"]) == i, "wrong case order")
        inp = Reader(row["input"])
        inp.ref()
        inp.finish()
        out = Reader(row["result"])
        out.item()
        out.finish()
        rows.append(row)
    return rows


def parser_tests():
    # All Ref constructors, both optional hashes, arbitrary children and nested items.
    h = list(range(32))
    cache = [2, 0, 255, 1, *h]
    # Build valid framing explicitly to keep tests independent of reply parser.
    leaf = [2, 1, 15, 2, 0, 255, *cache]
    ext = [3, 0, 2, 0, 0, 0, 0, 0, 0]
    inp = [4, 4, 0, 1, *h, *leaf, *ext, 2, 0, 255, 0, 0]
    good = dict(case=0, input=inp, result=[1, 3, 0, 3, 0, 255, 0, 1, 0, 0, 32, *h])
    empty = dict(case=0, input=[0], result=[0, 0])
    require(
        parse_records(json.dumps(good), 1) == [good], "complete nested record rejected"
    )
    require(parse_records(json.dumps(empty), 1) == [empty], "empty record rejected")
    bad = [
        "",
        json.dumps(good) + "\n" + json.dumps(good),
        json.dumps(dict(good, extra=0)),
        '{"case":0,"case":0,"input":[0],"result":[0,0]}',
        json.dumps(dict(good, case=1)),
        json.dumps(dict(good, input=[9])),
        json.dumps(dict(good, result=[9])),
        json.dumps(dict(good, result=[0, 1, 256])),
    ]
    for name in ("input", "result"):
        for cut in range(len(good[name])):
            bad.append(json.dumps(dict(good, **{name: good[name][:cut]})))
        bad.append(json.dumps(dict(good, **{name: good[name] + [0]})))
        for pos in range(len(good[name])):
            for invalid in (True, -1, 0.0):
                xs = good[name].copy()
                xs[pos] = invalid
                bad.append(json.dumps(dict(good, **{name: xs})))
    for invalid in (True, -1, 0.0):
        bad.append(json.dumps(dict(good, case=invalid)))
    bad += [
        json.dumps(dict(good, input=[2, 1, 16, 0, 0, 0])),
        json.dumps(dict(good, input=[2, 0, 0, 0, 2])),
        json.dumps(dict(good, input=[3, 0, 0, 0, 0])),
        json.dumps(dict(good, result=[1, 2, 0, 0])),
    ]
    swapped = json.dumps(dict(good, case=1)) + "\n" + json.dumps(good)
    bad.append(swapped)
    for text in bad:
        try:
            parse_records(text, 2 if text == swapped else 1)
        except (ValueError, TypeError, json.JSONDecodeError):
            continue
        raise RuntimeError("invalid reply accepted: " + text)
    print(json.dumps(dict(accepted=2, rejected=len(bad), optimized=sys.flags.optimize)))


def main():
    if sys.argv[1:] == ["--self-test"]:
        parser_tests()
        return 0
    require(
        sys.flags.isolated and sys.flags.dont_write_bytecode and not sys.flags.optimize,
        "use frozen unoptimized -I -B interpreter",
    )
    extra = argparse.ArgumentParser(add_help=False)
    extra.add_argument("--rlp-wheel", type=Path, required=True)
    extra.add_argument("--types-wheel", type=Path, required=True)
    extra.add_argument(
        "--resume-journal",
        type=Path,
        help="retain completed original-source prefix from a failed run",
    )
    wheels, remainder = extra.parse_known_args()
    sys.argv = [sys.argv[0]] + remainder
    destination = argparse.ArgumentParser(add_help=False)
    destination.add_argument("--output", type=Path, required=True)
    args, _ = destination.parse_known_args(remainder)
    log = args.output.resolve().parent / (args.output.stem + "-commands")
    log.mkdir(exist_ok=False)
    counter = 0

    def command(argv, cwd, input=None, env=None):
        nonlocal counter
        counter += 1
        d = log / f"{counter:04d}"
        d.mkdir()
        started = datetime.datetime.now(datetime.timezone.utc).isoformat()
        (d / "argv.nul").write_bytes(b"\0".join(os.fsencode(x) for x in argv) + b"\0")
        if input is not None:
            (d / "stdin").write_bytes(input)
        result = subprocess.run(
            argv, cwd=cwd, input=input, env=env, capture_output=True
        )
        (d / "stdout").write_bytes(result.stdout)
        (d / "stderr").write_bytes(result.stderr)
        (d / "command.json").write_text(
            json.dumps(
                dict(
                    argv=[str(x) for x in argv],
                    cwd=str(cwd),
                    started=started,
                    ended=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                    exit=result.returncode,
                ),
                indent=2,
            )
            + "\n"
        )
        return result

    sys.path.insert(0, str(ROOT / "scripts"))
    sys.path.insert(0, str(ROOT / "STFSpec/Conformance/Codec"))
    from differential import Driver
    from rlp_typed_differential import RlpSourceAuth, RlpFreshFinder

    class CapturedDriver(Driver):
        def git(self, *argv, input=None, text=False):
            env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
            env.update(GIT_NO_LAZY_FETCH="1", GIT_TERMINAL_PROMPT="0")
            result = command(
                ["git", "--no-replace-objects", "--no-optional-locks", *argv],
                self.eels,
                input,
                env,
            )
            require(result.returncode == 0, "reference Git acquisition failed")
            return result.stdout.decode() if text else result.stdout

    context = CapturedDriver(__doc__, Path(__file__), 156)
    auth = RlpSourceAuth(context)
    sys.meta_path.insert(0, RlpFreshFinder(auth))
    lock = tomllib.loads((context.eels / "uv.lock").read_text())
    dependency_inputs = []
    for package, wheel in [
        ("ethereum_rlp", wheels.rlp_wheel),
        ("ethereum_types", wheels.types_wheel),
    ]:
        distribution = importlib.metadata.distribution(package.replace("_", "-"))
        data = wheel.read_bytes()
        locked_package = [
            row
            for row in lock["package"]
            if row["name"] == package.replace("_", "-")
            and row["version"] == distribution.version
        ]
        require(len(locked_package) == 1, "dependency version absent from pinned lock")
        raw_hash = "sha256:" + hashlib.sha256(data).hexdigest()
        matching_wheels = [
            row
            for row in locked_package[0].get("wheels", [])
            if row["hash"] == raw_hash and row["size"] == len(data)
        ]
        require(
            len(matching_wheels) == 1, "raw dependency wheel differs from pinned lock"
        )
        with zipfile.ZipFile(wheel) as archive:
            files = {
                name: archive.read(name)
                for name in archive.namelist()
                if name.startswith(package + "/") and name.endswith(".py")
            }
        installed = Path(distribution.locate_file(package)).absolute()
        require(
            set(installed.rglob("*.py"))
            == {Path(distribution.locate_file(name)).absolute() for name in files},
            "wheel source inventory mismatch",
        )
        for name, contents in files.items():
            source = Path(distribution.locate_file(name)).absolute()
            require(
                source.resolve() == source and source.read_bytes() == contents,
                "installed dependency differs from original wheel",
            )
        dependency_inputs.append(
            dict(
                package=package,
                path=str(wheel.resolve()),
                sha256=hashlib.sha256(data).hexdigest(),
                size=len(data),
                locked_url=matching_wheels[0]["url"],
                sources={
                    name: hashlib.sha256(contents).hexdigest()
                    for name, contents in files.items()
                },
            )
        )
    from ethereum.forks.amsterdam import incremental_mpt as inc
    from ethereum import merkle_patricia_trie as mpt
    from ethereum.crypto import hash as hash_module
    from ethereum_rlp import rlp
    from ethereum_types.bytes import Bytes, Bytes32

    modules = [
        (inc, "ethereum/forks/amsterdam/incremental_mpt.py"),
        (mpt, "ethereum/merkle_patricia_trie.py"),
        (hash_module, "ethereum/crypto/hash.py"),
    ]
    for module, relative in modules:
        context.check_source(module, relative)
    context.check_source(rlp, "ethereum_rlp/rlp.py", dependency=True)
    fn, cls = inc._encode_mutable_node_to_extended, inc.MutableLeafNode
    classes = [
        inc.MutableLeafNode,
        inc.MutableExtensionNode,
        inc.MutableBranchNode,
        inc.HashedNode,
    ]
    original_classes = tuple(classes)
    functions = [
        fn,
        inc._encode_mutable_node,
        mpt.nibble_list_to_compact,
        hash_module.keccak256,
        rlp.encode,
        inc._decode_witness_node,
    ]
    identities = [(id(f), id(f.__code__)) for f in functions]

    def snapshot():
        for wheel in dependency_inputs:
            data = Path(wheel["path"]).read_bytes()
            require(
                hashlib.sha256(data).hexdigest() == wheel["sha256"]
                and len(data) == wheel["size"],
                "locked wheel changed during comparisons",
            )
        context.check_clean()
        context.check_dependency()
        auth.check()
        require(
            inc._encode_mutable_node_to_extended is fn
            and inc.MutableLeafNode is cls
            and inc._encode_mutable_node is functions[1]
            and inc.nibble_list_to_compact is functions[2]
            and inc.keccak256 is functions[3]
            and inc.rlp is rlp
            and rlp.encode is functions[4],
            "original callable/class replaced",
        )
        require(
            identities == [(id(f), id(f.__code__)) for f in functions],
            "function code replaced",
        )
        require(
            tuple(
                [
                    inc.MutableLeafNode,
                    inc.MutableExtensionNode,
                    inc.MutableBranchNode,
                    inc.HashedNode,
                ]
            )
            == original_classes
            and inc._decode_witness_node is functions[5],
            "original decoder/class replaced",
        )
        require(
            Bytes is bytes and hash_module.Hash32 is Bytes32,
            "actual Bytes/Hash32 identity differs",
        )
        return dict(
            pin=context.head,
            dependencies=dependency_inputs,
            class_identity=id(cls),
            functions=[
                dict(
                    module=f.__module__,
                    name=f.__qualname__,
                    filename=f.__code__.co_filename,
                    first_line=f.__code__.co_firstlineno,
                    function_id=x[0],
                    code_id=x[1],
                )
                for f, x in zip(functions, identities)
            ],
            source_lock={
                p: dict(
                    blob=b,
                    sha256=hashlib.sha256((context.eels / p).read_bytes()).hexdigest(),
                )
                for p, b in context.oracle_blobs.items()
            },
        )

    def capture_inputs(tag):
        target = args.output.parent / (args.output.stem + "-inputs-" + tag)
        target.mkdir(exist_ok=False)
        records = []
        for name in (
            "src/ethereum/forks/amsterdam/incremental_mpt.py",
            "src/ethereum/merkle_patricia_trie.py",
            "src/ethereum/crypto/hash.py",
            "uv.lock",
        ):
            source = context.eels / name
            raw = source.read_bytes()
            p = target / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(raw)
            blob = context.oracle_blobs[name]
            original = command(
                [
                    "git",
                    "--no-replace-objects",
                    "--no-optional-locks",
                    "cat-file",
                    "blob",
                    blob,
                ],
                context.eels,
                env={
                    **{k: v for k, v in os.environ.items() if not k.startswith("GIT_")},
                    "GIT_NO_LAZY_FETCH": "1",
                    "GIT_TERMINAL_PROMPT": "0",
                },
            )
            require(
                original.returncode == 0 and original.stdout == raw,
                "original focused blob differs",
            )
            records.append(
                dict(
                    path=name,
                    blob=blob,
                    sha256=hashlib.sha256(raw).hexdigest(),
                    size=len(raw),
                    mode=oct(source.stat().st_mode & 0o777),
                )
            )
        for entry in dependency_inputs:
            source = Path(entry["path"])
            raw = source.read_bytes()
            (target / source.name).write_bytes(raw)
            records.append(
                dict(
                    path=source.name,
                    sha256=hashlib.sha256(raw).hexdigest(),
                    size=len(raw),
                    mode=oct(source.stat().st_mode & 0o777),
                )
            )
            with zipfile.ZipFile(source) as archive:
                for name in archive.namelist():
                    if name.endswith("/"):
                        continue
                    p = target / source.stem / name
                    p.parent.mkdir(parents=True, exist_ok=True)
                    p.write_bytes(archive.read(name))
        (target / "manifest.json").write_text(json.dumps(records, indent=2) + "\n")
        return records

    before_identity = snapshot()
    before_inputs = capture_inputs("before")
    args.output.with_suffix(".before-identity.json").write_text(
        json.dumps(before_identity, indent=2) + "\n"
    )
    journal = args.output.with_suffix(".source-journal.jsonl")

    def record(row):
        with journal.open("a") as f:
            f.write(json.dumps(row) + "\n")

    def array(xs):
        return [len(xs), *xs]

    def item_wire(item):
        if type(item) in (Bytes, Bytes32):
            return [0, *array(list(item))]
        require(type(item) in (tuple, list), "unexpected original Extended class")
        return [1, len(item), *[x for child in item for x in item_wire(child)]]

    def view(node):
        if node is None:
            return dict(tag=0)
        if type(node) is inc.HashedNode:
            require(
                type(node._hash) in (Bytes, Bytes32) and len(node._hash) == 32,
                "stub premise",
            )
            return dict(tag=1, hash=list(node._hash))
        require(
            type(node) in original_classes[:3] and type(node._dirty) is bool,
            "resolved class premise",
        )
        require(node._rlp is None or type(node._rlp) is Bytes, "raw class premise")
        require(
            node._hash is None
            or (type(node._hash) in (Bytes, Bytes32) and len(node._hash) == 32),
            "hash class premise",
        )
        common = dict(
            raw=None if node._rlp is None else list(node._rlp),
            hash=None if node._hash is None else list(node._hash),
            dirty=node._dirty,
        )
        require(
            type(node.value) is Bytes
            if type(node) is not inc.MutableExtensionNode
            else True,
            "value class premise",
        )
        if type(node) is inc.MutableLeafNode:
            require(
                type(node.rest_of_key) is Bytes
                and all(x < 16 for x in node.rest_of_key),
                "leaf path premise",
            )
            return dict(
                tag=2, path=list(node.rest_of_key), value=list(node.value), **common
            )
        if type(node) is inc.MutableExtensionNode:
            require(
                type(node.key_segment) is Bytes
                and all(x < 16 for x in node.key_segment)
                and node.child is not None,
                "extension premise",
            )
            return dict(
                tag=3, path=list(node.key_segment), child=view(node.child), **common
            )
        require(type(node.children) is list, "branch children class premise")
        return dict(
            tag=4,
            children=[view(c) for c in node.children],
            value=list(node.value),
            **common,
        )

    def ref_wire(v):
        tag = v["tag"]
        if tag == 0:
            return [0]
        if tag == 1:
            return [1, *v["hash"]]
        cache = [
            *array(v["raw"] or []),
            *([0] if v["hash"] is None else [1, *v["hash"]]),
        ]
        if tag == 2:
            return [2, *array(v["path"]), *array(v["value"]), *cache]
        if tag == 3:
            return [3, *array(v["path"]), *ref_wire(v["child"]), *cache]
        return [
            4,
            len(v["children"]),
            *[x for c in v["children"] for x in ref_wire(c)],
            *array(v["value"]),
            *cache,
        ]

    def bs(xs):
        return "bytes [" + ",".join(map(str, xs)) + "]"

    def hs(xs):
        return (
            "(Hash32.ofBytes32 (FixedBytes.ofNat "
            + str(int.from_bytes(bytes(xs), "big"))
            + "))"
        )

    def expression(v):
        tag = v["tag"]
        if tag == 0:
            return "none"
        if tag == 1:
            return "some (.hashed " + hs(v["hash"]) + ")"
        cache = (
            "(Enc.mk ("
            + bs(v["raw"] or [])
            + ") "
            + ("none" if v["hash"] is None else "(some " + hs(v["hash"]) + ")")
            + ")"
        )
        p = "(path [" + ",".join(map(str, v.get("path", []))) + "])"
        if tag == 2:
            return "some (.leaf " + p + " (" + bs(v["value"]) + ") " + cache + ")"
        if tag == 3:
            child = expression(v["child"])
            require(child.startswith("some "), "extension absent")
            return "some (.ext " + p + " (" + child[5:] + ") " + cache + ")"
        return (
            "some (.branch #["
            + ",".join(expression(c) for c in v["children"])
            + "] ("
            + bs(v["value"])
            + ") "
            + cache
            + ")"
        )

    cases = []

    def add(name, node, agree=True):
        cases.append((name, node, agree))

    def leaf(p=b"", v=b"", raw=None, h=None, dirty=False):
        return inc.MutableLeafNode(
            Bytes(p),
            Bytes(v),
            _rlp=None if raw is None else Bytes(raw),
            _hash=h,
            _dirty=dirty,
        )

    def ext(p, c, raw=None, h=None, dirty=False):
        return inc.MutableExtensionNode(
            Bytes(p), c, _rlp=None if raw is None else Bytes(raw), _hash=h, _dirty=dirty
        )

    def branch(cs, v=b"", raw=None, h=None, dirty=False):
        return inc.MutableBranchNode(
            cs,
            Bytes(v),
            _rlp=None if raw is None else Bytes(raw),
            _hash=h,
            _dirty=dirty,
        )

    add("absent", None)
    for n in (0, 1, 255):
        add("stub32", inc.HashedNode(Bytes32(n.to_bytes(32, "big"))))
    for p in (b"", b"\0", b"\0\x0f", b"\0\x0f\0", bytes(range(16))):
        for v in (b"", b"\0", b"\x7f", b"\x80", b"\0\xff\0"):
            for raw in (None, b"", b"\xff", bytes(range(40))):
                add("short-fields-raw-ignored", leaf(p, v, raw))
    for h in (
        Bytes32(bytes(32)),
        Bytes32(bytes(31) + b"\x07"),
        Bytes32(bytes(range(32))),
    ):
        for raw in (None, b"", b"\xff", bytes(range(64))):
            add("clean-cached-leaf", leaf(bytes(range(16)), bytes(range(100)), raw, h))
            add("clean-cached-ext-bypass", ext(b"", leaf(v=bytes(100)), raw, h))
            add(
                "clean-cached-branch-bypass",
                branch([None, leaf(v=bytes(100))], bytes(range(40)), raw, h),
            )
    for n in (0, 1, 15, 16, 17, 33):
        add("all-actual-branch-slots-width-boundary", branch([None] * n), n < 30)
    add(
        "ordered-mixed-short-branch",
        branch([leaf(b"\x0f", b"\0"), None, leaf(b"\0", b"\xff")], b"\0"),
    )
    add("empty-ext-chain", ext(b"", ext(b"", leaf(b"\0\x0f", b"\0\xff"))))
    add("nonempty-ext-to-leaf", ext(b"\0\x0f", leaf(b"\x01", b"\0")))
    # A 32-byte stub makes extension encoding long: source query boundary.
    add(
        "hashless-long-ext-stub",
        ext(b"", inc.HashedNode(Bytes32(bytes(31) + b"\x05"))),
        False,
    )
    for n in (28, 29, 30, 55):
        add("hashless-width-boundary", leaf(v=bytes(n)), n < 29)
    for v in (b"", bytes(29), bytes(70)):
        raw = rlp.encode((mpt.nibble_list_to_compact(b"", True), v))
        h = hash_module.keccak256(raw)
        add(
            "dirty-completed-cache", leaf(v=v, raw=raw, h=h, dirty=True), len(raw) >= 32
        )
    add(
        "dirty-short-cached-divergence",
        leaf(b"\x01", b"\0", b"\xff", Bytes32(bytes(31) + b"\x09"), True),
        False,
    )
    # Strict original witness decoding retains accepted noncanonical HP/raw fields.
    for first in (0x31, 0x71, 0xF1):
        raw = rlp.encode((Bytes([first, 0x23]), Bytes([0, 255])))
        add("decoded-noncanonical-inline-HP", functions[5]({}, raw))
    raw = rlp.encode(
        [(Bytes([0x20]), Bytes([0x01])), (Bytes([0x21]), Bytes([0x02]))]
        + [Bytes(b"")] * 14
        + [[]]
    )
    add("decoded-lenient-branch-ending", functions[5]({}, raw))
    rng = random.Random(context.seed)
    for i in range(24):
        p = bytes(rng.randrange(16) for _ in range(i % 7))
        v = bytes(rng.randrange(256) for _ in range(i % 8))
        add("seeded-short-current-fields", ext(b"", leaf(p, v, bytes([255, i]))))
    expected = []
    expressions = []
    observations = []
    prior = {}
    if wheels.resume_journal is not None:
        previous = wheels.resume_journal.read_bytes()
        for line in previous.splitlines():
            row = json.loads(line)
            if row["phase"] == "after":
                prior[row["case"]] = row
        require(
            sorted(prior) == list(range(len(prior))),
            "resume must be a complete successful prefix",
        )
        record(
            dict(
                phase="resume",
                path=str(wheels.resume_journal),
                sha256=hashlib.sha256(previous).hexdigest(),
                completed_prefix=len(prior),
            )
        )
    for i, (name, node, agree) in enumerate(cases):
        before = view(node)
        calls = []
        throws = []
        record(dict(phase="before", case=i, name=name, input=before, agreement=agree))
        if i in prior:
            old = prior[i]
            require(
                old["before"] == before
                and old["name"] == name
                and old["agreement"] == agree,
                "resume source input differs",
            )
            expected.append(dict(case=i, input=ref_wire(before), result=old["result"]))
            expressions.append(expression(before))
            observations.append(old)
            record(dict(old, retained_from=str(wheels.resume_journal)))
            continue

        def trace(frame, event, arg):
            if frame.f_code is hash_module.keccak256.__code__:
                if event == "call":
                    calls.append(
                        dict(preimage=list(frame.f_locals["buffer"]), answer=None)
                    )
                elif event == "return":
                    calls[-1]["answer"] = None if arg is None else list(arg)
            if event == "exception" and frame.f_code is fn.__code__:
                throws.append(
                    dict(
                        line=frame.f_lineno,
                        class_module=arg[0].__module__,
                        class_name=arg[0].__qualname__,
                        message=str(arg[1]),
                    )
                )
            return trace

        previous = sys.gettrace()
        try:
            sys.settrace(trace)
            result = fn(node)
        except Exception as error:
            record(
                dict(
                    phase="original-error",
                    case=i,
                    after=view(node),
                    calls=calls,
                    throws=throws,
                    message=str(error),
                    traceback=traceback.format_exc(),
                )
            )
            raise
        finally:
            sys.settrace(previous)
        after = view(node)
        wire = item_wire(result)
        if agree and (
            node is None
            or type(node) is inc.HashedNode
            or (before.get("hash") is not None and not before.get("dirty"))
        ):
            require(not calls, "shortcut queried")
        elif agree and before.get("hash") is None:
            require(
                not calls and len(rlp.encode(result)) < 32,
                "inline source-domain premise failed",
            )
        if not agree:
            require(calls or before.get("dirty"), "boundary control not distinguished")
        row = dict(case=i, input=ref_wire(before), result=wire)
        expected.append(row)
        expressions.append(expression(before))
        observation = dict(
            case=i,
            name=name,
            before=before,
            after=after,
            hash_calls=calls,
            result=wire,
            agreement=agree,
            throw_stages=throws,
        )
        observations.append(observation)
        record(dict(phase="after", **observation))
    after_identity = snapshot()
    after_inputs = capture_inputs("after")
    require(
        before_identity == after_identity and before_inputs == after_inputs,
        "authenticated source changed",
    )
    args.output.with_suffix(".after-identity.json").write_text(
        json.dumps(after_identity, indent=2) + "\n"
    )
    guards = (ROOT / "STFSpec/Conformance/Commit/ChildRefGuards.lean").read_text()
    observer = guards[
        guards.index("private def wireBytes") : guards.index("private def same")
    ]
    emit = guards[
        guards.index("private def emit") : guards.index(
            "\nend STFSpec.Conformance.Commit.ChildRefGuards"
        )
    ]
    args.output.write_text(
        "import STFSpec.Commit\nopen STFSpec.Base STFSpec.Codec STFSpec.Commit\nset_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\nprivate def bytes (xs : List UInt8) : ByteArray := xs.toByteArray\nprivate def path (xs : List (Fin 16)) : Nibbles := Nibbles.ofList xs\n"
        + observer
        + emit
        + "\n#eval emit [\n"
        + ",\n".join(expressions)
        + "]\n"
    )
    meta = args.output.with_suffix(".observations.json")
    meta.write_text(
        json.dumps(
            dict(
                seed=context.seed,
                before_identity=before_identity,
                after_identity=after_identity,
                cases=observations,
                expected_source=expected,
            ),
            indent=2,
        )
        + "\n"
    )
    execution = command(["lake", "env", "lean", str(args.output)], ROOT)
    require(execution.returncode == 0, "complete child-reference observer failed")
    actual = parse_records(execution.stdout.decode(), len(expected))
    for observation, got, want in zip(observations, actual, expected):
        require(
            got["case"] == want["case"] and got["input"] == want["input"],
            "full bare fields differ",
        )
        require(
            (got["result"] == want["result"]) == observation["agreement"],
            "conditional source result/boundary mismatch",
        )
    args.output.with_suffix(".actual.json").write_text(
        json.dumps(actual, indent=2) + "\n"
    )
    snapshot()
    print(
        json.dumps(
            dict(
                seed=context.seed,
                cases=len(expected),
                agreements=sum(x["agreement"] for x in observations),
                boundary_divergences=sum(not x["agreement"] for x in observations),
                queries=sum(len(x["hash_calls"]) for x in observations),
                pin=context.head,
                generated=str(args.output),
            )
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
