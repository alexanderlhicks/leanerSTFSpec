#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Actual original one-splice deletion/collapse stages and fresh completion.

Use frozen EELS/.venv/bin/python -I -B with --eels, --output EXTERNAL.lean,
--rlp-wheel and --types-wheel. Authenticate actual unstubbed source before/after;
record whole returned new_child, witness/embedding/own query stages and mutable
after-state separately from the immutable retained-child image. No generic action
or retained mutable-cache simulation is claimed. --self-test also runs with -O.
"""

import argparse
import datetime
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
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
            type(row) is dict and set(row) == {"case", "path", "input", "result"},
            "unknown/missing reply field",
        )
        require(natural(row["case"]) == i, "wrong case order")
        require(
            type(row["path"]) is list and all(natural(x) < 16 for x in row["path"]),
            "invalid prefix",
        )
        inp = Reader(row["input"])
        child = inp.ref()
        inp.finish()
        require(child[0] != 0, "absent input child")
        out = Reader(row["result"])
        result = out.ref()
        out.finish()
        require(result[0] != 0, "absent result node")
        rows.append(row)
    return rows


def parser_tests():
    h = list(range(32))
    leaf = [2, 1, 15, 3, 0, 255, 0, 2, 193, 128, 1, *h]
    inp = [3, 0, *leaf, 2, 0, 255, 0]
    result = [
        3,
        2,
        0,
        15,
        4,
        3,
        0,
        1,
        *h,
        *leaf,
        3,
        0,
        255,
        0,
        2,
        193,
        128,
        1,
        *h,
        3,
        0,
        128,
        255,
        1,
        *h,
    ]
    good = dict(case=0, path=[0, 15], input=inp, result=result)
    empty = dict(case=0, path=[], input=[2, 0, 0, 0, 0], result=[2, 0, 0, 0, 0])
    require(
        parse_records(json.dumps(good), 1) == [good],
        "complete recursive record rejected",
    )
    require(parse_records(json.dumps(empty), 1) == [empty], "empty fields rejected")
    bad = [
        "",
        json.dumps(good) + "\n" + json.dumps(good),
        json.dumps(dict(good, extra=0)),
        '{"case":0,"case":0,"path":[],"input":[2,0,0,0,0],"result":[2,0,0,0,0]}',
    ]
    for invalid in (True, -1, 0.0, 1):
        bad.append(json.dumps(dict(good, case=invalid)))
    for invalid in ([True], [-1], [0.0], [16], False):
        bad.append(json.dumps(dict(good, path=invalid)))
    for name in ("input", "result"):
        for cut in range(len(good[name])):
            bad.append(json.dumps(dict(good, **{name: good[name][:cut]})))
        for invalid in (
            [0],
            [9],
            [3, 0, 0, 0, 0],
            [1] + [0] * 31,
            [2, 0, 0, 0, 2],
            [2, 1, 16, 0, 0, 0],
        ):
            bad.append(json.dumps(dict(good, **{name: invalid})))
        bad.append(json.dumps(dict(good, **{name: good[name] + [0]})))
        for pos in range(len(good[name])):
            for invalid in (True, -1, 0.0):
                xs = good[name].copy()
                xs[pos] = invalid
                bad.append(json.dumps(dict(good, **{name: xs})))
    swapped = json.dumps(dict(good, case=1)) + "\n" + json.dumps(good)
    bad.append(swapped)
    for text in bad:
        try:
            parse_records(text, 2 if text == swapped else 1)
        except (ValueError, TypeError, json.JSONDecodeError):
            continue
        raise RuntimeError("invalid full recursive reply accepted: " + text)
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

    context = CapturedDriver(__doc__, Path(__file__), 157)
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
    fn, cls = inc._compute_node_hash_and_rlp, inc.MutableLeafNode
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
        inc._mpt_delete_node,
        inc._delete_from_extension,
        inc._collapse_branch,
        inc._record_witness,
        inc._insert_into_extension,
        inc._split_extension,
        inc._encode_mutable_node_to_extended,
        inc._delete_from_branch,
        inc._mpt_insert_node,
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
            inc._compute_node_hash_and_rlp is fn
            and inc.MutableLeafNode is cls
            and inc._encode_mutable_node is functions[1]
            and inc.nibble_list_to_compact is functions[2]
            and inc.keccak256 is functions[3]
            and inc.rlp is rlp
            and rlp.encode is functions[4],
            "original callable/class replaced",
        )
        require(
            [
                inc._mpt_delete_node,
                inc._delete_from_extension,
                inc._collapse_branch,
                inc._record_witness,
                inc._insert_into_extension,
                inc._split_extension,
                inc._encode_mutable_node_to_extended,
                inc._delete_from_branch,
                inc._mpt_insert_node,
            ]
            == functions[6:],
            "original mutation/helper stage replaced",
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

    from ethereum_types.numeric import Uint

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

    def view(node):
        if node is None:
            return dict(tag=0)
        if type(node) is inc.HashedNode:
            require(
                type(node._hash) in (Bytes, Bytes32) and len(node._hash) == 32,
                "stub32 premise",
            )
            return dict(tag=1, hash=list(node._hash))
        require(
            type(node) in original_classes[:3] and type(node._dirty) is bool,
            "resolved source class premise",
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
        if type(node) is inc.MutableLeafNode:
            require(
                type(node.rest_of_key) is Bytes
                and all(x < 16 for x in node.rest_of_key)
                and type(node.value) is Bytes,
                "leaf fields premise",
            )
            return dict(
                tag=2, path=list(node.rest_of_key), value=list(node.value), **common
            )
        if type(node) is inc.MutableExtensionNode:
            require(
                type(node.key_segment) is Bytes
                and all(x < 16 for x in node.key_segment)
                and node.child is not None,
                "ext fields premise",
            )
            return dict(
                tag=3, path=list(node.key_segment), child=view(node.child), **common
            )
        require(
            type(node.children) is list and type(node.value) is Bytes,
            "branch fields premise",
        )
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
            require(child.startswith("some "), "absent extension child")
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

    def projected_item(v):
        tag = v["tag"]
        if tag == 0:
            return b""
        if tag == 1:
            return bytes(v["hash"])
        if v["hash"] is not None:
            return bytes(v["hash"])
        if tag == 2:
            return (
                mpt.nibble_list_to_compact(Bytes(v["path"]), True),
                Bytes(v["value"]),
            )
        if tag == 3:
            return (
                mpt.nibble_list_to_compact(Bytes(v["path"]), False),
                projected_item(v["child"]),
            )
        return [projected_item(c) for c in v["children"]] + [Bytes(v["value"])]

    def current_item(v):
        fields = dict(v, hash=None)
        return projected_item(fields)

    def embedding_premise(before, after):
        tag = before["tag"]
        if tag in (0, 1):
            return True, dict(kind="absence-or-stub")
        if before["hash"] is not None and not before["dirty"]:
            return True, dict(kind="clean-stored-hash")
        children = []
        if tag == 3:
            children = [embedding_premise(before["child"], after["child"])]
        if tag == 4:
            children = [
                embedding_premise(a, b)
                for a, b in zip(before["children"], after["children"])
            ]
        raw = rlp.encode(current_item(before))
        compatible = all(x[0] for x in children)
        if before["hash"] is None:
            ok = compatible and len(raw) < 32
            return ok, dict(
                kind="hashless-short-current-item", width=len(raw), children=children
            )
        ok = (
            compatible
            and len(raw) >= 32
            and before["hash"] == after["hash"]
            and list(raw) == after["raw"]
        )
        return ok, dict(
            kind="dirty-stored-hash-current-materialization",
            width=len(raw),
            children=children,
            supplied_hash=before["hash"],
            materialized_hash=after["hash"],
        )

    def leaf(p=b"", v=b"", dirty=False):
        return inc.MutableLeafNode(Bytes(p), Bytes(v), _dirty=dirty)

    def ext(p, c, dirty=False):
        return inc.MutableExtensionNode(Bytes(p), c, _dirty=dirty)

    def branch(n, v=b"", dirty=False):
        return inc.MutableBranchNode([None] * n, Bytes(v), _dirty=dirty)

    def digits(n):
        return bytes(i % 16 for i in range(n))

    def witness(w):
        return [dict(hash=list(h), raw=list(r)) for h, r in w.accessed_nodes.items()]

    descriptors = []
    for n in (0, 1, 2, 63, 64, 65, 108, 110, 508, 510):
        for q in (0, 1, 2):
            for v in (0, 29):
                descriptors.append(dict(mode="delete", kind="leaf", p=n, q=q, v=v))
    for v in (28, 29, 30, 53, 54, 55, 56, 252, 253, 254, 255, 256):
        descriptors.append(dict(mode="delete", kind="leaf", p=0, q=0, v=v))
    for p in (0, 1, 3):
        for q in (1, 2):
            for grand in (
                "short-leaf",
                "nested-ext",
                "clean-completed-long",
                "dirty-completed-long",
            ):
                descriptors.append(
                    dict(mode="delete", kind="ext", p=p, q=q, grand=grand)
                )
    for p in (0, 1, 3):
        for n in (0, 1, 15, 16, 17, 33):
            descriptors.append(dict(mode="delete", kind="branch", p=p, arity=n))
    for i in (0, 15):
        for q in (0, 1, 2):
            for v in (0, 29, 55, 253):
                descriptors.append(dict(mode="collapse", kind="leaf", idx=i, q=q, v=v))
        for q in (0, 1, 2):
            for grand in ("short-leaf", "nested-ext", "clean-completed-long"):
                descriptors.append(
                    dict(mode="collapse", kind="ext", idx=i, q=q, grand=grand)
                )
        for n in (0, 1, 15, 16, 17, 33):
            descriptors.append(dict(mode="collapse", kind="branch", idx=i, arity=n))
    for p in (0, 1, 2, 63, 108):
        descriptors.append(dict(mode="fresh-stub", kind="stub", p=p))
    for size in (27, 28, 29):
        descriptors.append(
            dict(mode="fresh-branch-boundary", kind="branch", p=0, arity=0, v=size)
        )
        descriptors.append(
            dict(mode="delete", kind="ext", p=0, q=1, grand="boundary-branch", v=size)
        )
    for p in (0, 1, 3):
        for n in (3, 15, 16, 17, 33):
            descriptors.append(
                dict(mode="delete", kind="branch", p=p, arity=n, changed=True)
            )
    stage_codes = {f.__code__: f.__qualname__ for f in functions}
    stage_codes.update(
        {
            inc._delete_from_branch.__code__: inc._delete_from_branch.__qualname__,
            inc._mpt_insert_node.__code__: inc._mpt_insert_node.__qualname__,
        }
    )
    observations = []
    expected = []
    expressions = []
    for i, d in enumerate(descriptors):
        stage = "fixture"
        calls = []
        events = []
        throws = []
        capture = {}
        outer = None
        pre_child = None

        def trace(frame, event, arg):
            code = frame.f_code
            if code is hash_module.keccak256.__code__:
                if event == "call":
                    calls.append(
                        dict(
                            stage=stage,
                            preimage=list(frame.f_locals["buffer"]),
                            answer=None,
                        )
                    )
                elif event == "return":
                    calls[-1]["answer"] = None if arg is None else list(arg)
            if code in stage_codes:
                row = dict(
                    stage=stage,
                    function=stage_codes[code],
                    event=event,
                    line=frame.f_lineno,
                )
                if event == "call" and "node" in frame.f_locals:
                    row["node"] = view(frame.f_locals["node"])
                if event == "return" and (arg is None or type(arg) in original_classes):
                    row["result"] = view(arg)
                if event in ("call", "return", "exception"):
                    events.append(row)
                if event == "exception":
                    throws.append(
                        dict(
                            stage=stage,
                            function=stage_codes[code],
                            line=frame.f_lineno,
                            class_module=arg[0].__module__,
                            class_name=arg[0].__qualname__,
                            message=str(arg[1]),
                        )
                    )
            if (
                event == "return"
                and code is inc._mpt_delete_node.__code__
                and frame.f_back
                and frame.f_back.f_code is inc._delete_from_extension.__code__
                and frame.f_back.f_locals["node"] is outer
            ):
                capture["new_child"] = view(arg)
                capture["new_child_identity"] = id(arg)
            if (
                event == "return"
                and code is inc._record_witness.__code__
                and frame.f_back
                and frame.f_back.f_code is inc._collapse_branch.__code__
            ):
                capture["new_child"] = view(frame.f_locals["node"])
                capture["new_child_identity"] = id(frame.f_locals["node"])
            return trace

        previous = sys.gettrace()
        sys.settrace(trace)
        try:
            if d["kind"] == "leaf":
                child = leaf(digits(d["q"]), bytes(x % 256 for x in range(d["v"])))
            elif d["kind"] == "ext":
                grand = d["grand"]
                if grand == "boundary-branch":
                    c = branch(0, bytes(d["v"]))
                elif grand == "short-leaf":
                    c = leaf(b"\0\x0f", b"\0\xff")
                elif grand == "nested-ext":
                    c = ext(b"", ext(b"\x02", leaf(b"\x03", b"\0")))
                else:
                    c = leaf(
                        b"\x0f", bytes(range(40)), dirty=grand == "dirty-completed-long"
                    )
                    stage = "fixture-completion"
                    fn(c)
                child = ext(digits(d["q"]), c)
            elif d["kind"] == "branch":
                child = branch(d["arity"], bytes(d.get("v", 0)))
                if d.get("changed"):
                    child.children[:3] = [
                        leaf(b"", b"remove"),
                        leaf(b"\x00", b"\x01"),
                        leaf(b"\x01", b"\x02"),
                    ]
            else:
                child = inc.HashedNode(Bytes32(bytes(31) + b"\x09"))
            pre_child = view(child)
            prefix = digits(d["p"]) if d["mode"] != "collapse" else bytes([d["idx"]])
            context_mpt = inc.IncrementalMPT(secured=False, default=Bytes(b""))
            if d["mode"] == "delete":
                outer = ext(prefix, child)
                context_mpt.root_node = outer
                # Terminal branch leaves its value unchanged; leaf/ext use a true
                # unmatched suffix after the matched parent prefix.
                suffix = (
                    (b"\x00" if d.get("changed") else b"")
                    if d["kind"] == "branch"
                    else bytes(
                        [
                            (child.rest_of_key[0] + 1) % 16
                            if d["kind"] == "leaf" and child.rest_of_key
                            else (child.key_segment[0] + 1) % 16
                            if d["kind"] == "ext"
                            else 1
                        ]
                    )
                )
                source_before = view(outer)
                stage = "matched-deletion"
                result = inc._mpt_delete_node(
                    context_mpt, outer, Bytes(prefix + suffix), Uint(0)
                )
            elif d["mode"] == "fresh-branch-boundary":
                source_before = view(child)
                capture["new_child"] = view(child)
                capture["new_child_identity"] = id(child)
                stage = "fresh-extension-only-branch-boundary"
                result = ext(prefix, child, dirty=True)
            elif d["mode"] == "collapse":
                parent = branch(16)
                parent.children[d["idx"]] = child
                context_mpt.root_node = parent
                source_before = view(parent)
                stage = "sole-child-collapse-with-witness"
                result = inc._collapse_branch(context_mpt, parent)
            else:
                source_before = view(child)
                capture["new_child"] = view(child)
                capture["new_child_identity"] = id(child)
                stage = "fresh-extension-only-stub"
                result = ext(prefix, child, dirty=True)
            require(
                result is not None and "new_child" in capture,
                "original stage failed to return a splice input",
            )
            new_child = capture["new_child"]
            before_completion = view(result)
            require(
                before_completion["raw"] is None and before_completion["hash"] is None,
                "outer is not fresh/invalidated",
            )
            record(
                dict(
                    phase="constructed",
                    case=i,
                    descriptor=d,
                    prefix=list(prefix),
                    pre_child=pre_child,
                    source_before=source_before,
                    new_child=new_child,
                    returned=before_completion,
                    stage_events=events.copy(),
                    hash_calls=calls.copy(),
                    witness=witness(context_mpt.witness),
                )
            )
            stage = "fresh-own-completion"
            h, r = fn(result)
            after = view(result)
            require(
                type(r) is Bytes and (h is None or type(h) in (Bytes, Bytes32)),
                "actual completed cache classes differ",
            )
            require(
                after["raw"] == list(r)
                and after["hash"] == (None if h is None else list(h)),
                "outer caches not retained",
            )
            # The expected immutable image preserves the exact retained child at
            # constructor return. Record actual mutable after-state separately.
            image = json.loads(json.dumps(after))
            if image["tag"] == 3:
                image["child"] = before_completion["child"]
            if d.get("changed"):
                require(
                    new_child["tag"] == 4
                    and new_child["children"][0]["tag"] == 0
                    and sum(c["tag"] != 0 for c in new_child["children"]) == 2
                    and any(
                        e["function"] == inc._delete_from_extension.__qualname__
                        and e["event"] == "return"
                        and e["line"] == 750
                        for e in events
                    ),
                    "changed branch did not reach actual parent join",
                )
            if new_child["tag"] == 2:
                agree = True
                premise = dict(kind="fresh-merged-leaf")
            else:
                retained = new_child["child"] if new_child["tag"] == 3 else new_child
                agree, premise = embedding_premise(retained, after["child"])
            want = dict(
                case=i,
                path=list(prefix),
                input=ref_wire(new_child),
                result=ref_wire(image),
            )
            observation = dict(
                case=i,
                descriptor=d,
                prefix=list(prefix),
                pre_child=pre_child,
                source_before=source_before,
                new_child=new_child,
                returned_before_completion=before_completion,
                actual_source_after=after,
                immutable_image=image,
                expected=want,
                agreement=agree,
                embedding_premise=premise,
                new_child_identity=capture["new_child_identity"],
                hash_calls=calls,
                stage_events=events,
                throw_stages=throws,
                witness=witness(context_mpt.witness),
            )
            observations.append(observation)
            expected.append(want)
            expressions.append(
                "(path ["
                + ",".join(map(str, prefix))
                + "],("
                + expression(new_child)[5:]
                + "))"
            )
            record(dict(phase="after", **observation))
        except Exception as error:
            record(
                dict(
                    phase="original-or-tool-error",
                    case=i,
                    descriptor=d,
                    stage=stage,
                    hash_calls=calls,
                    throw_stages=throws,
                    traceback=traceback.format_exc(),
                )
            )
            raise
        finally:
            sys.settrace(previous)

    # Existing mutation stages preserve fields instead of generic mkExt-splicing.
    controls = []
    for name in (
        "matched-insertion-preserves-extension",
        "split-preserves-suffix-extension",
        "stub-witness-rejects-before-collapse",
    ):
        calls = []
        events = []
        throws = []
        stage = name
        previous = sys.gettrace()
        sys.settrace(trace)
        try:
            mpt_state = inc.IncrementalMPT(secured=False, default=Bytes(b""))
            if name == "matched-insertion-preserves-extension":
                n = ext(b"\x01", leaf(b"\x02", b"\x05"))
                before = view(n)
                got = inc._insert_into_extension(
                    mpt_state, n, Bytes([1, 2]), Bytes([7]), Uint(0)
                )
                require(
                    type(got) is inc.MutableExtensionNode
                    and got.key_segment == Bytes([1])
                    and type(got.child) is inc.MutableLeafNode,
                    "matched insertion was normalized",
                )
                control = dict(
                    name=name,
                    before=before,
                    after=view(got),
                    hash_calls=calls,
                    stage_events=events,
                    throw_stages=throws,
                )
            elif name == "split-preserves-suffix-extension":
                n = ext(b"\x01\x02\x03", leaf(b"\x04", b"\x05"))
                before = view(n)
                got = inc._split_extension(n, Bytes([1, 5]), Bytes([6]), 1)
                require(
                    type(got) is inc.MutableBranchNode
                    and type(got.children[2]) is inc.MutableExtensionNode
                    and got.children[2].key_segment == Bytes([3])
                    and got.children[2].child is n.child,
                    "split suffix child was normalized",
                )
                control = dict(
                    name=name,
                    before=before,
                    after=view(got),
                    hash_calls=calls,
                    stage_events=events,
                    throw_stages=throws,
                )
            else:
                n = branch(16)
                n.children[0] = inc.HashedNode(Bytes32(bytes(31) + b"\x05"))
                before = view(n)
                try:
                    inc._collapse_branch(mpt_state, n)
                except AssertionError as error:
                    require(
                        str(error) == "HashedNode cannot be witnessed" and not calls,
                        "wrong original stub failure/stage",
                    )
                    control = dict(
                        name=name,
                        before=before,
                        after=view(n),
                        error=dict(
                            module=type(error).__module__,
                            class_name=type(error).__qualname__,
                            message=str(error),
                        ),
                        hash_calls=calls,
                        stage_events=events,
                        throw_stages=throws,
                    )
                else:
                    raise RuntimeError("original stub witness failure missing")
            controls.append(control)
            record(dict(phase="stage-control", **control))
        finally:
            sys.settrace(previous)
    after_identity = snapshot()
    after_inputs = capture_inputs("after")
    require(
        before_identity == after_identity and before_inputs == after_inputs,
        "original input identities changed",
    )
    args.output.with_suffix(".after-identity.json").write_text(
        json.dumps(after_identity, indent=2) + "\n"
    )
    guards = (ROOT / "STFSpec/Conformance/Commit/ExtensionGuards.lean").read_text()
    observer = guards[
        guards.index("private def wireBytes") : guards.index("private def joined")
    ]
    emit = guards[
        guards.index("private def emit") : guards.index(
            "\nend STFSpec.Conformance.Commit.ExtensionGuards"
        )
    ]
    args.output.write_text(
        "import STFSpec.Commit\nopen STFSpec.Base STFSpec.Codec STFSpec.Hash STFSpec.Commit\nset_option maxRecDepth 100000\nset_option maxHeartbeats 8000000\nprivate def bytes (xs : List UInt8) : ByteArray := xs.toByteArray\nprivate def path (xs : List (Fin 16)) : Nibbles := Nibbles.ofList xs\n"
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
                expected=expected,
                stage_controls=controls,
            ),
            indent=2,
        )
        + "\n"
    )
    execution = command(["lake", "env", "lean", str(args.output)], ROOT)
    require(execution.returncode == 0, "full returned-node observer failed")
    actual = parse_records(execution.stdout.decode(), len(expected))
    for case, got, want in zip(observations, actual, expected):
        require(
            got["case"] == want["case"]
            and got["path"] == want["path"]
            and got["input"] == want["input"],
            "whole original splice input differs",
        )
        require(
            (got["result"] == want["result"]) == case["agreement"],
            "completed immutable-image/source boundary mismatch",
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
                immutable_image_agreements=sum(x["agreement"] for x in observations),
                boundary_divergences=sum(not x["agreement"] for x in observations),
                stage_controls=len(controls),
                queries=sum(len(x["hash_calls"]) for x in observations),
                pin=context.head,
                generated=str(args.output),
            )
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
