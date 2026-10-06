#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Full reached-collapse/strict-completion controls on unchanged original EELS.

Use pinned EELS/.venv/bin/python -I -B, --eels, --output EXTERNAL.lean,
--rlp-wheel and --types-wheel. Concrete original comparisons have explicit clean
child/local embedding/cacheless parent premises. Dirty/index/cache boundaries
are observations, not universal source action equality. --self-test supports -O.
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
import traceback
import types
import zipfile

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(Path(__file__).resolve().parent))
from extension_differential import Reader, natural, object_pairs, require


def read_result(values):
    r = Reader(values)
    tag = r.take()
    require(tag in (0, 1), "result tag")
    if tag == 0:
        out = r.ref()
        require(out[0] != 0, "unexpected absent successful branch result")
    else:
        error = r.take()
        require(error in (0, 1, 2), "unexpected branch diagnostic")
        out = r.octets(32) if error == 0 else r.take()
    r.finish()
    return values


def parse_records(text, count):
    lines = text.splitlines()
    require(len(lines) == count, "missing/trailing records")
    rows = []
    for i, line in enumerate(lines):
        row = json.loads(line, object_pairs_hook=object_pairs)
        require(
            type(row) is dict
            and set(row) == {"case", "input", "result", "stateResult", "queries", "counter"},
            "reply fields",
        )
        require(natural(row["case"]) == i, "case order")
        inp = Reader(row["input"])
        n = inp.ref()
        inp.finish()
        require(n[0] == 4, "input branch fields")
        read_result(row["result"])
        read_result(row["stateResult"])
        require(type(row["queries"]) is list, "query list")
        for q in row["queries"]:
            r = Reader(q)
            r.array()
            r.finish()
        natural(row["counter"])
        rows.append(row)
    return rows


def parser_tests():
    leaf = [2, 1, 15, 2, 0, 255, 2, 193, 128, 1, *range(32)]
    good = dict(
        case=0,
        input=[4, 3, 0, *leaf, 0, 2, 0, 255, 0, 0],
        result=[0, *leaf],
        stateResult=[1, 2, 256],
        queries=[[0], [3, 0, 255, 0]],
        counter=8,
    )
    positives = [good, dict(good, result=[1, 0, *range(32)], stateResult=[1, 1, 0], queries=[])]
    for g in positives:
        require(parse_records(json.dumps(g), 1) == [g], "positive complete frame")
    bad = [
        "",
        json.dumps(good) + "\n" + json.dumps(good),
        json.dumps(dict(good, extra=0)),
        json.dumps({k: v for k, v in good.items() if k != "counter"}),
        '{"case":0,"case":0,"input":[],"result":[],"stateResult":[],"queries":[],"counter":0}',
    ]
    for key in ("case", "counter"):
        for x in (True, False, -1, 0.0, None):
            bad.append(json.dumps(dict(good, **{key: x})))
    for key in ("input", "result", "stateResult"):
        for cut in range(len(good[key])):
            bad.append(json.dumps(dict(good, **{key: good[key][:cut]})))
        bad.append(json.dumps(dict(good, **{key: good[key] + [0]})))
        for pos in range(len(good[key])):
            for x in (True, False, -1, 0.0, None):
                xs = good[key].copy()
                xs[pos] = x
                bad.append(json.dumps(dict(good, **{key: xs})))
    for x in ([1, 3], [0, 0], [1, 0, *range(31)], [1, 0, *range(33)], [1, 1, True]):
        bad.append(json.dumps(dict(good, result=x)))
    for x in (False, [False], [[True]], [[1, 256]], [[0, 0]], [[3, 0, 1]], [[1, False]]):
        bad.append(json.dumps(dict(good, queries=x)))
    for x in ([4, True], [4, 1, 3, 0, 0, 0, 0, 0, 0], [4, 1, 2, 1, 16, 0, 0, 0, 0, 0]):
        bad.append(json.dumps(dict(good, input=x)))
    for s in bad:
        try:
            parse_records(s, 1)
        except (ValueError, TypeError, json.JSONDecodeError):
            continue
        raise RuntimeError("invalid full branch frame accepted: " + s)
    print(
        json.dumps(dict(accepted=len(positives), rejected=len(bad), optimized=sys.flags.optimize))
    )


def main():
    if sys.argv[1:] == ["--self-test"]:
        parser_tests()
        return 0
    require(
        sys.flags.isolated and sys.flags.dont_write_bytecode and not sys.flags.optimize,
        "pinned unoptimized -I -B",
    )
    extra = argparse.ArgumentParser(add_help=False)
    extra.add_argument("--rlp-wheel", type=Path, required=True)
    extra.add_argument("--types-wheel", type=Path, required=True)
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

    context = CapturedDriver(__doc__, Path(__file__), 179)
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
                n: z.read(n)
                for n in z.namelist()
                if n.startswith(pkg + "/") and n.endswith(".py")
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

    before = identity()
    before_inputs = inputs("before")
    out.with_suffix(".before-identity.json").write_text(json.dumps(before, indent=2) + "\n")

    def view(n):
        if n is None:
            return dict(tag=0)
        if type(n) is classes[3]:
            return dict(tag=1, hash=list(n._hash))
        require(type(n) in classes[:3], "resolved original class")
        common = dict(
            raw=None if n._rlp is None else list(n._rlp),
            hash=None if n._hash is None else list(n._hash),
            dirty=n._dirty,
        )
        if type(n) is classes[0]:
            return dict(tag=2, path=list(n.rest_of_key), value=list(n.value), **common)
        if type(n) is classes[1]:
            return dict(tag=3, path=list(n.key_segment), child=view(n.child), **common)
        return dict(tag=4, children=[view(x) for x in n.children], value=list(n.value), **common)

    def arr(xs):
        return [len(xs), *xs]

    def wire(n):
        t = n["tag"]
        if t == 0:
            return [0]
        if t == 1:
            return [1, *n["hash"]]
        cache = [*arr(n["raw"] or []), *([0] if n["hash"] is None else [1, *n["hash"]])]
        if t == 2:
            return [2, *arr(n["path"]), *arr(n["value"]), *cache]
        if t == 3:
            return [3, *arr(n["path"]), *wire(n["child"]), *cache]
        return [
            4,
            len(n["children"]),
            *[a for c in n["children"] for a in wire(c)],
            *arr(n["value"]),
            *cache,
        ]

    def expression(n):
        def bs(xs):
            return "(bytes [" + ",".join(map(str, xs)) + "])"

        def hs(h):
            return (
                "(Hash32.ofBytes32 (FixedBytes.ofNat "
                + str(int.from_bytes(bytes(h), "big"))
                + "))"
            )

        t = n["tag"]
        if t == 0:
            return "none"
        if t == 1:
            return "some (.hashed " + hs(n["hash"]) + ")"
        cache = (
            "(Enc.mk "
            + bs(n["raw"] or [])
            + " "
            + ("none" if n["hash"] is None else "(some " + hs(n["hash"]) + ")")
            + ")"
        )
        p = "(path [" + ",".join(map(str, n.get("path", []))) + "])"
        if t == 2:
            return "some (.leaf " + p + " " + bs(n["value"]) + " " + cache + ")"
        if t == 3:
            return "some (.ext " + p + " (" + expression(n["child"])[5:] + ") " + cache + ")"
        return (
            "some (.branch #["
            + ",".join(expression(c) for c in n["children"])
            + "] "
            + bs(n["value"])
            + " "
            + cache
            + ")"
        )

    def pure_child(n):
        if n["tag"] == 0:
            return b""
        if n["tag"] == 1:
            return bytes(n["hash"])
        if n["hash"] is not None:
            return bytes(n["hash"])
        return current(n)

    def current(n):
        if n["tag"] == 2:
            return [mpt.nibble_list_to_compact(Bytes(n["path"]), True), Bytes(n["value"])]
        if n["tag"] == 3:
            return [mpt.nibble_list_to_compact(Bytes(n["path"]), False), pure_child(n["child"])]
        return [*[pure_child(c) for c in n["children"]], Bytes(n["value"])]

    def embedding_compatible(n):
        if n["tag"] in (0, 1):
            return True
        if n["dirty"]:
            return False
        if n["hash"] is not None:
            return True
        raw = rlp.encode(current(n))
        if len(raw) >= 32 or list(raw) != n["raw"]:
            return False
        if n["tag"] == 3:
            return embedding_compatible(n["child"])
        if n["tag"] == 4:
            return all(embedding_compatible(c) for c in n["children"])
        return True

    def model(xs, v, state=False):
        xs = json.loads(json.dumps(xs))
        queries = []
        number = 7

        def query(raw):
            nonlocal number
            h = bytes(31) + bytes([number]) if state else hash_module.keccak256(raw)
            queries.append(dict(preimage=list(raw), answer=list(h)))
            number += 1
            return h

        def fresh(n):
            raw = rlp.encode(current(n))
            n.update(raw=list(raw), hash=None, dirty=False)
            if len(raw) >= 32:
                n["hash"] = list(query(raw))
            return n

        present = [(i, n) for i, n in enumerate(xs) if n["tag"] != 0]
        if not present and not v:
            return [1, 1, 0], queries, number
        if len(present) == 1 and not v:
            i, n = present[0]
            if n["tag"] == 1:
                return [1, 0, *n["hash"]], queries, number
            if n["hash"] is None:
                if len(n["raw"]) >= 32:
                    query(Bytes(n["raw"]))
                else:
                    raw = rlp.encode(current(n))
                    n["raw"] = list(raw)
                    if len(raw) >= 32:
                        n["hash"] = list(query(raw))
            if i >= 16:
                return [1, 2, i], queries, number
            if n["tag"] == 2:
                result = dict(n, path=[i, *n["path"]])
            elif n["tag"] == 3:
                result = dict(n, path=[i, *n["path"]])
            else:
                result = dict(tag=3, path=[i], child=n, raw=None, hash=None, dirty=False)
            return [0, *wire(fresh(result))], queries, number
        if not present:
            result = dict(tag=2, path=[], value=v, raw=None, hash=None, dirty=False)
        else:
            result = dict(tag=4, children=xs, value=v, raw=None, hash=None, dirty=False)
        return [0, *wire(fresh(result))], queries, number

    def leaf(v=2):
        return inc.MutableLeafNode(Bytes([0, 15]), Bytes(bytes(range(v))))

    def fixture(kind, gate):
        if kind == "stub":
            return inc.HashedNode(Bytes32(bytes(31) + b"\x09"))
        if kind == "leaf-short":
            n = leaf(2)
        elif kind == "leaf-long":
            n = leaf(40)
        elif kind == "ext":
            c = leaf(2)
            c._rlp = rlp.encode(current(view(c)))
            n = inc.MutableExtensionNode(Bytes(b""), c)
        elif kind == "branch-short":
            n = inc.MutableBranchNode([None], Bytes(b""))
        else:
            n = inc.MutableBranchNode(
                [inc.HashedNode(Bytes32(bytes(31) + b"\x03")), None], Bytes([0, 255])
            )
        n._rlp = Bytes([255]) * int(gate[3:]) if gate.startswith("raw") else Bytes(b"\xff")
        n._hash = Bytes32(bytes(31) + b"\x5b") if gate == "hash" else None
        if gate == "coherent":
            n._rlp = rlp.encode(current(view(n)))
        return n

    descriptors = []
    for arity in (0, 1, 15, 16, 17, 257):
        for v in (0, 1, 28, 29, 30, 40):
            descriptors.append(dict(mode="zero", arity=arity, v=v))
    for i in (0, 15, 16, 255, 256):
        for kind in ("leaf-short", "leaf-long", "ext", "branch-short", "branch-long", "stub"):
            for gate in (
                ("raw0", "raw31", "raw32", "raw33", "hash", "coherent")
                if kind != "stub"
                else ("raw0",)
            ):
                for v in (0, 1):
                    descriptors.append(dict(mode="sole", idx=i, kind=kind, gate=gate, v=v))
    for arity in (2, 15, 16, 17, 257):
        for v in (0, 1):
            descriptors.append(dict(mode="multiple", arity=arity, v=v))
    # Explicit source boundaries; same bare execution remains admitted.
    for boundary in (
        "dirty-selected",
        "cached-long-retained-branch",
        "parent-cached-pair",
        "parent-cached-long",
        "dirty-descendant",
        "alias",
    ):
        descriptors.append(dict(mode="boundary", boundary=boundary))
    journal = out.with_suffix(".source-journal.jsonl")

    def record(row):
        with journal.open("a") as f:
            f.write(json.dumps(row) + "\n")

    observations = []
    expressions = []
    for i, d in enumerate(descriptors):
        if d["mode"] == "zero":
            xs = [None] * d["arity"]
            v = Bytes(bytes(x % 256 for x in range(d["v"])))
        elif d["mode"] == "sole":
            xs = [None] * (d["idx"] + 1)
            xs[d["idx"]] = fixture(d["kind"], d["gate"])
            v = Bytes(b"" if d["v"] == 0 else b"\x00")
        elif d["mode"] == "multiple":
            xs = [None] * d["arity"]
            xs[0] = fixture("leaf-short", "hash")
            xs[-1] = fixture("ext", "hash")
            v = Bytes(b"" if d["v"] == 0 else b"\x00")
        else:
            name = d["boundary"]
            xs = [fixture("leaf-long", "raw33")]
            v = Bytes(b"")
            if name == "dirty-selected":
                xs[0]._dirty = True
            if name == "cached-long-retained-branch":
                xs = [fixture("branch-long", "raw33")]
            if name.startswith("parent-"):
                xs = [fixture("leaf-short", "hash"), None]
                v = Bytes(b"\x01")
            if name == "dirty-descendant":
                c = leaf(40)
                c._rlp = Bytes([255]) * 33
                c._dirty = True
                xs = [inc.MutableExtensionNode(Bytes(b""), c, _rlp=Bytes(b""))]
            if name == "alias":
                c = fixture("leaf-short", "hash")
                xs = [c, c]
        parent = inc.MutableBranchNode(xs, v, _dirty=bool(i % 2))
        state = inc.IncrementalMPT(secured=False, default=Bytes(b""), root_node=parent)
        if d.get("boundary") == "parent-cached-pair":
            parent._rlp = Bytes([255]) * 33
            parent._hash = Bytes32(bytes(31) + b"\x6f")
        if d.get("boundary") == "parent-cached-long":
            parent._rlp = Bytes([255]) * 33
        source_before = view(parent)
        inputs_view = [view(c) for c in xs]
        inp = dict(tag=4, children=inputs_view, value=list(v), raw=[], hash=None, dirty=False)
        case_expression = (
            "(#["
            + ",".join(expression(n) for n in inputs_view)
            + "],(bytes ["
            + ",".join(map(str, v))
            + "]))"
        )
        calls = []
        events = []
        throws = []
        stage = "collapse"
        result = None
        error = None
        immediate = None
        codes = {f.__code__: f.__qualname__ for f in functions}

        def trace(frame, event, arg):
            if frame.f_code is hash_module.keccak256.__code__:
                if event == "call":
                    calls.append(
                        dict(stage=stage, preimage=list(frame.f_locals["buffer"]), answer=None)
                    )
                elif event == "return":
                    calls[-1]["answer"] = None if arg is None else list(arg)
            if frame.f_code in codes and event in ("call", "return", "exception"):
                row = dict(
                    stage=stage, function=codes[frame.f_code], event=event, line=frame.f_lineno
                )
                if event == "call" and "node" in frame.f_locals:
                    row["node"] = view(frame.f_locals["node"])
                if event == "exception":
                    throws.append(
                        dict(
                            stage=stage,
                            function=codes[frame.f_code],
                            line=frame.f_lineno,
                            module=arg[0].__module__,
                            name=arg[0].__qualname__,
                            args=list(arg[1].args),
                            message=str(arg[1]),
                        )
                    )
                events.append(row)
            return trace

        previous = sys.gettrace()
        record(dict(phase="before", case=i, descriptor=d, input=source_before))
        sys.settrace(trace)
        try:
            try:
                result = inc._collapse_branch(state, parent)
                immediate = view(result)
                stage = "separate-strict-completion"
                if result is not None:
                    inc._compute_node_hash_and_rlp(result)
            except Exception as e:
                error = dict(
                    stage=stage,
                    module=type(e).__module__,
                    name=type(e).__qualname__,
                    args=list(e.args),
                    traceback=traceback.format_exc(),
                )
        finally:
            sys.settrace(previous)
        record(
            dict(
                phase="original-returned",
                case=i,
                descriptor=d,
                input_after=view(parent),
                immediate=immediate,
                source_after=None if result is None else view(result),
                error=error,
                queries=calls,
                events=events,
                throws=throws,
                witness=[
                    dict(hash=list(h), raw=list(r))
                    for h, r in state.witness.accessed_nodes.items()
                ],
            )
        )
        expected_error = (d["mode"] == "zero" and d["v"] == 0) or (
            d["mode"] == "sole" and d["v"] == 0 and (d["kind"] == "stub" or d["idx"] >= 256)
        )
        if error is not None and error["stage"] == "separate-strict-completion":
            require(
                d["mode"] == "sole"
                and d["v"] == 0
                and 16 <= d["idx"] < 256
                and d["kind"] != "stub"
                and immediate is not None,
                "unexpected completion error domain",
            )
            require(error["name"] == "ValueError", "outside-nibble HP completion first failure")
        else:
            require(
                (error is not None) == expected_error,
                "unexpected original collapse success/error domain",
            )
            if error is not None:
                expected_class = (
                    "ValueError"
                    if d["mode"] == "sole" and d["idx"] >= 256 and d["kind"] != "stub"
                    else "AssertionError"
                )
                require(error["name"] == expected_class, "original collapse first failure class")
        expected_id, id_queries, _ = model(inputs_view, list(v), False)
        expected_state, state_queries, number = model(inputs_view, list(v), True)
        # Whole completion bridge is intentionally local. Error/index/boundary
        # observations retain original outcomes without claiming universal equality.
        bridge = d["mode"] != "boundary"
        if d["mode"] == "sole" and d["v"] != 0:
            bridge = all(embedding_compatible(n) for n in inputs_view)
        if d["mode"] == "sole" and d["v"] == 0:
            if d["idx"] >= 16 or d["kind"] == "stub":
                bridge = False
            if (
                d["kind"] in ("branch-short", "branch-long")
                and d["gate"] in ("raw32", "raw33", "coherent")
                and len(inputs_view[d["idx"]]["raw"]) >= 32
            ):
                bridge = False
        source_after = view(result) if result is not None else None
        if bridge and error is None:
            require(
                expected_id == [0, *wire(source_after)], "local completed source image differs"
            )
            require(
                id_queries == [dict(preimage=c["preimage"], answer=c["answer"]) for c in calls],
                "local source query actions differ",
            )
        elif bridge:
            require(
                expected_id == [1, 1, 0] and error["name"] == "AssertionError",
                "unexpected bridge error",
            )
        row = dict(
            phase="complete",
            case=i,
            descriptor=d,
            input=source_before,
            input_after=view(parent),
            immediate=immediate,
            source_after=source_after,
            error=error,
            queries=calls,
            events=events,
            throws=throws,
            witness=[
                dict(hash=list(h), raw=list(r)) for h, r in state.witness.accessed_nodes.items()
            ],
            source_bridge=bridge,
            expression=case_expression,
            expected=dict(
                case=i,
                input=wire(inp),
                result=expected_id,
                stateResult=expected_state,
                queries=[arr([0, 255, 66])] + [arr(q["preimage"]) for q in state_queries],
                counter=number,
            ),
            id_model_queries=id_queries,
            state_model_queries=state_queries,
        )
        record(row)
        observations.append(row)
        expressions.append(case_expression)
    after = identity()
    after_inputs = inputs("after")
    require(before == after and before_inputs == after_inputs, "original identities changed")
    out.with_suffix(".after-identity.json").write_text(json.dumps(after, indent=2) + "\n")
    guards = (ROOT / "STFSpec/Conformance/Commit/BranchGuards.lean").read_text()
    observer = guards[guards.index("private def wireBytes") : guards.index("private def item")]
    recording = guards[
        guards.index("private abbrev Trace") : guards.index("-- Independent List census")
    ]
    emit = guards[
        guards.index("private def emit") : guards.index(
            "\nend STFSpec.Conformance.Commit.BranchGuards"
        )
    ]
    out.write_text(
        "import STFSpec.Commit\nopen STFSpec.Base STFSpec.Codec STFSpec.Hash STFSpec.Commit\nset_option maxRecDepth 100000\nset_option maxHeartbeats 8000000\nprivate def bytes (xs : List UInt8) : ByteArray := xs.toByteArray\nprivate def path (xs : List (Fin 16)) : Nibbles := Nibbles.ofList xs\nprivate def answer (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)\nprivate def enc (raw : List UInt8 := []) (h : Option Hash32 := none) : Enc := ⟨bytes raw, h⟩\n"
        + observer
        + recording
        + emit
        + "\n#eval emit [\n"
        + ",\n".join(expressions)
        + "]\n"
    )
    out.with_suffix(".observations.json").write_text(
        json.dumps(
            dict(cases=observations, before_identity=before, after_identity=after), indent=2
        )
        + "\n"
    )
    execution = command(["lake", "env", "lean", str(out)], ROOT)
    require(execution.returncode == 0, "full mkBranch observer")
    actual = parse_records(execution.stdout.decode(), len(observations))
    for row, got in zip(observations, actual):
        require(
            got == row["expected"],
            "complete Id/State branch frame differs at " + str(row["case"]),
        )
    out.with_suffix(".actual.json").write_text(json.dumps(actual, indent=2) + "\n")
    print(
        json.dumps(
            dict(
                cases=len(observations),
                source_bridges=sum(r["source_bridge"] for r in observations),
                source_errors=sum(r["error"] is not None for r in observations),
                actual_source_queries=sum(len(r["queries"]) for r in observations),
                pin=context.head,
                generated=str(out),
            )
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
