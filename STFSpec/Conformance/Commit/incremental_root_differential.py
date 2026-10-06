#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Supplied incremental-root commitments with complete fields, queries and source stages.

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
import marshal
import tomllib
import subprocess
import sys
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
            type(row) is dict
            and set(row) == {"case", "secured", "empty", "input", "result", "queries"},
            "unknown/missing reply field",
        )
        require(
            natural(row["case"]) == i and type(row["secured"]) is bool,
            "case order/flag",
        )
        for name in ("empty", "result"):
            require(type(row[name]) is list and len(row[name]) == 32, "hash width")
            require(all(natural(x) < 256 for x in row[name]), "hash octet")
        inp = Reader(row["input"])
        inp.ref()
        inp.finish()
        require(
            type(row["queries"]) is list and len(row["queries"]) <= 1,
            "local query arity",
        )
        for q in row["queries"]:
            r = Reader(q)
            r.array()
            r.octets(32)
            r.finish()
        rows.append(row)
    return rows


def parser_tests():
    h = list(range(32))
    leaf = [2, 1, 15, 2, 0, 255, 2, 255, 0, 1, *h]
    inp = [4, 3, 0, 1, *h, 3, 0, *leaf, 0, 0, 2, 0, 255, 0, 0]
    good = dict(
        case=0, secured=True, empty=h, input=inp, result=h, queries=[[3, 0, 255, 0, *h]]
    )
    empty = dict(case=0, secured=False, empty=h, input=[0], result=h, queries=[])
    require(parse_records(json.dumps(good), 1) == [good], "complete record")
    require(parse_records(json.dumps(empty), 1) == [empty], "empty record")
    bad = [
        "",
        json.dumps(good) + "\n" + json.dumps(good),
        json.dumps(dict(good, extra=0)),
        '{"case":0,"case":0,"secured":false,"empty":[],"input":[0],"result":[],"queries":[]}',
        json.dumps(dict(good, case=1)),
        json.dumps(dict(good, input=[9])),
        json.dumps(dict(good, input=[3, 0, 0, 0, 0])),
        json.dumps(dict(good, queries=good["queries"] * 2)),
        json.dumps(dict(good, queries=[[0, *h, 0]])),
        json.dumps(dict(good, secured=0)),
    ]
    for name in good:
        bad.append(json.dumps({k: v for k, v in good.items() if k != name}))
    for name in ("empty", "input", "result"):
        for cut in range(len(good[name])):
            bad.append(json.dumps(dict(good, **{name: good[name][:cut]})))
        bad.append(json.dumps(dict(good, **{name: good[name] + [0]})))
        for pos in range(len(good[name])):
            for invalid in (True, -1, 0.0, 256):
                xs = good[name].copy()
                xs[pos] = invalid
                bad.append(json.dumps(dict(good, **{name: xs})))
    q = good["queries"][0]
    for cut in range(len(q)):
        bad.append(json.dumps(dict(good, queries=[q[:cut]])))
    for pos in range(len(q)):
        for invalid in (True, -1, 0.0, 256):
            xs = q.copy()
            xs[pos] = invalid
            bad.append(json.dumps(dict(good, queries=[xs])))
    for invalid in (True, -1, 0.0):
        bad.append(json.dumps(dict(good, case=invalid)))
    for invalid in (None, True, 0):
        bad.append(json.dumps(dict(good, queries=invalid)))
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

    context = CapturedDriver(__doc__, Path(__file__), 161)
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
                wheel=str(wheel.resolve()),
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
    from ethereum import state as state_module
    from ethereum.crypto import hash as hash_module
    from ethereum_rlp import rlp
    from ethereum_types.bytes import Bytes, Bytes32

    modules = [
        (inc, "ethereum/forks/amsterdam/incremental_mpt.py"),
        (mpt, "ethereum/merkle_patricia_trie.py"),
        (state_module, "ethereum/state.py"),
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
        inc.mpt_root,
    ]
    identities = [(id(f), id(f.__code__)) for f in functions]
    original_root = inc.Root
    original_mpt = inc.IncrementalMPT
    constructor_ids = [
        (id(c), id(c.__init__), id(c.__init__.__code__))
        for c in classes + [original_mpt]
    ]

    def startup_identity():
        executable = Path(sys.executable).resolve()
        return dict(
            executable=str(executable),
            sha256=hashlib.sha256(executable.read_bytes()).hexdigest(),
            mode=oct(executable.stat().st_mode & 0o777),
            prefix=sys.prefix,
            base_prefix=sys.base_prefix,
            version=sys.version,
            flags=dict(
                isolated=sys.flags.isolated,
                dont_write_bytecode=sys.flags.dont_write_bytecode,
                optimize=sys.flags.optimize,
                no_user_site=sys.flags.no_user_site,
                ignore_environment=sys.flags.ignore_environment,
            ),
            path=list(sys.path),
            trace_id=id(sys.gettrace()),
            profile_id=id(sys.getprofile()),
            meta_path=[
                dict(
                    class_module=type(x).__module__,
                    class_name=type(x).__qualname__,
                    identity=id(x),
                )
                for x in sys.meta_path
            ],
        )

    startup = startup_identity()

    def snapshot():
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
            Bytes is bytes
            and hash_module.Hash32 is Bytes32
            and inc.Root is state_module.Root is original_root is Bytes32,
            "actual Bytes/Hash32/Root identity differs",
        )
        require(
            inc.mpt_root is functions[6] and inc.IncrementalMPT is original_mpt,
            "original root operation/carrier replaced",
        )
        require(
            constructor_ids
            == [
                (id(c), id(c.__init__), id(c.__init__.__code__))
                for c in classes + [original_mpt]
            ],
            "original constructors replaced",
        )
        require(startup_identity() == startup, "startup identity changed")
        for entry in dependency_inputs:
            require(
                hashlib.sha256(Path(entry["wheel"]).read_bytes()).hexdigest()
                == entry["sha256"]
                and Path(entry["wheel"]).stat().st_size == entry["size"],
                "wheel changed",
            )
        return dict(
            pin=context.head,
            dependencies=dependency_inputs,
            startup=startup,
            classes=[
                dict(
                    module=c.__module__,
                    name=c.__qualname__,
                    class_id=ci,
                    init_id=ii,
                    code_id=co,
                    code_sha256=hashlib.sha256(
                        marshal.dumps(c.__init__.__code__)
                    ).hexdigest(),
                )
                for c, (ci, ii, co) in zip(classes + [original_mpt], constructor_ids)
            ],
            Root=dict(
                module=original_root.__module__,
                name=original_root.__qualname__,
                identity=id(original_root),
            ),
            loaded_modules=[
                dict(
                    name=name,
                    path=str(Path(mod.__file__).resolve()),
                    sha256=hashlib.sha256(Path(mod.__file__).read_bytes()).hexdigest(),
                    identity=id(mod),
                )
                for name, mod in sorted(sys.modules.items())
                if name.split(".", 1)[0]
                in ("ethereum", "ethereum_types", "ethereum_rlp")
                and getattr(mod, "__file__", None)
            ],
            class_identity=id(cls),
            functions=[
                dict(
                    module=f.__module__,
                    name=f.__qualname__,
                    filename=f.__code__.co_filename,
                    first_line=f.__code__.co_firstlineno,
                    function_id=x[0],
                    code_id=x[1],
                    code_sha256=hashlib.sha256(marshal.dumps(f.__code__)).hexdigest(),
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
            "src/ethereum/state.py",
            "uv.lock",
        ):
            source = context.eels / name
            raw = source.read_bytes()
            p = target / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(raw)
            p.chmod(source.stat().st_mode & 0o777)
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
            source = Path(entry["wheel"])
            raw = source.read_bytes()
            (target / source.name).write_bytes(raw)
            (target / source.name).chmod(source.stat().st_mode & 0o777)
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
        members = []
        for entry in dependency_inputs:
            with zipfile.ZipFile(entry["wheel"]) as archive:
                for z in archive.infolist():
                    members.append(
                        dict(
                            wheel=Path(entry["wheel"]).name,
                            path=z.filename,
                            size=z.file_size,
                            sha256=hashlib.sha256(archive.read(z)).hexdigest(),
                            external_attr=z.external_attr,
                            compress_type=z.compress_type,
                            CRC=z.CRC,
                        )
                    )
        (target / "members.json").write_text(json.dumps(members, indent=2) + "\n")
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

    cases = []
    setup_calls = []

    def add(name, node, agree=True, repeats=1):
        cases.append((name, node, agree, repeats))

    def setup_hash(wire):
        h = hash_module.keccak256(wire)
        setup_calls.append(dict(preimage=list(wire), answer=list(h)))
        return h

    add("absent", None)
    for n in (0, 1, 255):
        add("stub32", inc.HashedNode(Bytes32(n.to_bytes(32, "big"))))
    for p in (b"", b"\0", b"\0\x0f", b"\0\x0f\0", bytes(range(16))):
        for v in (b"", b"\0", b"\x7f", b"\x80", b"\0\xff\0"):
            for raw in (None, b"", b"\xff", bytes(range(40))):
                add("fields-raw-ignored", leaf(p, v, raw))
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
        add("all-actual-branch-slots", branch([None] * n))
    add(
        "ordered-mixed-short-branch",
        branch([leaf(b"\x0f", b"\0"), None, leaf(b"\0", b"\xff")], b"\0"),
    )
    add("empty-ext-chain", ext(b"", ext(b"", leaf(b"\0\x0f", b"\0\xff"))))
    add(
        "hashless-long-ext-stub", ext(b"", inc.HashedNode(Bytes32(bytes(31) + b"\x05")))
    )
    for n in (28, 29, 30, 53, 54, 55, 56, 253, 254, 255, 256):
        add("top-width-and-framing", leaf(v=bytes(n)))
    add("repeat-clean-long", leaf(v=bytes(70)), repeats=3)
    add("repeat-dirty-long", leaf(v=bytes(70), dirty=True), repeats=3)
    add("repeat-short", leaf(v=b"\0"), repeats=3)
    for v in (b"", bytes(29), bytes(70)):
        raw = rlp.encode((mpt.nibble_list_to_compact(b"", True), v))
        h = setup_hash(raw)
        add("dirty-coherent-cached", leaf(v=v, raw=raw, h=h, dirty=True))
    add(
        "dirty-short-stale-cached",
        leaf(b"\x01", b"\0", b"\xff", Bytes32(bytes(31) + b"\x09"), True),
        False,
    )
    add(
        "dirty-long-stale-cached",
        leaf(v=bytes(70), raw=b"\xff", h=Bytes32(bytes(31) + b"\x09"), dirty=True),
        False,
    )
    add("recursive-hashless-long-child-boundary", ext(b"\0", leaf(v=bytes(70))), False)
    child_raw = rlp.encode((mpt.nibble_list_to_compact(b"", True), Bytes(bytes(70))))
    add(
        "recursive-clean-completed-child",
        ext(b"\0", leaf(v=bytes(70), raw=child_raw, h=setup_hash(child_raw))),
    )
    add(
        "ordered-child-materialization-boundary",
        branch([leaf(v=bytes(70)), leaf(b"\x0f", bytes(60)), None]),
        False,
    )
    for first in (0x31, 0x71, 0xF1):
        raw = rlp.encode((Bytes([first, 0x23]), Bytes([0, 255])))
        add("decoded-noncanonical-current-fields", functions[5]({}, raw))
    rng = random.Random(context.seed)
    for i in range(24):
        p = bytes(rng.randrange(16) for _ in range(i % 9))
        v = bytes(rng.randrange(256) for _ in range(i % 13))
        add("seeded-current-fields", ext(b"", leaf(p, v, bytes([255, i]))))
    bypass_child = leaf(v=bytes(32))
    require(
        len(rlp.encode((mpt.nibble_list_to_compact(b"", True), bypass_child.value)))
        == 35,
        "cached bypass descendant width",
    )
    add(
        "clean-cached-root-bypasses-hashless-35",
        ext(b"", bypass_child, raw=b"\xff", h=Bytes32(bytes(32))),
    )
    expected = []
    expressions = []
    observations = []
    for name, node, agree, repeats in cases:
        for repeat in range(repeats):
            i = len(observations)
            secured = bool(i % 2)
            trie = inc.IncrementalMPT(
                secured=secured, default=Bytes(b""), root_node=node
            )
            before = view(node)
            calls = []
            events = []
            throws = []
            record(
                dict(
                    phase="before",
                    case=i,
                    name=name,
                    repeat=repeat,
                    input=before,
                    agreement=agree,
                    secured=secured,
                )
            )
            codes = {
                f.__code__: f.__qualname__
                for f in [
                    inc.mpt_root,
                    fn,
                    inc._encode_mutable_node,
                    hash_module.keccak256,
                ]
            }

            def trace(frame, event, arg):
                code = frame.f_code
                if code in codes:
                    event_record = dict(
                        function=codes[code], event=event, line=frame.f_lineno
                    )
                    if "node" in frame.f_locals:
                        event_record["node"] = view(frame.f_locals["node"])
                    if event == "return":
                        if type(arg) in (Bytes, Bytes32):
                            event_record["bytes"] = list(arg)
                        elif type(arg) in (tuple, list):
                            event_record["item"] = item_wire(arg)
                    if event == "exception":
                        exception = dict(
                            class_module=arg[0].__module__,
                            class_name=arg[0].__qualname__,
                            message=str(arg[1]),
                        )
                        event_record["exception"] = exception
                        throws.append(exception)
                    events.append(event_record)
                if code is hash_module.keccak256.__code__:
                    if event == "call":
                        parent = frame.f_back
                        stage = (
                            "top-wrapper"
                            if parent.f_code is inc.mpt_root.__code__
                            else (
                                "top-materialization"
                                if parent.f_locals.get("node") is node
                                else "descendant-materialization"
                            )
                        )
                        calls.append(
                            dict(
                                stage=stage,
                                preimage=list(frame.f_locals["buffer"]),
                                answer=None,
                            )
                        )
                    elif event == "return":
                        calls[-1]["answer"] = None if arg is None else list(arg)
                return trace

            previous = sys.gettrace()
            try:
                sys.settrace(trace)
                result = inc.mpt_root(trie)
            except Exception as error:
                record(
                    dict(
                        phase="original-error",
                        case=i,
                        after=view(node),
                        calls=calls,
                        events=events,
                        throws=throws,
                        message=str(error),
                        traceback=traceback.format_exc(),
                    )
                )
                raise
            finally:
                sys.settrace(previous)
            require(
                type(result) is original_root and len(result) == 32,
                "actual Root result class/width",
            )
            after = view(node)
            shortcut = (
                node is None
                or type(node) is inc.HashedNode
                or (before.get("hash") is not None and not before.get("dirty"))
            )
            if shortcut:
                require(not calls, "original shortcut queried")
                require(before == after, "original shortcut changed caches")
            else:
                require(
                    sum(q["stage"].startswith("top-") for q in calls) == 1,
                    "original top query site/count",
                )
            top_positions = [
                j for j, q in enumerate(calls) if q["stage"].startswith("top-")
            ]
            if top_positions:
                require(
                    top_positions == [len(calls) - 1],
                    "descendant query followed top query",
                )
            wrapper_top = [q for q in calls if q["stage"] == "top-wrapper"]
            if wrapper_top:
                require(
                    after["hash"] == before["hash"],
                    "short wrapper answer installed in source cache",
                )
            require(not throws, "unexpected source throw")
            row = dict(
                case=i,
                secured=secured,
                empty=list(mpt.EMPTY_TRIE_ROOT),
                input=ref_wire(before),
                result=list(result),
            )
            expected.append(row)
            expressions.append(
                "("
                + str(secured).lower()
                + ", "
                + hs(row["empty"])
                + ", "
                + expression(before)
                + ")"
            )
            observation = dict(
                case=i,
                name=name,
                repeat=repeat,
                before=before,
                after=after,
                hash_calls=calls,
                result=list(result),
                agreement=agree,
                events=events,
                throw_stages=throws,
                secured=secured,
                wrapper=dict(
                    default=[],
                    witness_entries=len(trie.witness.accessed_nodes),
                    data_entries=len(trie._data),
                ),
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
    guards = (
        ROOT / "STFSpec/Conformance/Commit/IncrementalRootGuards.lean"
    ).read_text()
    observer = guards[
        guards.index("private def bytes") : guards.index("private def stored")
    ]
    emit = guards[
        guards.index("private def concrete") : guards.index(
            "\nend STFSpec.Conformance.Commit.IncrementalRootGuards"
        )
    ]
    args.output.write_text(
        "import STFSpec.Commit\nopen STFSpec.Base STFSpec.Codec STFSpec.Hash STFSpec.Commit\nset_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\n"
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
                fixture_setup_queries=setup_calls,
            ),
            indent=2,
        )
        + "\n"
    )
    execution = command(["lake", "env", "lean", str(args.output)], ROOT)
    require(execution.returncode == 0, "complete incremental-root observer failed")
    actual = parse_records(execution.stdout.decode(), len(expected))
    for observation, got, want in zip(observations, actual, expected):
        require(
            all(got[k] == want[k] for k in ("case", "secured", "empty", "input")),
            "complete supplied fields differ",
        )
        require(
            (got["result"] == want["result"]) == observation["agreement"],
            "conditional root value/boundary mismatch",
        )
        before = observation["before"]
        local_cached = before["tag"] in (0, 1) or before.get("hash") is not None
        require(
            len(got["queries"]) == (0 if local_cached else 1), "local zero/one query"
        )
        if got["queries"]:
            frame = Reader(got["queries"][0])
            preimage = frame.array()
            ans = frame.octets(32)
            frame.finish()
            require(ans == got["result"], "local actual answer")
            if observation["agreement"]:
                top = [
                    q
                    for q in observation["hash_calls"]
                    if q["stage"].startswith("top-")
                ]
                require(
                    len(top) == 1
                    and top[0]["preimage"] == preimage
                    and top[0]["answer"] == ans,
                    "whole top preimage/answer",
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
                fixture_queries=len(setup_calls),
                pin=context.head,
                generated=str(args.output),
            )
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
