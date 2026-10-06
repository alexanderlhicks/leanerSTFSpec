#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Fresh complete-value observations of original pinned witness_state._trie_lookup.

Use frozen EELS/.venv/bin/python -I -B, --eels, --output EXTERNAL.lean and
--rlp-wheel/--types-wheel original authenticated wheels. Source values/stubs are
compared on actual Hash32 keys and represented finite acyclic classes. Missing
selected slots test Q59's typed adaptation separately, not Python payload/guest
output equivalence. Complete original input/cache fields and errors are retained.
Interpreter, frozen startup/installation and host remain trust inputs. --self-test
runs strict full-value/input grammar controls with ordinary Python, also -O.
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
sys.path.insert(0, str(Path(__file__).resolve().parent))
from decoder_differential import WireReader, natural, object_pairs, require


class LookupReader(WireReader):
    """Bare-tree input grammar allows all finite branch arities; decoder stays strict."""

    def ref(self):
        tag = self.take()
        if tag == 0:
            return
        if tag == 1:
            self.octets(32)
        elif tag == 2:
            self.path()
            self.byte_array()
            self.enc()
        elif tag == 3:
            self.path()
            self.enc()
            self.ref()
        elif tag == 4:
            self.byte_array()
            self.enc()
            for _ in range(self.take()):
                self.ref()
        else:
            raise ValueError("bad bare node tag")

    def result(self):
        tag = self.take()
        require(tag in (0, 1), "bad lookup result tag")
        if tag == 0:
            self.offset -= 1
            super().result()
        else:
            option = self.take()
            require(option in (0, 1), "bad optional value tag")
            if option == 1:
                self.byte_array()


def parse_records(text, count):
    lines = text.splitlines()
    require(len(lines) == count, "missing/trailing lookup records")
    rows = []
    for i, line in enumerate(lines):
        row = json.loads(line, object_pairs_hook=object_pairs)
        require(
            type(row) is dict and set(row) == {"case", "key", "input", "result"},
            "wrong lookup fields",
        )
        require(natural(row["case"]) == i, "wrong lookup case order")
        for name, method in [("key", "path"), ("input", "ref"), ("result", "result")]:
            reader = LookupReader(row[name])
            getattr(reader, method)()
            reader.finish()
        rows.append(row)
    return rows


def parser_tests():
    good = dict(case=0, key=[0], input=[0], result=[1, 1, 0])
    require(parse_records(json.dumps(good), 1) == [good], "present empty rejected")
    accepted = []
    for arity in (0, 1, 15, 16, 17, 32):
        row = dict(good, input=[4, 0, 0, 0, arity] + [0] * arity)
        require(parse_records(json.dumps(row), 1) == [row], "bare arity rejected")
        accepted.append(row)
    for result in (
        [1, 0],
        [1, 1, 3, 0, 255, 0],
        [0, 1, 11, 10**100, 10**200],
        [0, 2] + [255] * 32,
    ):
        row = dict(good, result=result)
        require(
            parse_records(json.dumps(row), 1) == [row], "complete value/error rejected"
        )
        accepted.append(row)
    bad = []
    for field, values in [
        ("case", [True, -1, 0.0]),
        ("key", [[1, 16], [1], [0, 0]]),
        ("input", [[4, 0, 0, 0, 1], [9], [1] + [0] * 31]),
        (
            "result",
            [
                [1, 2],
                [1, 1],
                [1, 1, 1, 256],
                [1, 0, 0],
                [0, 1, 11],
                [0, 1, 11, 1],
                [0, 1, 11, 0, 0, 0],
                [0, 1, 11, True, 0],
                [0, 1, 11, 0, True],
                [0, 1, 11, -1, 0],
                [0, 1, 11, 0, -1],
                [0, 1, 11, 0.0, 0],
                [0, 1, 11, 0, 0.0],
                [0, 1, 12, 0, 0],
            ],
        ),
    ]:
        for value in values:
            row = dict(good)
            row[field] = value
            bad.append(json.dumps(row))
    bad += [
        "",
        json.dumps(good) + "\n" + json.dumps(good),
        json.dumps(dict(good, extra=0)),
        '{"case":0,"case":0,"key":[0],"input":[0],"result":[1,0]}',
    ]
    for text in bad:
        try:
            parse_records(text, 1)
        except (ValueError, TypeError, json.JSONDecodeError):
            continue
        raise RuntimeError("invalid lookup frame accepted: " + text)
    print(
        json.dumps(
            dict(
                accepted=len(accepted) + 1,
                rejected=len(bad),
                optimized=sys.flags.optimize,
            )
        )
    )


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
    sys.path.insert(0, str(ROOT / "scripts"))
    sys.path.insert(0, str(ROOT / "STFSpec/Conformance/Codec"))
    from differential import Driver
    from rlp_typed_differential import RlpSourceAuth, RlpFreshFinder

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

    class CapturedDriver(Driver):
        def git(self, *argv, input=None, text=False):
            env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
            result = command(
                ["git", "--no-replace-objects", "--no-optional-locks", *argv],
                self.eels,
                input,
                env,
            )
            require(result.returncode == 0, "reference Git acquisition failed")
            return result.stdout.decode() if text else result.stdout

    context = CapturedDriver(__doc__, Path(__file__), 146)
    auth = RlpSourceAuth(context)
    sys.meta_path.insert(0, RlpFreshFinder(auth))
    lock = tomllib.loads((context.eels / "uv.lock").read_text())
    wheel_rows = []
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
        wheel_rows.append(
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
    from ethereum.forks.amsterdam import witness_state as ws, incremental_mpt as inc
    from ethereum.crypto.hash import Hash32

    context.check_source(ws, "ethereum/forks/amsterdam/witness_state.py")
    context.check_source(inc, "ethereum/forks/amsterdam/incremental_mpt.py")
    fn = ws._trie_lookup
    classes = [
        inc.MutableLeafNode,
        inc.MutableExtensionNode,
        inc.MutableBranchNode,
        inc.HashedNode,
    ]
    identity = [(id(x), id(getattr(x, "__code__", None))) for x in [fn, *classes]]

    def snapshot():
        for wheel in wheel_rows:
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
            ws._trie_lookup is fn
            and [
                inc.MutableLeafNode,
                inc.MutableExtensionNode,
                inc.MutableBranchNode,
                inc.HashedNode,
            ]
            == classes,
            "original callable/class changed",
        )
        require(
            identity
            == [(id(x), id(getattr(x, "__code__", None))) for x in [fn, *classes]],
            "original function code changed",
        )
        return dict(
            pin=context.head,
            dependencies=wheel_rows,
            source_lock={
                p: dict(
                    blob=b,
                    sha256=hashlib.sha256((context.eels / p).read_bytes()).hexdigest(),
                )
                for p, b in context.oracle_blobs.items()
            },
            function=dict(
                module=fn.__module__,
                name=fn.__qualname__,
                filename=fn.__code__.co_filename,
                first_line=fn.__code__.co_firstlineno,
                identity=identity,
            ),
        )

    before_identity = snapshot()
    args.output.with_suffix(".before-identity.json").write_text(
        json.dumps(before_identity, indent=2) + "\n"
    )
    journal = args.output.with_suffix(".source-journal.jsonl")

    def record(row):
        with journal.open("a") as stream:
            stream.write(json.dumps(row) + "\n")

    def h(n):
        return Hash32(n.to_bytes(32, "big"))

    def cache(n):
        return dict(
            _rlp=bytes([0, 255, n % 256]),
            _hash=None if n % 2 == 0 else h(n),
            _dirty=False,
        )

    def leaf(p, v, n=1):
        return inc.MutableLeafNode(bytes(p), bytes(v), **cache(n))

    def ext(p, child, n=2):
        return inc.MutableExtensionNode(bytes(p), child, **cache(n))

    def branch(cs, value=b"", n=3):
        return inc.MutableBranchNode(cs, bytes(value), **cache(n))

    def stub(n=9):
        return inc.HashedNode(h(n))

    def digits(key):
        return bytes(x for b in key for x in (b >> 4, b & 15))

    cases = []

    def add(name, root, raw=bytes(32)):
        cases.append((name, root, Hash32(raw)))

    add("none", None)
    add("stub", stub())
    for raw in (bytes(32), bytes([255]) * 32, bytes(range(32))):
        p = digits(raw)
        for value in (b"", b"\0", bytes(range(256))):
            add("full-leaf", leaf(p, value), raw)
        add("mismatch-leaf", leaf(p[:-1] + bytes([(p[-1] + 1) % 16]), b"ignored"), raw)
        add("overlong-extension", ext(p + b"\0", stub()), raw)
        add("mismatch-extension", ext(bytes([(p[0] + 1) % 16]), stub()), raw)
        add("full-extension-stub", ext(p, stub()), raw)
        add("full-extension-terminal-empty", ext(p, branch([], b"")), raw)
        add("full-extension-terminal-value", ext(p, branch([], b"\0\xff\0")), raw)
        add("extension-to-leaf", ext(p[:7], leaf(p[7:], b"\0\xff\0")), raw)
        add("extension-to-extension", ext(p[:1], ext(p[1:3], leaf(p[3:], b""))), raw)
        node = leaf(p, bytes(range(256)))
        for i in range(100):
            node = ext(b"", node, i)
        add("empty-extension-chain", node, raw)
    for arity in (0, 1, 15, 16, 17):
        for i in range(16):
            raw = bytes([i << 4]) + bytes(31)
            p = digits(raw)
            for selected in (None, stub(), leaf(p[1:], b"\0\xff\0", i + 11)):
                cs = [stub(999)] * arity
                if i < arity:
                    cs[i] = selected
                add("selected-arity", branch(cs, b"nonterminal ignored", arity), raw)
        add(
            "terminal-before-bounds",
            ext(bytes(64), branch([stub()] * arity, b"\0\xff\0")),
        )
        add("terminal-empty", ext(bytes(64), branch([stub()] * arity)))
    rng = random.Random(context.seed)
    for j in range(80):
        raw = bytes(rng.randrange(256) for _ in range(32))
        p = digits(raw)
        cut = rng.randrange(65)
        node = leaf(p[cut:], bytes(rng.randrange(256) for _ in range(j % 33)), j)
        node = ext(p[:cut], node, j + 1)
        add("random-full-prefix", node, raw)

    def view(node):
        if node is None:
            return None
        if type(node) is inc.HashedNode:
            return dict(kind="hashed", hash=bytes(node._hash).hex())
        common = dict(
            rlp=None if node._rlp is None else bytes(node._rlp).hex(),
            hash=None if node._hash is None else bytes(node._hash).hex(),
            dirty=node._dirty,
        )
        require(
            type(node._dirty) is bool
            and node._dirty is False
            and type(node._rlp) is bytes,
            "represented completed-cache premise failed",
        )
        if type(node) is inc.MutableLeafNode:
            require(
                type(node.rest_of_key) is bytes and type(node.value) is bytes,
                "bad leaf source fields",
            )
            return dict(
                kind="leaf",
                path=node.rest_of_key.hex(),
                value=node.value.hex(),
                **common,
            )
        if type(node) is inc.MutableExtensionNode:
            require(type(node.key_segment) is bytes, "bad extension source field")
            return dict(
                kind="ext",
                path=node.key_segment.hex(),
                child=view(node.child),
                **common,
            )
        require(
            type(node) is inc.MutableBranchNode
            and type(node.children) is list
            and type(node.value) is bytes,
            "bad branch source fields",
        )
        return dict(
            kind="branch",
            children=[view(x) for x in node.children],
            value=node.value.hex(),
            **common,
        )

    def byte_wire(raw):
        return [len(raw), *raw]

    def node_wire(v):
        if v is None:
            return [0]
        if v["kind"] == "hashed":
            return [1, *bytes.fromhex(v["hash"])]
        enc = byte_wire(bytes.fromhex(v["rlp"])) + (
            [0] if v["hash"] is None else [1, *bytes.fromhex(v["hash"])]
        )
        if v["kind"] == "leaf":
            return [
                2,
                *byte_wire(bytes.fromhex(v["path"])),
                *byte_wire(bytes.fromhex(v["value"])),
                *enc,
            ]
        if v["kind"] == "ext":
            return [
                3,
                *byte_wire(bytes.fromhex(v["path"])),
                *enc,
                *node_wire(v["child"]),
            ]
        return [
            4,
            *byte_wire(bytes.fromhex(v["value"])),
            *enc,
            len(v["children"]),
            *[a for c in v["children"] for a in node_wire(c)],
        ]

    def lean_bytes(raw):
        return "bytes [" + ",".join(str(x) for x in raw) + "]"

    def lean_ref(v):
        return "none" if v is None else "some (" + lean_node(v) + ")"

    def lean_node(v):
        if v["kind"] == "hashed":
            return ".hashed (hash " + str(int(v["hash"], 16)) + ")"
        enc = (
            "⟨"
            + lean_bytes(bytes.fromhex(v["rlp"]))
            + ", "
            + (
                "none"
                if v["hash"] is None
                else "some (hash " + str(int(v["hash"], 16)) + ")"
            )
            + "⟩"
        )
        if v["kind"] == "leaf":
            return (
                ".leaf (path ["
                + ",".join(str(x) for x in bytes.fromhex(v["path"]))
                + "]) ("
                + lean_bytes(bytes.fromhex(v["value"]))
                + ") "
                + enc
            )
        if v["kind"] == "ext":
            return (
                ".ext (path ["
                + ",".join(str(x) for x in bytes.fromhex(v["path"]))
                + "]) ("
                + lean_node(v["child"])
                + ") "
                + enc
            )
        return (
            ".branch #["
            + ",".join(lean_ref(c) for c in v["children"])
            + "] ("
            + lean_bytes(bytes.fromhex(v["value"]))
            + ") "
            + enc
        )

    observations, expected, declarations = [], [], []
    for i, (name, root, key) in enumerate(cases):
        require(type(key) is Hash32 and len(key) == 32, "actual Hash32 key required")
        before = view(root)
        effects = []
        thrown = []
        frame_locals = {}
        record(
            dict(phase="before", case=i, name=name, input=before, key=bytes(key).hex())
        )

        def trace(frame, event, arg):
            filename = frame.f_code.co_filename
            protocol_effect = (
                filename.endswith("/ethereum/crypto/hash.py")
                and frame.f_code.co_name == "keccak256"
                or filename.endswith("/ethereum_rlp/rlp.py")
                and frame.f_code.co_name in ("encode", "decode")
                or filename.endswith("/src/ethereum/state.py")
            )
            if event == "call" and protocol_effect:
                effects.append((frame.f_code.co_filename, frame.f_code.co_name))
            if frame.f_code is fn.__code__ and event == "exception":
                frame_locals.update(frame.f_locals)
                thrown.append(
                    dict(
                        line=frame.f_lineno,
                        class_name=arg[0].__qualname__,
                        message=str(arg[1]),
                    )
                )
            return trace

        prior_trace = sys.gettrace()
        try:
            sys.settrace(trace)
            value = fn(root, key)
            require(
                value is None or type(value) is bytes,
                "unexpected original optional byte class",
            )
            outcome = dict(kind="value", value=None if value is None else value.hex())
            result = [1, 0] if value is None else [1, 1, *byte_wire(value)]
        except (AssertionError, IndexError) as error:
            tb = traceback.extract_tb(error.__traceback__)
            outcome = dict(
                kind="exception",
                class_module=type(error).__module__,
                class_name=type(error).__qualname__,
                message=str(error),
                args=list(error.args),
                traceback=[
                    dict(file=x.filename, line=x.lineno, name=x.name) for x in tb
                ],
            )
            record(dict(phase="exception", case=i, outcome=outcome, thrown=thrown))
            if type(error) is AssertionError:
                require(
                    type(frame_locals.get("node")) is inc.HashedNode
                    and thrown[-1]["line"] == 73,
                    "unexpected assertion source",
                )
                result = [0, 2, *bytes(frame_locals["node"]._hash)]
            else:
                node = frame_locals.get("node")
                idx = frame_locals.get("idx")
                require(
                    type(node) is inc.MutableBranchNode
                    and type(idx) is int
                    and idx >= len(node.children)
                    and thrown[-1]["line"] == 98,
                    "unexpected IndexError source",
                )
                result = [0, 1, 11, idx, len(node.children)]
                outcome["typed_adaptation_only"] = dict(
                    index=idx, arity=len(node.children)
                )
        finally:
            sys.settrace(prior_trace)
        after = view(root)
        record(
            dict(
                phase="post-call", case=i, input=after, outcome=outcome, effects=effects
            )
        )
        require(
            before == after and effects == [],
            "pure lookup changed fields or used local codec/hash/state",
        )
        observation = dict(
            case=i,
            name=name,
            key_class=type(key).__qualname__,
            key=bytes(key).hex(),
            before=before,
            after=after,
            outcome=outcome,
            exceptions=thrown,
            local_effect_calls=effects,
        )
        observations.append(observation)
        record(dict(phase="after", **observation))
        expected.append(
            dict(
                case=i,
                key=byte_wire(digits(key)),
                input=node_wire(before),
                result=result,
            )
        )
        declarations += [
            f"private def root{i} : Ref := {lean_ref(before)}",
            f"private def key{i} : Nibbles := bytesToNibbleList ({lean_bytes(key)})",
            f"#eval emit {i} root{i} key{i}",
        ]
    after_identity = snapshot()
    require(before_identity == after_identity, "source identities changed")
    prefix = (ROOT / "STFSpec/Conformance/Commit/DecoderGuards.lean").read_text()
    helpers = prefix[
        prefix.index("private def byteWire") : prefix.index("private def resultWire")
    ]
    args.output.write_text(
        """import Lean
import STFSpec.Commit
open Lean STFSpec.Base STFSpec.Commit
private def bytes (xs : List UInt8) : ByteArray := xs.toByteArray
private def path (xs : List (Fin 16)) : Nibbles := Nibbles.ofList xs
private def hash (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
"""
        + helpers
        + """
private def valueWire : Except TrieError (Option ByteArray) → List Nat
  | .error e => 0 :: errorWire e
  | .ok none => [1, 0]
  | .ok (some b) => 1 :: 1 :: byteWire b
private def jsonNats (xs : List Nat) : Lean.Json := toJson xs
private def emit (i : Nat) (root : Ref) (key : Nibbles) : IO Unit :=
  IO.println ((Lean.Json.mkObj [("case", toJson i), ("key", jsonNats (pathWire key)),
    ("input", jsonNats (refWire root)), ("result", jsonNats (valueWire (lookup root key)))]).compress)
"""
        + "\n".join(declarations)
        + "\n"
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
            ),
            indent=2,
        )
        + "\n"
    )
    execution = command(["lake", "env", "lean", str(args.output)], ROOT)
    require(execution.returncode == 0, "generated Lean lookup observer failed")
    actual = parse_records(execution.stdout.decode(), len(expected))
    require(actual == expected, "complete lookup input/key/value/error mismatch")
    snapshot()
    print(
        json.dumps(
            dict(
                seed=context.seed,
                cases=len(cases),
                values=sum(x["outcome"]["kind"] == "value" for x in observations),
                stub_errors=sum(
                    x["outcome"].get("class_name") == "AssertionError"
                    for x in observations
                ),
                index_adaptations=sum(
                    x["outcome"].get("class_name") == "IndexError" for x in observations
                ),
                whole_records_compared=len(actual),
                local_effect_calls=0,
                pin=context.head,
                generated=str(args.output),
                observations=str(meta),
            )
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
