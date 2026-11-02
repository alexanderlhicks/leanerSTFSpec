#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Fresh original-source completed leaves, compared with complete Id mkLeaf fields.

Run frozen EELS/.venv/bin/python -I -B with --eels, --output EXTERNAL.lean,
--rlp-wheel and --types-wheel. Both original caches must initially be None.
Actual source calls/classes/hashes are observed, never replaced. Source success
requires concrete classes, complete assembled Encodable and finite host/crypto
premises; arbitrary caches or partial failure object states are not simulated.
--self-test checks complete reply framing with ordinary Python and also -O.
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
        result = natural(self.values[self.offset])
        self.offset += 1
        return result

    def octets(self, count, bound=256):
        require(count <= len(self.values) - self.offset, "truncated bytes")
        result = [self.take() for _ in range(count)]
        require(all(x < bound for x in result), "out of range field")
        return result

    def array(self, bound=256):
        return self.octets(self.take(), bound)

    def leaf(self):
        require(self.take() == 2, "non-leaf result")
        path, value, raw = self.array(16), self.array(), self.array()
        tag = self.take()
        require(tag in (0, 1), "bad hash option")
        answer = None if tag == 0 else self.octets(32)
        require(self.offset == len(self.values), "trailing result bytes")
        return path, value, raw, answer


def parse_records(text, count):
    lines = text.splitlines()
    require(len(lines) == count, "missing/trailing records")
    rows = []
    for i, line in enumerate(lines):
        row = json.loads(line, object_pairs_hook=object_pairs)
        require(
            type(row) is dict and set(row) == {"case", "path", "value", "result"},
            "wrong reply fields",
        )
        require(natural(row["case"]) == i, "wrong case order")
        for name, bound in [("path", 16), ("value", 256)]:
            require(type(row[name]) is list, "input must be a list")
            require(all(natural(x) < bound for x in row[name]), "bad input field")
        p, v, _, _ = Reader(row["result"]).leaf()
        require(p == row["path"] and v == row["value"], "result lost input fields")
        rows.append(row)
    return rows


def parser_tests():
    good = dict(
        case=0,
        path=[0, 15],
        value=[0, 255, 0],
        result=[2, 2, 0, 15, 3, 0, 255, 0, 3, 0xC2, 0x20, 0x80, 1] + [0] * 31 + [7],
    )
    empty = dict(case=0, path=[], value=[], result=[2, 0, 0, 0, 0])
    require(parse_records(json.dumps(good), 1) == [good], "full leaf rejected")
    require(parse_records(json.dumps(empty), 1) == [empty], "empty fields rejected")
    bad = [
        "",
        json.dumps(good) + "\n" + json.dumps(good),
        json.dumps(dict(good, extra=0)),
        '{"case":0,"case":0,"path":[],"value":[],"result":[2,0,0,0,0]}',
    ]
    for field, values in [
        ("case", [True, -1, 0.0, 1]),
        ("path", [[16], [False], [0]]),
        ("value", [[256], [-1], [0.0], [0, 255]]),
        (
            "result",
            [
                [],
                [9],
                good["result"] + [0],
                [2, 0, 0, 0, 2],
                [2, 0, 0, 0, 1] + [0] * 31,
            ],
        ),
    ]:
        for value in values:
            bad.append(json.dumps(dict(good, **{field: value})))
    for cut in range(len(good["result"])):
        bad.append(json.dumps(dict(good, result=good["result"][:cut])))
    for pos in range(len(good["result"])):
        for invalid in (True, -1, 1.5):
            result = good["result"].copy()
            result[pos] = invalid
            bad.append(json.dumps(dict(good, result=result)))
    swapped = json.dumps(dict(good, case=1)) + "\n" + json.dumps(good)
    bad.append(swapped)
    for text in bad:
        try:
            parse_records(text, 2 if text == swapped else 1)
        except (ValueError, TypeError, json.JSONDecodeError):
            continue
        raise RuntimeError("invalid complete leaf reply accepted: " + text)
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
        "--extra-boundaries",
        action="store_true",
        help="run only additional HP and joined-payload boundaries",
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

    context = CapturedDriver(__doc__, Path(__file__), 151)
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
    functions = [
        fn,
        inc._encode_mutable_node,
        mpt.nibble_list_to_compact,
        hash_module.keccak256,
        rlp.encode,
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
            identities == [(id(f), id(f.__code__)) for f in functions],
            "function code replaced",
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

    before_identity = snapshot()
    args.output.with_suffix(".before-identity.json").write_text(
        json.dumps(before_identity, indent=2) + "\n"
    )
    journal = args.output.with_suffix(".source-journal.jsonl")

    def record(row):
        with journal.open("a") as stream:
            stream.write(json.dumps(row) + "\n")

    def view(node):
        require(
            type(node) is cls
            and type(node.rest_of_key) is Bytes
            and type(node.value) is Bytes
            and type(node._dirty) is bool
            and all(x < 16 for x in node.rest_of_key),
            "fresh leaf class/field premise failed",
        )
        require(node._rlp is None or type(node._rlp) is Bytes, "raw class differs")
        require(node._hash is None or type(node._hash) is Bytes32, "hash class differs")
        return dict(
            path=list(node.rest_of_key),
            value=list(node.value),
            dirty=node._dirty,
            raw=None if node._rlp is None else list(node._rlp),
            hash=None if node._hash is None else list(node._hash),
        )

    inputs = []
    for n in (0, 1, 2, 63, 64, 65):
        for size in (0, 1, 28, 29, 30, 53, 54, 55, 56, 253, 254, 255, 256):
            inputs.append(
                (
                    "path/value-prefix-boundary",
                    bytes(i % 16 for i in range(n)),
                    bytes(i % 256 for i in range(size)),
                )
            )
    for n in range(16):
        inputs.append(("all-digits", bytes([n]), bytes([0, n, 255, 0])))
    for v in (b"", b"\0", b"\x7f", b"\x80", b"\xff", bytes(range(256))):
        for p in (b"", b"\0", b"\0\0", b"\x0f\0\x0f"):
            inputs.append(("byte/zero-boundary", p, v))
    rng = random.Random(context.seed)
    for i in range(40):
        inputs.append(
            (
                "seeded-complete-leaf",
                bytes(rng.randrange(16) for _ in range(i % 67)),
                bytes(rng.randrange(256) for _ in range((i * 17) % 300)),
            )
        )
    if wheels.extra_boundaries:
        inputs = [
            ("HP-field-prefix-boundary", bytes(i % 16 for i in range(n)), bytes(size))
            for n in (108, 110, 508, 510)
            for size in (0, 1)
        ]
        inputs += [("joined-payload-255/256", b"", bytes(size)) for size in (252, 253)]
    expected, observations, expressions = [], [], []
    for name, p, v in inputs:
        for dirty in (False, True):
            i = len(expected)
            node = cls(Bytes(p), Bytes(v), _dirty=dirty)
            before = view(node)
            require(
                before["raw"] is None and before["hash"] is None,
                "initial caches present",
            )
            calls, errors = [], []
            record(dict(phase="before", case=i, name=name, input=before))

            def trace(frame, event, arg):
                if frame.f_code is hash_module.keccak256.__code__:
                    if event == "call":
                        calls.append(
                            dict(preimage=list(frame.f_locals["buffer"]), answer=None)
                        )
                    elif event == "return":
                        calls[-1]["answer"] = None if arg is None else list(arg)
                if event == "exception" and frame.f_code is fn.__code__:
                    errors.append(
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
                h, raw = fn(node)
            except Exception as error:
                record(
                    dict(
                        phase="original-error",
                        case=i,
                        after=view(node),
                        calls=calls,
                        throw_stages=errors,
                        class_name=type(error).__qualname__,
                        message=str(error),
                        traceback=traceback.format_exc(),
                    )
                )
                raise
            finally:
                sys.settrace(previous)
            after = view(node)
            require(
                type(raw) is Bytes and (h is None or type(h) is Bytes32),
                "returned source class differs",
            )
            require(
                after["path"] == before["path"]
                and after["value"] == before["value"]
                and after["dirty"] == dirty
                and after["raw"] == list(raw)
                and after["hash"] == (None if h is None else list(h)),
                "fresh complete fields differ",
            )
            require(
                calls
                == (
                    [] if len(raw) < 32 else [dict(preimage=list(raw), answer=list(h))]
                ),
                "wrong complete hash call/answer",
            )
            require((h is None) == (len(raw) < 32), "wrong fresh cache presence")
            row = dict(
                case=i,
                path=list(p),
                value=list(v),
                result=[
                    2,
                    len(p),
                    *p,
                    len(v),
                    *v,
                    len(raw),
                    *raw,
                    *([0] if h is None else [1, *h]),
                ],
            )
            expected.append(row)
            observation = dict(
                case=i,
                name=name,
                before=before,
                after=after,
                hash_calls=calls,
                result=dict(hash=None if h is None else list(h), raw=list(raw)),
                throw_stages=errors,
            )
            observations.append(observation)
            record(dict(phase="after", **observation))
            expressions.append(
                "(path ["
                + ",".join(map(str, p))
                + "], bytes ["
                + ",".join(map(str, v))
                + "])"
            )
    after_identity = snapshot()
    require(before_identity == after_identity, "source identities changed")
    args.output.with_suffix(".after-identity.json").write_text(
        json.dumps(after_identity, indent=2) + "\n"
    )
    guards = (ROOT / "STFSpec/Conformance/Commit/LeafGuards.lean").read_text()
    observer = guards[
        guards.index("private def wireBytes") : guards.index(
            "\nend STFSpec.Conformance.Commit.LeafGuards"
        )
    ]
    args.output.write_text(
        """import STFSpec.Commit
open STFSpec.Base STFSpec.Commit
set_option maxRecDepth 100000
private def bytes (xs : List UInt8) : ByteArray := xs.toByteArray
private def path (xs : List (Fin 16)) : Nibbles := Nibbles.ofList xs
"""
        + observer
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
            ),
            indent=2,
        )
        + "\n"
    )
    execution = command(["lake", "env", "lean", str(args.output)], ROOT)
    require(execution.returncode == 0, "generated complete-leaf observer failed")
    actual = parse_records(execution.stdout.decode(), len(expected))
    require(actual == expected, "full leaf fields/cache mismatch")
    snapshot()
    print(
        json.dumps(
            dict(
                seed=context.seed,
                cases=len(expected),
                complete_records=len(actual),
                query_count=sum(len(x["hash_calls"]) for x in observations),
                raw_widths=sorted({len(x["result"]["raw"]) for x in observations}),
                pin=context.head,
                generated=str(args.output),
                observations=str(meta),
            )
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
