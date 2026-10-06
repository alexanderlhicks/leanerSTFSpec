#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Complete finite acyclic decoder comparisons against the original pinned EELS.

Use frozen EELS/.venv/bin/python -I -B, --eels EELS --output EXTERNAL.lean,
--rlp-wheel WHEEL and --types-wheel WHEEL. Source and installed package bytes are
authenticated before import and after execution. The interpreter, host, frozen
installation/RECORD and crypto backend remain trusted inputs. Original functions
are traced without replacement; all recursive fields, raw/cache bytes, concrete
query preimages/answers and original first errors are compared. Cycles belong to
the deterministic Lean controls, never a Python recursion-limit oracle.
Use --self-test with ordinary Python (also -O) for strict output-parser controls.
"""

import argparse
import base64
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
from textwrap import dedent
import zipfile

ROOT = Path(__file__).resolve().parents[3]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def natural(value):
    require(type(value) is int and value >= 0, "expected exact nonnegative integer")
    return value


class WireReader:
    """Length framing rejects invalid tags, truncation, widths and trailing data."""

    def __init__(self, values):
        require(type(values) is list, "wire must be a list")
        self.values = [natural(x) for x in values]
        self.offset = 0

    def take(self):
        require(self.offset < len(self.values), "truncated wire")
        x = self.values[self.offset]
        self.offset += 1
        return x

    def octets(self, width):
        for _ in range(width):
            require(self.take() < 256, "byte outside UInt8")

    def byte_array(self):
        self.octets(self.take())

    def path(self):
        for _ in range(self.take()):
            require(self.take() < 16, "nibble outside Fin 16")

    def enc(self):
        self.byte_array()
        flag = self.take()
        require(flag in (0, 1), "bad cache tag")
        if flag == 1:
            self.octets(32)

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
            count = self.take()
            require(count == 16, "decoder branch width differs from sixteen")
            for _ in range(count):
                self.ref()
        else:
            raise ValueError("bad node tag")

    def result(self):
        tag = self.take()
        require(tag in (0, 1), "bad result tag")
        if tag == 1:
            require(self.take() in (0, 1), "bad returned secured tag")
            self.ref()
        else:
            error = self.take()
            if error in (0, 2):
                self.octets(32)
            elif error == 1:
                why = self.take()
                require(why <= 11, "bad malformed tag")
                if why in (6, 7, 9):
                    self.take()
                elif why == 11:
                    self.take()
                    self.take()
            else:
                raise ValueError("bad error tag")

    def finish(self):
        require(self.offset == len(self.values), "trailing wire data")


def object_pairs(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON field")
        result[key] = value
    return result


def parse_records(text, count):
    lines = text.splitlines()
    require(len(lines) == count, "missing or trailing output records")
    result = []
    for index, line in enumerate(lines):
        row = json.loads(line, object_pairs_hook=object_pairs)
        require(
            type(row) is dict
            and set(row) == {"case", "input_secured", "id", "result", "queries"},
            "wrong output fields",
        )
        require(natural(row["case"]) == index, "duplicate/out-of-order case")
        require(type(row["input_secured"]) is bool, "input_secured must be exact Bool")
        for field in ("id", "result"):
            reader = WireReader(row[field])
            reader.result()
            reader.finish()
        require(type(row["queries"]) is list, "queries must be a list")
        for query in row["queries"]:
            reader = WireReader(query)
            reader.byte_array()
            reader.octets(32)
            reader.finish()
        result.append(row)
    return result


def parser_tests():
    good = dict(case=0, input_secured=False, id=[1, 0, 0], result=[1, 0, 0], queries=[])
    require(parse_records(json.dumps(good), 1) == [good], "valid record rejected")
    returned_true = dict(good, input_secured=True, id=[1, 1, 0], result=[1, 1, 0])
    require(
        parse_records(json.dumps(returned_true), 1) == [returned_true],
        "valid returned true flag rejected",
    )
    probes = []
    for field, value in [
        ("case", True),
        ("case", -1),
        ("case", 0.0),
        ("input_secured", 0),
        ("result", [True, 0]),
        ("result", [1, True, 0]),
        ("result", [1, 2, 0]),
        ("result", [1, 0]),
        ("result", [1, 0, 1] + [0] * 31),
        ("result", [1, 0, 2, 1, 16, 0, 0, 0]),
        ("result", [1, 0, 0, 9]),
        ("result", [1, 0, 9]),
        ("queries", [[0] + [0] * 31]),
        ("queries", [[1, 256] + [0] * 32]),
        ("queries", [[0] + [0] * 33]),
    ]:
        row = dict(good)
        row[field] = value
        probes.append((json.dumps(row), 1))
    probes += [
        (json.dumps(good) + "\n" + json.dumps(good), 1),
        ("", 1),
        (
            '{"case":0,"case":0,"input_secured":false,"id":[1,0,0],"result":[1,0,0],"queries":[]}',
            1,
        ),
    ]
    row = dict(good, extra=0)
    probes.append((json.dumps(row), 1))
    for field in ("id", "result"):
        for payload in ([0, 0], [15, 3], [10**100, 10**200]):
            row = dict(good)
            row[field] = [0, 1, 11] + payload
            require(
                parse_records(json.dumps(row), 1) == [row],
                "two-field diagnostic rejected",
            )
        for wire in (
            [0, 1, 11],
            [0, 1, 11, 0],
            [0, 1, 11, 0, 0, 0],
            [0, 1, 12, 0, 0],
            [0, 1, 11, True, 0],
            [0, 1, 11, 0, True],
            [0, 1, 11, 0.0, 0],
            [0, 1, 11, 0, 0.0],
            [0, 1, 11, -1, 0],
            [0, 1, 11, 0, -1],
        ):
            row = dict(good)
            row[field] = wire
            probes.append((json.dumps(row), 1))
    for text, count in probes:
        try:
            parse_records(text, count)
        except (ValueError, TypeError, json.JSONDecodeError):
            continue
        raise RuntimeError("invalid framing probe accepted: " + text)
    print(
        json.dumps(
            {"parser_rejection_controls": len(probes), "optimized": sys.flags.optimize}
        )
    )


def main():
    if sys.argv[1:] == ["--self-test"]:
        parser_tests()
        return 0
    require(
        sys.flags.isolated and sys.flags.dont_write_bytecode and not sys.flags.optimize,
        "use frozen unoptimized interpreter -I -B",
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

    output_parser = argparse.ArgumentParser(add_help=False)
    output_parser.add_argument("--output", type=Path, required=True)
    destination, _ = output_parser.parse_known_args(remainder)
    log = destination.output.resolve().parent / "decoder-reference-commands"
    log.mkdir(exist_ok=False)
    counter = 0

    def command(argv, cwd, input=None, env=None):
        nonlocal counter
        counter += 1
        directory = log / f"{counter:04d}"
        directory.mkdir()
        start = datetime.datetime.now(datetime.timezone.utc).isoformat()
        if input is not None:
            (directory / "stdin").write_bytes(input)
        (directory / "argv.nul").write_bytes(
            b"\0".join(os.fsencode(a) for a in argv) + b"\0"
        )
        result = subprocess.run(
            argv, cwd=cwd, input=input, env=env, capture_output=True
        )
        (directory / "stdout").write_bytes(result.stdout)
        (directory / "stderr").write_bytes(result.stderr)
        (directory / "command.json").write_text(
            json.dumps(
                dict(
                    argv=[str(a) for a in argv],
                    cwd=str(cwd),
                    started=start,
                    ended=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                    exit=result.returncode,
                ),
                indent=2,
            )
            + "\n"
        )
        return result

    class CapturedDriver(Driver):
        def git(self, *args, input=None, text=False):
            env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
            result = command(
                ["git", "--no-replace-objects", "--no-optional-locks", *args],
                self.eels,
                input=input,
                env=env,
            )
            require(result.returncode == 0, "reference Git acquisition failed")
            return result.stdout.decode() if text else result.stdout

    context = CapturedDriver(__doc__, Path(__file__), 142)
    auth = RlpSourceAuth(context)
    sys.meta_path.insert(0, RlpFreshFinder(auth))
    pin = tomllib.loads((ROOT / "reference.toml").read_text())["release"]
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
    crypto_dist = importlib.metadata.distribution("pycryptodome")
    require(
        crypto_dist.version == pin["python_dependencies"]["pycryptodome"],
        "crypto version mismatch",
    )
    crypto_files, crypto_records = {}, []
    for file in crypto_dist.files or []:
        source = Path(crypto_dist.locate_file(file)).absolute()
        if file.name == "RECORD" and file.parent.name.endswith(".dist-info"):
            crypto_records.append(source)
        if file.parts and file.parts[0] == "Crypto":
            require(
                source.resolve() == source
                and source.is_relative_to(context.eels / ".venv")
                and file.hash is not None
                and file.hash.mode == "sha256"
                and file.size is not None,
                "invalid crypto RECORD entry",
            )
            contents = source.read_bytes()
            digest = (
                base64.urlsafe_b64encode(hashlib.sha256(contents).digest())
                .decode()
                .rstrip("=")
            )
            require(
                (digest, len(contents)) == (file.hash.value, file.size),
                "crypto bytes differ from RECORD",
            )
            crypto_files[source] = hashlib.sha256(contents).hexdigest()
    require(len(crypto_records) == 1, "crypto RECORD missing/ambiguous")
    crypto_record = crypto_records[0].read_bytes()
    crypto_package = Path(crypto_dist.locate_file("Crypto")).absolute()

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
            crypto_records[0].read_bytes() == crypto_record, "crypto RECORD changed"
        )
        require(
            set(crypto_package.rglob("*.py"))
            == {p for p in crypto_files if p.suffix == ".py"},
            "crypto Python inventory changed",
        )
        for source, digest in crypto_files.items():
            require(
                hashlib.sha256(source.read_bytes()).hexdigest() == digest,
                "crypto source changed",
            )
        return dict(
            pin=context.head,
            source_lock={
                name: dict(
                    blob=blob,
                    sha256=hashlib.sha256(
                        (context.eels / name).read_bytes()
                    ).hexdigest(),
                )
                for name, blob in context.oracle_blobs.items()
            },
            wheels=wheel_rows,
            types_sources=context.dependency_sources(),
            types_record_sha256=hashlib.sha256(
                context.dependency_record_bytes
            ).hexdigest(),
            rlp_sources={str(p): digest for p, digest in auth.expected.items()},
            rlp_record_sha256=hashlib.sha256(auth.record_bytes).hexdigest(),
            crypto_sources={str(p): digest for p, digest in crypto_files.items()},
            crypto_record_sha256=hashlib.sha256(crypto_record).hexdigest(),
        )

    before = snapshot()
    from ethereum_rlp import rlp
    from ethereum_types.bytes import Bytes, Bytes32
    from ethereum.forks.amsterdam import incremental_mpt as inc
    from ethereum.crypto import hash as crypto

    context.check_source(inc, "ethereum/forks/amsterdam/incremental_mpt.py")
    context.check_source(crypto, "ethereum/crypto/hash.py")
    context.check_source(rlp, "ethereum_rlp/rlp.py", dependency=True)
    require(Bytes is bytes, "unexpected Bytes class")
    functions = [
        inc._decode_witness_node,
        inc._resolve_child_ref,
        inc.compact_to_nibbles,
        inc.decode_witness_to_mpt,
        rlp.decode,
        crypto.keccak256,
    ]
    codes = [(fn, fn.__code__) for fn in functions]

    def octets(value):
        require(type(value) in (bytes, Bytes32), "unexpected source byte class")
        return list(value)

    def byte_wire(value):
        return [len(value)] + octets(value)

    def enc_wire(node):
        require(
            type(node._dirty) is bool and node._dirty is False,
            "unexpected source dirty state",
        )
        require(node._rlp is not None, "source completed node lacks raw bytes")
        return byte_wire(node._rlp) + (
            [0] if node._hash is None else [1] + octets(node._hash)
        )

    def node_wire(node):
        if node is None:
            return [0]
        if type(node) is inc.HashedNode:
            require(len(node._hash) == 32, "wrong source hash width")
            return [1] + octets(node._hash)
        if type(node) is inc.MutableLeafNode:
            path = octets(node.rest_of_key)
            return [2, len(path)] + path + byte_wire(node.value) + enc_wire(node)
        if type(node) is inc.MutableExtensionNode:
            path = octets(node.key_segment)
            return [3, len(path)] + path + enc_wire(node) + node_wire(node.child)
        if type(node) is inc.MutableBranchNode:
            require(
                type(node.children) is list and len(node.children) == 16,
                "source children width",
            )
            return (
                [4]
                + byte_wire(node.value)
                + enc_wire(node)
                + [16]
                + sum((node_wire(child) for child in node.children), [])
            )
        raise TypeError("unexpected source node class")

    def source_raw(value):
        cls = type(value)
        if cls in (bytes, Bytes32):
            return dict(
                class_name=cls.__module__ + "." + cls.__qualname__,
                hex=value.hex(),
                length=len(value),
            )
        if value is None or cls in (bool, str, int):
            return dict(class_name=cls.__name__, value=value)
        if cls in (list, tuple):
            return dict(class_name=cls.__name__, items=[source_raw(x) for x in value])
        if hasattr(value, "__dataclass_fields__"):
            return dict(
                class_name=cls.__module__ + "." + cls.__qualname__,
                fields={
                    name: source_raw(getattr(value, name))
                    for name in value.__dataclass_fields__
                },
            )
        if cls is dict:
            return dict(
                class_name="dict",
                entries=[[source_raw(k), source_raw(v)] for k, v in value.items()],
            )
        raise TypeError("unclassified source field " + repr(cls))

    def exception_wire(exc, root):
        if type(exc) is KeyError:
            require(exc.args == (root,), "unexpected source lookup failure")
            return [0, 0] + octets(root)
        if type(exc) is rlp.DecodingError:
            return [0, 1, 0]
        sites = []
        tb = exc.__traceback__
        while tb is not None:
            sites.append((tb.tb_frame.f_code, tb.tb_lineno, tb.tb_frame.f_locals))
            tb = tb.tb_next
        if type(exc) is IndexError:
            require(
                sites[-1][0] is inc.compact_to_nibbles.__code__,
                "unexpected IndexError site",
            )
            return [0, 1, 3]
        require(type(exc) is AssertionError, "unexpected source failure")
        message = str(exc)
        if message == "Expected empty node":
            return [0, 1, 1]
        if message == "ExtensionNode must have a non-empty path":
            return [0, 1, 5]
        if message == "ExtensionNode child must be a BranchNode":
            return [0, 1, 8]
        if message.startswith("Unexpected child ref length: "):
            return [0, 1, 7, len(sites[-1][2]["ref_bytes"])]
        if message.startswith("Invalid RLP node length: "):
            return [0, 1, 6, len(sites[-1][2]["decoded"])]
        if message == "BranchNode must have at least 2 occupied entries":
            return [0, 1, 9, natural(sites[-1][2]["occupied"])]
        require(
            not exc.args and sites[-1][0] is inc._decode_witness_node.__code__,
            "unknown assertion site",
        )
        # The original failing assertion line, rather than a second decoder model,
        # distinguishes the two empty-message field-shape assertions.
        source_line = (
            Path(sites[-1][0].co_filename)
            .read_text()
            .splitlines()[sites[-1][1] - 1]
            .strip()
        )
        if source_line == "assert isinstance(path_bytes, (bytes, bytearray))":
            return [0, 1, 2]
        if source_line == "assert isinstance(value, (bytes, bytearray))":
            return [0, 1, 4]
        raise ValueError("unclassified original assertion: " + source_line)

    def observe(db, root, secured, traced=True):
        queries = []

        def trace(frame, event, arg):
            if frame.f_code is crypto.keccak256.__code__ and event == "return":
                queries.append(byte_wire(frame.f_locals["buffer"]) + octets(arg))
            return trace

        require(sys.gettrace() is None, "preexisting trace hook")
        if traced:
            sys.settrace(trace)
        try:
            try:
                trie = inc.decode_witness_to_mpt(db, root, secured, b"")
                require(
                    type(trie) is inc.IncrementalMPT
                    and type(trie.secured) is bool
                    and trie.secured is secured,
                    "source wrapper flag mismatch",
                )
                result = [1, int(trie.secured)] + node_wire(trie.root_node)
                raw = source_raw(trie)
            except (KeyError, AssertionError, IndexError, rlp.DecodingError) as exc:
                result = exception_wire(exc, root)
                raw = dict(
                    class_name=type(exc).__module__ + "." + type(exc).__qualname__,
                    message=str(exc),
                    args=source_raw(exc.args),
                )
        finally:
            sys.settrace(None)
        require(
            all(fn.__code__ is code for fn, code in codes),
            "original source function replaced",
        )
        return result, queries, raw

    def key(n):
        return Bytes32(n.to_bytes(32, "big"))

    cases = []

    def add(name, raw=None, extra=(), root=None):
        db = {} if raw is None else {key(1): Bytes(raw)}
        db.update({key(n): Bytes(value) for n, value in extra})
        cases.append((name, db, key(1) if root is None else root))

    def leaf(width=0, flag=0x20):
        return [bytes([flag]), b"z" * width]

    def ext(child, flag=0x11):
        return [bytes([flag]), child]

    def branch(children, value=b""):
        return children + [value]

    empty = Bytes32(inc.EMPTY_TRIE_ROOT)
    add("empty-bypass", b"\xff" * 40, root=empty)
    cases[-1][1][empty] = b"\xff" * 40
    add("missing")
    for flag in range(256):
        add(f"compact-flag-{flag}", rlp.encode(leaf(flag=flag)))
    for width in (0, 1, 27, 28, 29, 30, 31, 32, 33, 56, 64):
        add(f"leaf-width-{width}", rlp.encode(leaf(width)))
    for i, raw in enumerate(
        [
            b"",
            b"\x80",
            b"\x00",
            b"\xc0",
            b"\xff" * 32,
            b"\xff" * 33,
            b"\xc1\x80\x00",
            b"\x81\x01",
            b"\xb8\x01\x80",
        ]
    ):
        add(f"raw-{i}", raw)
    for i, item in enumerate(
        [
            [[], []],
            [b"", []],
            [b"\x20", []],
            [b"\x00", b"\x01"],
            [b"\x11", b""],
            ext(leaf()),
            ext([]),
            ext(ext(b"")),
            ext(key(2)),
            ext(branch([key(2), key(3)] + [b""] * 14)),
            [b"", b"", b""],
        ]
    ):
        add(f"dispatch-{i}", rlp.encode(item))
    for width in (0, 1, 31, 32, 33):
        add(f"child-width-{width}", rlp.encode(branch([b"x" * width] + [b""] * 15)))
    for ending in (b"", b"v", [], [leaf()]):
        for count in range(3):
            add(
                f"occupancy-{count}-{repr(ending)}",
                rlp.encode(branch([key(2)] * count + [b""] * (16 - count), ending)),
            )
    for width in (0, 29, 56):
        add(
            f"present-width-{width}",
            rlp.encode(branch([key(2), key(3)] + [b""] * 14)),
            [(2, rlp.encode(leaf(width)))],
        )
        add(
            f"inline-width-{width}",
            rlp.encode(branch([leaf(width), key(3)] + [b""] * 14)),
        )
    raw = rlp.encode(branch([empty, key(2)] + [b""] * 14))
    add("empty-child-absent", raw)
    add("empty-child-present-80", raw)
    cases[-1][1][empty] = b"\x80"
    for position in range(16):
        add(
            f"first-error-{position}",
            rlp.encode(
                branch([leaf(29)] * position + [b"x"] + [leaf(29)] * (15 - position))
            ),
        )
        add(
            f"nested-error-{position}",
            rlp.encode(
                branch([leaf(29)] * position + [ext([])] + [leaf(29)] * (15 - position))
            ),
        )
    add(
        "repeated-sixteen",
        rlp.encode(branch([key(2)] * 16)),
        [(2, rlp.encode(leaf(29)))],
    )
    shared = branch([key(2), key(2)] + [b""] * 14)
    add(
        "diamond",
        rlp.encode(branch([shared, shared] + [b""] * 14)),
        [(2, rlp.encode(leaf(29)))],
    )
    rng = random.Random(context.seed)

    def tree(depth):
        if depth == 0 or rng.randrange(3) == 0:
            return leaf(
                rng.choice([0, 1, 29, 32]), rng.choice([0x20, 0x2F, 0x31, 0xF1])
            )
        if rng.randrange(2) == 0:
            return ext(tree(depth - 1))
        children = [b""] * 16
        for index in rng.sample(range(16), rng.randrange(1, 4)):
            children[index] = (
                tree(depth - 1) if rng.randrange(2) else key(rng.randrange(2, 10))
            )
        return branch(children, rng.choice([b"", b"v", []]))

    for index in range(24):
        add(f"acyclic-tree-{index}", rlp.encode(tree(3)))

    observations, expected, guards = [], [], []
    # Reuse only the observer source definitions; their old outcomes are not inputs.
    source = (ROOT / "STFSpec/Conformance/Commit/DecoderGuards.lean").read_text()
    observer = source[
        source.index("private def byteWire") : source.index("private abbrev Trace")
    ]
    guards = [
        "import STFSpec.Commit",
        "import Lean",
        "open STFSpec.Base STFSpec.Hash STFSpec.Codec STFSpec.Commit Lean",
        observer,
        "private abbrev Trace := List (ByteArray × Hash32)",
        dedent("""
            private def traceOracle (raw : ByteArray) : StateM Trace Hash32 := fun trace =>
              let h := keccak256 raw
              (h, trace ++ [(raw, h)])
            """).strip(),
        dedent("""
            private def emit (index : Nat) (secured : Bool) (empty r : Hash32)
                (db : NodeDB) : IO Unit := do
              letI : KeccakQuery (StateM Trace) := ⟨traceOracle⟩
              let (result, trace) :=
                (decodeWitnessToMpt (m := StateM Trace) empty db r secured).run []
              let project := fun (value : Except TrieError IncrementalMPT) => match value with
                | .error error => 0 :: errorWire error
                | .ok trie => 1 :: (if trie.secured then 1 else 0) :: refWire trie.root
              let idResult := decodeWitnessToMpt (m := Id) empty db r secured
              let wire := trace.map (fun (raw, h) => byteWire raw ++ hashWire h)
              IO.println ((Lean.Json.mkObj [
                ("case", toJson index), ("input_secured", toJson secured),
                ("id", toJson (project idResult)), ("result", toJson (project result)),
                ("queries", toJson wire)]).compress)
            """).strip(),
    ]

    def lean_bytes(raw):
        return f"(({list(raw)} : List UInt8).toByteArray)"

    def lean_hash(h):
        return f"(Hash32.ofBytes32 (FixedBytes.ofNat {int.from_bytes(h, 'big')}))"

    index = 0
    for name, db, root in cases:
        for secured in (False, True):
            result, queries, raw = observe(db, root, secured)
            # A fresh original replay without tracing verifies that the trace hook
            # leaves the returned complete source value/first failure unchanged.
            replay, replay_queries, replay_raw = observe(
                db, root, secured, traced=False
            )
            require(
                (result, raw) == (replay, replay_raw) and replay_queries == [],
                "source replay differs",
            )
            expected.append(
                dict(
                    case=index,
                    input_secured=secured,
                    id=result,
                    result=result,
                    queries=queries,
                )
            )
            observations.append(
                dict(
                    case=index,
                    name=name,
                    secured=secured,
                    root=source_raw(root),
                    db=[[source_raw(k), source_raw(v)] for k, v in db.items()],
                    complete_source_result=raw,
                    wire=result,
                    queries=queries,
                )
            )
            db_expr = "({} : Std.HashMap Hash32 ByteArray)"
            for h, value in db.items():
                db_expr = f"({db_expr}.insert {lean_hash(h)} {lean_bytes(value)})"
            guards.append(
                f"#eval emit {index} {str(secured).lower()} "
                f"{lean_hash(empty)} {lean_hash(root)} ⟨{db_expr}⟩"
            )
            index += 1
    context.output.write_text(
        "-- Generated finite decoder comparison evidence; do not commit.\n"
        + "\n".join(guards)
        + "\n"
    )
    context.output.with_suffix(".source.json").write_text(
        json.dumps(observations, indent=2) + "\n"
    )
    context.output.with_suffix(".identities.json").write_text(
        json.dumps(before, indent=2) + "\n"
    )
    result = command(["lake", "env", "lean", str(context.output)], ROOT)
    require(result.returncode == 0, "generated complete decoder driver failed")
    actual = parse_records(result.stdout.decode(), len(expected))
    require(actual == expected, "complete source/Id/state/query observations differ")
    after = snapshot()
    require(before == after, "reference inputs changed during comparisons")
    require(
        all(fn.__code__ is code for fn, code in codes),
        "original decoder function changed",
    )
    context.output.with_suffix(".actual.json").write_text(
        json.dumps(actual, indent=2) + "\n"
    )
    print(
        json.dumps(
            dict(
                cases=len(cases),
                records=len(expected),
                seed=context.seed,
                pin=context.head,
                full_fields=True,
                returned_secured=True,
                raw_cache_bytes=True,
                query_order=True,
                lean_exit=result.returncode,
            )
        )
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
