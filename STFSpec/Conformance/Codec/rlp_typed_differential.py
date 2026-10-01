#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Typed RLP model observations against locked ethereum-rlp 0.1.6.

Run EELS/.venv/bin/python -I -B with --eels EELS --output SCRATCH/observations.lean.
The shared driver authenticates EELS and ethereum-types. This driver additionally
checks installed ethereum-rlp RECORD/current source and compiles those bytes without
cached code. Interpreter, frozen installation and RECORD are trusted inputs.
Raw wire decoding, child schemas and model-only generic unions are separate.
"""
import base64
import hashlib
import importlib.abc
import importlib.machinery
import importlib.metadata
from pathlib import Path
import random
import sys
import tomllib

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from differential import setup_driver


class RlpSourceAuth:
    """Authenticate executed Python source against the installed trusted RECORD."""

    def __init__(self, context):
        distribution = importlib.metadata.distribution("ethereum-rlp")
        pinned_version = tomllib.loads((context.root / "reference.toml").read_text())["release"]["python_dependencies"]["ethereum-rlp"]
        if distribution.version != pinned_version:
            raise ImportError("ethereum-rlp version differs from reference.toml")
        self.package = Path(distribution.locate_file("ethereum_rlp")).absolute()
        self.expected = {}
        records = []
        for file in distribution.files or []:
            source = Path(distribution.locate_file(file)).absolute()
            if file.name == "RECORD" and file.parent.name.endswith(".dist-info"):
                records.append(source)
            if file.parts and file.parts[0] == "ethereum_rlp" and file.suffix == ".py":
                if (source.resolve() != source or not source.is_relative_to(context.eels / ".venv")
                        or file.hash is None or file.hash.mode != "sha256" or file.size is None):
                    raise ImportError(f"invalid ethereum-rlp source RECORD entry: {file}")
                data = source.read_bytes()
                digest = base64.urlsafe_b64encode(hashlib.sha256(data).digest()).decode().rstrip("=")
                if digest != file.hash.value or len(data) != file.size:
                    raise ImportError(f"ethereum-rlp source differs from RECORD: {file}")
                self.expected[source] = hashlib.sha256(data).hexdigest()
        if (len(records) != 1 or records[0].resolve() != records[0] or
                not records[0].is_relative_to(context.eels / ".venv") or not self.expected):
            raise ImportError("invalid ethereum-rlp RECORD location")
        self.record = records[0]
        self.record_bytes = self.record.read_bytes()
        self.check()

    @classmethod
    def for_fixture(cls, package, expected):
        """Generated trusted-package fixtures for cache and origin regression probes."""
        instance = cls.__new__(cls)
        instance.package, instance.expected = package, expected
        instance.record = None
        instance.check()
        return instance

    def verify(self, source, data):
        """Reject wrong origins, aliases and changed bytes at actual execution."""
        path = Path(source).absolute()
        if (path.resolve() != path or path not in self.expected or
                hashlib.sha256(data).hexdigest() != self.expected[path]):
            raise ImportError(f"unauthenticated ethereum-rlp source: {path}")

    def check(self):
        """Compare complete package source inventory and trusted metadata pre/post."""
        if set(self.package.rglob("*.py")) != set(self.expected):
            raise ImportError("ethereum-rlp source inventory changed")
        for path in self.expected:
            self.verify(path, path.read_bytes())
        if self.record is not None and self.record.read_bytes() != self.record_bytes:
            raise ImportError("ethereum-rlp RECORD changed")


class RlpFreshLoader(importlib.machinery.SourceFileLoader):
    """Compile verified current bytes directly rather than admitting cached code."""

    def __init__(self, fullname, path, auth):
        super().__init__(fullname, path)
        self.auth = auth

    def get_code(self, fullname):
        source = self.get_filename(fullname)
        data = self.get_data(source)
        self.auth.verify(source, data)
        return self.source_to_code(data, source)


class RlpFreshFinder(importlib.abc.MetaPathFinder):
    """Require installed authenticated source for every ethereum_rlp import."""

    def __init__(self, auth):
        self.auth = auth

    def find_spec(self, fullname, path=None, target=None):
        if fullname.split(".", 1)[0] != "ethereum_rlp":
            return None
        spec = importlib.machinery.PathFinder.find_spec(fullname, path)
        if spec is None or not isinstance(spec.loader, importlib.machinery.SourceFileLoader):
            raise ImportError(f"ethereum_rlp module is not source: {fullname}")
        self.auth.verify(spec.origin, Path(spec.origin).read_bytes())
        spec.loader = RlpFreshLoader(fullname, spec.origin, self.auth)
        return spec


def require_type(value, cls):
    """Exact type checks exclude Python bool/int equality and width/class confusion."""
    if type(value) is not cls:
        raise TypeError(f"expected exact {cls.__name__}, got {type(value).__name__}")


def main():
    context = setup_driver(__doc__, __file__, 5015)
    if not sys.flags.isolated or not sys.flags.dont_write_bytecode:
        context.parser.error("use the frozen interpreter -I -B")
    if any(name.split(".", 1)[0] == "ethereum_rlp" for name in sys.modules):
        raise ImportError("ethereum_rlp imported before authentication")
    auth = RlpSourceAuth(context)
    sys.meta_path.insert(0, RlpFreshFinder(auth))
    from ethereum_rlp import rlp
    from ethereum_types.numeric import Uint, U64, U256
    from ethereum_types.bytes import Bytes, Bytes0, Bytes20, Bytes32
    from dataclasses import make_dataclass
    from typing import Union
    context.check_source(rlp, "ethereum_rlp/rlp.py", dependency=True)
    rng = random.Random(context.seed)
    guards = ["import STFSpec.Codec", "open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base"]
    counts = {"integers": 0, "booleans": 0, "bytes": 0, "fixed": 0,
              "lists": 0, "fields": 0, "unions": 0, "integer_encodings": 0,
              "accepted": 0, "rejected": 0}

    def lean_bytes(data):
        return f"(ByteArray.mk ({list(data)} : List UInt8).toArray)"

    def leaf(data):
        return f"(RlpItem.bytes {lean_bytes(data)})" if type(data) is bytes else "(RlpItem.list [])"

    def observe(target, data):
        try:
            value = rlp.deserialize_to(target, data)
        except rlp.DecodingError:
            counts["rejected"] += 1
            return None
        counts["accepted"] += 1
        return value

    def guard_option(expression, expected):
        guards.append(f"#guard ({expression}).toOption = {expected}")

    cases = [b"", b"\x01", b"\x7f", b"\x80", b"\x01\x00", b"\x00", b"\x00\x01",
             b"\x00\x00\x01", bytes([255])*8, b"\x01"+bytes(8), bytes([255])*32,
             b"\x01"+bytes(32), [], [b""], [[b"\x01"]]]
    for width in [1, 7, 8, 9, 19, 20, 21, 31, 32, 33, 64, 128, 512]:
        cases += [bytes(rng.randrange(256) for _ in range(width)), bytes(width)]
    for cls, width in [(Uint, None), (U64, 8), (U256, 32)]:
        for data in cases:
            result = observe(cls, data)
            if result is not None:
                require_type(result, cls)
            op = "toNat" if width is None else f"toNatBounded {width}"
            guard_option(f"{op} {leaf(data)}", "none" if result is None else f"some {int(result)}")
            counts["integers"] += 1
    for n in [0, 1, 127, 128, 255, 256, 2**64-1, 2**64, 2**256, *[rng.getrandbits(512) for _ in range(16)]]:
        # The dependency minimal integer payload, not a wire-encoding claim.
        payload = Uint(n).to_be_bytes()
        require_type(payload, bytes)
        guards.append(f"#guard (toBytes (ofNat {n})).toOption = some {lean_bytes(payload)}")
        counts["integer_encodings"] += 1
    for data in cases + [b"\x02", b"\x01\x01", b"\xff"]:
        result = observe(bool, data)
        if result is not None:
            require_type(result, bool)
        guard_option(f"toBool {leaf(data)}", "none" if result is None else f"some {str(result).lower()}")
        counts["booleans"] += 1
    for data in cases:
        result = observe(Bytes, data)
        if result is not None:
            require_type(result, bytes)
        guard_option(f"toBytes {leaf(data)}", "none" if result is None else f"some {lean_bytes(result)}")
        counts["bytes"] += 1
    for cls, width in [(Bytes0, 0), (Bytes20, 20), (Bytes32, 32)]:
        for data in cases:
            result = observe(cls, data)
            if result is not None:
                require_type(result, cls)
            expression = f"(toFixed {width} {leaf(data)}).map (fun v => v.toBytes.toByteArray)"
            guard_option(expression, "none" if result is None else f"some {lean_bytes(result)}")
            counts["fixed"] += 1
    for data in [b"", [], [b""], [b"\x01", b"\x02"], [b"\x01"]*4]:
        result = observe(list[Bytes], data)
        if result is not None:
            require_type(result, list)
            for child in result:
                require_type(child, bytes)
        item = leaf(data) if type(data) is bytes else f"(RlpItem.list [{', '.join(leaf(x) for x in data)}])"
        children = "none" if result is None else f"some {[list(child) for child in result]}"
        guard_option(f"(toList {item}).map (fun xs => xs.map (fun child => ((toBytes child).toOption.getD ByteArray.empty).data.toList))", children)
        counts["lists"] += 1
        for n in range(4):
            cls = make_dataclass(f"Fields{n}", [(f"field{i}", Bytes) for i in range(n)])
            result = observe(cls, data)
            if result is not None:
                require_type(result, cls)
                for i in range(n):
                    require_type(getattr(result, f"field{i}"), bytes)
            children = "none" if result is None else f"some {[list(getattr(result, f'field{i}')) for i in range(n)]}"
            guard_option(f"(toFields {n} {item}).map (fun v => v.toList.map (fun child => ((toBytes child).toOption.getD ByteArray.empty).data.toList))", children)
            counts["fields"] += 1
    for data in cases:
        result = observe(Union[Bytes0, Bytes20], data)
        if result is not None and type(result) not in (Bytes0, Bytes20):
            raise TypeError("union returned unexpected variant class")
        expression = (f"union2 (fun x => (toFixed 0 x).map (fun v => v.toBytes.toByteArray)) "
                      f"(fun x => (toFixed 20 x).map (fun v => v.toBytes.toByteArray)) {leaf(data)}")
        guard_option(expression, "none" if result is None else f"some {lean_bytes(result)}")
        counts["unions"] += 1
    auth.check()
    exit_code = context.run(guards, counts=counts, ethereum_rlp="0.1.6",
                            rlp_sources={str(k): v for k, v in auth.expected.items()},
                            rlp_record_sha256=hashlib.sha256(auth.record_bytes).hexdigest(),
                            dependency_sources={str(k): {"sha256_urlsafe": v[0], "size": v[1]}
                                                for k, v in context.dependency_hashes.items()},
                            dependency_record_sha256=hashlib.sha256(context.dependency_record_bytes).hexdigest(),
                            oracle_sources=context.oracle_blobs,
                            domain="typed raw model leaves; lists/fields have valid Bytes children")
    auth.check()
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
