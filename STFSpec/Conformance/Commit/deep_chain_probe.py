#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Decode-level deep-nesting probes for `decode_witness_to_mpt` (DISC-001, Q6, C17).

Run with the frozen EELS interpreter, from the repository root:
EELS/.venv/bin/python -I -B STFSpec/Conformance/Commit/deep_chain_probe.py --eels EELS \
  --chain 63 64 49995 49996 --value-nest 33330 33331

`--chain N` builds a chain of N branch nodes. Each has a hashed child at slot 0 (the
next node) and a 32-byte stub at slot 1 that is absent from the node DB. The chain ends
in a leaf with a one-nibble path and a 32-byte value, so every node is at least 32 bytes
long and is referenced by hash (no DISC-003 short hashed node). `--value-nest N` builds
one branch with two stub children whose value (slot 16) is an RLP list nested N deep,
which EELS reads as `b""` (DISC-003, list-valued branch values).

Each input is deterministic, and the probe prints its SHA-256 digest. The probe imports
`py_ecc` first, as the guest process does, which raises the recursion limit to 100,000.
It decodes each input with `secured` false and true and prints the outcome: `ok`, or the
exception class and the first 60 characters of its message. It refuses to run without
`-I -B`, under `-O` (which removes the EELS asserts being measured), or on a checkout
whose HEAD is not reference.toml's `release.commit` or which has local changes (tracked
or untracked) under `src/`.

This is decode-level evidence from the probe's own shallow call stack on one host. In
the guest, decoding runs lazily inside block and EVM execution, so the guest's failing
depth is lower by the caller's frames, and it depends on the interpreter, its frame
layout and the node shape (DISC-001).
"""

import argparse
import hashlib
import importlib.metadata
import platform
import subprocess
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]


def main():
    if not sys.flags.isolated or not sys.flags.dont_write_bytecode:
        sys.exit("run with the frozen EELS .venv interpreter -I -B")
    if sys.flags.optimize:
        sys.exit("refusing to run under -O: it removes the EELS asserts being measured")
    parser = argparse.ArgumentParser()
    parser.add_argument("--eels", type=Path, required=True)
    parser.add_argument("--chain", type=int, nargs="*", default=[])
    parser.add_argument("--value-nest", type=int, nargs="*", default=[])
    args = parser.parse_args()

    pin = tomllib.loads((ROOT / "reference.toml").read_text())["release"]["commit"]
    git = ["git", "-C", str(args.eels)]
    head = subprocess.run(git + ["rev-parse", "HEAD"], capture_output=True, text=True,
                          check=True).stdout.strip()
    if head != pin:
        sys.exit(f"EELS checkout is at {head}, not reference.toml's {pin}")
    dirty = subprocess.run(git + ["status", "--porcelain", "--", "src"],
                           capture_output=True, text=True, check=True).stdout
    if dirty:
        sys.exit("EELS checkout has local changes")
    sys.path.insert(0, str(args.eels / "src"))

    import py_ecc  # noqa: F401  (raises the recursion limit, as in the guest process)
    from ethereum.crypto.hash import keccak256
    from ethereum.forks.amsterdam import incremental_mpt as inc
    from ethereum_rlp import rlp

    if not Path(inc.__file__).resolve().is_relative_to((args.eels / "src").resolve()):
        sys.exit(f"incremental_mpt imported from {inc.__file__}, not from --eels")
    rlp_file = Path(rlp.__file__).resolve()
    if rlp_file.is_relative_to((args.eels / "src").resolve()):
        sys.exit(f"ethereum_rlp imported from {rlp_file}, not from the locked environment")

    stub = b"\xaa" * 32

    def chain(depth):
        node = rlp.encode([bytes([0x31]), b"\x01" * 32])  # leaf, odd compact path [1]
        db = {}
        for _ in range(depth):
            child = keccak256(node)
            db[child] = node
            node = rlp.encode([child, stub] + [b""] * 15)
        return db, node

    def header(base, length):
        if length < 56:
            return bytes([base + length])
        size = length.to_bytes((length.bit_length() + 7) // 8, "big")
        return bytes([base + 55 + len(size)]) + size

    def value_nest(depth):
        value = b"\xc0"
        for _ in range(depth):
            value = header(0xC0, len(value)) + value
        items = rlp.encode(stub) + rlp.encode(b"\xbb" * 32) + b"\x80" * 14 + value
        return {}, header(0xC0, len(items)) + items

    print(f"EELS {head}, python {platform.python_version()}, "
          f"ethereum-rlp {importlib.metadata.version('ethereum-rlp')}, "
          f"recursion limit {sys.getrecursionlimit()}")
    cases = [("chain", d, chain) for d in args.chain]
    cases += [("value-nest", d, value_nest) for d in args.value_nest]
    for kind, depth, build in cases:
        db, node = build(depth)
        root = keccak256(node)
        db[root] = node
        digest = hashlib.sha256(
            root + b"".join(k + v for k, v in sorted(db.items()))
        ).hexdigest()
        for secured in (False, True):
            try:
                inc.decode_witness_to_mpt(db, root, secured, b"")
                outcome = "ok"
            except Exception as error:  # noqa: BLE001  (the guest catch-all, stateless.py:294)
                outcome = f"{type(error).__name__}: {str(error)[:60]}"
            mode = "secured" if secured else "plain"
            print(f"{kind} {depth} sha256 {digest[:16]} {mode}: {outcome}")


if __name__ == "__main__":
    main()
