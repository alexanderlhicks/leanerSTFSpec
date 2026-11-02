#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Finite legacy Keccak digest comparisons against authenticated pinned EELS.

Run with EELS/.venv/bin/python -I -B, --eels EELS --output EXTERNAL.lean.
Invokes actual crypto/hash.py keccak256/keccak512, records the selected backend,
checks the frozen pycryptodome version when used, and runs bounded seeded cases.
This is digest-value evidence, not EEST guest execution or a security theorem.
Spec guidance: STFSpec/informal/modules/EthHash.md §§3–4.
"""

import importlib.metadata
from pathlib import Path
import random
import sys
import tomllib

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from differential import setup_driver


def array(message):
    return "⟨#[" + ", ".join(f"0x{x:02x}" for x in message) + "]⟩"


def main():
    context = setup_driver(__doc__, __file__, 1401600)
    from ethereum.crypto import hash as source
    context.check_source(source, "ethereum/crypto/hash.py")
    pin = tomllib.loads((context.root / "reference.toml").read_text())["release"]
    version = importlib.metadata.version("pycryptodome")
    if version != pin["python_dependencies"]["pycryptodome"]:
        raise RuntimeError("pycryptodome version differs from reference.toml")
    rng = random.Random(context.seed)
    lengths = [0, 1, 2, 3, 7, 8, 31, 32, 63, 64, 70, 71, 72, 73,
               134, 135, 136, 137, 143, 144, 145, 271, 272, 273, 4096]
    messages = [bytes((17 * i + 131) % 256 for i in range(n)) for n in lengths]
    messages += [b"abc", bytes(136), bytes([255]) * 72]
    messages += [rng.randbytes(rng.randrange(4097)) for _ in range(64)]
    guards = ["import STFSpec.Hash", "open STFSpec.Hash STFSpec.Base"]
    for msg in messages:
        for bits, oracle in ((256, source.keccak256), (512, source.keccak512)):
            digest = oracle(msg)
            if len(digest) != bits // 8:
                raise RuntimeError("pinned EELS returned an unexpected digest width")
            guards.append(f"#guard (keccak{bits} {array(msg)}).toBytes.toByteArray = {array(digest)}")
    return context.run(guards, messages=len(messages), random_messages=64,
        tested_lengths=[len(m) for m in messages], algorithms=["Keccak-256", "Keccak-512"],
        oracle="actual authenticated pinned ethereum.crypto.hash functions",
        backend="hashlib" if source._USE_HASHLIB else "pycryptodome",
        pycryptodome=version, limitations="finite digest values; no EEST guest or security claim")


if __name__ == "__main__":
    raise SystemExit(main())
