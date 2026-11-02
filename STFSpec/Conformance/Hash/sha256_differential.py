#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Finite production SHA-256 digest differential against the pinned host surface.

Run EELS/.venv/bin/python -I -B this_file --eels EELS --output SCRATCH.lean.
The shared driver authenticates source bytes and frozen ethereum-types imports;
the oracle is source.hashlib.sha256 from the pinned SHA-256 precompile module.
Compare the actual Lean sha256 API (including production padding/parsing/output),
not Python-composed Lean compression. Separate padding expectations use the
standard finite byte-domain equation. Random lengths range from 0 through 4096.
Q46's conceptual above-domain extension is checked only by helper guards, not
by gigantic host or guest runs. No precompile gas/effect or guest claim is made.
Spec guidance: STFSpec/informal/modules/EthHash.md §§3–4.
"""

from pathlib import Path
import random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from differential import setup_driver


def byte_array(value):
    return f'fromHex "{value.hex()}"'


def byte_list(value):
    return f'(fromHex "{value.hex()}").data.toList'


def padded(message):
    """Test expectation on finite FIPS-domain bytes, independent of Lean padding."""
    if len(message) * 8 >= 1 << 64:
        raise ValueError("finite host comparison requires the FIPS length domain")
    return (message + b"\x80" + bytes((55 - len(message)) % 64)
            + (8 * len(message)).to_bytes(8, "big"))


def main():
    context = setup_driver(__doc__, __file__, 16016)
    from ethereum.forks.amsterdam.vm.precompiled_contracts import sha256 as source
    context.check_source(source, "ethereum/forks/amsterdam/vm/precompiled_contracts/sha256.py")
    rng = random.Random(context.seed)
    lengths = [0, 1, 2, 3, 7, 31, 32, 54, 55, 56, 57, 63, 64, 65, 66,
               118, 119, 120, 121, 127, 128, 129, 255, 256, 257, 4095, 4096]
    messages = [bytes((17 * i + 131) % 256 for i in range(n)) for n in lengths]
    messages += [bytes(n) for n in (55, 56, 64, 128, 4096)]
    messages += [bytes([255]) * n for n in (55, 56, 64, 128, 4096)]
    asymmetry = bytes(range(256)) * 2 + bytes([0x80, 0, 1])
    messages += [asymmetry, asymmetry[::-1], b"abc"]
    messages += [rng.randbytes(rng.randrange(4097)) for _ in range(128)]
    guards = ["import STFSpec.Hash", "open STFSpec.Base STFSpec.Hash STFSpec.Hash.Sha256",
        # Test-only compact literal decoder. Python bytes.hex guarantees lowercase,
        # valid, even-length input; no unconstrained parser observation is accepted.
        "def hexDigit (c : Char) : Nat := if c ≤ '9' then c.toNat - 48 else c.toNat - 87",
        "def hexLoop : List Char → ByteArray → ByteArray\n"
        "  | a :: b :: rest, out => hexLoop rest (out.push (UInt8.ofNat (16 * hexDigit a + hexDigit b)))\n"
        "  | _, out => out",
        "def fromHex (s : String) : ByteArray := hexLoop s.toList ByteArray.empty"]
    blocks = 0
    for i, message in enumerate(messages):
        name = f"message{i}"
        guards.append(f"def {name} : ByteArray := {byte_array(message)}")
        expected_pad = padded(message)
        blocks += len(expected_pad) // 64
        digest = source.hashlib.sha256(message).digest()
        guards.append(f"#guard (sha256 {name}).toBytes.toList = {byte_list(digest)}")
        guards.append(f"#guard (pad {name}).toList = {byte_list(expected_pad)}")
    return context.run(guards, production_digest_cases=len(messages), random_cases=128,
        observation_guards=2 * len(messages), message_definitions=len(messages),
        padding_cases=len(messages), digest_compression_blocks=blocks,
        deterministic_boundary_lengths=lengths, message_lengths=[len(m) for m in messages],
        digest_oracle="source.hashlib.sha256 from authenticated pinned precompile module",
        padding_oracle="independent finite FIPS 180-4 byte-domain equation",
        limitations="finite FIPS-domain bytes; no above-domain host, gas/effects, guest or security claim")


if __name__ == "__main__":
    raise SystemExit(main())
