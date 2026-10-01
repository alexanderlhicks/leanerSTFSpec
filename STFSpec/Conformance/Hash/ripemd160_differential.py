#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Production RIPEMD-160 digest comparison against the actual pinned precompile.

Run EELS/.venv/bin/python -I -B this_file --eels EELS --output SCRATCH.lean.
The shared Driver authenticates source bytes and frozen ethereum-types RECORD;
this driver calls ripemd160.py:26–54 with funded gas, checks all twelve leading
zero bytes and compares the remaining twenty bytes with Lean's production API.
Nine primary digest facts: https://homes.esat.kuleuven.be/~bosselae/ripemd160.html.
Independent finite padding expectation: corrected author pseudocode's MD4 padding,
RFC 1320 §§2, 3.1–3.2. Conceptual lengths are helper-only tests in the guard module.
Source/interpreter/driver identities are captured before/after. The interpreter,
OpenSSL, frozen installation and RECORD remain trusted inputs. No universal host,
resource, Lean precompile effects/gas, guest, security or performance claim follows.
Spec guidance: STFSpec/informal/modules/EthHash.md §§3–4.
"""

import hashlib
import json
from pathlib import Path
import random
import ssl
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts"))
from differential import setup_driver

# Selected mathematical facts, independently checked on the author's primary page.
PRIMARY = (
    (b"", "9c1185a5c5e9fc54612808977ee8f548b2258d31"),
    (b"a", "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe"),
    (b"abc", "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"),
    (b"message digest", "5d0689ef49d2fae572b881b123a85ffa21595f36"),
    (b"abcdefghijklmnopqrstuvwxyz", "f71c27109c692c1b56bbdceb5b9d2865b3708dbc"),
    (b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
     "12a053384a9c0c88e405a06c27dcf49ada62eb2b"),
    (b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789",
     "b0e20b6e3116640286ed3a87a5713079b21f5189"),
    (b"1234567890" * 8, "9b752e45573d4b39f4dbd3323cab82bf63326bfb"),
    (b"a" * 1_000_000, "52783243c1697bdbe16d37f97f68f08325dc1528"))


def identity(paths):
    return {str(p): {"sha256": hashlib.sha256(p.read_bytes()).hexdigest(),
                     "bytes": p.stat().st_size, "mode": oct(p.stat().st_mode & 0o777)}
            for p in paths}


def byte_array(value):
    return f'fromHex "{value.hex()}"'


def padded(message):
    return (message + b"\x80" + bytes((55 - len(message)) % 64)
            + ((8 * len(message)) % (1 << 64)).to_bytes(8, "little"))


def main():
    context = setup_driver(__doc__, __file__, 220160)
    if not sys.flags.dont_write_bytecode:
        context.parser.error("use the frozen interpreter with -I -B")
    from ethereum.forks.amsterdam.vm.precompiled_contracts import ripemd160 as source
    from ethereum.forks.amsterdam.fork_types import ExecutionGas, StateGas
    from ethereum.forks.amsterdam.vm.gas import GasMeter
    from ethereum_types.numeric import Uint
    from ethereum_types.bytes import Bytes
    from ethereum.trace import discard_evm_trace, set_evm_trace
    set_evm_trace(discard_evm_trace)
    oracle_path = context.check_source(source,
        "ethereum/forks/amsterdam/vm/precompiled_contracts/ripemd160.py")
    paths = [Path(__file__), ROOT / "scripts/differential.py", ROOT / "reference.toml",
             ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json",
             ROOT / "STFSpec/Hash.lean", ROOT / "STFSpec/Conformance.lean",
             ROOT / "STFSpec/Hash/Ripemd160Digest.lean",
             ROOT / "STFSpec/Hash/Ripemd160Compression.lean",
             ROOT / "STFSpec/Conformance/Hash/Ripemd160DigestGuards.lean",
             ROOT / "STFSpec/Conformance/Hash/Ripemd160DigestCallerProofs.lean",
             Path(sys.executable).resolve(), oracle_path, context.eels / "uv.lock",
             context.dependency_record]
    before = identity(paths)
    rng = random.Random(context.seed)
    lengths = [0, 1, 2, 3, 7, 31, 32, 54, 55, 56, 57, 63, 64, 65, 66,
               118, 119, 120, 121, 127, 128, 129, 255, 256, 257, 4095, 4096]
    messages = list(PRIMARY)
    messages += [(bytes((17 * i + 131) % 256 for i in range(n)), None) for n in lengths]
    messages += [(bytes(n), None) for n in (55, 56, 64, 128, 4096)]
    messages += [(bytes([255]) * n, None) for n in (55, 56, 64, 128, 4096)]
    asymmetry = bytes(range(256)) * 2 + bytes([0x80, 0, 1])
    messages += [(asymmetry, None), (asymmetry[::-1], None)]
    messages += [(rng.randbytes(rng.randrange(4097)), None) for _ in range(128)]
    preamble = ["import STFSpec.Hash", "open STFSpec.Base STFSpec.Hash STFSpec.Hash.Ripemd160",
        "def hexDigit (c : Char) : Nat := if c ≤ '9' then c.toNat - 48 else c.toNat - 87",
        "def hexLoop : List Char → ByteArray → ByteArray\n"
        "  | a :: b :: rest, out => hexLoop rest (out.push (UInt8.ofNat (16 * hexDigit a + hexDigit b)))\n"
        "  | _, out => out",
        "def fromHex (s : String) : ByteArray := hexLoop s.toList ByteArray.empty"]
    declarations, guards, native_checks, observations = [], [], [], []
    for case, (message, primary) in enumerate(messages):
        cost = 600 + 120 * ((len(message) + 31) // 32)
        frame = context.frame([])
        frame.call_data = Bytes(message)
        frame.gas_meter = GasMeter(ExecutionGas(Uint(cost + 1)), StateGas(Uint(0)), StateGas(Uint(0)))
        source.ripemd160(frame)
        output = bytes(frame.output)
        if len(output) != 32 or output[:12] != bytes(12) or int(frame.gas_meter.gas_left) != 1:
            raise RuntimeError("actual precompile adapter output/gas mismatch")
        digest = output[12:]
        if len(digest) != 20 or (primary is not None and digest.hex() != primary):
            raise RuntimeError("pinned digest disagrees with selected primary fact")
        expression = ("(Bytes.generate 1000000 (fun _ => 0x61)).toByteArray"
                      if len(message) == 1_000_000 else byte_array(message))
        name = f"message{case}"
        declarations.append(f"def {name} : ByteArray := {expression}")
        expected = f"({byte_array(digest)}).data.toList"
        guards.append(f"#guard (ripemd160 {name}).toBytes.toList = {expected}")
        native_checks.append(f'  if (ripemd160 {name}).toBytes.toList != {expected} then\n'
                             f'    throw (IO.userError "native digest mismatch {case}")')
        if len(message) != 1_000_000:
            expectation = f"({byte_array(padded(message))}).data.toList"
            guards.append(f"#guard (pad {name}).toList = {expectation}")
        observations.append({"case": case, "bytes": len(message),
            "message_sha256": hashlib.sha256(message).hexdigest(),
            "blocks": len(padded(message)) // 64, "digest": digest.hex(), "primary": primary is not None,
            "prefix_bytes_checked": 12, "gas_left": int(frame.gas_meter.gas_left)})
    # Separate complete native result comparisons; no hash checksum is substituted.
    native = context.output.with_name(context.output.stem + "Native.lean")
    native.write_text("\n".join(preamble + declarations + ["def main : IO Unit := do"] +
                     native_checks + [f'  IO.println "native production digests: {len(messages)} passed"']) + "\n")
    # Keep Driver's guard count exact: all test declarations belong to preamble item2.
    emitted = [preamble[0], "\n".join(preamble[1:] + declarations)] + guards
    result = context.run(emitted, production_digest_cases=len(messages), random_cases=128,
        observation_guards=len(guards), message_definitions=len(declarations),
        padding_cases=len(messages) - 1, primary_cases=9,
        digest_compression_blocks=sum(o["blocks"] for o in observations),
        deterministic_boundary_lengths=lengths,
        digest_oracle="actual pinned ripemd160.py:26–54; twelve zero bytes checked then stripped",
        padding_oracle="independent finite MD4 byte equation")
    after = identity(paths)
    report = {"before": before, "after": after, "unchanged": before == after,
        "eels_commit": context.head, "python": sys.version, "openssl": ssl.OPENSSL_VERSION,
        "ripemd160_capability": "ripemd160" in hashlib.algorithms_available,
        "isolated": sys.flags.isolated, "no_bytecode_writes": sys.flags.dont_write_bytecode,
        "source": str(oracle_path),
        "source_blob": context.oracle_blobs[str(oracle_path.relative_to(context.eels))],
        "parent": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "seed": context.seed, "generated_sha256": hashlib.sha256(context.output.read_bytes()).hexdigest(),
        "native_source": str(native), "native_sha256": hashlib.sha256(native.read_bytes()).hexdigest(),
        "observations": observations, "digest_cases": len(messages), "primary_cases": 9,
        "padding_cases": len(messages) - 1, "random_cases": 128, "guard_cases": len(guards),
        "lean_exit": result,
        "limits": "finite supported-host digest evidence; no all-host/resources, Lean gas/effects, guest, security or cost-gate claim"}
    context.output.with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"digest_cases": len(messages), "guard_cases": len(guards),
                      "unchanged": before == after, "lean_exit": result}), flush=True)
    return result or int(before != after)


if __name__ == "__main__":
    raise SystemExit(main())
