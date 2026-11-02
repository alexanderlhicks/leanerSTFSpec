#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Packed Keccak values against authenticated EELS and an independent lane model.

Run EELS/.venv/bin/python -I -B this_file --eels EELS --output OUTSIDE.lean.
The actual pinned crypto/hash.py functions return exact Bytes32/Bytes64 values;
result shape/type checks precede byte observations and reject bool/int coercions.
The separate coordinate/LFSR model supplies finite step/prefix/permutation checks;
EELS has no raw permutation API. Uses retained local reference driver model code,
whose hash is recorded, not Lean constants. Neither finite comparator is a guest,
security, accelerator or universal host-equivalence claim. Benchmark expected
values include 1 MiB, but giant messages are not emitted as compile-time guards.
Spec guidance: STFSpec/informal/modules/EthHash.md §§3–4,7.
"""

import hashlib
import importlib.metadata
import importlib.util
import json
from pathlib import Path
import random
import sys
import tomllib

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts"))
from differential import setup_driver


def checked_digest(value, expected_type, width):
    """Check the exact pinned result class and fixed-width raw byte domain."""
    if type(value) is not expected_type or len(value) != width:
        raise RuntimeError("digest must have the exact pinned fixed-bytes type and width")
    result = bytes(value)
    if type(result) is not bytes or len(result) != width:
        raise RuntimeError("digest byte conversion changed its fixed width")
    if any(type(b) is not int or not 0 <= b < 256 for b in result):
        raise RuntimeError("digest observation must contain exact in-range integer bytes")
    return result


def domain_regressions(bytes32, bytes64):
    """Reject coercible or malformed values before emitting observation facts."""
    checked_digest(bytes32(bytes(32)), bytes32, 32)
    checked_digest(bytes64(bytes(64)), bytes64, 64)
    invalid = [True, False, 32, bytes(32), bytearray(32), [0] * 32,
               bytes64(bytes(64)), bytes.__new__(bytes32, bytes(31)),
               bytes32(bytes(32)), bytes.__new__(bytes64, bytes(63)),
               bytes.__new__(bytes32, bytes(33))]
    for index, value in enumerate(invalid):
        cls, width = (bytes64, 64) if index in (8, 9) else (bytes32, 32)
        try:
            checked_digest(value, cls, width)
        except RuntimeError:
            continue
        raise RuntimeError("digest result-domain regression accepted an invalid result")
    return len(invalid)


def model_guards(seed):
    """Reuse self-written independent forward-pi/coordinate-walk/LFSR model."""
    path = Path(__file__).with_name("keccak_permutation_differential.py")
    spec = importlib.util.spec_from_file_location("packed_coordinate_model", path)
    model = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(model)
    def vector(words):
        return model.vector(words).replace("keccakOfLanes", "STFSpec.Hash.keccakOfLanes").replace(
            "keccakLaneIndex", "STFSpec.Hash.keccakLaneIndex")
    rng = random.Random(seed)
    states = [[0] * 25, [model.MASK] * 25, list(range(25))]
    states += [[(1 << (i * 7 % 64)) if j == i else 0 for j in range(25)]
               for i in range(25)]
    states += [[rng.getrandbits(64) for _ in range(25)] for _ in range(32)]
    guards, facts = [], []
    counts = dict.fromkeys(["theta", "rho", "pi", "chi", "iota", "round",
                           "rounds", "permutation"], 0)
    for index, initial in enumerate(states):
        state = initial
        packed = f"(ofReference {vector(initial)})"
        if index < 8:
            guards.append(f"#guard toReference (rounds {packed} 0 (by decide)) = "
                          f"{vector(state)}")
            counts["rounds"] += 1
        for r in range(24):
            snapshots = model.steps(state, r)
            if r in [0, 1, 11, 23]:
                for name, before, after in snapshots:
                    name = name.lower()
                    extra = f" {r}" if name == "iota" else ""
                    guards.append(f"#guard toReference ({name} "
                                  f"(ofReference {vector(before)}){extra}) = "
                                  f"{vector(after)}")
                    counts[name] += 1
                guards.append(f"#guard toReference (round "
                              f"(ofReference {vector(state)}) {r}) = "
                              f"{vector(snapshots[-1][2])}")
                counts["round"] += 1
            state = snapshots[-1][2]
            if index < 8:
                guards.append(f"#guard toReference (rounds {packed} {r + 1} "
                              f"(by decide)) = {vector(state)}")
                counts["rounds"] += 1
        guards.append(f"#guard toReference (permutation {packed}) = {vector(state)}")
        counts["permutation"] += 1
        facts.append({"input_lanes": initial, "output_lanes": state})
    return guards, {"description": model.MODEL, "seed": seed, "states": len(states),
                    "operation_counts": counts, "guard_count": sum(counts.values()),
                    "model_driver_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                    "observations": facts}


# Compact valid-even lowercase hex literals avoid huge syntax trees; the adapter
# is test-only and unconstrained parser behavior is never used as oracle evidence.
HEX_HELPERS = [
    "def hexDigit (c : Char) : Nat := if c ≤ '9' then c.toNat - 48 else c.toNat - 87",
    "def hexLoop : List Char → ByteArray → ByteArray\n"
    "  | a :: b :: rest, out => hexLoop rest "
    "(out.push (UInt8.ofNat (16 * hexDigit a + hexDigit b)))\n"
    "  | _, out => out",
    "def fromHex (s : String) : ByteArray := hexLoop s.toList ByteArray.empty",
]


def main():
    context = setup_driver(__doc__, __file__, 21021)
    from ethereum.crypto import hash as source
    from ethereum_types.bytes import Bytes32, Bytes64
    source_path = context.check_source(source, "ethereum/crypto/hash.py")
    pin = tomllib.loads((ROOT / "reference.toml").read_text())["release"]
    version = importlib.metadata.version("pycryptodome")
    if version != pin["python_dependencies"]["pycryptodome"]:
        raise RuntimeError("pycryptodome version differs from reference.toml")
    regressions = domain_regressions(Bytes32, Bytes64)
    rng = random.Random(context.seed)
    lengths = [0, 1, 3, 31, 32, 64, 71, 72, 73, 135, 136, 137, 4096]
    messages = [bytes((17 * i + 131) % 256 for i in range(n)) for n in lengths]
    messages += [b"abc", bytes(136), bytes([255]) * 72]
    messages += [rng.randbytes(rng.randrange(4097)) for _ in range(64)]
    guards = ["import STFSpec.Hash", "open STFSpec.Hash.PackedKeccak STFSpec.Base",
              "set_option warningAsError true", "namespace PackedObservations"] + HEX_HELPERS
    facts, benchmarks = [], []
    for index, msg in enumerate(messages):
        guards.append(f'def message{index} : ByteArray := fromHex "{msg.hex()}"')
        for bits, cls, oracle in ((256, Bytes32, source.keccak256),
                                 (512, Bytes64, source.keccak512)):
            value = checked_digest(oracle(msg), cls, bits // 8)
            guards.append(f"#guard (keccak{bits} message{index}).toBytes.toByteArray = "
                          f'fromHex "{value.hex()}"')
            facts.append({"message_hex": msg.hex(), "bits": bits, "digest_hex": value.hex()})
    for n in [0, 32, 64, 135, 136, 137, 71, 72, 73, 4096, 1048576]:
        msg = bytes((17 * i + 131) % 256 for i in range(n))
        for bits, cls, oracle in ((256, Bytes32, source.keccak256),
                                 (512, Bytes64, source.keccak512)):
            value = checked_digest(oracle(msg), cls, bits // 8)
            benchmarks.append({"length": n, "bits": bits, "digest_hex": value.hex()})
    lane_guards, model_report = model_guards(context.seed)
    guards += lane_guards + ["end PackedObservations"]
    metadata = {"seed": context.seed, "messages": len(messages), "random_messages": 64,
                "digest_guards": len(facts), "result_domain_regressions": regressions,
                "digest_oracle": "actual authenticated pinned EELS public functions",
                "source_sha256": hashlib.sha256(source_path.read_bytes()).hexdigest(),
                "backend": "hashlib" if source._USE_HASHLIB else "pycryptodome",
                "pycryptodome": version, "python": sys.version,
                "driver_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                "frozen_interpreter_isolated": bool(sys.flags.isolated),
                "dont_write_bytecode": sys.dont_write_bytecode,
                "digest_observations": facts, "benchmark_oracles": benchmarks,
                "model": model_report}
    context.output.with_suffix(".json").write_text(json.dumps(metadata, indent=2) + "\n")
    return context.run(guards, messages=len(messages), random_messages=64,
                       digest_guards=len(facts), model_guards=model_report["guard_count"],
                       result_domain_regressions=regressions, backend=metadata["backend"],
                       pycryptodome=version, source_sha256=metadata["source_sha256"],
                       limits="finite lane/digest values; no guest, security or host theorem")


if __name__ == "__main__":
    raise SystemExit(main())
