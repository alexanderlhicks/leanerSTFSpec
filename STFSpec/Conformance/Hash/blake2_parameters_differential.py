#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Compare raw BLAKE2F parameters with authenticated pinned EELS source.

Run with isolated startup and bytecode writes disabled:
  EELS/.venv/bin/python -I -B STFSpec/Conformance/Hash/blake2_parameters_differential.py \
    --eels EELS --output <outside-worktree>/blake2-parameters.lean

Sources: crypto/blake2.py:10–32,133–150,253–266 and locked ethereum-types.
Every input is exactly 213 bytes. Flags are not validated and compression is never
called, including for rounds = 2^32-1. Generated guards are finite, uncommitted
parser observations, not EEST guest fixtures. Shared scripts/differential.py
checks the exact pin, source bytes and installed dependency before and after use.
Spec guidance: STFSpec/informal/modules/EthHash.md §§3–4.
"""

import hashlib
from pathlib import Path
import random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from differential import setup_driver

# Selected factual input bytes from primary EIP-152 examples 3–8:
# https://eips.ethereum.org/EIPS/eip-152#test-cases
EIP152_BODY = bytes.fromhex(
    "48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5"
    "d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b"
    "616263" + "00" * 125 + "03000000000000000000000000000000"
)


def checked_fields(result, uint_type):
    """Require the reference's exact tuple, list and Uint result domains."""
    if type(result) is not tuple or len(result) != 6:
        raise RuntimeError("parser must return a six-element tuple")
    rounds, h, m, t0, t1, flag = result
    if type(h) is not list or len(h) != 8 or type(m) is not list or len(m) != 16:
        raise RuntimeError("parser must return eight state words and sixteen message words")
    scalars = ((rounds, 32), (t0, 64), (t1, 64), (flag, 8))
    for value, width in scalars:
        if type(value) is not uint_type or not 0 <= int(value) < 2**width:
            raise RuntimeError(f"parser scalar must be an in-range Uint/{width}")
    for value in h + m:
        if type(value) is not uint_type or not 0 <= int(value) < 2**64:
            raise RuntimeError("parser word must be an in-range Uint/64")
    return int(rounds), list(map(int, h)), list(map(int, m)), int(t0), int(t1), int(flag)


def result_domain_regressions(uint_type):
    """Regression checks reject Boolean/int coercions and malformed field domains."""
    valid = (uint_type(1), [uint_type(2)] * 8, [uint_type(3)] * 16,
             uint_type(4), uint_type(5), uint_type(255))
    checked_fields(valid, uint_type)
    invalid = [list(valid), valid[:-1],
               (valid[0], tuple(valid[1]), *valid[2:]),
               (valid[0], valid[1][:-1], *valid[2:]),
               (valid[0], valid[1], valid[2] + [uint_type(0)], *valid[3:])]
    for position, value in ((0, 1), (0, True), (0, uint_type(2**32)),
                            (3, uint_type(2**64)), (4, uint_type(2**64)),
                            (5, True), (5, uint_type(256))):
        case = list(valid)
        case[position] = value
        invalid.append(tuple(case))
    invalid.append((valid[0], [True] + valid[1][1:], *valid[2:]))
    invalid.append((valid[0], valid[1], [uint_type(2**64)] + valid[2][1:], *valid[3:]))
    for case in invalid:
        try:
            checked_fields(case, uint_type)
        except RuntimeError:
            continue
        raise RuntimeError("result-domain regression admitted an invalid parser result")
    return len(invalid) + 1


def lean_params(fields):
    rounds, h, m, t0, t1, flag = fields
    state = ",".join(map(str, h))
    message = ",".join(map(str, m))
    return (f"({{ rounds := {rounds}, h := #v[{state}], m := #v[{message}], "
            f"t0 := {t0}, t1 := {t1}, f := {flag} }} : Params)")


def main():
    context = setup_driver(__doc__, __file__, 4013)
    from ethereum.crypto import blake2
    from ethereum_types.numeric import Uint
    source = context.check_source(blake2, "ethereum/crypto/blake2.py")
    domain_regressions = result_domain_regressions(Uint)
    oracle = blake2.Blake2b()
    rng = random.Random(context.seed)
    cases = []
    counts = {}

    def add(group, data):
        if type(data) is not bytes or len(data) != 213:
            raise RuntimeError("differential case must be exactly 213 raw bytes")
        cases.append(data)
        counts[group] = counts.get(group, 0) + 1

    for rounds, flag in ((12, 2), (0, 1), (12, 1), (12, 0), (1, 1), (2**32 - 1, 1)):
        add("primary_eip152", rounds.to_bytes(4, "big") + EIP152_BODY + bytes([flag]))
    asymmetric = bytes((37 * i + 11) % 256 for i in range(213))
    add("asymmetric", asymmetric)
    for flag in range(256):
        rounds = (0, 1, 2**31, 2**32 - 1)[flag % 4]
        add("all_flags_round_boundaries", rounds.to_bytes(4, "big") + asymmetric[4:212] + bytes([flag]))
    # Move a high bit and a full byte through every field position, including all seams.
    for position in range(213):
        for value in (0x80, 0xFF):
            data = bytearray(213)
            data[position] = value
            add("byte_positions_high_bits", bytes(data))
    add("all_zero", bytes(213))
    add("all_one_bits", b"\xff" * 213)
    for _ in range(256):
        add("random", rng.randbytes(213))

    guards = ["import STFSpec.Hash.Blake2Parameters", "open STFSpec.Hash.Blake2b\nset_option maxRecDepth 1024"]
    observations = hashlib.sha256()
    for index, data in enumerate(cases):
        fields = checked_fields(oracle.get_blake2_parameters(data), Uint)
        name = f"blake2Input{index}"
        literal = ",".join(map(str, data))
        guards.append(f"private def {name} : ByteArray := ⟨#[{literal}]⟩")
        guards.append(f"#guard getParameters {name} (by decide) = {lean_params(fields)}")
        guards.append(f"#guard (serialize {lean_params(fields)}).data = {name}.data")
        observations.update(data)
        observations.update(repr(fields).encode())
    return context.run(
        guards, cases=counts, parser_cases=len(cases), value_guards=2 * len(cases),
        result_domain_regressions=domain_regressions,
        compression_calls=0, observations_sha256=observations.hexdigest(),
        python=sys.version, oracle_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        uv_lock_sha256=hashlib.sha256((context.eels / "uv.lock").read_bytes()).hexdigest(),
        dependency_sha256=hashlib.sha256(context.dependency.read_bytes()).hexdigest())


if __name__ == "__main__":
    raise SystemExit(main())
