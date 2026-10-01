#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Actual pinned CREATE/CREATE2 observations, including complete query traces.

Run EELS/.venv/bin/python -I -B with --eels EELS --output EXTERNAL.lean.
Reuse the shared EELS/ethereum-types source authentication and the typed RLP
current-source/RECORD loader. Instrument only the ephemeral loaded address
module's keccak binding, forward the original hash, and restore it in finally.
No cached source, checkout edits, nonce cap or manual recursion-limit change.
Interpreter/startup, frozen installation/RECORD and the concrete hash backend
remain trust inputs. Finite derivations do not establish Python equivalence,
VM/state/gas behavior, EEST guest execution, oracle coupling or security.
"""
from pathlib import Path
import hashlib
import importlib.metadata
import random
import sys
import tomllib

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from rlp_typed_differential import setup_driver, RlpSourceAuth, RlpFreshFinder, require_type
from rlp_encode_differential import lean_bytes


# Numerical facts from EIP-1014 examples 0–3, https://eips.ethereum.org/EIPS/eip-1014#examples.
EIP1014 = [
    ("00" * 20, "00" * 32, "00", "4d1a2e2bb4f88f0250f26ffff098b0b30b26bf38"),
    ("deadbeef" + "00" * 16, "00" * 32, "00", "b928f69bb1d91cd65274e3c79d8986362984fda3"),
    ("deadbeef" + "00" * 16,
     "000000000000000000000000feed000000000000000000000000000000000000",
     "00", "d04116cdd17bebe565eb2422f2497e06cc1c9833"),
    ("00" * 20, "00" * 32, "deadbeef", "70f2b2914a2a4b783faefb75f459a580616fcb5e"),
]


def main():
    context = setup_driver(__doc__, __file__, 5028)
    if not sys.flags.isolated or not sys.flags.dont_write_bytecode:
        context.parser.error("use the frozen interpreter -I -B")
    if any(name.split(".", 1)[0] == "ethereum_rlp" for name in sys.modules):
        raise ImportError("ethereum_rlp imported before authentication")
    auth = RlpSourceAuth(context)
    sys.meta_path.insert(0, RlpFreshFinder(auth))
    pin = tomllib.loads((context.root / "reference.toml").read_text())["release"]
    versions = {}
    for name in ("ethereum-types", "ethereum-rlp", "pycryptodome"):
        versions[name] = importlib.metadata.version(name)
        if versions[name] != pin["python_dependencies"][name]:
            raise ImportError(f"dependency version differs from pin: {name}")
    from ethereum_rlp import rlp
    from ethereum_types.bytes import Bytes, Bytes32
    from ethereum_types.numeric import Uint
    from ethereum.state import Address
    from ethereum.crypto import hash as hash_module
    from ethereum.forks.amsterdam.utils import address as address_module
    from ethereum.utils import byte as byte_module
    sources = {}
    for module in (address_module, hash_module, byte_module):
        relative = Path(module.__file__).resolve().relative_to(context.eels / "src").as_posix()
        source = context.check_source(module, relative)
        sources[relative] = hashlib.sha256(source.read_bytes()).hexdigest()
    context.check_source(rlp, "ethereum_rlp/rlp.py", dependency=True)
    original = address_module.keccak256
    if original is not hash_module.keccak256:
        raise RuntimeError("address hash binding differs from authenticated provider")
    recursion_limit = sys.getrecursionlimit()
    rng = random.Random(context.seed)
    guards = ["import STFSpec.Codec", "open STFSpec.Codec STFSpec.Base STFSpec.Hash"]
    observations = []
    counts = {"create": 0, "create2": 0, "random_derivations": 0,
              "negative_controls": 0, "eip1014": 0}

    # Exact-type negative controls exercise the same checks used on actual calls/results.
    class IntSubclass(int):
        pass

    class BytesSubclass(bytes):
        pass

    for expected, wrongs in [(Uint, [True, 0, 0.0, IntSubclass(0)]),
                            (Address, [bytes(20), bytearray(20), Bytes32(bytes(32))]),
                            (Bytes32, [bytes(32), Address(bytes(20)), bytearray(32)]),
                            (Bytes, [bytearray(), memoryview(b""), BytesSubclass(b"")])]:
        for wrong in wrongs:
            try:
                require_type(wrong, expected)
            except TypeError:
                counts["negative_controls"] += 1
            else:
                raise AssertionError("exact-type negative control accepted")

    def observe(sender_bytes, nonce=None, salt_bytes=None, code=None, published=None,
                randomized=False):
        require_type(sender_bytes, bytes)
        if len(sender_bytes) != 20:
            raise ValueError("sender must have exactly twenty bytes")
        sender = Address(sender_bytes)
        require_type(sender, Address)
        if nonce is not None:
            require_type(nonce, int)
            if nonce < 0:
                raise ValueError("nonce must be nonnegative")
            typed_nonce = Uint(nonce)
            require_type(typed_nonce, Uint)
        else:
            require_type(salt_bytes, bytes)
            require_type(code, Bytes)
            if len(salt_bytes) != 32:
                raise ValueError("salt must have exactly thirty-two bytes")
            salt = Bytes32(salt_bytes)
            require_type(salt, Bytes32)
        trace = []

        def recording_hash(preimage):
            require_type(preimage, Bytes)
            answer = original(preimage)
            require_type(answer, Bytes32)
            if len(answer) != 32:
                raise ValueError("hash provider returned wrong width")
            trace.append((preimage, bytes(answer)))
            return answer

        address_module.keccak256 = recording_hash
        try:
            if nonce is not None:
                result = address_module.compute_contract_address(sender, typed_nonce)
            else:
                result = address_module.compute_create2_contract_address(sender, salt, code)
        finally:
            address_module.keccak256 = original
        require_type(result, Address)
        if len(result) != 20:
            raise ValueError("address function returned wrong width")
        result_bytes = bytes(result)
        if published is not None and result_bytes.hex() != published:
            raise AssertionError("actual pinned CREATE2 differs from EIP-1014 example")
        if nonce is not None:
            expected_preimage = rlp.encode([sender, typed_nonce])
            require_type(expected_preimage, bytes)
            if len(trace) != 1 or trace[0][0] != expected_preimage:
                raise AssertionError("CREATE did not issue the exact sole RLP query")
            expression = f"computeContractAddress (Address.ofNat {int.from_bytes(sender_bytes, 'big')}) {nonce}"
            preimage_expr = ("Rlp.encode (.list [.bytes " + lean_bytes(sender_bytes) +
                             f", Rlp.ofNat {nonce}])")
            guards.append(f"#guard {preimage_expr} = {lean_bytes(trace[0][0])}")
            counts["create"] += 1
            item = {"operation": "CREATE", "sender": sender_bytes.hex(), "nonce": nonce}
        else:
            if (len(trace) != 2 or trace[0][0] != code or trace[1][0] !=
                    b"\xff" + sender_bytes + salt_bytes + trace[0][1]):
                raise AssertionError("CREATE2 query order/preimage/answer dependence differs")
            expression = (f"computeCreate2ContractAddress (Address.ofNat {int.from_bytes(sender_bytes, 'big')}) "
                          f"(FixedBytes.ofNat {int.from_bytes(salt_bytes, 'big')}) {lean_bytes(code)}")
            counts["create2"] += 1
            item = {"operation": "CREATE2", "sender": sender_bytes.hex(),
                    "salt": salt_bytes.hex(), "init_code": code.hex()}
        if result_bytes != trace[-1][1][12:]:
            raise AssertionError("address result differs from final exact twenty-byte suffix")
        guards.append(f"#guard ({expression}).toBytes.toByteArray = {lean_bytes(result_bytes)}")
        for preimage, digest in trace:
            guards.append(f"#guard (KeccakQuery.keccak (m := Id) {lean_bytes(preimage)}).toBytes.toByteArray = {lean_bytes(digest)}")
        item.update(address=result_bytes.hex(),
                    trace=[{"preimage": p.hex(), "digest": h.hex()} for p, h in trace])
        observations.append(item)
        counts["random_derivations"] += int(randomized)

    sender = bytes.fromhex("deadbeef00000000000000000000000000000000")
    for nonce in [0, 1, 2, 3, 127, 128, 255, 256, 2**64-1, 2**64, 2**64+1,
                  2**128-1, 2**128, 2**256-1, 2**256, 2**512]:
        observe(sender, nonce=nonce)
    observe(bytes(20), nonce=0)
    observe(bytes(range(20)), nonce=256)
    for sender_hex, salt_hex, code_hex, expected in EIP1014:
        observe(bytes.fromhex(sender_hex), salt_bytes=bytes.fromhex(salt_hex),
                code=bytes.fromhex(code_hex), published=expected)
        counts["eip1014"] += 1
    for width in [0, 1, 31, 32, 33, 135, 136, 137, 271, 272, 273]:
        observe(bytes(range(20)), salt_bytes=bytes(range(32)),
                code=bytes((i * 37) % 256 for i in range(width)))
    for i in range(64):
        sender = bytes(rng.randrange(256) for _ in range(20))
        nonce = rng.getrandbits(rng.choice([0, 7, 8, 64, 65, 128, 256, 512]))
        observe(sender, nonce=nonce, randomized=True)
        salt = bytes(rng.randrange(256) for _ in range(32))
        width = rng.choice([0, 1, 2, 31, 32, 33, 135, 136, 137, 271, 272, 273])
        code = bytes(rng.randrange(256) for _ in range(width))
        observe(sender, salt_bytes=salt, code=code, randomized=True)
    if address_module.keccak256 is not original or sys.getrecursionlimit() != recursion_limit:
        raise AssertionError("module binding or imported recursion setup changed")
    auth.check()
    result = context.run(guards, counts=counts, observations=observations, versions=versions,
                         backend="hashlib" if hash_module._USE_HASHLIB else "pycryptodome",
                         recursion_limit=recursion_limit, recursion_limit_policy="unchanged after pinned imports",
                         sources=sources, oracle_sources=context.oracle_blobs,
                         rlp_sources={str(p): h for p, h in auth.expected.items()},
                         rlp_record_sha256=hashlib.sha256(auth.record_bytes).hexdigest(),
                         dependency_sources=context.dependency_sources(),
                         dependency_record_sha256=hashlib.sha256(context.dependency_record_bytes).hexdigest(),
                         limits="bounded complete results/traces; no EEST guest, universal Python or security theorem")
    auth.check()
    return result


if __name__ == "__main__":
    raise SystemExit(main())
