# `EthHash`: Keccak, SHA-256, RIPEMD-160, BLAKE2b F and the `KeccakQuery` seam

*Status: informal specification, draft. Date: 2026-09-29. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1–F4, F15, F16, F18 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D4, D5, D21 · questions: B10/Q12, Q18, Q19, F1–F4, F15, F18.*

Paths are relative to `src/ethereum/` at the pin unless prefixed. Host-library behaviour was first checked in a scratch venv (Python 3.12, OpenSSL 3.0.13, pycryptodome 3.23.0) and re-observed in a lock-exact environment (CPython 3.13.7, OpenSSL 3.0.16, pycryptodome 3.23.0) used for the full-corpus EELS run. Both hosts lack OpenSSL keccak-256 and provide RIPEMD-160.

## 1. Purpose

`EthHash` (layer L0) provides the hash functions whose outputs the protocol depends on:
- `keccak256` for state/storage keys, trie nodes, code hashes, headers, transaction hashes, CREATE addresses and `KECCAK256`;
- `sha256` for SSZ `hash_tree_root`, request hashes, KZG versioned hashes and precompile 0x02;
- `ripemd160` for precompile 0x03;
- the BLAKE2b compression function `F` for precompile 0x09 (EIP-152).

It also defines the tiny `KeccakQuery` monad class, its `Id` and transformer-lift instances, and `HashConsts.query`, so that keccak-touching kernels are written once, generic in the monad, and later bridged to an oracle model in `EthSecurity` (D5). The references are legible sponge/compression definitions. Proved fast paths may be attached later (D4).

## 2. Requirements

**R1. `keccak256`** (`crypto/hash.py:62`) must equal pre-NIST Keccak-256: rate 1088 bits, capacity 512, **padding `0x01 … 0x80`** (not SHA3's `0x06`), output 32 bytes. EELS chooses its implementation at import time. It uses `hashlib.new("keccak-256")` if OpenSSL provides it (OpenSSL ≥ 3.2 default provider), and pycryptodome's `keccak.new(digest_bits=256)` otherwise (`crypto/hash.py:23–59`; `_USE_HASHLIB` at `:39`). On both checked hosts (OpenSSL 3.0.13 and 3.0.16) OpenSSL lacks it, so pycryptodome is used. Both backends are standard Keccak-256, so *no behavioural difference is expected*; this is inferred from the library specifications, not proved. The spec implements one function.

**R2. `keccak512`** (`crypto/hash.py:80`) is Keccak-512 (rate 576). **It has no caller in scope**: only `ethash.py`, which is outside the guest, uses it. It is specified for completeness as the same sponge with a different rate and output.

**R3. `sha256`** is FIPS 180-4 SHA-256 via `hashlib` (external `hashlib.sha256`). The callers are:
- `forks/amsterdam/requests.py:322–324`: `sha256` of the concatenation of per-request `sha256` digests;
- `crypto/kzg.py:73`: versioned hash = `0x01 ‖ sha256(commitment)[1:]`;
- `vm/precompiled_contracts/sha256.py:51`;
- remerkleable's `merkle_hash` (`remerkleable/settings.py:16–17`), used by `EthCodec`.

**R4. `ripemd160`** is RIPEMD-160 via `hashlib.new("ripemd160", data)` (`vm/precompiled_contracts/ripemd160.py:52`). The precompile left-pads the 20-byte digest to 32 bytes.

*Host dependency (naive-reading trap).* On hosts whose OpenSSL build/provider configuration lacks RIPEMD-160, `hashlib.new("ripemd160")` raises `ValueError`, and Python 3.12 has no built-in fallback. `ValueError` is not an `ExceptionalHalt`, so on such a host the exception would escape the frame and invalidate the block (`stateless.py:303`). The checked host computes it: `9c1185a5…` for the empty input. The spec implements RIPEMD-160 unconditionally. DISC-005 records this host dependence; the exact D14/O12 policy remains open.

**R5. BLAKE2b `F`** (`crypto/blake2.py`). The precompile (`vm/precompiled_contracts/blake2f.py:30–42`) proceeds in this order:
1. it requires exactly 213 input bytes (`InvalidParameter` otherwise);
2. it parses the parameters (below) and charges `rounds × PER_ROUND` gas;
3. it **then** rejects a final flag other than 0 or 1;
4. it computes `compress`.

`EthHash` specifies steps 2 (parse) and 4 (compress); the checks and gas belong to `EthPrecompiles`. The parse (`get_blake2_parameters`, `:133–150`):

| field | encoding | bytes |
|---|---|---|
| `rounds` | big-endian `u32` | 0..3 |
| `h[0..7]` | little-endian `u64` each | 4..67 |
| `m[0..15]` | little-endian `u64` each | 68..195 |
| `t0`, `t1` | little-endian `u64` each | 196..211 |
| `f` | `Uint.from_be_bytes` of one byte | 212 |

`compress` (`:194–247`) is RFC 7693 §3.2 `F`, with these details:
- the rounds are **unbounded** (`r` ranges over `0..rounds−1`, and σ is indexed by `r mod 10`);
- `v[12] ^= t0`, `v[13] ^= t1`;
- if `f` then `v[14] ^= 2^64−1`;
- the output is `h[i] ^ v[i] ^ v[i+8]` for `i < 8`, packed as 8 little-endian `u64`s (64 bytes).

There are two naive-reading traps, both harmless but worth stating:
- *(a)* `v[8:15] = self.IV` assigns 8 values to a 7-element slice. The Python list grows to 17 entries, with `v[8..15] = IV` and an unused trailing `v[16] = 0`, which I checked on the installed code. The result equals the RFC's 16-word vector.
- *(b)* In `G` (`:152–192`), `x >> R ^ (x << (w−R)) % 2^w` parses as `(x >> R) ^ ((x << (w−R)) % 2^w)`, because `%` binds tighter than `^`. Since all words are < 2^64, this is exactly `rotr64(x, R)`, with `R1..R4 = 32, 24, 16, 63` (`:259–266`).

The generic `Blake2` dataclass (`:35–247`) is instantiated only as `Blake2b` (`:253`); the spec specialises to `w = 64`.

**R6. `KeccakQuery`.** **Every** keccak use in the spec goes through `[Monad m] [KeccakQuery m]` (D5 broad scope, B10; interfaces settled by DECISIONS §3, F1–F4, F15, F18). That covers the trie, witness and code DBs, the header chain and `validate_header`'s parent hash, the block-hash check, the transaction and withdrawal roots, the KECCAK256 opcode, CREATE/CREATE2 addresses, ECRECOVER's address hash, code preimages and newly installed code hashes, the EIP-7708 transfer topic, and the keccak-derived constants.
- **Monad-parametric interfaces.** Everything that hashes is generic in `{m} [Monad m] [KeccakQuery m]`; the types that only carry a hashing pre-state or precompile (`PreState m`, `StateM m`, `VmM m`, `PrecompileFn m`, owned by their modules) take `{m} [Monad m]` and never mention the class. Public entry points specialise to `m := Id`. The class stays here; `EthState` and `EthVmCore` mention `m` but never need the class, so no import boundary changes.
- **Constants.** The keccak-derived constants are the `HashConsts` record (`EthBase`). `HashConsts.query` computes them through the oracle; `EthBlock.executeBlock` calls it once per block and carries the result in the block state. The literal values (`HashConsts.literals`, `EthBase`) are the `Id` values, and §7 checks that they agree.
- **Lifts.** `KeccakQuery` has instances for `ExceptT ε m` and `StateT σ m` that forward to the underlying oracle, so the spec's transformer stacks inherit it and add no hashing.
- A narrower scope must be justified by the witness/full-state agreement prototype. The executable instance at `m := Id` must be definitionally `keccak256`, so that no proof is needed to run the spec.

**R7. Totality and resources.** All functions are total on all inputs. `compress` runs in `O(rounds)` time. `rounds ≤ 2^32 − 1` is bounded only by the gas the precompile charges first (`blake2f.py:37`), so a caller must not evaluate `compress` before that charge succeeds. This ordering obligation belongs to `EthPrecompiles`.

**R8. No `hashlib`/OpenSSL at runtime.** The Lean definitions are self-contained. There is no `@[extern]` (CONTRIBUTING §4). A fast path is an executable definition with a legible reference beside it and an ordinary equality proof (D4, D21); `@[csimp]` is banned.

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `crypto/hash.py::_hashlib_has_keccak` | 23 | none (backend probe) | host dispatch; the spec has a single implementation (R1) |
| `crypto/hash.py::_USE_HASHLIB` | 39 | none | as above; recorded as a host dependency |
| `crypto/hash.py::keccak256` | 62 | `STFSpec.Hash.keccak256 : ByteArray → Hash32` | public |
| `crypto/hash.py::keccak512` | 80 | `STFSpec.Hash.keccak512 : ByteArray → Hash64` | unreachable from the guest; exclusion candidate |
| `crypto/blake2.py::spit_le_to_uint` | 10 | `Blake2b.leWords` (internal) | name typo (`spit`) is EELS's |
| `crypto/blake2.py::Blake2` | 35 | `STFSpec.Hash.Blake2b` namespace | specialised to 64-bit words |
| `crypto/blake2.py::Blake2.max_word` | 53 | implicit in `UInt64` wrap-around | `2^64` |
| `crypto/blake2.py::Blake2.w_R1` | 60 | constant `64 − 32` | folded into `rotr` |
| `crypto/blake2.py::Blake2.w_R2` | 68 | constant `64 − 24` | |
| `crypto/blake2.py::Blake2.w_R3` | 76 | constant `64 − 16` | |
| `crypto/blake2.py::Blake2.w_R4` | 84 | constant `64 − 63` | |
| `crypto/blake2.py::Blake2.sigma_len` | 127 | constant `10` | |
| `crypto/blake2.py::Blake2.get_blake2_parameters` | 133 | `Blake2b.getParameters` | requires size 213 (caller-checked) |
| `crypto/blake2.py::Blake2.G` | 152 | `Blake2b.G` (internal) | trap (b) |
| `crypto/blake2.py::Blake2.compress` | 194 | `Blake2b.compress` | trap (a) |
| `crypto/blake2.py::Blake2b` | 253 | `Blake2b` constants (IV, σ, rotations) | |

**External semantics.**
- `hashlib` / `hashlib.sha256` → `STFSpec.Hash.sha256` (FIPS 180-4).
- `hashlib.new("ripemd160")` (not a separate inventory entry; it goes through `hashlib`) → `STFSpec.Hash.ripemd160` (Dobbertin–Bosselaers–Preneel 1996).
- `Crypto.Hash.keccak` (pycryptodome) → `keccak256`/`keccak512`.

Each is specified as the published algorithm, with known-answer tests. Host variability (R1, R4) is recorded, not modelled.

## 4. Tests

- **EEST fixture areas.**
  - Keccak is exercised by every block: header hash, state/storage trie keys and nodes, code hashes. `frontier/opcodes` and `ported_static/vmTests` cover the `KECCAK256` opcode (no `stSHA3` area exists in this corpus); `constantinople/eip1014_create2` and `ported_static/stCreate2` cover the CREATE2 preimage.
  - SHA-256: `ported_static/stPreCompiledContracts`, `stPreCompiledContracts2`, `frontier/precompiles`, plus every request hash and SSZ root through the guest output root. `prague/eip7685_general_purpose_el_requests`, `eip6110_deposits`, `eip7002_el_triggerable_withdrawals`, `eip7251_consolidations` and `amsterdam/eip8282_builder_execution_requests` cover request hashing. `cancun/eip4844_blobs` covers versioned hashes.
  - RIPEMD-160: `ported_static/stPreCompiledContracts*`, `frontier/precompiles`.
  - BLAKE2F: `istanbul/eip152_blake2` (5 files per format), `ported_static/stPreCompiledContracts2`.
- **EELS unit tests:** none at the pin for `crypto/hash.py` or `crypto/blake2.py` (`tests/json_loader/` has none).
- **`core` `#guard` cases.**
  - `keccak256 ""` = `c5d24601…5d85a470`; `keccak256 "abc"`.
  - Inputs of 135, 136 and 137 bytes: the rate boundary and the padding of `0x01` and `0x80` into the same byte at length 135.
  - A 1 MiB input, for performance only.
  - `keccak512 ""`.
  - SHA-256 NIST vectors: empty, `"abc"`, 55/56/64-byte boundaries.
  - RIPEMD-160 vectors from the original paper: empty = `9c1185a5c5e9fc54612808977ee8f548b2258d31`, `"abc"`, and the million-`a` test.
  - BLAKE2F: the EIP-152 vectors 4–8, including `rounds = 0`, `f = 0`, and `rounds = 2^32 − 1` as a *parse-only* guard (the compression is not run).
  - `keccakF1600` on the all-zero state (the published permutation KAT).
- **Property / differential tests.**
  - Output sizes, as theorems rather than tests.
  - A differential test against pycryptodome and `hashlib` in the scratch venv on random lengths 0..4096 (bug-finding only).
  - When a fast path is attached: fast ≡ reference on random inputs, then as a proof (D4).
  - A bridge test comparing `keccakF1600` with the ZisK accelerator's `keccakF` (§10) on random states.

## 5. Interface

The namespace is `STFSpec.Hash`. All items are public unless marked internal.

```lean
-- Keccak
abbrev KeccakState := Vector UInt64 25         -- lanes, x + 5*y indexing (FIPS 202)
def keccakF1600 : KeccakState → KeccakState     -- 24 rounds θ ρ π χ ι
def keccakSponge (rateBytes : Nat) (outBytes : Nat) (msg : ByteArray) : ByteArray  -- internal; pad 0x01…0x80
def keccak256 (msg : ByteArray) : Hash32        -- rate 136, out 32
def keccak512 (msg : ByteArray) : Hash64        -- rate 72, out 64 (unreachable)

-- SHA-256 and RIPEMD-160
def sha256    (msg : ByteArray) : Bytes32
def sha256Compress : Vector UInt32 8 → Vector UInt32 16 → Vector UInt32 8   -- internal
def ripemd160 (msg : ByteArray) : FixedBytes 20

-- BLAKE2b F (EIP-152)
namespace Blake2b
  structure Params where
    rounds : UInt32
    h : Vector UInt64 8
    m : Vector UInt64 16
    t0 t1 : UInt64
    f : UInt8                                   -- raw byte; the precompile checks f ∈ {0,1}
  def getParameters (data : ByteArray) (h : data.size = 213) : Params
  def G : Vector UInt64 16 → (a b c d : Fin 16) → (x y : UInt64) → Vector UInt64 16  -- internal
  def compress (rounds : UInt32) (h : Vector UInt64 8) (m : Vector UInt64 16)
      (t0 t1 : UInt64) (f : Bool) : ByteArray   -- 64 bytes
  def IV : Vector UInt64 8; def sigma : Vector (Vector (Fin 16) 16) 10  -- constants
end Blake2b

-- Oracle seam (D5)
class KeccakQuery (m : Type → Type) where
  keccak : ByteArray → m Hash32
instance : KeccakQuery Id := ⟨fun b => keccak256 b⟩
instance [Monad m] [KeccakQuery m] : KeccakQuery (ExceptT ε m) := ⟨fun b => ExceptT.lift (keccak b)⟩
instance [Monad m] [KeccakQuery m] : KeccakQuery (StateT σ m)  := ⟨fun b => StateT.lift (keccak b)⟩
-- (EthSecurity, outside the core:  instance [HasQuery keccakSpec m] : KeccakQuery m)

-- Keccak-derived constants (EthBase.HashConsts), one query each; called once per block
def HashConsts.query {m} [Monad m] [KeccakQuery m] : m HashConsts
  -- emptyCodeHash ← keccak b"", emptyTrieRoot ← keccak 0x80,
  -- emptyOmmerHash ← keccak 0xc0, transferTopic ← keccak b"Transfer(address,address,uint256)"
```

The `sha256` digest type is `Bytes32`; `EthCodec` and requests use it as SSZ `Root`/`Bytes32`. The choice of lane container is part of D4: `Vector UInt64 25` for the reference, and an unboxed 25-field structure for the candidate fast path.

## 6. Data structures

| Type | Representation | Model | Invariant | Persistence | Complexity |
|---|---|---|---|---|---|
| `KeccakState` | `Vector UInt64 25` (reference) | the FIPS 202 state `Fin 5 × Fin 5 → BitVec 64` via lane indexing | size 25 (by type) | local to one hash call, linear | `keccakF1600`: O(1) (24 rounds). `keccak256`: O(⌈(n+1)/136⌉) permutations |
| SHA-256 state | `Vector UInt32 8` + 64-word schedule | FIPS 180-4 | by type | linear, local | O(⌈(n+9)/64⌉) compressions |
| RIPEMD-160 state | `Vector UInt32 5` | the original specification | by type | linear, local | O(⌈(n+9)/64⌉) |
| BLAKE2b work vector | `Vector UInt64 16` | RFC 7693 `v` | by type | linear, local | O(rounds) |
| `Params` | record | the parsed fields | `getParameters` is a bijection on 213-byte inputs | immutable | O(1) |

None of these structures is snapshot-reachable; they live only within one call. A first-pass measurement shows that allocation dominates: a boxed `Array` keccak takes 200–300 µs per 64-byte hash, against 1.0–1.4× C for an unboxed struct. So the reference must avoid `List`-building rounds even before any fast path is added; for each hot path, inspect the generated C/IR and count boxing, allocation and bignum calls.

## 7. Contract and laws

The representation here *is* the model, because these are pure functions. The contract is therefore functional correctness against the published algorithms, plus these laws.

- [C] `(keccak256 b).toBytes.size = 32`, `(sha256 b).toBytes.size = 32`, `(ripemd160 b).toBytes.size = 20`, and `(Blake2b.compress …).size = 64`. The first three hold by type; the last must be proved.
- [C] Sponge decomposition: `keccak256 b = squeeze (absorb (pad b))`, with `pad` giving `(b ++ 0x01 ++ zeros ++ 0x80)` of length a multiple of 136, or `b ++ 0x81` when exactly one padding byte remains. This is the statement that fast paths refine.
- [C] KATs as `#guard` (compile-time), not `native_decide` (CONTRIBUTING §4).
- [C] BLAKE2b: `getParameters` round-trips with the obvious serializer. `G` rotates correctly: `rotr64 x r = (x >>> r) ||| (x <<< (64 − r))` for `0 < r < 64`, which is exactly EELS's `(x >> R) ^ ((x << (w−R)) % 2^w)` on words < 2^64 (trap (b)). The 17-element trap (a) does not change the output.
- [T] Every function is structurally recursive over the input blocks or over `rounds : UInt32` (via `Nat` fuel = `rounds.toNat`).
- [F] (D4) the executable `keccak256` equals the legible reference `keccak256Reference`, as an ordinary theorem (no `@[csimp]`, D21), and likewise for SHA-256. The proof strategy is a round-by-round simulation of the unrolled permutation against `keccakF1600` (not yet done; §10).
- [R] (bridge module outside the core) `keccakF1600 ≡` the ZisK accelerator's `keccakF` (`ZiskAccel.lean:113`; §10) under the lane-order correspondence.
- [C] `HashConsts.query (m := Id) = HashConsts.literals` (`EthBase`), as a `#guard` or theorem; by F16 this is evaluable only once `keccak256` has no `sorry` leaf. A compiled prototype of the interfaces checked the same values at `Id`.
- [C] The lift instances forward: `keccak (m := ExceptT ε m) b = ExceptT.lift (keccak b)` and likewise for `StateT` (definitional).
- [S] `KeccakQuery Id` is definitionally `keccak256` (`rfl`). In `EthSecurity`, kernels are run under `simulateQ` with a random oracle, and collision/ROM bounds are stated there, never assumed here. `sha256` is used under a separate collision-resistance assumption for SSZ request binding (CONTRACT §7). The two oracles must not be conflated (D5).

### Informal correctness argument

**Claim.** Each concrete hash function returns the bytes specified by its standard and the pinned dependency, and the query interface specialises to concrete Keccak under its identity instance.

**Premises.** EthBase byte and word laws; exact padding, constants and endian conventions; the reference host supports the requested algorithm when reference equivalence is claimed.

**Argument.** Relate each implementation state to the standard's chaining state after the same number of blocks. The initialisation establishes the relation; one compression/permutation round preserves it by the word equations; induction over rounds and blocks gives the final digest. Padding requires separate cases at the final-block boundary, including the empty message and a full block. BLAKE2F additionally checks its fixed input layout and final flag before executing exactly the encoded round count. For the query abstraction, induction over the query computation replaces each query by concrete Keccak, preserving returned values and error order. This is functional correctness. Collision resistance is a separate assumption in EthSecurity and cannot follow from matching test vectors.

**Open obligations.** Round-level correspondence and complete boundary vectors remain unwritten. The oracle scope is fixed (D5; a compiled prototype of the interfaces showed it flows through every interface, F1–F4, F15, F18); the oracle coupling for `Models` at generic `m` remains open (it is stated at `PreState Id`). RIPEMD reference equivalence is conditional on host capability (DISC-005), not solely an OpenSSL major version.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthBase`.
- **Used by:** `EthCodec` (SSZ merkleization, address derivation), `EthVmInstructions` (`KECCAK256`, `EXTCODEHASH`, CREATE/CREATE2), `EthPrecompiles` (SHA-256, RIPEMD-160, BLAKE2F, and ECRECOVER's address hash through `KeccakQuery`), `EthBlock` (`HashConsts.query`, once per block), and transitively `EthCommit`, `EthStateWitness`, `EthVmRunner` and `EthStateless` (via `KeccakQuery`).
- **Seams provided.** `keccak256`/`sha256` as plain functions. `KeccakQuery m`, with its `Id`, `ExceptT` and `StateT` instances, for kernels that `EthSecurity` must reinterpret. `HashConsts.query` for the keccak-derived constants. `Blake2b.getParameters` and `compress` for the precompile, which must charge gas *before* calling `compress`.
- **Guarantees.** Totality, determinism and independence from the host.
- **Relies on.** `Hash32`, `Bytes32` and `FixedBytes` from `EthBase`, and Lean core `UInt64`/`UInt32` rotations.

## 9. Open decisions

- **D4** (hash implementations): reference first. A proved unrolled fast path is attached only after measurement; keccak dominates witness cost.
- **D5** (provisional: broad scope with monad-parametric interfaces; B10 and DECISIONS §3): **every** keccak call goes through `KeccakQuery` (R6). A compiled prototype of the interfaces showed that the dependency flows through every interface once the signatures are monad-parametric (F1–F4, F15, F18). Open: the oracle coupling for `Models` at generic `m`.
- **D21** (accepted, 2026-09-28): no `@[csimp]` and no axiom-adding tactics (`native_decide`, `bv_decide`). A fast path is either a representation replacement proved against this module's contract (D25), or an executable definition with a legible reference beside it and an ordinary equality proof (`CONTRIBUTING.md` §4).
- **P2** (authority order): host-dependent `hashlib` behaviour falls under CONTRACT §6.
- `ripemd160` host dependency: tracked as DISC-005 (DECISIONS Q19). The spec implements the algorithm unconditionally; the host-capability policy is O12 (DISC-001).

## 10. Gaps

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **No core reference implementation yet**, and no KAT file is checked in. A prototype outside the core has an executable Keccak-f[1600] and sponge matching reference vectors (empty input, `0x80`, 135 and 200 bytes). It is **not promoted**: it is the executable side of D4 only, with no legible reference or equality proof. The `#guard` vectors listed in §4 must be transcribed from the primary sources (FIPS 202 / Keccak team, FIPS 180-4, the RIPEMD-160 paper, EIP-152), not from the host.
- **Backend equivalence unverified.** That OpenSSL keccak-256 and pycryptodome keccak are bit-identical on all inputs is assumed from their specifications, not tested. A differential run over random lengths would at least provide evidence.
- **RIPEMD-160 host discrepancy** (R4): recorded as DISC-005; no upstream report has been made.
- **BLAKE2F coverage** in EEST is 5 files per format. Beyond the EIP-152 vectors I have not checked whether any fixture exercises `rounds` near `2^32 − 1` with sufficient gas (probably impossible within the block gas limit), `f` exactly 0 versus 1 at the same rounds, or `t` counters with the high bit set.
- **The gas-before-compute ordering** for BLAKE2F is a cross-module obligation with no stated theorem yet. `EthPrecompiles` must own it. If it were violated, an adversarial `rounds` value could make evaluation hang in the guest while the reference charges out of gas first.
- **Fast-path proof strategy** (D4): the simulation proof of an unrolled keccak against the reference is unscoped. No existing Lean proof of this shape was found in this repository. VCV-io's `Keccak.lean` is a candidate reference but is slow (compiled at `f5119c6`: about 200–300 µs per 64-byte hash, allocation-bound).
- **Bridge to the ZisK accelerator's `keccakF`** (`RiscvZkvm.Rv64.ZiskAccel`, `ZiskAccel.lean:113`; the copy checked locally is evm-asm's `EvmAsm/Rv64/ZiskAccel.lean`, the same file `EthField` §4 cites at `:313`/`:489`): the lane-order and endianness correspondence (it acts on `List (BitVec 64)`) is not written down. The bridge module has no owner package yet: it would need riscv-zkvm, which is on toolchain v4.33.
- **`sha256` for SSZ versus request hashing**: whether both uses must be modelled by one collision-resistance assumption in `EthSecurity` has no owner.
- **Performance:** no measurement yet of the legible reference against the "code-shape gate" (no `List` allocation per round).
- **`keccak512`, `_hashlib_has_keccak` and `_USE_HASHLIB`** are specified only nominally. A static call-graph pass over the pinned EELS, run by the failure ledger (maintained outside this repository), places `keccak512` outside the guest call graph and finds the backend probe runs at import time only, so they can be excluded in `STFSpec/informal/EXCLUDED.md` with that reason (DECISIONS Q18).
