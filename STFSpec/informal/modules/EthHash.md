# `EthHash`: Keccak, SHA-256, RIPEMD-160, BLAKE2b F and the `KeccakQuery` seam

*Status: informal specification, draft. Date: 2026-09-30. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1–F4, F15, F16, F18, F20 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D4, D5, D21 · questions: B10/Q12, Q18, Q19, Q46, F1–F4, F15, F18.*

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

The total SHA-256 input-domain policy is Q46: the padding trailer contains the low 64 bits of the original bit length, encoded big-endian. FIPS 180-4 correspondence requires `8 * msg.size < 2^64`. Beyond that domain the total extension claims neither FIPS nor pinned-host equivalence. Fixed-word compression is independent of this bound.

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
- **Constants.** The keccak-derived constants are the `HashConsts` record (`EthBase`). `HashConsts.query` computes them through the oracle; acquisition and consumer coherence follow F20 (EthStateless R5, EthBlock §2.7). The literal values (`HashConsts.literals`, `EthBase`) are the `Id` values, and §7 checks that they agree.
- **Lifts.** `KeccakQuery` has instances for `ExceptT ε m` and `StateT σ m` that forward to the underlying oracle, so the spec's transformer stacks inherit it and add no hashing.
- A narrower scope must be justified by the witness/full-state agreement prototype. The executable instance at `m := Id` must be definitionally `keccak256`, so that no proof is needed to run the spec.

**R7. Totality and resources.** All functions are total on all inputs; SHA-256 standard correspondence uses the Q46 domain. `compress` runs in `O(rounds)` time. `rounds ≤ 2^32 − 1` is bounded only by the gas the precompile charges first (`blake2f.py:37`), so a caller must not evaluate `compress` before that charge succeeds. This ordering obligation belongs to `EthPrecompiles`.

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

### Implemented reference permutation slice

`STFSpec/Hash/KeccakPermutation.lean` owns the reference permutation and coordinate
model. The rows below are **discharged for this permutation slice**: total and pure,
with no state effects outside the returned state and no failures or consuming error
handler. EELS `crypto/hash.py:62–77` delegates to its backend; it has no raw permutation
surface. Accordingly these rows cite the published algorithm underlying the pinned
pycryptodome 3.23.0 dependency rather than claim Python round execution. The Keccak
sponge, digest, byte-packing and query APIs are **unimplemented**.

| Source | Public declaration and type | Domain / success observation | Ordered failures / consumer | Public laws | Tests |
|---|---|---|---|---|---|
| FIPS 202 §3.1.2 | `KeccakState := Vector UInt64 25`; `KeccakModel := Fin 5 × Fin 5 → BitVec 64`; `keccakLaneIndex : Fin 5 → Fin 5 → Fin 25` | All 25-lane states; x+5*y indexing | None; bounded by types | `keccakLane_ofLanes`, `keccakToModel_inj` | Asymmetric lane positions 0,4,5,24 |
| FIPS 202 §3.1.2 | `keccakLane : KeccakState → Fin 5 → Fin 5 → UInt64`; `keccakToModel : KeccakState → KeccakModel` | All states/coordinates; numeric bit z is lane bit z | None | `keccakLane_bit`, `keccakToModel_inj` | Asymmetric low-bit probes; model-law clients |
| Coordinate constructor | `keccakOfLanes : (Fin 5 → Fin 5 → UInt64) → KeccakState` | Every coordinate function; exact lane preservation, array-backed construction | None | `keccakLane_ofLanes` | Asymmetric and constant lane construction |
| FIPS 202 §3.2 | `keccakCoord : Fin 5 → Nat → Fin 5` | Coordinate addition modulo five | None | `keccakLane_pi_forward` | All 25 pi coordinate pairs proved with ordinary `decide` |
| FIPS 202 §§3.2.1–3.2.2 | `keccakRotl : UInt64 → Nat → UInt64` | Every lane and rotation amount; modulo-64 left rotation, zero preserved | None | `toBitVec_keccakRotl`, `keccakRotl_bit` | Zero/63/64/65/128 rotation probes; differential boundary rotations |
| FIPS 202 Table 2 | `keccakRhoOffsets : Vector Nat 25` | All offsets in x+5*y order | None | Used by `keccakToModel_rho` | All 25 entries compared with independent coordinate-walk generation |
| FIPS 202 Algorithms 5–6 | `keccakRoundConstants : Vector UInt64 24` | Constants for rounds 0 through 23 | None | Used by `keccakToModel_iota` | All 24 compared with independent LFSR generation; first/last probes |
| FIPS 202 §3.2.1 | `keccakTheta : KeccakState → KeccakState`; `KeccakModel.column`, `KeccakModel.theta` | Every state; five cached column parities/corrections | None | `keccakToModel_theta` | Asymmetric lane 0; per-step differential |
| FIPS 202 §3.2.2 | `keccakRho : KeccakState → KeccakState`; `KeccakModel.rho` | Every state; per-lane left rotation | None | `keccakToModel_rho` | Asymmetric lane 1; per-step differential |
| FIPS 202 §3.2.3 | `keccakPi : KeccakState → KeccakState`; `KeccakModel.pi` | Every state; output (x,y) takes input (x+3*y,x), modulo five | None | `keccakToModel_pi`, `keccakLane_pi_forward` | Asymmetric coordinates; forward-placement client |
| FIPS 202 §3.2.4 | `keccakChi : KeccakState → KeccakState`; `KeccakModel.chi` | Every state; reads all operands from the original row | None | `keccakToModel_chi` | Asymmetric lane 1; per-step differential |
| FIPS 202 §3.2.5 | `keccakIota : KeccakState → Fin 24 → KeccakState`; `KeccakModel.iota` | Every state/round; XOR constant into (0,0) only | None | `keccakToModel_iota` | First/last constants and unchanged lane 24 |
| FIPS 202 §3.3 | `keccakRound : KeccakState → Fin 24 → KeccakState`; `KeccakModel.round` | Every state/round; theta, rho, pi, chi, iota in order | None | `keccakToModel_round` | Zero first round; per-round differential; composition clients |
| FIPS 202 §§3.3–3.4 | `keccakRounds : KeccakState → (n : Nat) → n ≤ 24 → KeccakState`; `KeccakModel.rounds` | Every state and bounded prefix; rounds 0 through n−1 in ascending order | None; caller supplies n≤24 | `keccakToModel_rounds` | Prefixes 0/1; differential prefixes 0 through 24; public-law client |
| FIPS 202 §§3.3–3.4 | `keccakF1600 : KeccakState → KeccakState` | Every state; exactly 24 rounds | None | `keccakToModel_f1600` | Published all-zero 25-lane KAT; full-state differential; model-extensional client |

`STFSpec/Conformance/Hash/KeccakPermutationGuards.lean` owns 25 deterministic
guards, including the full published zero-state permutation KAT. Its provenance is
[the Keccak team's round-3 archive](https://keccak.team/obsolete/KeccakKAT-3.zip),
member `KeccakKAT/KeccakPermutationIntermediateValues.txt`, first all-zero example,
"State after permutation". Serialized bytes are decoded little endian. The test
module records the archive/member SHA-256 and exact selection; expected lanes are
transcribed from the primary source, not generated by a host hash backend.
`KeccakPermutationCallerProofs.lean` contains six public-law composition clients.

`keccak_permutation_differential.py` is a self-written independent coordinate model
of FIPS 202, not EELS execution or a pinned pycryptodome oracle. It uses forward pi
placement, coordinate-walk rho generation and LFSR round-constant generation,
independent of Lean's inverse pi expression and literal tables. Seed 1101600 covers
60 full states (zero, all ones, ascending lanes, 25 single-lane bit probes and 32
random states), 240 cases per step and per round at rounds 0,1,11,23, 200 prefix
cases, 65 rotation probes, all 25 offsets and all 24 constants: 1814 generated
guards. Generated observations and identity/count reports are written outside the
implementation checkout and remain finite bug-finding evidence. No digest, guest/EEST, accelerator,
performance refinement or cryptographic security claim follows from these tests.

**Discharged SHA-256 fixed-word compression slice.** All operations below are pure,
with no failure channel or caller premise beyond the fixed vector sizes. Native
words observe as `BitVec 32` using `Sha256.wordsModel`; all additions wrap modulo
2^32. `sha256`, padding, byte parsing and serialization remain unimplemented.
Compression equations do not depend on the Q46 message-length domain.

| Source / operation | Lean declaration and domain/effects | Public law / model | Deterministic evidence / status |
|---|---|---|---|
| FIPS 180-4 §4.1.2 rotations, Ch, Maj and four sigma functions (external `hashlib.sha256` semantics) | `Sha256.rotr`, `ch`, `maj`, `bigSigma0/1`, `smallSigma0/1`; native UInt32 inputs, rotation law for `0 < r < 32` | `toBitVec_rotr`, `toBitVec_ch/maj/bigSigma0/bigSigma1/smallSigma0/smallSigma1`, corresponding `Sha256.Model` word definitions | arithmetic/rotation guards and NIST abc intermediate-state KATs; **discharged** |
| FIPS 180-4 §§4.2.2, 5.3.3 constants and initial chaining value | `Sha256.roundConstants : Vector UInt32 64`, `initialState : Vector UInt32 8`, ascending round and a,b,c,d,e,f,g,h order | constants used explicitly by native/model rounds; `wordsModel_get` observes each word | NIST empty/abc fixed-block compression and four abc round prefixes; **discharged** |
| FIPS 180-4 §6.2.2 schedule | `Sha256.scheduleInit`, `scheduleStep`, `scheduleIter`, `schedule : Vector UInt32 16 → Vector UInt32 64`; 48 structural updates following the sixteen inputs | `wordsModel_scheduleInit/scheduleStep/scheduleIter/schedule`; `schedule_get_input`, `schedule_get_expanded`, `scheduleIter_stable` | asymmetric input/first expansion guards; finite independent-model differential of all 64 words; **discharged** |
| FIPS 180-4 §6.2.2 rounds | `Sha256.round`, `rounds`; simultaneous eight-word update, first `n ≤ 64` rounds | `wordsModel_round`, `wordsModel_rounds`, `rounds_zero`, `rounds_succ` | NIST abc after rounds 0,1,16,63 (prefixes 1,2,17,64); independent-model prefixes 0,1,2,17,64; **discharged** |
| FIPS 180-4 §6.2.2 feed-forward/compression | `Sha256.feedForward`, `sha256Compress : Vector UInt32 8 → Vector UInt32 16 → Vector UInt32 8`; add original chaining words after round 63 | `wordsModel_feedForward`, `feedForward_get`, `sha256Compress_model`, `sha256Compress_eq`, `wordsModel_injective` | carry/feed-forward guard; NIST empty/abc fixed blocks; two-block public-law composition client; **discharged** |

Tests: `STFSpec/Conformance/Hash/Sha256CompressionGuards.lean` and
`Sha256CompressionCallerProofs.lean`. The bounded seeded driver
`STFSpec/Conformance/Hash/sha256_compression_differential.py` compares compression
with an independent integer model of FIPS 180-4, **not pinned EELS compression**
(EELS exposes only hashlib digests). It also uses test-only Python padding/parsing
and serial compression composition to compare selected finite messages with the
hashlib alias observed through the authenticated pinned precompile source. This
supports compression composition; it does not implement or validate production
padding, digest code, precompile gas/effects or guest behavior.


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
  - Implemented fixed-block SHA-256 compression KATs: explicitly supplied padded empty/abc words, and NIST abc states after rounds 0,1,16,63. Digest/padding KATs for the production `sha256` API, including 55/56/64-byte boundaries, remain pending.
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

-- Keccak-derived constants (EthBase.HashConsts), one query each; acquisition scope is F20
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

The contract is functional correctness against the published algorithms, plus these laws. The SHA-256 compression slice observes native UInt32 vectors through `Sha256.wordsModel` into its explicit `BitVec 32` model; its discharged equations are listed in §3.

- [C] `(keccak256 b).toBytes.size = 32`, `(sha256 b).toBytes.size = 32`, `(ripemd160 b).toBytes.size = 20`, and `(Blake2b.compress …).size = 64`. The first three hold by type; the last must be proved.
- [C] Sponge decomposition: `keccak256 b = squeeze (absorb (pad b))`, with `pad` giving `(b ++ 0x01 ++ zeros ++ 0x80)` of length a multiple of 136, or `b ++ 0x81` when exactly one padding byte remains. This is the statement that fast paths refine.
- [C] Fixed-word SHA-256 compression correspondence, schedule recurrence/input preservation, bounded round-prefix correspondence and original-state feed-forward are discharged by the §3 laws. Digest/padding/byte correspondence remains open; standard correspondence for a future `sha256` theorem requires the Q46 domain.
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

**Open obligations.** Reference permutation step/round/prefix and lane-bit correspondence
and SHA-256 fixed-word schedule/round/feed-forward correspondence are discharged
for the slices in §3. Sponge padding/byte packing, digest correspondence, RIPEMD-160
and BLAKE2F rounds and their complete boundary vectors remain unwritten. Q46 supplies
the SHA-256 domain policy. The oracle scope is fixed (D5; a compiled prototype of the interfaces showed it flows through every interface, F1–F4, F15, F18); the oracle coupling for `Models` at generic `m` remains open (it is stated at `PreState Id`). RIPEMD reference equivalence is conditional on host capability (DISC-005), not solely an OpenSSL major version.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthBase`.
- **Used by:** `EthCodec` (SSZ merkleization, address derivation), `EthVmInstructions` (`KECCAK256`, `EXTCODEHASH`, CREATE/CREATE2), `EthPrecompiles` (SHA-256, RIPEMD-160, BLAKE2F, and ECRECOVER's address hash through `KeccakQuery`), `EthBlock` (standalone acquisition wrapper, F20), `EthStateless` (guest acquisition, F20), `EthConformance` (engine acquisition, R4/F20), and transitively `EthCommit`, `EthStateWitness` and `EthVmRunner` (via `KeccakQuery`).
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

- **SHA-256 remaining work.** The fixed-word compression slice is discharged in §3; the production `sha256` digest, padding, big-endian byte parsing/serialization, block iteration and digest boundary KATs remain unimplemented. Q46 governs the total trailer and qualified FIPS correspondence; no enormous-input host equivalence is claimed. The finite differential’s test-only composition is not production digest coverage.

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Remaining core hash implementations.** The legible Keccak-f[1600] reference,
coordinate-model laws and primary zero-state permutation KAT, and the SHA-256
fixed-word compression reference/model laws and primary KATs, are implemented (§3).
The sponge, Keccak digests, query seam, SHA-256 digest, RIPEMD-160 and BLAKE2F remain
unimplemented. Their §4 vectors still need transcription from primary sources
(Keccak team, FIPS 180-4, the RIPEMD-160 paper, EIP-152), not from the host.
Historical prototypes are evidence only, not promoted core code.
- **Backend equivalence unverified.** That OpenSSL keccak-256 and pycryptodome keccak are bit-identical on all inputs is assumed from their specifications, not tested. A differential run over random lengths would at least provide evidence.
- **RIPEMD-160 host discrepancy** (R4): recorded as DISC-005; no upstream report has been made.
- **BLAKE2F coverage** in EEST is 5 files per format. Beyond the EIP-152 vectors I have not checked whether any fixture exercises `rounds` near `2^32 − 1` with sufficient gas (probably impossible within the block gas limit), `f` exactly 0 versus 1 at the same rounds, or `t` counters with the high bit set.
- **The gas-before-compute ordering** for BLAKE2F is a cross-module obligation with no stated theorem yet. `EthPrecompiles` must own it. If it were violated, an adversarial `rounds` value could make evaluation hang in the guest while the reference charges out of gas first.
- **Fast-path proof strategy** (D4): the simulation proof of an unrolled keccak against the reference is unscoped. No existing Lean proof of this shape was found in this repository. VCV-io's `Keccak.lean` is a candidate reference but is slow (compiled at `f5119c6`: about 200–300 µs per 64-byte hash, allocation-bound).
- **Bridge to the ZisK accelerator's `keccakF`** (`RiscvZkvm.Rv64.ZiskAccel`, `ZiskAccel.lean:113`; the copy checked locally is evm-asm's `EvmAsm/Rv64/ZiskAccel.lean`, the same file `EthField` §4 cites at `:313`/`:489`): the lane-order and endianness correspondence (it acts on `List (BitVec 64)`) is not written down. The bridge module has no owner package yet: it would need riscv-zkvm, which is on toolchain v4.33.
- **`sha256` for SSZ versus request hashing**: whether both uses must be modelled by one collision-resistance assumption in `EthSecurity` has no owner.
- **Performance:** the permutation uses array-backed `Vector.ofFn` and cached
column vectors, with no `List` construction in the executable round path. Its
generated C is inspected for this bounded code-shape gate. No throughput target,
allocation benchmark, fast-path equivalence or whole-hash cost gate is discharged.
- **`keccak512`, `_hashlib_has_keccak` and `_USE_HASHLIB`** are specified only nominally. A static call-graph pass over the pinned EELS, run by the failure ledger (maintained outside this repository), places `keccak512` outside the guest call graph and finds the backend probe runs at import time only, so they can be excluded in `STFSpec/informal/EXCLUDED.md` with that reason (DECISIONS Q18).
