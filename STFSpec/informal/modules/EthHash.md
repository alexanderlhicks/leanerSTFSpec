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

**R7. Totality and resources.** All functions are total on all inputs; SHA-256 standard correspondence uses the Q46 domain. `compress` runs in `O(rounds)` time. `rounds ≤ 2^32 − 1` is bounded only by the gas the precompile charges first (`blake2f.py:38`), so a caller must not evaluate `compress` before that charge succeeds. This ordering obligation belongs to `EthPrecompiles`.

**R8. No `hashlib`/OpenSSL at runtime.** The Lean definitions are self-contained. There is no `@[extern]` (CONTRIBUTING §4). A fast path is an executable definition with a legible reference beside it and an ordinary equality proof (D4, D21); `@[csimp]` is banned.

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `crypto/hash.py::_hashlib_has_keccak` | 23 | none (backend probe) | host dispatch; the spec has a single implementation (R1) |
| `crypto/hash.py::_USE_HASHLIB` | 39 | none | as above; recorded as a host dependency |
| `crypto/hash.py::keccak256` | 62 | `STFSpec.Hash.keccak256 : ByteArray → Hash32` | public |
| `crypto/hash.py::keccak512` | 80 | `STFSpec.Hash.keccak512 : ByteArray → Hash64` | unreachable from the guest; exclusion candidate |
| `crypto/blake2.py::spit_le_to_uint` | 10 | `Blake2b.leWord` (bounded word model) | public numeric bridge to EthBase; generic arbitrary-window `leWords` remains unimplemented; name typo (`spit`) is EELS's |
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

### Implemented reference permutation

`STFSpec/Hash/KeccakPermutation.lean` owns the reference permutation and coordinate
model. The rows below describe the implemented permutation: total and pure,
with no state effects outside the returned state and no failures or consuming error
handler. EELS `crypto/hash.py:62–77` delegates to its backend; it has no raw permutation
surface. Accordingly these rows cite the published algorithm underlying the pinned
pycryptodome 3.23.0 dependency rather than claim Python round execution. The
fixed-rate sponge below is also implemented and proved; remaining hash and query APIs
are listed in §10.

| Source | Public declaration and type | Domain / success observation | Ordered failures / consumer | Public laws | Tests |
|---|---|---|---|---|---|
| FIPS 202 §3.1.2 | `KeccakState` (private lane storage); `KeccakModel := Fin 5 × Fin 5 → BitVec 64`; `keccakLaneIndex : Fin 5 → Fin 5 → Fin 25` | All 25-lane states; x+5*y indexing | None; bounded by types | `keccakLane_ofLanes`, `keccakToModel_inj` | Asymmetric lane positions 0,4,5,24 |
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

[`KeccakPermutationGuards.lean`](../../Conformance/Hash/KeccakPermutationGuards.lean) owns the deterministic coordinate, rotation and storage-boundary cases and the full published zero-state permutation KAT. The module records the primary archive/member checksums, exact example and little-endian decoding. [`KeccakPermutationCallerProofs.lean`](../../Conformance/Hash/KeccakPermutationCallerProofs.lean) exercises composition through public coordinate-model laws.

[`keccak_permutation_differential.py`](../../Conformance/Hash/keccak_permutation_differential.py) owns the finite coverage and seed configuration. Its FIPS 202 model uses forward pi placement, coordinate-walk rho generation and LFSR round-constant generation, independently of Lean's inverse pi expression and literal tables. The generated report records observation counts and source identities outside the checkout. This is finite bug-finding evidence, with no digest, guest/EEST, accelerator, performance refinement or cryptographic security claim.

The native/model laws reuse the literal rho, iota and SHA constant tables. They prove representation correspondence, not independent derivation of those constants from the standards. Constant fidelity is supported by primary KATs, source inspection and the independent generators in the permutation driver; SHA's finite digest compositions additionally compare with hashlib through authenticated pinned source.

**Implemented SHA-256 fixed-word compression.** Compression is pure and has no failure channel or caller premise beyond the fixed vector sizes. Its helper laws retain their stated bounds: rotations require `0 < r < 32`, schedule prefixes `n ≤ 48`, and round prefixes `n ≤ 64`. Native words observe as `BitVec 32` using `Sha256.wordsModel`; additions wrap modulo 2^32. The message-digest operations are described separately below. Compression equations do not depend on Q46.

| Source / operation | Lean declaration and domain/effects | Public law / model | Deterministic evidence / status |
|---|---|---|---|
| FIPS 180-4 §4.1.2 rotations, Ch, Maj and four sigma functions (external `hashlib.sha256` semantics) | `Sha256.rotr`, `ch`, `maj`, `bigSigma0/1`, `smallSigma0/1`; native UInt32 inputs, rotation law for `0 < r < 32` | `toBitVec_rotr`, `toBitVec_ch/maj/bigSigma0/bigSigma1/smallSigma0/smallSigma1`, corresponding `Sha256.Model` word definitions | arithmetic/rotation guards and NIST abc intermediate-state KATs; **implemented; model correspondence proved** |
| FIPS 180-4 §§4.2.2, 5.3.3 constants and initial chaining value | `Sha256.roundConstants : Vector UInt32 64`, `initialState : Vector UInt32 8`, ascending round and a,b,c,d,e,f,g,h order | constants used explicitly by native/model rounds; `wordsModel_get` observes each word | NIST empty/abc fixed-block compression and abc round prefixes; **implemented; constant fidelity tested** |
| FIPS 180-4 §6.2.2 schedule | `Sha256.scheduleInit`, `scheduleStep`, `scheduleIter`, `schedule : Vector UInt32 16 → Vector UInt32 64`; 48 structural updates following the sixteen inputs | `wordsModel_scheduleInit/scheduleStep/scheduleIter/schedule`; `schedule_get_input`, `schedule_get_expanded`, `scheduleIter_stable` | asymmetric input/first expansion guards; finite independent-model differential of all 64 words; **implemented; model correspondence proved** |
| FIPS 180-4 §6.2.2 rounds | `Sha256.round`, `rounds`; simultaneous eight-word update, first `n ≤ 64` rounds | `wordsModel_round`, `wordsModel_rounds`, `rounds_zero`, `rounds_succ` | NIST abc after rounds 0,1,16,63 (prefixes 1,2,17,64); independent-model prefixes 0,1,2,17,64; **implemented; model correspondence proved** |
| FIPS 180-4 §6.2.2 feed-forward/compression | `Sha256.feedForward`, `sha256Compress : Vector UInt32 8 → Vector UInt32 16 → Vector UInt32 8`; add original chaining words after round 63 | `wordsModel_feedForward`, `feedForward_get`, `sha256Compress_model`, `sha256Compress_eq`, `wordsModel_injective` | carry/feed-forward guard; NIST empty/abc fixed blocks; two-block public-law composition client; **implemented; model correspondence proved** |

Tests: `STFSpec/Conformance/Hash/Sha256CompressionGuards.lean` and
`Sha256CompressionCallerProofs.lean`. The bounded seeded driver
`STFSpec/Conformance/Hash/sha256_compression_differential.py` compares compression
with an independent integer model of FIPS 180-4, **not pinned EELS compression**
(EELS exposes only hashlib digests). It also uses test-only Python padding/parsing
and serial compression composition to compare selected finite messages with the
hashlib alias observed through the authenticated pinned precompile source. This
supports compression composition; production padding and digests have separate
evidence below. It does not validate precompile gas/effects or guest behavior.

### Raw BLAKE2F parameters

The operations below are implemented and proved for the stated domains. Remaining hash,
compression and precompile operations retain their open obligations in §10.

| Pinned EELS source / dependency | Lean declaration and public type | Domain, effects and failure owner | Public law | Deterministic evidence |
|---|---|---|---|---|
| `crypto/blake2.py:10–32,133–150`; `ethereum-types` 0.4.1 `Uint.from_le_bytes` / `Uint.from_be_bytes` | `Blake2b.getParameters (data : ByteArray) (h : data.size = 213) : Params`; `Params` fields as §5 | Every 213-byte input; all `UInt32` rounds and all `UInt8` flags retained; pure. `EthPrecompiles` establishes the size premise after its size check, then owns gas charging and flag rejection (`vm/precompiled_contracts/blake2f.py:30–42`, O9/O8). No parser failure on this domain. The bounded 8/16/2 little-endian windows use `leWord`; generic arbitrary-window `leWords` remains unimplemented. | `getParameters_rounds`, `getParameters_h`, `getParameters_m`, `getParameters_t0`, `getParameters_t1`, `getParameters_f`; `toNat_leWord_succ`, `toNat_leWord_eq_ofLeBytes` (EthBase endian bridge), `wordByte_toNat`, `wordByte_leWord`, `leWord_wordByte` | `STFSpec/Conformance/Hash/Blake2ParametersGuards.lean`: primary [EIP-152](https://eips.ethereum.org/EIPS/eip-152#test-cases) examples 3–8, every raw flag, high round bit and asymmetric lane/counter bytes. `blake2_parameters_differential.py` calls the actual authenticated pinned parser; maximum rounds are parse-only. |
| Contract witness, using the same raw layout | `Blake2b.serialize : Params → ByteArray` and `parameterByte : Params → Fin 213 → UInt8` | Every raw `Params`; pure and no failures; preserves fixed widths and unvalidated flag | `serialize_size`, `inputByte_serialize`, `getParameters_serialize`, `serialize_getParameters`, `parameterByte_getParameters` | `Blake2ParametersCallerProofs.lean`: both round trips, codec injectivity, field observations and an EthBase endian bridge using public laws; guards and differential serialize the observed fields back to the original bytes. |

The parser differential driver checks scalar `Uint` types and exact vector shapes
before emitting Lean values; its result-domain regressions reject Boolean/int
coercions, wrong lengths and out-of-range fields. It uses `scripts/differential.py`
for the pin, source and installed dependency checks before and after observation.
Generated oracle observations stay outside both repositories and are finite evidence.
No compression, gas ordering, whole-hash refinement or EEST guest result is claimed.

### SHA-256 message digest

`STFSpec/Hash/Sha256Digest.lean` implements the production `sha256` API using the
accepted compression laws. All operations below are pure and total: their only
effect is the returned value, with no failure channel or consuming error handler.
Q46 owns the length-domain policy. `zeroCount_bit_congr` and
`zeroCount_bit_le_of_congr` state the FIPS congruence and minimality directly,
including comparison with arbitrary natural bit counts. The list padding model
shares the zero-count formula; its equality alone does not establish minimality. Mathematical totality does not establish host
memory availability or above-domain pinned-host agreement. EELS
`forks/amsterdam/vm/precompiled_contracts/sha256.py:42–51` charges gas before its
`hashlib.sha256(data).digest()` call; that gas/effect wrapper remains outside this
implementation. FIPS 180-4 supplies the external algorithm behind that host call.

| Source / operation | Lean declaration and domain/effects | Public law / model | Deterministic evidence / status |
|---|---|---|---|
| FIPS 180-4 §5.1.1; Q46 length trailer | `Sha256.bitLength : Nat → Nat`, `lengthTrailer : Nat → Bytes`; any conceptual original byte length, eight big-endian bytes of the bit length modulo 2^64 | `bitLength_mod/lt/of_fipsDomain`, `size_lengthTrailer`, `getElem_lengthTrailer`, `lengthTrailer_value` (public Base big-endian numeric decode); original length retained when `8*n < 2^64` | asymmetric trailer digits, conceptual 2^61−1/2^61/2^61+1 and 2^64+0x10203, allocating only eight bytes; **discharged** |
| FIPS 180-4 §5.1.1 padding | `Sha256.zeroCount/paddedLength : Nat → Nat`, `paddingSuffix : Nat → Bytes`, `pad : ByteArray → Bytes`; marker 0x80, at most 63 zeros, eight trailer bytes; one packed suffix and append | `zeroCount_congr`, `zeroCount_le_of_congr`, `zeroCount_bit_congr`, `zeroCount_bit_le_of_congr` (least FIPS-compatible zero padding), `toList_paddingSuffix`, `toList_pad`, `pad_prefix`, `size_pad`, `size_pad_mod64`, `zeroCount_boundaries`, `paddedLength_div64`, `paddedLength_ge`, `pad_model`, `pad_fipsDomain` | exact suffix, empty/55/56/63/64-byte boundaries, finite differential padding observations; **discharged** |
| FIPS 180-4 §5.2.1 block/word parsing | `Sha256.parseWord : UInt8 → UInt8 → UInt8 → UInt8 → UInt32`, `parseBlock : Bytes → Nat → Vector UInt32 16`; big-endian four-byte words, ascending word order; helper zero-extends unavailable bytes after Nat bounds checks | `toNat_parseWord`, `parseWord_wordByte`, `toBitVec_parseWord`, `wordsModel_parseBlock`, `parseBlock_get` (caller supplies a complete 64-byte window), `getElem?_toByteArray/of_lt` | asymmetric high/low bytes, all sixteen ascending words and offset 64, huge unavailable offset; **discharged** |
| FIPS 180-4 §6.2.2 ascending chaining | `Sha256.blocks : Bytes → Nat → Nat → Vector UInt32 8 → Vector UInt32 8`; structural remaining-block recursion, one accepted compression at each offset | `blocks_model`, `blocks_add`, `Model.blocks_chain`, `Model.Chain.eq_blocks`; separate BitVec32 serial fold and inductive chaining trace | public-law three-block split/composition client and asymmetric multiblock host inputs; **discharged** |
| FIPS 180-4 §§6.2.1–6.2.2 output | `Sha256.wordByte : UInt32 → Nat → UInt8`, `serialize : Vector UInt32 8 → Bytes`, `digestValue : Vector UInt32 8 → Bytes32`; each of eight words serialized big-endian, leading zeros retained; public checked Base fixed-byte construction proved successful | `serialize_get/model`, `size_serialize`, `toBytes_digestValue` | eight distinct word positions, leading zeros and high-bit probes; **discharged** |
| EELS `forks/amsterdam/vm/precompiled_contracts/sha256.py:51`; external `hashlib.sha256` / FIPS 180-4 §§5.1.1, 5.2.1, 6.2 | `STFSpec.Hash.sha256 : ByteArray → Bytes32`; standard IV, pad, ascending compression fold and ordered digest bytes; total extension on all sizes, standard-domain equivalence requires caller premise `8*msg.size < 2^64`; no gas/effect changes | `size_sha256`, `sha256_model`, `sha256_digest` against `Model.Digest`, `sha256_fipsDigest` against unwrapped `Model.fipsPad` under the explicit domain | primary production KATs: empty/abc and NIST CAVP 55/56/64-byte messages; finite authenticated pinned-host differential; **proved for the stated model/domain** |

`STFSpec/Conformance/Hash/Sha256DigestGuards.lean` owns the primary KATs
and deterministic padding, byte-order and conceptual-length probes;
`Sha256DigestCallerProofs.lean` composes only public Hash/Base laws, including
shorter-padding impossibility and uniqueness of the bounded congruent zero count.
The NIST CAVP byte-oriented archive's `SHA256ShortMsg.rsp` entries at bit lengths
0, 440, 448 and 512 supply the exact messages and digests; the NIST SHA256
worked example supplies abc. Links and selectors are recorded in the test module.
`STFSpec/Conformance/Hash/sha256_differential.py`, run with the lock-exact EELS
interpreter using `-I -B`,
compares actual production digest bytes with `source.hashlib.sha256` observed
through authenticated pinned source, plus independently generated finite padding.
The driver owns the seed and case inventory: bounded random messages plus
deterministic boundary, zero, all-one and asymmetric inputs, with a digest and
padding observation per message. The finite tests assume the FIPS byte domain and a working host SHA-256;
no gigantic input, precompile gas/effect, guest, collision-resistance or ROM theorem
is established.

The executable path has one packed append, constant-width word parsing/output,
and a tail-recursive forward loop over the padded buffer. Its O(n) byte work and
O(⌈(n+9)/64⌉) compressions avoid per-block copies or traversals of the full message.
Generated C inspection confirms the loop and packed accesses; native vectors retain
boxed words and fixed-size schedule allocations. This is a bounded code-shape check,
not a throughput, allocation-volume, target-zkVM or C1–C4 measurement claim.


### Fixed-rate Keccak digests

`STFSpec/Hash/KeccakSponge.lean` implements byte-aligned legacy Keccak-256 and
Keccak-512. These rows are **discharged against the explicit standard sponge
model**, not a universal host-backend or guest-equivalence theorem. Each accepts
every finite input, is pure and total, has no ordered failures or consuming handler,
and returns only the stated value. The executable path uses packed Base `Bytes`
and native lanes; the model uses byte lists and BitVec coordinates. Only rates
136/72 and outputs 32/64 are exposed by `KeccakSponge.Rate`; no arbitrary-rate
semantics are adopted.

| Source | Public declaration and type | Domain / success observation | Ordered failures / consumer | Public laws | Tests |
|---|---|---|---|---|---|
| Keccak reference v3 §§1.1.2, 1.4; FIPS 202 §5.1 | `KeccakSponge.pad : Rate → Bytes → Bytes` | Every byte string; legacy first 0x01 / last 0x80, combined 0x81; exact multiples add a block | None | `size_pad`, `paddedSize_eq`, `paddedSize_mod`, `paddingCount_bounds`, `getElem_pad_prefix`, `getElem_pad_first`, `getElem_pad_last`, `getElem_pad_single`, `getElem_pad_middle`, `pad_model` | Empty, one-byte padding, exact-rate padding at both rates; 135/136/137-byte KATs |
| FIPS 202 §3.1.2 | `KeccakSponge.decodeLane : (Nat → UInt8) → UInt64`; `encodeLaneByte : UInt64 → Fin 8 → UInt8` | Eight little-endian bytes per lane; extract bytes 0 through 7 | None | `decodeLane_model`, `encodeLaneByte_model` | Asymmetric 0x0807060504030201; all-ones lane |
| Keccak reference v3 §1.3; FIPS 202 §4 | `KeccakSponge.xorBlock : Rate → Bytes → Nat → KeccakState → KeccakState`; `absorbBlock` same type; `absorb : Rate → Bytes → Nat → Nat → KeccakState → KeccakState` | Every offset/state/count; zero extension beyond bytes, leading rate lanes XORed, capacity unchanged, ordered permutation after each block | None; digest supplies fully padded blocks | `xorBlock_model`, `absorbBlock_model`, `absorb_model`, `absorb_zero`, `absorb_add` | Both capacity boundaries; public ordered-block composition client |
| Keccak reference v3 §1.3; FIPS 202 §4 | `KeccakSponge.squeeze : KeccakState → (n : Nat) → n ≤ 200 → Bytes`; `digestBytes : Rate → Bytes → Bytes` | Every state/bounded output; little-endian x+5*y order. Fixed digest outputs fit one rate block | None; squeeze caller supplies n≤200 | `size_squeeze`, `squeeze_model`, `size_digestBytes`, `digestBytes_model` | Asymmetric sixteen-byte squeeze; public model client |
| EELS `crypto/hash.py:62–77`; pinned pycryptodome 3.23.0 | `STFSpec.Hash.keccak256 : ByteArray → Hash32` | Every finite message; rate136/output32, no SHA-3 domain suffix | None | `keccak256_bytes`, `keccak256_model`, `size_keccak256` | Four published primary KATs, supplemental abc; actual pinned EELS differential |
| EELS `crypto/hash.py:80–95`; pinned pycryptodome 3.23.0 | `STFSpec.Hash.keccak512 : ByteArray → Hash64` | Every finite message; rate72/output64. Retained pending Q18 disposition | None | `keccak512_bytes`, `keccak512_model`, `size_keccak512` | Published empty KAT; actual pinned EELS differential |

`STFSpec/Conformance/Hash/KeccakSpongeGuards.lean` owns the deterministic guards.
Published KATs come from the [Keccak team round-3 archive](https://keccak.team/obsolete/KeccakKAT-3.zip),
`ShortMsgKAT_256.txt` at Len=0/1080/1088/1096 and `ShortMsgKAT_512.txt` at Len=0;
the test records archive/member hashes and exact selected messages. The abc value
is supplemental, generated by the primary XKCP reference, not a published KAT.
`KeccakSpongeCallerProofs.lean` supplies public composition and replacement proofs.

`keccak_differential.py` calls authenticated actual pinned EELS functions using the
lock-exact interpreter (`.venv/bin/python -I -B`), its shared source/dependency
integrity driver and pycryptodome 3.23.0 version check. The driver owns the seed
and case inventory: bounded random messages plus rate/boundary, zero, all-one
and asymmetric messages, observing both fixed digest outputs.
This is finite value evidence for the selected backend, not OpenSSL equivalence,
EEST execution, query composition or cryptographic security. The separate native
1 MiB performance case checks its expected digest outside the timed loop; bounded
cost evidence does not discharge a throughput target or accelerator replacement.

### Implemented RIPEMD-160 fixed-word compression slice

`STFSpec/Hash/Ripemd160Compression.lean` owns this **discharged** bounded slice.
The public compression domain is literally `Vector UInt32 5` × `Vector UInt32 16`;
there is no length or host-capability premise. Words are already parsed. Both
working branches store A,B,C,D,E in that order. Ascending rounds use f(j) on the
left and f(79−j) on the right, with separate order/rotation/constant tables; updates
are simultaneous. Feedforward reads all five original chaining words.

EELS `forks/amsterdam/vm/precompiled_contracts/ripemd160.py:26–54`, notably `:52`,
invokes `hashlib.new("ripemd160", data)`, without exposing raw compression.
The algorithm rows therefore cite Dobbertin–Bosselaers–Preneel, *RIPEMD-160:
A Strengthened Version of RIPEMD*, FSE 1996, pp. 71–82, and
[the corrected author pseudocode](https://homes.esat.kuleuven.be/~bosselae/ripemd/rmd160.txt).
No publication copy is retained. The independent model shares standard literal
table data but uses only BitVec arithmetic; separate integer-model tests audit all
entries against independently transcribed primary mathematical data.

| Source | Public declaration and type | Domain / success observation | Ordered failures / consumer | Public laws | Tests |
|---|---|---|---|---|---|
| Author word convention | `Ripemd160Model n := Vector (BitVec 32) n`; `ripemd160ToModel : Vector UInt32 n → Ripemd160Model n` | Every word vector; exact unsigned words and low bit order | None; fixed sizes | `ripemd160ToModel_word`, `_bit`, `_inj` | Public observers and six composition clients |
| Author cyclic left shift | `ripemd160Rotl : UInt32 → Nat → UInt32` | Every word/amount, rotation modulo 32 | None | `toBitVec_ripemd160Rotl`, `ripemd160Rotl_bit` | 0/31/32/33/64 and independent rotation probes |
| Author f(j) | `ripemd160F : Fin 80 → UInt32 → UInt32 → UInt32 → UInt32`; `Ripemd160Model.f` | Five 16-round Boolean groups | None | `toBitVec_ripemd160F` | Every j, all group boundaries |
| Author initial value | `ripemd160IV : Vector UInt32 5` | Original five chaining words | None | Used by primary KATs | All five IV words; empty/abc compression KATs |
| Author r,r′,s,s′,K,K′ | `ripemd160LeftOrder`, `ripemd160RightOrder : Vector (Fin 16) 80`; `ripemd160LeftRotations`, `ripemd160RightRotations : Vector Nat 80`; `ripemd160LeftConstants`, `ripemd160RightConstants : Vector UInt32 5` | Exact branch/group tables | None; indexes bounded by types | Used by round law | All 320 order/rotation entries and ten constants |
| Author round selection | `ripemd160Group : Fin 80 → Fin 5`; `ripemd160Reverse : Fin 80 → Fin 80` | j/16 and 79−j | None | Used by round law | Every j, boundaries |
| Author simultaneous update | `ripemd160Step : Vector UInt32 5 → Fin 80 → UInt32 → UInt32 → Nat → Vector UInt32 5`; `Ripemd160Model.step` | A=E,B=T,C=B,D=rotl10(C),E=D, original operands | None | `ripemd160ToModel_step` | Explicit simultaneous update and asymmetric branch cases |
| Author dual loop body | `Ripemd160Work` (two five-word branches); `ripemd160WorkToModel`; `ripemd160Round : Ripemd160Work → Vector UInt32 16 → Fin 80 → Ripemd160Work`; `Ripemd160Model.round` | Independent left/right updates on every working state | None | `ripemd160WorkToModel_inj`, `_round` | Distinct arbitrary initial branches and every round group |
| Author ascending j loop | `ripemd160Rounds : Ripemd160Work → Vector UInt32 16 → (n : Nat) → n ≤ 80 → Ripemd160Work`; `Ripemd160Model.rounds` | Prefix 0 through n−1, structural recursion | None; n≤80 supplied by caller | `ripemd160WorkToModel_rounds` | All prefixes 0–80 on eight states |
| Author cross-branch combine | `ripemd160Feedforward : Vector UInt32 5 → Ripemd160Work → Vector UInt32 5`; `Ripemd160Model.feedforward` | Original h1+C+D′,h2+D+E′,h3+E+A′,h4+A+B′,h0+B+C′ | None | `ripemd160ToModel_feedforward` | Unequal original/left/right words; wraparound; arbitrary states |
| Author complete compression | `ripemd160Compress : Vector UInt32 5 → Vector UInt32 16 → Vector UInt32 5`; `Ripemd160Model.compress` | Initialize both branches from h, exactly 80 rounds, original-state feedforward | None | `ripemd160ToModel_compress` | Primary compression KATs, integer-model comparison, finite test-only EELS composition |

`Ripemd160CompressionGuards.lean` has 36 deterministic guards, including primary
empty/abc compression KATs for explicitly supplied MD4-padded little-endian blocks.
These are not production digest tests. `Ripemd160CompressionCallerProofs.lean`
has six clients using public laws, including two consecutive compressions and
prefix-feedforward composition without unfolding native word/storage arithmetic.

`ripemd160_compression_differential.py` uses an independently written integer model
with cyclic feedforward indexing, seed 170160, 41 arbitrary original chaining states,
unequal working branches, all table entries, every group boundary and prefixes
0–80: 2827 generated guards. Its finite test-only MD4 padding and serial compression
on 92 messages are compared against
actual authenticated pinned `ripemd160.py` precompile execution and its supported
host `hashlib` backend. Nine primary author digest facts, including million-a, are
checked separately; random/boundary message observations remain bug-finding evidence.
The interpreter is the frozen EELS venv with `-I -B`; the shared Driver authenticates
current source/lock bytes against the unreplaced pin and ethereum-types against its
installed RECORD. Pre/post identities include sources, interpreter and shared driver.
These tests establish no all-host, all-resource, guest/EEST or cryptographic claim.
DISC-005/Q19/D14/O12 dispositions stay open and unchanged.

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
  - Implemented fixed-block SHA-256 compression KATs: explicitly supplied padded empty/abc words, and NIST abc states after rounds 0,1,16,63. Production `sha256` KATs cover empty/abc and the exact NIST CAVP 55/56/64-byte messages (§3), with deterministic padding/trailer and endian probes.
  - RIPEMD-160 vectors from the original paper: empty = `9c1185a5c5e9fc54612808977ee8f548b2258d31`, `"abc"`, and the million-`a` test.
  - BLAKE2F: the EIP-152 vectors 4–8, including `rounds = 0`, `f = 0`, and `rounds = 2^32 − 1` as a *parse-only* guard (the compression is not run).
  - `keccakF1600` on the all-zero state (the published permutation KAT), implemented in the guard module linked in §3.
- **Property / differential tests.**
  - Output sizes, as theorems rather than tests.
  - A differential test against pycryptodome and `hashlib` in the scratch venv on random lengths 0..4096 (bug-finding only).
  - When a fast path is attached: fast ≡ reference on random inputs, then as a proof (D4).
  - A bridge test comparing `keccakF1600` with the ZisK accelerator's `keccakF` (§10) on random states.

## 5. Interface

The namespace is `STFSpec.Hash`. All items are public unless marked internal.

```lean
-- Keccak
structure KeccakState                        -- private lane storage; coordinate API
def keccakF1600 : KeccakState → KeccakState     -- 24 rounds θ ρ π χ ι
namespace KeccakSponge
  inductive Rate where | keccak256 | keccak512
  def Rate.bytes : Rate → Nat
  def Rate.output : Rate → Nat
  def digestBytes : Rate → Bytes → Bytes
end KeccakSponge
-- Arbitrary-rate/output sponge behaviour remains unspecified.
def keccak256 (msg : ByteArray) : Hash32        -- rate 136, out 32
def keccak512 (msg : ByteArray) : Hash64        -- rate 72, out 64 (unreachable)

-- SHA-256 and RIPEMD-160
def sha256    (msg : ByteArray) : Bytes32
def sha256Compress : Vector UInt32 8 → Vector UInt32 16 → Vector UInt32 8   -- internal
def ripemd160 (msg : ByteArray) : FixedBytes 20
def ripemd160Compress : Vector UInt32 5 → Vector UInt32 16 → Vector UInt32 5 -- fixed-word reference

-- BLAKE2b F (EIP-152)
namespace Blake2b
  structure Params where
    rounds : UInt32
    h : Vector UInt64 8
    m : Vector UInt64 16
    t0 t1 : UInt64
    f : UInt8                                   -- raw byte; the precompile checks f ∈ {0,1}
  def getParameters (data : ByteArray) (h : data.size = 213) : Params
  def serialize : Params → ByteArray
  def parameterByte : Params → Fin 213 → UInt8
  def leWord : (n : Nat) → (Fin n → UInt8) → BitVec (8 * n)  -- Base bridge in §3
  def wordByte {n : Nat} : BitVec (8 * n) → Fin n → UInt8
  def G : Vector UInt64 16 → (a b c d : Fin 16) → (x y : UInt64) → Vector UInt64 16  -- internal
  def compress (rounds : UInt32) (h : Vector UInt64 8) (m : Vector UInt64 16)
      (t0 t1 : UInt64) (f : Bool) : ByteArray   -- 64 bytes
  def IV : Vector UInt64 8; def sigma : Vector (Vector (Fin 16) 16) 10  -- constants
end Blake2b

-- Oracle seam (D5)
class KeccakQuery (m : Type → Type) where
  keccak : ByteArray → m Hash32
instance : KeccakQuery Id := ⟨fun b ↦ keccak256 b⟩
instance [Monad m] [KeccakQuery m] : KeccakQuery (ExceptT ε m) := ⟨fun b ↦ ExceptT.lift (keccak b)⟩
instance [Monad m] [KeccakQuery m] : KeccakQuery (StateT σ m)  := ⟨fun b ↦ StateT.lift (keccak b)⟩
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
| `KeccakState` | private `Vector UInt64 25` (reference) | the FIPS 202 state `Fin 5 × Fin 5 → BitVec 64` via lane indexing | size 25 (by type) | local to one hash call, linear | `keccakF1600`: O(1) (24 rounds). `keccak256`: O(⌈(n+1)/136⌉) permutations |
| SHA-256 state | `Vector UInt32 8` + 64-word schedule | FIPS 180-4 | by type | linear, local | O(⌈(n+9)/64⌉) compressions |
| RIPEMD-160 state | `Vector UInt32 5` | the original specification | by type | linear, local | O(⌈(n+9)/64⌉) |
| BLAKE2b work vector | `Vector UInt64 16` | RFC 7693 `v` | by type | linear, local | O(rounds) |
| `Params` | record | the parsed fields | `getParameters` is a bijection on 213-byte inputs | immutable | O(1) |

None of these structures is snapshot-reachable; they live only within one call.
[DEBT-HASH-REFERENCE](../DEBT.md#debt-hash-reference--boxed-reference-rounds)
owns round allocation evidence and its replacement criterion;
[DEBT-KECCAK-DIGEST](../DEBT.md#debt-keccak-digest--reference-sponge-cost)
owns digest-level padding and traversal costs. Inspect generated C/IR on each
hot path, separating static code shape from dynamic allocation measurements.

## 7. Contract and laws

The contract is functional correctness against the published algorithms, plus these laws. The SHA-256 compression implementation observes native UInt32 vectors through `Sha256.wordsModel` into its explicit `BitVec 32` model; its discharged equations are listed in §3.

The Keccak implementation is related to a BitVec-coordinate and byte-list model
by the permutation laws (§3) and `KeccakSponge.digestBytes_model`. The model
shares `Rate.bytes`, `paddingCount` and `keccakLaneIndex` with the implementation;
model correspondence alone does not independently certify those formulas.
Per-byte padding laws, primary KATs and authenticated finite differentials provide
additional evidence for standard fidelity. Induction over ordered blocks lifts the accepted permutation relation through padding, lane
packing and squeezing to both public digest observers. The remaining operations
must establish their corresponding standard relations and these laws.

- [C] `(keccak256 b).toBytes.size = 32`, `(sha256 b).toBytes.size = 32`, `(ripemd160 b).toBytes.size = 20`, and `(Blake2b.compress …).size = 64`. The first three hold by type; the last must be proved.
- [C] Sponge decomposition is implemented by `KeccakSponge.digestBytes` and
  exposed by `keccak256_bytes`/`keccak512_bytes`: pad, ordered absorb, then squeeze, with `pad` giving `(b ++ 0x01 ++ zeros ++ 0x80)` of length a multiple of 136, or `b ++ 0x81` when exactly one padding byte remains. This is the statement that fast paths refine.
- [C] Fixed-word SHA-256 compression correspondence, schedule recurrence/input preservation, bounded round-prefix correspondence and original-state feed-forward are discharged by the §3 laws. Message padding, byte correspondence, serial block composition and the inductive full-digest relation are discharged in §3; FIPS-domain correspondence retains the explicit Q46 hypothesis.
- [C] KATs as `#guard` (compile-time), not `native_decide` (CONTRIBUTING §4).
- [C] BLAKE2b raw parameters: `getParameters_serialize` and `serialize_getParameters` prove the two-way bijection between all raw `Params` and 213-byte inputs; `serialize_size` proves its exact size. `getParameters_rounds/h/m/t0/t1/f` expose the field windows; `wordByte_leWord`, `leWord_wordByte`, `toNat_leWord_succ`, `toNat_leWord_eq_ofLeBytes` and `wordByte_toNat` connect bytes, bits and numeric radix-256 digits. These parameter laws are proved in §3.
- [C] BLAKE2b compression: `G` rotates correctly: `rotr64 x r = (x >>> r) ||| (x <<< (64 − r))` for `0 < r < 64`, which is exactly EELS's `(x >> R) ^ ((x << (w−R)) % 2^w)` on words < 2^64 (trap (b)). The 17-element trap (a) does not change the output.
- [T] Every function is structurally recursive over the input blocks or over `rounds : UInt32` (via `Nat` fuel = `rounds.toNat`).
- [F] (D4) a future faster digest must equal the present legible reference through
  an ordinary equality or model refinement (no `@[csimp]`, D21). A candidate
  unrolled permutation needs a round-by-round simulation against `keccakF1600`;
  no fast path is implemented (§10).
- [R] (bridge module outside the core) `keccakF1600 ≡` the ZisK accelerator's `keccakF` (`ZiskAccel.lean:113`; §10) under the lane-order correspondence.
- [C] `HashConsts.query (m := Id) = HashConsts.literals` (`EthBase`), as a `#guard` or theorem; by F16 this is evaluable only once `keccak256` has no `sorry` leaf. A compiled prototype of the interfaces checked the same values at `Id`.
- [C] The lift instances forward: `keccak (m := ExceptT ε m) b = ExceptT.lift (keccak b)` and likewise for `StateT` (definitional).
- [S] `KeccakQuery Id` is definitionally `keccak256` (`rfl`). In `EthSecurity`, kernels are run under `simulateQ` with a random oracle, and collision/ROM bounds are stated there, never assumed here. `sha256` is used under a separate collision-resistance assumption for SSZ request binding (CONTRACT §7). The two oracles must not be conflated (D5).

### Informal correctness argument

**Claim.** Each concrete hash function returns the bytes specified by its standard and the pinned dependency, and the query interface specialises to concrete Keccak under its identity instance.

**Premises.** EthBase byte and word laws; exact padding, constants and endian conventions; the reference host supports the requested algorithm when reference equivalence is claimed.

**Argument.** Relate each implementation state to the standard's chaining state after the same number of blocks. The initialisation establishes the relation; one compression/permutation round preserves it by the word equations; induction over rounds and blocks gives the final digest. Padding requires separate cases at the final-block boundary, including the empty message and a full block. BLAKE2F parsing has the two-way raw-layout laws in §3; the precompile checks size, parses, charges gas, then validates the final flag before compression (R5). For the query abstraction, induction over the query computation replaces each query by concrete Keccak, preserving returned values and error order. This is functional correctness. Collision resistance is a separate assumption in EthSecurity and cannot follow from matching test vectors.

**Open obligations.** Reference permutation step/round/prefix and lane-bit correspondence,
fixed-rate Keccak padding, byte packing, ordered absorption, squeezing and digest
correspondence, SHA-256 fixed-word and message-digest correspondence, and BLAKE2F
raw parameter byte-layout correspondence with both round trips are discharged
for the slices in §3. RIPEMD-160 Boolean/rotation/step/dual-round, bounded-prefix
and complete fixed-word compression correspondence are also discharged on every
parsed-word input. RIPEMD digest/padding/serialization and BLAKE2F compression
rounds and their complete boundary laws remain unwritten. Q46 supplies the SHA-256 domain policy.
The oracle scope is fixed (D5; a compiled prototype of the interfaces showed it flows through every interface, F1–F4, F15, F18); the oracle coupling for `Models` at generic `m` remains open (it is stated at `PreState Id`). RIPEMD reference equivalence is conditional on host capability (DISC-005), not solely an OpenSSL major version.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthBase`.
- **Used by:** `EthCodec` (SSZ merkleization, address derivation), `EthVmInstructions` (`KECCAK256`, `EXTCODEHASH`, CREATE/CREATE2), `EthPrecompiles` (SHA-256, RIPEMD-160, BLAKE2F, and ECRECOVER's address hash through `KeccakQuery`), `EthBlock` (standalone acquisition wrapper, F20), `EthStateless` (guest acquisition, F20), `EthConformance` (engine acquisition, R4/F20), and transitively `EthCommit`, `EthStateWitness` and `EthVmRunner` (via `KeccakQuery`).
- **Seams provided.** `keccak256`/`sha256` as plain functions. `KeccakQuery m`, with its `Id`, `ExceptT` and `StateT` instances, for kernels that `EthSecurity` must reinterpret. `HashConsts.query` for the keccak-derived constants. `Blake2b.getParameters` and `compress` for the precompile, which must charge gas *before* calling `compress`.
- **Guarantees.** Totality, determinism and independence from the host.
- **Relies on.** `Hash32`, `Bytes32` and `FixedBytes` from `EthBase`, and Lean core `UInt64`/`UInt32` rotations.

## 9. Open decisions

- **D4** (hash implementations): reference first. A proved fast path follows measurement; the local reference allocation exception and replacement criterion are owned by [DEBT-HASH-REFERENCE](../DEBT.md#debt-hash-reference--boxed-reference-rounds).
- **D5** (provisional: broad scope with monad-parametric interfaces; B10 and DECISIONS §3): **every** keccak call goes through `KeccakQuery` (R6). A compiled prototype of the interfaces showed that the dependency flows through every interface once the signatures are monad-parametric (F1–F4, F15, F18). Open: the oracle coupling for `Models` at generic `m`.
- **D21** (accepted, 2026-09-28): no `@[csimp]` and no axiom-adding tactics (`native_decide`, `bv_decide`). A fast path is either a representation replacement proved against this module's contract (D25), or an executable definition with a legible reference beside it and an ordinary equality proof (`CONTRIBUTING.md` §4).
- **Q46**: the SHA-256 input-domain disposition is owned by [DECISIONS §4](../DECISIONS.md#4-question-dispositions); fixed-word compression has no message-length premise.
- **P2** (authority order): host-dependent `hashlib` behaviour falls under CONTRACT §6.
- `ripemd160` host dependency: tracked as DISC-005 (DECISIONS Q19). The spec implements the algorithm unconditionally; the host-capability policy is O12 (DISC-001).

## 10. Gaps

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Remaining core hash implementations.** The implemented providers, laws and
  deterministic/differential evidence are owned by §3–§4. The query interface,
  RIPEMD-160 digest/padding/serialization and BLAKE2F compression remain
  unimplemented. Their vectors need transcription from primary sources
  (the RIPEMD-160 paper and EIP-152). Historical prototypes are evidence only.
- **Backend equivalence unverified.** That OpenSSL keccak-256 and pycryptodome keccak are bit-identical on all inputs is assumed from their specifications, not tested. The fixed-rate driver supplies finite evidence against the actual pinned
pycryptodome backend; it does not compare OpenSSL or prove backend equivalence.
- **RIPEMD-160 host discrepancy** (R4): recorded as DISC-005; no upstream report has been made.
- **BLAKE2F coverage** in EEST is 5 files per format. The parameter-only tests in §3 do not execute these guest fixtures or compression. Beyond the EIP-152 vectors I have not checked whether any fixture exercises `rounds` near `2^32 − 1` with sufficient gas (probably impossible within the block gas limit), `f` exactly 0 versus 1 at the same rounds, or `t` counters with the high bit set.
- **The gas-before-compute ordering** for BLAKE2F is a cross-module obligation with no stated theorem yet. `EthPrecompiles` must own it. If it were violated, an adversarial `rounds` value could make evaluation hang in the guest while the reference charges out of gas first.
- **Fast-path proof strategy** (D4): the simulation proof of an unrolled keccak against the reference is unscoped. No existing Lean proof of this shape was found in this repository. VCV-io's `Keccak.lean` is a candidate reference but is slow (compiled at `f5119c6`: about 200–300 µs per 64-byte hash, allocation-bound).
- **Bridge to the ZisK accelerator's `keccakF`** (`RiscvZkvm.Rv64.ZiskAccel`, `ZiskAccel.lean:113`; the copy checked locally is evm-asm's `EvmAsm/Rv64/ZiskAccel.lean`, the same file `EthField` §4 cites at `:313`/`:489`): the lane-order and endianness correspondence (it acts on `List (BitVec 64)`) is not written down. The bridge module has no owner package yet: it would need riscv-zkvm, which is on toolchain v4.33.
- **`sha256` for SSZ versus request hashing**: whether both uses must be modelled by one collision-resistance assumption in `EthSecurity` has no owner.
- **Performance:** reference rounds use arrays with boxed lanes and closure dispatch, with no `List` construction in the executable round path. [DEBT-HASH-REFERENCE](../DEBT.md#debt-hash-reference--boxed-reference-rounds) owns the generated-C procedure/results, historical diagnostics and replacement criterion under D4/D18. No throughput target, dynamic allocation total, fast-path equivalence or whole-hash cost gate is discharged.
The fixed-rate sponge uses packed bytes and native lanes, copying the padded
message once and processing blocks with a tail-recursive loop. Generated C and
the retained historical native diagnostic provide local cost evidence; their
source basis and limitations are recorded in
[DEBT-KECCAK-DIGEST](../DEBT.md#debt-keccak-digest--reference-sponge-cost).
D4’s status is unchanged.
RIPEMD-160 uses array-backed fixed-word vectors and native UInt32 arithmetic,
with no executable per-round List or bignum lane arithmetic. Its generated C is
inspected and compiled with strict checks; static boxing/index sites are code
shape observations, not measured allocation totals. No RIPEMD performance or
whole-hash cost gate is discharged.
- **`keccak512`, `_hashlib_has_keccak` and `_USE_HASHLIB` scope (Q18).** Keccak512 is
implemented and proved against the fixed-rate model. The backend probe remains
host dispatch with no corresponding Lean operation. A static call-graph pass over the pinned EELS, run by the failure ledger (maintained outside this repository), places `keccak512` outside the guest call graph and finds the backend probe runs at import time only, so they can be excluded in `STFSpec/informal/EXCLUDED.md` with that reason (DECISIONS Q18).
