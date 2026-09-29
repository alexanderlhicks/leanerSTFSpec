# `EthPrecompiles`: the Amsterdam precompiled contracts

*Status: informal specification, draft. Date: 2026-09-29. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F3, F9, F16 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D3, D4, D5, D6, D7, D12, D14, D15, D17, D18, D21 · questions: B8/Q43, B13/Q40–Q42, Q19.*

Tags: **[V]** verified by reading the pinned source (or running the pinned dependency);
**[I]** inference, not yet checked. Paths are relative to
`src/ethereum/forks/amsterdam/vm/precompiled_contracts/` unless they start with `crypto/`,
`vm/` or a package name; `vm/` means `src/ethereum/forks/amsterdam/vm/`.

## 1. Purpose

`EthPrecompiles` specifies the 18 precompiled contracts active in Amsterdam: for each, its
address, gas formula, input parsing and padding, output encoding, and which failures are an
exceptional halt and which are a successful call with empty output. It also owns the EVM byte
codecs for curve points (EIP-196/197, EIP-2537), the KZG
versioned hash, and the address → implementation table. It specifies the EIP-2537 MSM discount
tables, but their values are `GasCosts` fields defined in `EthFork` (DECISIONS B8). It sits beside opcode stepping in layer
L3 (ARCHITECTURE §2, §5.5): it depends on `EthVmCore` for the gas meter and halt type, on
`EthPairing` (hence `EthCurve`, `EthField`) for the mathematics, and on `EthHash`. The runner
reaches it only through the table that `EthFork` installs (D17), so no opcode proof depends on
it. D12 puts three deliverables in scope: this executable behaviour (i), mathematical
correctness through the Mathlib partners (ii), and cryptographic-security statements (iii).

## 2. Requirements

### 2.1 Calling convention (all precompiles)

- **Dispatch.** If the message's `code_address` is a key of `PRE_COMPILED_CONTRACTS` and
  precompiles are not disabled for this frame, the runner calls the implementation instead of
  interpreting code (`vm/interpreter.py:438–441`) [V]. Value transfer happens first (`:424–437`).
  `disable_precompiles` is set when the target is an EIP-7702 delegation
  (`vm/interpreter.py:194`); that is the runner's concern (`EthVmRunner`). All precompile
  addresses are pre-warmed (`vm/interpreter.py:172`); `EthPrecompiles` exports the address set.
- **Effects.** Every implementation reads only `evm.call_data`, calls `charge_gas` (execution
  gas only, `vm/gas.py:408–422`, `:391–405`) and assigns `evm.output`, or raises [V: every file
  read]. No precompile touches state, logs, refunds, state gas, return data or memory.
- **Failure → outcome** (`STFSpec/informal/CONTRACT.md` O8/O9). Any `ExceptionalHalt` (including
  `OutOfGasError`, `InvalidParameter`, `KZGProofError`, `vm/exceptions.py:51`, `:110`, `:134`)
  is handled by the runner: state gas restored, remaining gas forfeited, output `b""`, tx state
  restored to the pre-call snapshot, so value transfer is undone (`vm/interpreter.py:456–474`)
  [V]. The error class is not otherwise observable in the guest output [I: only success/failure
  reaches the parent or the receipt]. "Empty output" failures (ECRECOVER, P256VERIFY) are
  **successful** calls with `output = b""`.
- **Normal form.** Every precompile is equivalent to: *(a)* pre-charge validity checks,
  *(b)* `charge_gas(cost(data))`, *(c)* a computation that returns output or halts. Pre-charge
  failures and post-charge failures are both exceptional halts and forfeit all gas, so the
  position of a check relative to the charge is unobservable [I, relies on the previous point];
  the gas *amount* on success paths is observable exactly.
- **Padding.** `buffer_read(data, start, size)` returns `data[start:start+size]` right-padded
  with zeros to `size` (`vm/memory.py:63–83`) [V]. Precompiles that use it (ECRECOVER, MODEXP,
  ECADD, ECMUL, P256VERIFY) therefore read short input as zero-extended and ignore excess input.
- **Arithmetic types.** Lengths and word counts are `Uint` (unbounded); `ceil32(len)//32` is
  `⌈len/32⌉` (`utils/numeric.py`); gas values are `ExecutionGas` (`Nat` in the spec, never
  wrapping).

### 2.2 Address, gas, input and output per precompile

Addresses from `__init__.py:38–55`; gas constants from `vm/gas.py:112–137` [V]. "Halt" means
exceptional halt; `⌈n⌉₃₂ := ⌈len(data)/32⌉`.

| Addr | Name (EELS) | Gas | Pre-charge checks (halt) | Output / post-charge failures |
|---|---|---|---|---|
| `0x01` | `ecrecover` | 3000 | — | 32-byte left-padded address, or **empty** on any invalid input |
| `0x02` | `sha256` | `60 + 12·⌈n⌉₃₂` | — | `SHA-256(data)`, 32 bytes |
| `0x03` | `ripemd160` | `600 + 120·⌈n⌉₃₂` | — | `RIPEMD-160(data)` left-padded to 32 bytes |
| `0x04` | `identity` | `15 + 3·⌈n⌉₃₂` | — | `data` |
| `0x05` | `modexp` | EIP-7883 (§2.3) | any length `> 1024` | `mod_len` bytes (§2.3) |
| `0x06` | `alt_bn128_add` | 150 | — | 64 bytes `x‖y`; invalid point → halt |
| `0x07` | `alt_bn128_mul` | 6000 | — | 64 bytes; invalid point → halt |
| `0x08` | `alt_bn128_pairing_check` | `45000 + 34000·⌊len/192⌋` | — | 32-byte `1`/`0`; `len mod 192 ≠ 0`, invalid point, G2 not in subgroup → halt |
| `0x09` | `blake2f` | `rounds` | `len ≠ 213` | 64 bytes; `f ∉ {0,1}` → halt |
| `0x0a` | `point_evaluation` | 50000 | `len ≠ 192` | 64 bytes `4096‖BLS_MODULUS`; any verification failure → halt |
| `0x0b` | `bls12_g1_add` | 375 | `len ≠ 256` | 128 bytes; invalid point → halt |
| `0x0c` | `bls12_g1_msm` | `k·12000·disc₁(k)/1000` | `len = 0` or `len mod 160 ≠ 0` | 128 bytes; invalid point or not in G1 → halt |
| `0x0d` | `bls12_g2_add` | 600 | `len ≠ 512` | 256 bytes; invalid point → halt |
| `0x0e` | `bls12_g2_msm` | `k·22500·disc₂(k)/1000` | `len = 0` or `len mod 288 ≠ 0` | 256 bytes; invalid or not in G2 → halt |
| `0x0f` | `bls12_pairing` | `32600·k + 37700` | `len = 0` or `len mod 384 ≠ 0` | 32-byte `1`/`0`; invalid or not in subgroup → halt |
| `0x10` | `bls12_map_fp_to_g1` | 5500 | `len ≠ 64` | 128 bytes; `fp ≥ q` → halt |
| `0x11` | `bls12_map_fp2_to_g2` | 23800 | `len ≠ 128` | 256 bytes; component `≥ q` → halt |
| `0x100` | `p256verify` | 6900 | — | 32-byte `1`, or **empty** on any invalid input or length `≠ 160` |

### 2.3 Details

**ECRECOVER** (`ecrecover.py:26–64`) [V]. Charge 3000 (`:40`). Read `h = data[0:32]`,
`v = data[32:64]`, `r = data[64:96]`, `s = data[96:128]` with zero padding (`:43–47`). Return
empty unless `v ∈ {27, 28}` (the full 32-byte word, so `v = 27 + 2^8` fails), `0 < r < n`,
`0 < s < n` (`:49–54`); high `s` is accepted. Call `EthCurve.Secp256k1.recover r s (v = 28) h`;
on `SignatureError` return empty (`:56–60`). Output
`0¹² ‖ (← KeccakQuery.keccak pub)[12:32]` (`:62–64`): the public-key hash is an oracle query
(D5), so ECRECOVER is a `PrecompileFn m`.

**SHA256 / RIPEMD160 / IDENTITY** (`sha256.py:28–51`, `ripemd160.py:29–54`, `identity.py:26–49`)
[V]. The hashes are Python `hashlib.sha256` and `hashlib.new("ripemd160")`, i.e. host OpenSSL
(`reference.toml` note) [V]; RIPEMD-160 output is 20 bytes, left-padded to 32.

**MODEXP** (`modexp.py:24–176`) [V], EIP-198 as amended by EIP-2565, EIP-7823 and EIP-7883.
1. `bl, el, ml` = the 32-byte big-endian words at offsets 0, 32, 64 (padded); each `> 1024`
   halts before charging (`:32–42`).
2. `head` = the first `min(32, el)` bytes of the exponent at offset `96 + bl`, as an integer of
   that many bytes, zero-padded past the end of input (`:44–48`).
3. Gas (`:143–176`): `max(500, complexity(bl, ml) · iterations(el, head))` where, with
   `L = max(bl, ml)` and `w = ⌈L/8⌉`, `complexity = 16` if `L ≤ 32` else `2·w²` (`:94–99`), and
   `iterations = max(1, c)` with `c = 0` if `el ≤ 32 ∧ head = 0`; `c = max(bitlen(head) − 1, 0)`
   if `el ≤ 32`; else `c = 16·(el − 32) + max(bitlen(head) − 1, 0)` (`:122–140`).
4. If `bl = 0 ∧ ml = 0`, output empty (`:56–58`). Otherwise read `base`, `exp`, `mod` (padded,
   `:60–66`); if `mod = 0`, output `ml` zero bytes (so empty when `ml = 0`) (`:68–69`); else
   output `base^exp mod mod` as exactly `ml` big-endian bytes (`:71–73`).

**BN254 codec** (`alt_bn128.py:40–137`) [V]. G1: 64 bytes, `x = [0:32]`, `y = [32:64]`
big-endian; `x ≥ q` or `y ≥ q` → `InvalidParameter`; `(0, 0)` ↦ infinity; off-curve →
`InvalidParameter`. **No G1 subgroup check** (cofactor 1). G2: 128 bytes in the order
`x_im, x_re, y_im, y_re` (`FQ2((x1, x0))`, `:124–125`); each `< q`; `(0,0,0,0)` ↦ infinity;
on-curve against the twist. Encoding of results: `x‖y`, 32 bytes each, of `toXY` (infinity ↦
64 zero bytes, `EthCurve` R2). In ECADD/ECMUL/ECPAIRING an `InvalidParameter` from decoding is
re-raised as `OutOfGasError` (`:159–160`, `:186–187`, `:225–226`) — still a halt.
- ECADD: decode `data[0:64]`, `data[64:128]` (padded), output `P + Q` (`:153–165`).
- ECMUL: decode `data[0:64]`; scalar `n = data[64:96]` (padded), **not reduced**; output `n·P`
  (`:181–193`).
- ECPAIRING: charge `34000·⌊len/192⌋ + 45000` *before* the length check (`:209–215`); then
  `len mod 192 ≠ 0` halts (`:218–219`); for each 192-byte chunk decode G1 (64) and G2 (128), halt
  if `r·P ≠ ∞` or `r·Q ≠ ∞` (`:227–230`; the G1 check never fails for on-curve points [I]);
  output 32-byte `1` iff the product of pairings is one (`EthPairing.Bn254.pairingCheck`), else
  `0`. Empty input: output `1`.

**BLAKE2F** (`blake2f.py:21–42`) [V]. `len ≠ 213` halts (`:32–33`). Parameters
(`crypto/blake2.py:133–150`, owned by `EthHash`): `rounds` = big-endian `u32` at `[0:4]`;
`h` = 8 little-endian `u64` at `[4:68]`; `m` = 16 at `[68:196]`; `t₀, t₁` at `[196:212]`;
`f = data[212]`. Charge `rounds` (`:38`), then `f ∉ {0, 1}` halts (`:39–40`); output the
64-byte F compression (`EthHash`).

**POINT_EVALUATION** (`point_evaluation.py:32–72`) [V]. `len ≠ 192` halts before charging
(`:44–45`). Fields: `vh = [0:32]`, `z = [32:64]`, `y = [64:96]`, `C = [96:144]`, `π = [144:192]`
(`:47–51`). Charge 50000 (`:54`). Halt unless `vh = 0x01 ‖ SHA-256(C)[1:32]`
(`kzg_commitment_to_versioned_hash`, `crypto/kzg.py:65–74`; `:55–56`). Call
`EthPairing.Kzg.verifyKzgProof C z y π`; **any** exception (`except Exception`, `:59–62`) or
`false` (`:64–65`) halts with `KZGProofError`. Output `U256(4096).to_be_bytes32() ‖
U256(BLS_MODULUS).to_be_bytes32()` (`:69–72`).

**EIP-2537 codec** (`bls12_381/__init__.py`) [V].
- `Fp` element: 64 bytes big-endian, value `< q` (implies 16 leading zero bytes) (`bytes_to_fq`,
  `:426–454`). `Fp2`: `c0 ‖ c1`, 64 bytes each (`bytes_to_fq2`, `:457–487`) — note the order is
  the reverse of BN254's.
- G1: `x ‖ y` (128 bytes); `(0, 0)` ↦ infinity; on-curve; subgroup check only when requested
  (`_bytes_to_g1_cached`, `:309–338`). G2: 256 bytes, `x ‖ y` as `Fp2`s (`:495–520`). The
  redundant `x ≥ field_modulus` tests at `:322–325` compare an `FQ` with an `int` and are always
  false after `bytes_to_fq` [V: evaluated]; the spec omits them.
- The `lru_cache` wrappers (`:308`, `:494`) are caches and **not semantic** (ARCHITECTURE §7).
- Encoding: `toXY` coordinates as 64-byte big-endian, infinity ↦ zeros (`g1_to_bytes`, `:372–391`;
  `fq2_to_bytes`, `g2_to_bytes`, `:554–591`).
- Scalar pairs: 160 bytes = G1 (with subgroup check) ‖ 32-byte scalar; 288 bytes = G2 (with
  subgroup check) ‖ 32-byte scalar; scalars unreduced (`decode_g1_scalar_pair`, `:394–423`;
  `decode_g2_scalar_pair`, `:594–622`).
- Discounts: `G1_K_DISCOUNT` (`:37`, 128 entries, 1000 … 519), `G2_K_DISCOUNT` (`:168`, 128
  entries, 1000 … 524), `G1_MAX_DISCOUNT = 519`, `G2_MAX_DISCOUNT = 524`, `MULTIPLIER = 1000`
  (`:299–301`) [V: lengths evaluated]. Index `k − 1` for `k ≤ 128`. These are pricing
  dependencies, so they are `GasCosts` fields (`blsG1KDiscount`, `blsG2KDiscount`,
  `blsG1MaxDiscount`, `blsG2MaxDiscount`, `blsMultiplier`; DECISIONS B8, F9) read from `cfg`; the
  Amsterdam values live in `EthFork`.

**EIP-2537 operations** (`bls12_381_g1.py`, `bls12_381_g2.py`, `bls12_381_pairing.py`) [V].
- G1ADD/G2ADD: exact length; decode two points **without** subgroup check; output the sum
  (`g1.py:42–70`, `g2.py:43–71`).
- G1MSM/G2MSM: `k = len / pairLength`; gas `⌊k · MUL · disc(k) / 1000⌋` (`g1.py:97–106`,
  `g2.py:98–107`); decode each pair with subgroup check; output `Σ mᵢ·Pᵢ` (`g1.py:109–121`).
  `k = 1` is the former G1MUL/G2MUL (EEST `bls12_g1mul`, `bls12_g2mul` target the MSM address).
- PAIRING: gas `32600·k + 37700` (literals in EELS, `pairing.py:45–47`; here the `GasCosts`
  fields `blsPairingPerPair` and `blsPairingBase`, B8, F9); per
  384-byte chunk, G1 (128) and G2 (256) decoded without the flag, then explicit subgroup checks
  (`:51–63`); output `0³¹‖01` iff the product of pairings is one, else `0³²` (`:67–70`).
- MAP_FP_TO_G1: `fp = data` as a 64-byte integer, `≥ q` halts (`g1.py:147–149`); output
  `EthCurve.Bls12381.clearCofactorG1 (mapToCurveG1 fp)` (`:151–152`).
- MAP_FP2_TO_G2: `bytes_to_fq2(data)` (twice; the duplicate call and the `assert isinstance` at
  `g2.py:148–151` are no-ops); output `clearCofactorG2 (mapToCurveG2 u)`.

**P256VERIFY** (`p256verify.py:31–90`) [V], EIP-7951. Charge 6900 **first** (`:44`); then
`len ≠ 160` → empty (`:46–47`). Read `h, r, s, qx, qy` (32 bytes each, `:50–59`). Empty unless
`0 < r < n`, `0 < s < n`, `qx < p`, `qy < p`, `(qx, qy) ≠ (0, 0)`, on curve (`:63–83`), and
`EthCurve.P256.verify` succeeds (`:85–88`). Output `0³¹‖01` (`:90`).

**R-total.** Every function is total on all byte inputs and all gas values; no Python exception
other than `ExceptionalHalt` is reachable from these files on EELS's own paths [I: checked by
reading for each file; residual risk is host-level, §10]. The failure ledger (maintained outside this repository)
holds the conservative superset of candidate sites: the
frame-exit consumer set is fully witnessed on the fixture corpus, and some static
sites remain unresolved.

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `forks/amsterdam/vm/precompiled_contracts/__init__.py::ECRECOVER_ADDRESS` | 38 | `ecrecoverAddress : Address` | `0x01` |
| `forks/amsterdam/vm/precompiled_contracts/__init__.py::SHA256_ADDRESS` | 39 | `sha256Address` | `0x02` |
| `forks/amsterdam/vm/precompiled_contracts/__init__.py::RIPEMD160_ADDRESS` | 40 | `ripemd160Address` | `0x03` |
| `forks/amsterdam/vm/precompiled_contracts/__init__.py::IDENTITY_ADDRESS` | 41 | `identityAddress` | `0x04` |
| `forks/amsterdam/vm/precompiled_contracts/__init__.py::MODEXP_ADDRESS` | 42 | `modexpAddress` | `0x05` |
| `forks/amsterdam/vm/precompiled_contracts/__init__.py::ALT_BN128_ADD_ADDRESS` | 43 | `altBn128AddAddress` | `0x06` |
| `forks/amsterdam/vm/precompiled_contracts/__init__.py::ALT_BN128_MUL_ADDRESS` | 44 | `altBn128MulAddress` | `0x07` |
| `forks/amsterdam/vm/precompiled_contracts/__init__.py::ALT_BN128_PAIRING_CHECK_ADDRESS` | 45 | `altBn128PairingCheckAddress` | `0x08` |
| `forks/amsterdam/vm/precompiled_contracts/__init__.py::BLAKE2F_ADDRESS` | 46 | `blake2fAddress` | `0x09` |
| `forks/amsterdam/vm/precompiled_contracts/__init__.py::POINT_EVALUATION_ADDRESS` | 47 | `pointEvaluationAddress` | `0x0a` |
| `forks/amsterdam/vm/precompiled_contracts/__init__.py::BLS12_G1_ADD_ADDRESS` | 48 | `bls12G1AddAddress` | `0x0b` |
| `forks/amsterdam/vm/precompiled_contracts/__init__.py::BLS12_G1_MSM_ADDRESS` | 49 | `bls12G1MsmAddress` | `0x0c` |
| `forks/amsterdam/vm/precompiled_contracts/__init__.py::BLS12_G2_ADD_ADDRESS` | 50 | `bls12G2AddAddress` | `0x0d` |
| `forks/amsterdam/vm/precompiled_contracts/__init__.py::BLS12_G2_MSM_ADDRESS` | 51 | `bls12G2MsmAddress` | `0x0e` |
| `forks/amsterdam/vm/precompiled_contracts/__init__.py::BLS12_PAIRING_ADDRESS` | 52 | `bls12PairingAddress` | `0x0f` |
| `forks/amsterdam/vm/precompiled_contracts/__init__.py::BLS12_MAP_FP_TO_G1_ADDRESS` | 53 | `bls12MapFpToG1Address` | `0x10` |
| `forks/amsterdam/vm/precompiled_contracts/__init__.py::BLS12_MAP_FP2_TO_G2_ADDRESS` | 54 | `bls12MapFp2ToG2Address` | `0x11` |
| `forks/amsterdam/vm/precompiled_contracts/__init__.py::P256VERIFY_ADDRESS` | 55 | `p256verifyAddress` | `0x100` |
| `forks/amsterdam/vm/precompiled_contracts/mapping.py::PRE_COMPILED_CONTRACTS` | 59 | `preCompiledContracts : List (Address × Precompile)`, `lookup`, `addresses` | installed by `EthFork` |
| `forks/amsterdam/vm/precompiled_contracts/ecrecover.py::ecrecover` | 26 | `ecrecover : Precompile` | |
| `forks/amsterdam/vm/precompiled_contracts/sha256.py::sha256` | 28 | `sha256 : Precompile` | hash from `EthHash` |
| `forks/amsterdam/vm/precompiled_contracts/ripemd160.py::ripemd160` | 29 | `ripemd160 : Precompile` | hash from `EthHash` |
| `forks/amsterdam/vm/precompiled_contracts/identity.py::identity` | 26 | `identity : Precompile` | |
| `forks/amsterdam/vm/precompiled_contracts/modexp.py::modexp` | 24 | `modexp : Precompile` | `EthField.powMod` |
| `forks/amsterdam/vm/precompiled_contracts/modexp.py::complexity` | 76 | `Modexp.complexity : Nat → Nat → Nat` | |
| `forks/amsterdam/vm/precompiled_contracts/modexp.py::iterations` | 102 | `Modexp.iterations : Nat → Nat → Nat` | |
| `forks/amsterdam/vm/precompiled_contracts/modexp.py::gas_cost` | 143 | `Modexp.gasCost : Nat → Nat → Nat → Nat → Nat` | |
| `forks/amsterdam/vm/precompiled_contracts/alt_bn128.py::bytes_to_g1` | 40 | `AltBn128.bytesToG1 : ByteArray → Except ExceptionalHalt Bn254.G1Proj` | |
| `forks/amsterdam/vm/precompiled_contracts/alt_bn128.py::bytes_to_g2` | 86 | `AltBn128.bytesToG2` | imaginary part first |
| `forks/amsterdam/vm/precompiled_contracts/alt_bn128.py::alt_bn128_add` | 140 | `altBn128Add : Precompile` | |
| `forks/amsterdam/vm/precompiled_contracts/alt_bn128.py::alt_bn128_mul` | 168 | `altBn128Mul : Precompile` | |
| `forks/amsterdam/vm/precompiled_contracts/alt_bn128.py::alt_bn128_pairing_check` | 196 | `altBn128PairingCheck : Precompile` | |
| `forks/amsterdam/vm/precompiled_contracts/blake2f.py::blake2f` | 21 | `blake2f : Precompile` | compression from `EthHash` |
| `forks/amsterdam/vm/precompiled_contracts/point_evaluation.py::FIELD_ELEMENTS_PER_BLOB` | 27 | `PointEvaluation.fieldElementsPerBlob = 4096` | |
| `forks/amsterdam/vm/precompiled_contracts/point_evaluation.py::BLS_MODULUS` | 28 | `PointEvaluation.blsModulus` | `#guard` = `EthField.Bls12381.r` |
| `forks/amsterdam/vm/precompiled_contracts/point_evaluation.py::VERSIONED_HASH_VERSION_KZG` | 29 | `PointEvaluation.versionedHashVersionKzg` | duplicate of the `crypto/kzg.py` constant |
| `forks/amsterdam/vm/precompiled_contracts/point_evaluation.py::point_evaluation` | 32 | `pointEvaluation : Precompile` | |
| `crypto/kzg.py::VersionedHash` | 48 | `Kzg.VersionedHash` (a `Bytes32`/`Hash32`) | here because it needs SHA-256 |
| `crypto/kzg.py::VERSIONED_HASH_VERSION_KZG` | 54 | `Kzg.versionedHashVersionKzg : UInt8 := 0x01` | |
| `crypto/kzg.py::kzg_commitment_to_versioned_hash` | 65 | `Kzg.commitmentToVersionedHash : ByteArray → Hash32` | `EthPairing` cannot see `EthHash` |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/__init__.py::G1_K_DISCOUNT` | 37 | field `GasCosts.blsG1KDiscount` | 128 entries; value in `EthFork` (B8) |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/__init__.py::G2_K_DISCOUNT` | 168 | field `GasCosts.blsG2KDiscount` | 128 entries; value in `EthFork` (B8) |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/__init__.py::G1_MAX_DISCOUNT` | 299 | field `GasCosts.blsG1MaxDiscount` (519) | value in `EthFork` (B8) |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/__init__.py::G2_MAX_DISCOUNT` | 300 | field `GasCosts.blsG2MaxDiscount` (524) | value in `EthFork` (B8) |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/__init__.py::MULTIPLIER` | 301 | field `GasCosts.blsMultiplier` (1000) | value in `EthFork` (B8) |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/__init__.py::_bytes_to_g1_cached` | 309 | folded into `Bls12.bytesToG1` | cache dropped (§7 of ARCHITECTURE) |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/__init__.py::bytes_to_g1` | 341 | `Bls12.bytesToG1 (subgroupCheck : Bool)` | |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/__init__.py::g1_to_bytes` | 372 | `Bls12.g1ToBytes` | |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/__init__.py::decode_g1_scalar_pair` | 394 | `Bls12.decodeG1ScalarPair` | subgroup-checked |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/__init__.py::bytes_to_fq` | 426 | `Bls12.bytesToFq` | |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/__init__.py::bytes_to_fq2` | 457 | `Bls12.bytesToFq2` | `c0` first |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/__init__.py::_bytes_to_g2_cached` | 495 | folded into `Bls12.bytesToG2` | cache dropped |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/__init__.py::bytes_to_g2` | 523 | `Bls12.bytesToG2 (subgroupCheck : Bool)` | |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/__init__.py::fq2_to_bytes` | 554 | `Bls12.fq2ToBytes` | |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/__init__.py::g2_to_bytes` | 573 | `Bls12.g2ToBytes` | |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/__init__.py::decode_g2_scalar_pair` | 594 | `Bls12.decodeG2ScalarPair` | |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_g1.py::LENGTH_PER_PAIR` | 39 | `Bls12.g1PairLength = 160` | |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_g1.py::bls12_g1_add` | 42 | `bls12G1Add : Precompile` | |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_g1.py::bls12_g1_msm` | 73 | `bls12G1Msm : Precompile` | |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_g1.py::bls12_map_fp_to_g1` | 124 | `bls12MapFpToG1 : Precompile` | |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_g2.py::LENGTH_PER_PAIR` | 40 | `Bls12.g2PairLength = 288` | |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_g2.py::bls12_g2_add` | 43 | `bls12G2Add : Precompile` | |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_g2.py::bls12_g2_msm` | 74 | `bls12G2Msm : Precompile` | |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_g2.py::bls12_map_fp2_to_g2` | 125 | `bls12MapFp2ToG2 : Precompile` | |
| `forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_pairing.py::bls12_pairing` | 25 | `bls12Pairing : Precompile` | |
| `forks/amsterdam/vm/precompiled_contracts/p256verify.py::p256verify` | 31 | `p256verify : Precompile` | |

**External semantics.** Specified here: `hashlib.sha256` and `hashlib.new("ripemd160")`
(delegated to `EthHash` functions with KATs; the host-OpenSSL dependence is a discrepancy
candidate, §10); `ethereum_types.numeric.{U256, Uint, ulen}` and `ethereum_types.bytes.{Bytes,
Bytes32, Bytes48}` conversions (via `EthBase`). The `py_ecc` names imported by these files
(`optimized_bn128.optimized_curve.*`, `optimized_bn128.optimized_pairing.pairing`,
`optimized_bls12_381.*`, `bls.hash_to_curve.*`, `py_ecc.typing.Optimized_Point3D`) are
specified in `EthField`, `EthCurve` and `EthPairing`; this library uses them only through those
libraries' public API.

## 4. Tests

- **EEST fixture areas** (`blockchain_tests`, from `STFSpec/informal/eest-fixture-index.txt`; the
  `blockchain_tests_engine` copies carry no guest records, GAPS-CROSSCUTTING X5):
  - `0x01`: `frontier/precompiles` (`ecrecover/*`), `ported_static/stPreCompiledContracts2`
    (`call[code]_ecrecover*`, `ecrecover_short_buff`);
  - `0x02`/`0x03`: `frontier/precompiles` (`ripemd/*`), `stPreCompiledContracts2`
    (`call[code]_sha256_*`, `call[code]_ripemd160_*`);
  - `0x04`: `frontier/identity_precompile`, `homestead/identity_precompile`;
  - `0x05`: `byzantium/eip198_modexp_precompile` (1 file), `osaka/eip7823_modexp_upper_bounds`
    (1), `osaka/eip7883_modexp_gas_increase` (12), `stPreCompiledContracts2` (`modexp_*`);
  - `0x06`–`0x08`: `byzantium/eip196_ec_add_mul` (6), `byzantium/eip197_ec_pairing` (11);
  - `0x09`: `istanbul/eip152_blake2` (5);
  - `0x0a`: `cancun/eip4844_blobs` (`point_evaluation_precompile/*`, `point_evaluation_precompile_gas/*`);
  - `0x0b`–`0x11`: `prague/eip2537_bls_12_381_precompiles` (52);
  - `0x100`: `osaka/eip7951_p256verify_precompiles` (12);
  - cross-cutting: `frontier/precompiles` (`precompiles`, `precompile_absence`,
    `precompile_as_coinbase`), `ported_static/stPreCompiledContracts` (`precomps_eip2929_cancun`,
    `sec80`), `byzantium/eip214_staticcall`, the call-family `ported_static` suites.
- **EELS unit tests:** none for precompiles at e1a316a0 (`tests/json_loader/` has only
  guest/state/codec tests) [V].
- **`core` `#guard` cases** (per precompile; a `#guard` evaluates only once every leaf it
  reaches is implemented, F16; the EEST source vectors are directly reusable:
  `tests/prague/eip2537_bls_12_381_precompiles/vectors/*.json`,
  `tests/cancun/eip4844_blobs/point_evaluation_vectors/go_kzg_4844_verify_kzg_proof.json`, and
  the Wycheproof data behind `eip7951`):
  - gas: every formula at its boundaries — `⌈n/32⌉` at `n = 0, 1, 32, 33`; MODEXP at `L = 32/33`,
    `el = 32/33`, `head = 0/1`, the 500 floor, lengths 1024/1025; MSM at `k = 1, 2, 128, 129`;
    ECPAIRING at `len = 191, 192, 193`;
  - padding: ECRECOVER/ECADD/ECMUL/MODEXP with short and over-long input;
  - edge: ECRECOVER `v = 27 + 2^8`, `r = n`, high `s`; MODEXP `bl = ml = 0`, `ml = 0 < bl`,
    `mod = 0`, `mod = 1`, `0^0`; BN254 `(0,0)` points, `P + (−P)`, scalar `2^256 − 1`; empty
    ECPAIRING; BLAKE2F `rounds = 0`, `f = 2`; POINT_EVALUATION wrong version byte, `z = r`;
    EIP-2537 infinity inputs, non-zero top padding bytes, `k = 1` MSM, all-infinity pairing;
    P256VERIFY length 159/161, `(0,0)` key, `qx = p`;
  - adversarial: on-curve but not-in-subgroup points for G1MSM/G2MSM/PAIRING/ECPAIRING G2 (must
    halt) and for G1ADD/G2ADD (must *succeed*: no subgroup check); `fail-*` EIP-2537 vectors.
- **Law tests:** the normal form of §2.1 checked on random inputs (outcome equals
  precheck-charge-compute); output-size laws of §7.
- **Differential checks (bug-finding, CONTRIBUTING §1):** each precompile against EELS itself
  (Python harness calling the functions with a stub `Evm`), and against evmone/revm precompile
  suites; disagreements are settled by fixtures or pinned EELS.

## 5. Interface

Public unless marked internal. Namespace `STFSpec.Precompiles`.

```lean
-- calling convention (GasMeter, ExceptionalHalt, bufferRead from EthVmCore)
-- Imported from EthVmCore; these are aliases, never new result/table declarations.
-- Everything below is generic in `{m} [Monad m] [KeccakQuery m]` (D5); only ECRECOVER queries.
abbrev Precompile (m : Type → Type) := PrecompileFn m

-- normal form (§2.1); every precompile has one. Only the body is monadic, so the meter is
-- fixed by `chargeGas` before it runs and `meter_law` holds for every `m`.
structure PrecompileSpec (m : Type → Type) where
  precheck : ByteArray → Option ExceptionalHalt        -- pre-charge failures
  gasCost  : ByteArray → Nat
  run      : ByteArray → m (Except ExceptionalHalt ByteArray)
def PrecompileSpec.toPrecompile : PrecompileSpec m → Precompile m

-- addresses and table
def ecrecoverAddress … p256verifyAddress : Address      -- 18 constants
def preCompiledContracts (cfg : VmConfig) : List (Address × Precompile m)
def lookup (cfg : VmConfig) : Address → Option (Precompile m)
def addresses : AddrSet                                  -- for pre-warming; equals the lookup domain
def table (cfg : VmConfig) : PrecompileTable m           -- closures capture costs; exact address set and meter law

-- the 18 precompiles
def ecrecover sha256 ripemd160 identity modexp altBn128Add altBn128Mul
    altBn128PairingCheck blake2f pointEvaluation bls12G1Add bls12G1Msm bls12G2Add
    bls12G2Msm bls12Pairing bls12MapFpToG1 bls12MapFp2ToG2 p256verify (cfg : VmConfig) : Precompile m
def ecrecoverSpec … p256verifySpec (cfg : VmConfig) : PrecompileSpec m   -- normal forms (public, for proofs)

namespace Modexp
def complexity (baseLength modulusLength : Nat) : Nat
def iterations (exponentLength exponentHead : Nat) : Nat
def gasCost (baseLength modulusLength exponentLength exponentHead : Nat) : Nat
end Modexp

namespace AltBn128                                      -- EIP-196/197 codec
def bytesToG1 : ByteArray → Except ExceptionalHalt Bn254.G1Proj
def bytesToG2 : ByteArray → Except ExceptionalHalt Bn254.G2Proj
def g1ToBytes : Bn254.G1Proj → ByteArray                -- internal
end AltBn128

namespace Bls12                                         -- EIP-2537 codec (pricing tables are GasCosts fields, B8)
def g1PairLength g2PairLength : Nat
def bytesToFq : ByteArray → Except ExceptionalHalt Bls12381.Fq
def bytesToFq2 : ByteArray → Except ExceptionalHalt Bls12381.Fq2
def bytesToG1 (data : ByteArray) (subgroupCheck : Bool := false) : Except ExceptionalHalt Bls12381.G1Proj
def bytesToG2 (data : ByteArray) (subgroupCheck : Bool := false) : Except ExceptionalHalt Bls12381.G2Proj
def g1ToBytes : Bls12381.G1Proj → ByteArray
def fq2ToBytes : Bls12381.Fq2 → ByteArray
def g2ToBytes : Bls12381.G2Proj → ByteArray
def decodeG1ScalarPair : ByteArray → Except ExceptionalHalt (Bls12381.G1Proj × Nat)
def decodeG2ScalarPair : ByteArray → Except ExceptionalHalt (Bls12381.G2Proj × Nat)
def msmGas (k mulCost : Nat) (table : Array Nat) (maxDiscount multiplier : Nat) : Nat   -- internal; arguments from cfg.costs
end Bls12

namespace PointEvaluation
def fieldElementsPerBlob blsModulus : Nat
def versionedHashVersionKzg : UInt8
end PointEvaluation

namespace Kzg
abbrev VersionedHash := Hash32
def versionedHashVersionKzg : UInt8
def commitmentToVersionedHash (commitment : ByteArray) : VersionedHash
end Kzg
```

`ExceptionalHalt` constructors used: `outOfGas`, `invalidParameter`, `kzgProofError` (owned by
`EthVmCore`). Gas constants (`PRECOMPILE_*`) are read from `EthVmCore`'s gas parameter record
(ARCHITECTURE §8). The EIP-2537 pairing literals (`bls12_381_pairing.py:46`), the MSM discount
tables, the maximum discounts and the multiplier are `GasCosts` fields too (DECISIONS B8, F9), with
their Amsterdam values in `EthFork`.

## 6. Data structures

| Type | Representation | Model | Invariant | Persistence | Complexity |
|---|---|---|---|---|---|
| `preCompiledContracts` | constant `List (Address × Precompile)`; `lookup` by `match` on the address (18 cases) | finite map `Address ⇀ Precompile` | keys distinct; equals the EELS dict | immutable constant, shared | `lookup` O(1) with a `match` on the low bytes after an "upper 18 bytes zero" test [I] |
| discount tables | `GasCosts` fields (`Array Nat`, 128 entries), read from `cfg` | `Fin 128 → Nat` | size 128, non-increasing [I: to check] | constant | O(1) index |
| call data | `ByteArray` slice from the frame (read-only) | byte list | — | shared read-only; never updated | `extract` O(len) per field |
| output | fresh `ByteArray` | byte list | size laws (§7) | linear, handed to the runner | O(size) |
| points, scalars | `EthCurve`/`EthField` values | as there | on-curve after decoding | immutable | as there |

No precompile keeps state across calls. The EELS `lru_cache` (maxsize 128) is omitted; if a
cache is ever added it must satisfy the memoisation-consistency invariant (ARCHITECTURE §7).

**Cost envelope** [I: analytical, unmeasured]. Gas is charged before heavy work, so the work per
call is bounded by forwarded gas, but the spec's per-gas cost is far from uniform: MODEXP up to
three 8192-bit operands; BLS12-381 MSM of `k` pairs, about `O(k·256/c + 2^c·256/c)` G1/G2 operations with Pippenger (`EthCurve` §6; naive would be `O(k·256)`) plus `k`
subgroup checks; pairings. These dominate guest runtime on precompile-heavy fixtures.

## 7. Contract and laws

Per operation:
- [C] **Frame law.** At `m := Id`: `p data g = .ok g' out → chargeGas g c = .ok g'` for the
  precompile's `c`; for general `m`, the same holds under `SatisfiesM`. Only `gas_left` changes
  (no state gas, refund or other field) [V: all files call only `charge_gas`]. This implies
  `EthVmCore`'s `meter_law`. Supports the runner's potential Φ (ARCHITECTURE §5.5): a precompile frame never
  increases Φ.
- [C] **Normal form.** `p = (pSpec).toPrecompile` up to the halt constructor, for every `p`.
  Proved per precompile against an EELS-shaped definition (check order as in EELS).
- [C] **Gas laws.** Closed forms of §2.2/§2.3, e.g. `sha256Gas n = 60 + 12 * ((n + 31) / 32)`;
  MODEXP: `gasCost ≥ 500`; MSM: `msmGas k = k * mul * disc k / 1000`. Do not claim MODEXP monotonicity in each length independently: changing `baseLength` moves the exponent-head window. Any monotonicity theorem must hold that head fixed and check the formula's boundary cases.
- [C] **Padding laws.** For ECRECOVER, ECADD, ECMUL, MODEXP: the result depends only on
  `data ++ zeros` (any number of zeros) truncated to the bytes read.
- [C] **Output-size laws** (for consumers such as evm-asm): ECRECOVER `∈ {0, 32}`; SHA256,
  RIPEMD160, ECPAIRING, BLS12_PAIRING `= 32`; IDENTITY `= len`; MODEXP `∈ {0, ml}`; ECADD, ECMUL,
  BLAKE2F, POINT_EVALUATION `= 64`; G1ADD, G1MSM, MAP_FP_TO_G1 `= 128`; G2ADD, G2MSM,
  MAP_FP2_TO_G2 `= 256`; P256VERIFY `∈ {0, 32}`.
- [C] **Codec laws.** `bytesToG1 (g1ToBytes P) = .ok P'` with `toAffine P' = toAffine P` for
  on-curve `P` (BN254 and EIP-2537); decoding rejects every `x ≥ q`; the all-zero encoding is the
  only encoding of infinity.
- [C] **Mathematical correctness (D12 (ii)),** stated on the Mathlib models: ECADD/G1ADD/G2ADD
  return the encoded group sum; ECMUL and MSMs return `Σ mᵢ • Pᵢ`; ECPAIRING/BLS12_PAIRING return 1
  iff `∏ e(Pᵢ, Qᵢ) = 1`; MAP_* return `h_eff • iso(sswu(u))`; MODEXP returns `b^e mod m` in `ml`
  bytes; ECRECOVER (at `m := Id`) returns `keccak(Q)[12:]` for the unique `Q` with `ECDSA.verify Q h (r, s)` and
  `R.y` parity `v − 27`; P256VERIFY returns 1 iff FIPS 186-5 verification holds;
  POINT_EVALUATION succeeds iff the versioned hash matches and the KZG check holds.
- [T] every precompile is total; loops are bounded by the input length or by `rounds`
  (structural), independent of gas.
- [R] ZisK/evm-asm bridge: evm-asm's software RIPEMD-160, SHA-256 wrapper and P-256 over
  `Arith256Mod` (per `ZiskAccel.lean:14–17`) must refine these functions.
- [S] (statements only, D12 (iii)): KZG binding (`EthPairing`), ECDSA unforgeability
  (`EthCurve`), SHA-256/RIPEMD-160 collision resistance where a consumer relies on it. None is
  needed for the guest's witness-soundness theorem.

**Derived laws** callers use: "a failing precompile call is an exceptional halt with empty
output and zero returned gas" (via the runner's halt law), and "a successful call returns
`gas − cost(data)`".

### Informal correctness argument

**Claim.** Every installed precompile has the same input acceptance, output bytes, gas charge and exceptional-halt behaviour as the pinned reference, and satisfies the shared meter contract.

**Premises.** Concrete hash/field/curve/pairing correspondence, exact gas constants and length rules, and a host-capability assumption for reference RIPEMD execution.

**Argument.** Split execution at each ordered input/length/field/subgroup check. For accepted inputs, adapter inverses transfer bytes to the mathematical inputs; the lower component's correctness gives the output, and the encoding law returns the same bytes. Mirror the reference's placement of gas charging relative to validation, since swapping them changes which exception wins. On success chargeGas changes only execution gas, hence the returned meter satisfies meter_law; on halt the runner performs ordinary halt settlement. ECRecover's accepted invalid signatures may return empty output rather than halt, and KZG/pairing require their distinct infinity/subgroup rules. Mapping precompiles apply clearCofactor exactly once to mapToCurve. MODEXP complexity/gas uses the reference exponent head at the offset determined by baseLength; varying that offset invalidates an unconditional monotonicity claim.

**Open obligations.** Complete adapter/error equations and exact pricing closures under VmConfig; pairings' algebraic proofs remain conditional. Tests of valid outputs do not establish rejection order or justify replacing a cryptographic algorithm by any function satisfying a weaker abstract property.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthVmCore`, `EthPairing`, `EthHash`
- **Used by:** `EthFork` (installs `preCompiledContracts` into the runner's table and exports
  the warm-address set). The runner (`EthVmRunner`) and instructions never import it (D17).
- **Seams consumed:** from `EthVmCore`: `GasMeter` with `chargeGas` and its law,
  `ExceptionalHalt` constructors (`vm/exceptions.py`), `bufferRead` and its padding law, the gas
  parameter record (`vm/gas.py:112–137`, plus the B8 pricing fields). From `EthHash`: `sha256`, `ripemd160`, the `KeccakQuery` class (ECRECOVER),
  and the BLAKE2 F compression with parameter extraction (`crypto/blake2.py`, including
  `Blake2b`'s `get_blake2_parameters` and `compress`). From `EthPairing`/`EthCurve`/`EthField`:
  everything mathematical, with their subgroup and predicate preconditions discharged here.
- **Seams provided:** the `Precompile` calling convention and the frame, normal-form and size
  laws. **Cross-module invariants:** the runner must treat `.halt` exactly like an opcode
  exceptional halt (O8), and must not call a precompile when precompiles are disabled for the
  frame (EIP-7702 delegation). The `EthVmCore` gas record must contain the `PRECOMPILE_*`
  constants and every other pricing dependency (B8); this library must not duplicate them.

## 9. Open decisions

- **D12** (accepted): all three deliverables; this file is (i), with (ii)/(iii) statements in §7.
- **D14** (accepted): precompile failures map to O8/O9 only. The frame-exit consumer set is
  fully witnessed on the fixture corpus (by running the pinned EELS over it); the unresolved static sites, and the host-level escapes of §10 (O12, DISC-001), remain.
- **D17**: precompiles reachable only through the table; `EthFork` owns installation.
- **D3**: Amsterdam only; the table is not fork-parameterised.
- **D4**: SHA-256/RIPEMD-160/BLAKE2 are `EthHash` references; their fast paths are D4's.
- **D5** (broad scope, monad-parametric): ECRECOVER's keccak of the public key goes through
  `KeccakQuery`, so every precompile is a `PrecompileFn m` and the meter law holds for every `m`
  (F3's pure form is not adopted). Execution uses `m := Id`.
- **D18** (accepted): MSM and pairings must use performance-appropriate executables (Pippenger-class MSM; Montgomery fields; easy/hard-part final exponentiation), with the naive or plain forms kept as legible references. Any exception is recorded in `STFSpec/informal/DEBT.md` with its justification.
- **D6**, **D7**, **D15**: via the crypto libraries.
- **D21** (accepted, 2026-09-28): no `@[csimp]` and no axiom-adding tactics (`native_decide`, `bv_decide`). A fast path is either a representation replacement proved against this module's contract (D25), or an executable definition with a legible reference beside it and an ordinary equality proof (`CONTRIBUTING.md` §4).
- Host-dependent RIPEMD-160: tracked as DISC-005 (DECISIONS Q19).
- NEW-CRYPTO-6 (precompile gas constants): resolved by DECISIONS B8 (Q43) and F9.
- **B13** (Q40–Q42): the pairing-as-predicate and recovery-basis decisions are scheduled, not
  settled; they fix `EthPairing`/`EthCurve` result types used here. The cofactor boundary has a
  working position (uncleared `mapToCurve*`, `mapFp*` wrappers clear exactly once; EthCurve R8).

## 10. Gaps

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Host-level escapes (O12).** A Python exception that is not an `ExceptionalHalt` inside a
  precompile — `RecursionError` from `py_ecc`'s recursive `multiply` at depth, `MemoryError`,
  or a missing RIPEMD-160 provider — escapes the frame and makes the block fail at the inner
  handler. None is shown reachable; none is excluded by proof. The guest-process recursion limit
  is 100,000 (py_ecc raises it; 12,288 applies only after `import ethereum` alone). See DISC-001
  and DISC-005.
- **Error-class observability** (§2.1) is inferred: that the exceptional-halt *class* never
  reaches the guest output needs confirmation from `EthVmRunner`/`EthBlock` (receipt status,
  `incorporate_child`, tracing only).
- **Thin or missing EEST coverage:** MODEXP has one `eip198` file and one `eip7823` file; no
  EIP-2565 area is present (its formula is superseded by EIP-7883, but boundary cases between the
  two are only in `eip7883`); the `ported_static/stZeroKnowledge` BN254
  suite exists in EEST sources but not in the zkevm corpus; `test_bls12_precompiles_before_fork`
  and `test_eip_mainnet` fixtures are absent; there is no ECRECOVER area beyond `frontier` and
  `stPreCompiledContracts2` [V: fixture index and file list].
- **`EthHash` must provide RIPEMD-160 and BLAKE2 F** with the EELS parameter extraction; `EthHash`
  owns RIPEMD-160 (its R4), although EELS calls `hashlib` directly in `ripemd160.py`.
- **Performance unmeasured.** No numbers exist for pure-Lean MODEXP at 8192 bits, BLS12-381 MSM
  at `k = 128`, or pairings; the cost envelope in §6 is analytical.
- **Mathematical-correctness proofs (ii)** inherit every gap of `EthCurveMathlib` and
  `EthPairingMathlib` (group orders, pairing bilinearity).
- **Discount-table monotonicity** and exact agreement with EIP-2537's published table are not
  checked (only lengths and endpoints were evaluated).
- **`disable_precompiles` semantics** (EIP-7702 delegation to a precompile address) belong to
  `EthVmRunner`; this spec assumes they are specified there.
- **Tracing** (`evm_trace(PrecompileStart…)`, `vm/interpreter.py:440–442`) is not semantic and
  is left to the diagnostic event interface (ARCHITECTURE §7).
