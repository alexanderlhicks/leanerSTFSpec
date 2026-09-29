# `EthCurve`: elliptic-curve groups, ECDSA, hash-to-curve maps and point codecs

*Status: informal specification, draft. Date: 2026-09-29. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: Montgomery backend results in `EthField` §6 and D6 · interface findings F16 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D6, D7, D12, D15, D18, D25, D26 · questions: B13/Q41, Q44, Q45.*

Tags: **[V]** verified by reading pinned source or running the pinned dependency (`esvenv`,
versions per `reference.toml`); **[I]** inference, not yet checked. Line numbers without a
path refer to `src/ethereum/crypto/elliptic_curve.py`; `py_ecc` paths are relative to
`site-packages/py_ecc/` (py-ecc 8.0.0).

## 1. Purpose

`EthCurve` defines the short-Weierstrass curve groups Ethereum uses (BN254 G1/G2, BLS12-381
G1/G2, secp256k1, P-256), their group law, scalar multiplication, subgroup checks and
multi-scalar multiplication (executable Pippenger with a small-input path; the naive fold as its reference); ECDSA public-key recovery on secp256k1 and verification on P-256;
the BLS12-381 SSWU maps with cofactor clearing (EIP-2537); and the BLS12-381 compressed-point
codec that KZG needs. It is layer L0 (ARCHITECTURE §2), above `EthField` and below `EthPairing`.
EVM byte encodings of *uncompressed* points (EIP-196/197/2537) are **not** here; they belong to
`EthPrecompiles`, which owns those EELS functions. Its contract is model-based (D25): an affine
model (in `EthCurveMathlib`, Mathlib's `WeierstrassCurve.Affine.Point`) with commuting equations
for every representation-level operation.

## 2. Requirements

**R1. Curve parameters** [V, py_ecc `optimized_bn128/optimized_curve.py:16–56`,
`optimized_bls12_381/optimized_curve.py`, `:17–23`, `:79–90`]:

| Curve | Field | Equation | Group order / subgroup |
|---|---|---|---|
| BN254 G1 | `Bn254.Fq` | `y² = x³ + 3` | `Bn254.r` (cofactor 1 [I]) |
| BN254 G2 | `Bn254.Fq2` | `y² = x³ + 3/(9 + i)` (py_ecc `b2 = FQ2([3,0]) / FQ2([9,1])`) | order-`r` subgroup of the twist |
| BLS12-381 G1 | `Bls12381.Fq` | `y² = x³ + 4` | `Bls12381.r`, cofactor `h₁` |
| BLS12-381 G2 | `Bls12381.Fq2` | `y² = x³ + 4(1 + i)` (`b2 = FQ2((4, 4))`) | `Bls12381.r`, cofactor `h₂` |
| secp256k1 | `Secp256k1.Fq` | `y² = x³ + 7` (`SECP256K1B`, `:17`) | `Secp256k1.n`, prime |
| P-256 | `P256.Fq` | `y² = x³ + a·x + b`, `a = p − 3`, `b` as `:88` | `P256.n`, prime |

Generators: BN254 G1 `(1, 2)`; BN254 and BLS12-381 generators as in `py_ecc`; secp256k1 and P-256
per SEC 2 (needed only inside ECDSA).

**R2. Projective representation and infinity** (D7). The reference formulas are `py_ecc`'s
homogeneous projective ones (`(X : Y : Z)`, affine `(X/Z, Y/Z)`, curve `Y²Z = X³ + aXZ² + bZ³` (a = 0 for the py_ecc BN/BLS instances))
[V: `optimized_curve.py:65–121`]. The point at infinity is *any* triple with `Z = 0`
(`is_inf`, `:60–61`); `py_ecc` produces `(1, 1, 0)` from `add(P, −P)` (`:110`), `(0, 0, 0)`
when EELS decodes the all-zero encoding (`alt_bn128.py:73–77`, `bls12_381/__init__.py:327–330`),
and `(·, ·, 0)` from doubling a 2-torsion point. `toAffine` must reproduce `normalize`
(`:146–150`) **including `inv0`**: infinity normalises to `(0, 0)` [V: evaluated]. EVM encoders
rely on this.

**R3. On-curve predicate.** `isOnCurve P = true` if `Z = 0`, else `Y²Z = X³ + aXZ² + bZ³` (a = 0 for these py_ecc instances)
(`optimized_curve.py:65–69`) [V]. For P-256 the affine check is the literal Python formula of
`is_on_curve_secp256r1` (`:134–169`), on `U256` inputs already known to be `< p`.

**R4. Group law.** `add`, `double`, `neg` must, on points satisfying R3, agree with the elliptic
curve group law under `toAffine` (R2's infinity convention). `py_ecc`'s `add` handles `P = Q`
(delegates to `double`) and `P = −Q` (returns infinity) explicitly (`:107–110`) [V]. P-256 has
`a ≠ 0`; `py_ecc`'s formulas assume `a = 0`, so P-256 needs separate (general-`a` or complete)
formulas; the EELS reference for P-256 arithmetic is OpenSSL inside `cryptography` [V: imports
`:5–9`].

**R5. Scalar multiplication.** `mulNat P n` must equal `n • P` in the group for every `n : Nat`,
without reducing `n` modulo the order: `py_ecc multiply` is recursive double-and-add on the
unreduced `n` (`:125–135`) [V]. EVM scalars are up to `2^256 − 1` (BN254 ECMUL,
`alt_bn128.py:188`; EIP-2537 MSM, `bls12_381/__init__.py:421`, `:620`). Because only affine
normalised results are observable, any algorithm equal on the model is admissible (windowed,
GLV, etc.).

**R6. Subgroup check.** `inSubgroup r P := isInfinity (mulNat P r)` (BLS12-381:
`bls12_381/__init__.py:335`, `:517`, `bls12_381_pairing.py:57`, `:62`; BN254: `alt_bn128.py:227–230`;
`py_ecc/bls/g2_primitives.py` `subgroup_check`) [V]. The infinity point passes. Faster checks
(endomorphism-based) are admissible only with a proof of equivalence on on-curve points.

**R7. MSM.** `msm [(P₀, m₀), …, (P_{k−1}, m_{k−1})] = Σ mᵢ • Pᵢ`, for `k ≥ 1`. EELS computes the
naive left fold `((m₀P₀) + m₁P₁) + …` (`bls12_381_g1.py:109–121`) [V]; the gas schedule's
discounts assume Pippenger-style algorithms (EELS docstring `:76–79`). Order of summation is not
observable.

**R8. SSWU map to G1/G2 (EIP-2537).** `mapFpToG1 u = clearCofactorG1 (isoMapG1 (sswuG1 u))`
with the 11-isogeny, and `mapFp2ToG2 u = clearCofactorG2 (isoMapG2 (sswuG2 u))` with the
3-isogeny, as RFC 9380 §6.6.3 and Appendix E [V: `py_ecc/bls/hash_to_curve.py:80–101`,
`:146–167`; `optimized_bls12_381/optimized_swu.py`]. Cofactor clearing is multiplication by
`h_eff`: `H_EFF_G1 = 0xd201000000010001` and the 636-bit `H_EFF_G2`
(`optimized_bls12_381/constants.py:311`, `:117`; `optimized_clear_cofactor.py`) [V]. Only
`map_to_curve` and `clear_cofactor` are used; there is no `hash_to_field` and no DST in the EVM
path. SSWU's exceptional case and the sign choice through `sgn0` (`optimized_swu.py:56`, `:110`)
are normative; EEST has `bls12_map_fp_to_g1/isogeny_kernel_values.json` for inputs whose image
hits the isogeny kernel [V: fixture name].

**R9. BLS12-381 compressed points (ZCash format), for KZG only.** `G1.decompress` on a 48-byte
big-endian integer `z` (`py_ecc/bls/point_compression.py:80–117`) [V]:
- `c_flag` (bit 383) must be 1;
- `b_flag` (bit 382) must equal "`z mod 2^381 = 0`"; if so, `a_flag` (bit 381) must be 0 and the
  result is infinity;
- otherwise `x = z mod 2^381` must be `< q`; `y = (x³ + 4)^((q+1)/4)` must square to `x³ + 4`;
  `y` is replaced by `q − y` unless `⌊2y/q⌋ = a_flag` (the lexicographically larger root has
  `a_flag = 1`).

`keyValidate b` (`py_ecc/bls/ciphersuites.py:113–125`) succeeds iff decompression succeeds, the
point is not infinity, and it is in the subgroup [V]. A consequence: `x = 0` with `b_flag = 0`
is rejected by the flag rule although `(0, ±2)` is on `E(Fq)`; such points have order 3 and
would fail the subgroup check anyway [I], so the ZCash-spec and `py_ecc` readings agree on every
input. `G2.decompress` (96 bytes, `decompress_G2`) is needed only to decode the fixed trusted-setup
constant (`EthPairing`), so it may be replaced by a checked constant.

**R10. `secp256k1Recover r s v msgHash`** (`:26–76`) must return the 64-byte `X‖Y` of the
recovered key, or `SignatureError`, exactly as EELS + `spec256k1` 0.2.3:
1. reject if `(r³ + 7)^((p−1)/2) mod p ≠ 1`, computed on `U256` with Python `pow` (`:47–56`);
2. build `r‖s‖v` (65 bytes, `:58–64`); `v > 255` raises an *uncaught* `ValueError` at `:64`, but
   every caller passes `v ∈ {0, 1}` (`ecrecover.py:49–57`, `transactions.py:944–1004`,
   `vm/eoa_delegation.py:137–155`) [V], so the spec takes `v : Bool`;
3. `spec256k1` (Rust `secp256k1` 0.30.0 over `secp256k1-sys` 0.10.1, i.e. libsecp256k1, per the
   wheel SBOM [V]) recovers `Q = r⁻¹(s·R − e·G)` with `R = (r, y)`, `y` of parity `v`,
   `e = msgHash mod n`. Observed [V, empirical]: `r = 0`, `s = 0`, `r ≥ n`, `s ≥ n` → error
   ("malformed signature"); high `s` accepted (recovers the same key with flipped parity); `v = 2, 3`
   → error for ordinary `r`; recovery id `≥ 4` → error; a non-32-byte message → error. Not
   observed but required: `Q = ∞` → error (EELS comment `:66–68`) [I: libsecp256k1 source not
   read];
4. `ValueError` from `spec256k1` becomes `InvalidSignatureError` (`:69–74`).

Callers enforce `0 < r < n`, `0 < s < n` (and `s ≤ n/2` for transactions and authorizations),
so on the reachable domain R10 is SEC 1 v2 §4.1.6 with recovery id `v`. Low-`s` is **not**
checked here (ecrecover accepts high `s`).

**R11. `secp256r1Verify r s x y msgHash`** (`:93–131`) must succeed iff FIPS 186-5 ECDSA
verification with the pre-hashed 32-byte digest succeeds: `e = msgHash` as an integer (no
truncation: `n` has 256 bits), `w = s⁻¹ mod n`, `R = (e·w)·G + (r·w)·Q`, reject `R = ∞`, accept iff
`R.x mod n = r` [I: OpenSSL behaviour via `cryptography` 45.0.7, not read; the "mod n" comparison
is exercised by `osaka/eip7951_p256verify_precompiles/p256verify/modular_comparison.json`]. The
DER encoding of `(r, s)` by `pycryptodome` `DerSequence` (`:123`) and key construction
(`:125–126`) are transport only. `EllipticCurvePublicNumbers.public_key` raises `ValueError` for
off-curve points *outside* the `try` (`:125–131`) [I]; `p256verify` prechecks the range, the
point at infinity and the curve equation (`p256verify.py:63–83`) [V], so that path is unreachable
from EELS.

**R12. Totality.** Every function is total; no `partial`, no panicking `get!`, no FFI.
Scalar multiplication and cofactor clearing recurse structurally on the scalar's bits.

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `crypto/elliptic_curve.py::SECP256K1B` | 17 | `Secp256k1.b : Secp256k1.Fq := 7` | |
| `crypto/elliptic_curve.py::SECP256K1P` | 18 | `Secp256k1.p` (in `EthField`, re-exported) | modulus lives in `EthField` |
| `crypto/elliptic_curve.py::SECP256K1N` | 21 | `Secp256k1.n` (re-exported) | used by ecrecover and tx checks |
| `crypto/elliptic_curve.py::secp256k1_recover` | 26 | `Secp256k1.recover : U256 → U256 → Bool → Hash32 → Except SignatureError Bytes64` | R10; `v : Bool` by caller precondition |
| `crypto/elliptic_curve.py::SECP256R1N` | 79 | `P256.n` (re-exported) | |
| `crypto/elliptic_curve.py::SECP256R1P` | 82 | `P256.p` (re-exported) | |
| `crypto/elliptic_curve.py::SECP256R1A` | 85 | `P256.a : P256.Fq` | `= p − 3` |
| `crypto/elliptic_curve.py::SECP256R1B` | 88 | `P256.b : P256.Fq` | |
| `crypto/elliptic_curve.py::secp256r1_verify` | 93 | `P256.verify : U256 → U256 → U256 → U256 → Hash32 → Except SignatureError Unit` | R11 |
| `crypto/elliptic_curve.py::is_on_curve_secp256r1` | 134 | `P256.isOnCurve : U256 → U256 → Bool` | R3 |
| `crypto/kzg.py::FQ` | 22 | `Bls12381.G1Proj` | EELS names a *point* type `FQ` (a triple of `FQ`) |
| `crypto/kzg.py::FQ2` | 25 | `Bls12381.G2Proj` | likewise |

**External semantics** to specify as total Lean definitions:
- `py_ecc.optimized_bn128.optimized_curve.{add, multiply, normalize, is_inf, is_on_curve, b, b2,
  curve_order}` and `py_ecc.typing.Optimized_Point3D` (R2–R6);
- `py_ecc.optimized_bls12_381.optimized_curve.{add, multiply, normalize, is_inf, is_on_curve,
  b, b2, curve_order, G1, G2}`, `py_ecc.optimized_bls12_381.{add, multiply, neg, is_inf,
  curve_order}` (R2–R7);
- `py_ecc.bls.hash_to_curve.{map_to_curve_G1, map_to_curve_G2, clear_cofactor_G1,
  clear_cofactor_G2}` (R8);
- `py_ecc.bls.g2_primitives.{pubkey_to_G1, signature_to_G2}` and `py_ecc.bls.G2ProofOfPossession`
  (`KeyValidate` only) (R9); `eth_typing.bls.BLSPubkey`/`BLSSignature` are byte aliases;
- `spec256k1` (R10), specified mathematically, with the empirical edge cases as `#guard`s;
- `cryptography.hazmat.primitives.asymmetric.ec`, `.hashes`, `.asymmetric.utils.Prehashed`,
  `cryptography.hazmat.backends.default_backend`, `cryptography.exceptions.InvalidSignature` and
  `Crypto.Util.asn1.DerSequence` (R11), specified by FIPS 186-5 on the reachable domain.

## 4. Tests

- **EEST fixture areas:** `byzantium/eip196_ec_add_mul` (6 files), `byzantium/eip197_ec_pairing`
  (11, including `ecpairing_fuzzed/invalid_g2_subgroup.json`), `prague/eip2537_bls_12_381_precompiles`
  (52, including `bls12_map_fp_to_g1/isogeny_kernel_values.json`, `bls12_pairing/*multi_inf*`),
  `cancun/eip4844_blobs` (`point_evaluation_precompile/*`: commitment/proof decompression),
  `osaka/eip7951_p256verify_precompiles` (12, including three Wycheproof files and
  `modular_comparison.json`), `frontier/precompiles/ecrecover`, `ported_static/stPreCompiledContracts2`
  (`*ecrecover*`), and every block with signed transactions or EIP-7702 authorizations
  (secp256k1 recovery through O5/O7). `blockchain_tests` only: it holds all 29,030 guest records, and `blockchain_tests_engine` has none (GAPS-CROSSCUTTING X5).
- **EELS unit tests:** none for `crypto/` at e1a316a0 [V].
- **`core` `#guard` cases** (F16: a `#guard` or `decide` cannot evaluate a term that reaches a `sorry` leaf, so each guard runs only once the operations it reaches are implemented):
  - typical: generators on curve; `r • G = ∞` for BN254 G1/G2 and BLS12-381 G1/G2; `G + 2G = 3G`
    (ZisK KATs, `ZiskAccel.lean:458`, `:516`); secp256k1 recovery of a key signed with a fixed
    secret (a vector generated in the pinned Python environment); Wycheproof P-256 valid vectors;
  - edge: `toAffine ∞ = (0, 0)` for every representative `(1,1,0)`, `(0,0,0)`, `(x,y,0)`;
    `add P (neg P)`, `add P P = double P`; `mulNat P 0`, `mulNat P r`, `mulNat P (2^256 − 1)`;
    MSM with all-zero scalars and with repeated points; `decompress` of `0xc0‖0⁴⁷` (infinity),
    of `0xe0‖…` (infinity with `a_flag`, rejected), of `x = q` (rejected), of `0x80‖0⁴⁷`
    (rejected by the flag rule); recovery with high `s`, `v` flipped;
  - adversarial: on-curve points outside the subgroup (BLS12-381 G1 and G2, BN254 G2; points
    from `invalid_g2_subgroup.json` and EIP-2537 `fail-*` vectors); SSWU exceptional inputs
    (`u = 0`, isogeny kernel values); P-256 `R.x ≥ n` cases (`modular_comparison.json`).
- **Differential checks (bug-finding):** against `py_ecc` for every operation on random valid
  and invalid points; against cryptography-specs `Bls/G1.lean`/`G2.lean` (Jacobian) and
  `Bls/HashToCurve.lean` (G2 only); against `spec256k1`/libsecp256k1 and `cryptography`/OpenSSL
  through a Python harness; against ZisK `curveAdd`/`curveDbl` (`ZiskAccel.lean:413–432`).

## 5. Interface

Public unless marked internal. Namespaces `STFSpec.Curve.*`.

```lean
-- generic short-Weierstrass data
structure Weierstrass (F : Type) where a b : F
inductive Affine (F : Type) where                       -- public model
  | infinity
  | point (x y : F)

structure Proj (F : Type) where                          -- homogeneous projective; D7
  x y z : F
namespace Proj
def infinity : Proj F                                    -- (1, 1, 0) as py_ecc
def isInfinity : Proj F → Bool                           -- z = 0
def isOnCurve (W : Weierstrass F) : Proj F → Bool        -- R3
def ofAffine : Affine F → Proj F
def toAffine : Proj F → Affine F                         -- R2 model map
def toXY : Proj F → F × F                                -- py_ecc normalize, inv0: ∞ ↦ (0,0)
def neg : Proj F → Proj F
def double (W) : Proj F → Proj F
def add (W) : Proj F → Proj F → Proj F
def mulNat (W) : Proj F → Nat → Proj F                   -- R5, structural on bits
def inSubgroup (W) (order : Nat) (P : Proj F) : Bool     -- R6
def msmReference (W) : List (Proj F × Nat) → Proj F      -- legible reference: Σ mᵢ • Pᵢ, any Nat scalars
-- executable: EIP-2537 scalars are exactly 256 bits (32 bytes, unreduced); the bounded type makes
-- dropping high bits impossible. Window width c ≥ 1; ⌈256 / c⌉ windows, the last one partial.
def msm (W) (c : Nat) (hc : 1 ≤ c) : List (Proj F × BitVec 256) → Proj F   -- R7 (k ≥ 1 enforced by caller)
def msmWindow (k : Nat) : {c : Nat // 1 ≤ c}              -- the chosen window width for k pairs (tuned)
def eqv : Proj F → Proj F → Bool                         -- projective equality (internal)
end Proj

-- instances
def Bn254.g1Curve : Weierstrass Bn254.Fq                 -- a = 0, b = 3
def Bn254.g2Curve : Weierstrass Bn254.Fq2                -- b = 3/(9+i)
def Bls12381.g1Curve : Weierstrass Bls12381.Fq           -- b = 4
def Bls12381.g2Curve : Weierstrass Bls12381.Fq2          -- b = 4(1+i)
abbrev Bn254.G1Proj := Proj Bn254.Fq
abbrev Bn254.G2Proj := Proj Bn254.Fq2
abbrev Bls12381.G1Proj := Proj Bls12381.Fq               -- EELS crypto/kzg.py `FQ`
abbrev Bls12381.G2Proj := Proj Bls12381.Fq2              -- EELS crypto/kzg.py `FQ2`
def Bn254.g1Gen Bn254.g2Gen Bls12381.g1Gen Bls12381.g2Gen : …

-- BLS12-381 hash-to-curve pieces (EIP-2537)
def Bls12381.sswuG1 : Bls12381.Fq → Proj Bls12381.Fq           -- on the 11-isogenous curve (internal)
def Bls12381.isoMapG1 : Proj Bls12381.Fq → Bls12381.G1Proj      -- internal
def Bls12381.mapToCurveG1 (u : Bls12381.Fq) : Bls12381.G1Proj
def Bls12381.clearCofactorG1 (P : Bls12381.G1Proj) : Bls12381.G1Proj   -- mulNat P hEffG1
def Bls12381.mapToCurveG2 (u : Bls12381.Fq2) : Bls12381.G2Proj
-- mapToCurveG1/G2 = isoMap(sswu(u)), WITHOUT cofactor clearing (py_ecc naming).
def Bls12381.mapFpToG1 (u : Bls12381.Fq) : Bls12381.G1Proj  -- clearCofactorG1 (mapToCurveG1 u)
def Bls12381.mapFp2ToG2 (u : Bls12381.Fq2) : Bls12381.G2Proj -- clearCofactorG2 (mapToCurveG2 u)
def Bls12381.clearCofactorG2 (P : Bls12381.G2Proj) : Bls12381.G2Proj
def Bls12381.hEffG1 Bls12381.hEffG2 : Nat

-- BLS12-381 ZCash compressed codec (R9)
inductive CompressError | noCFlag | badInfinity | xNotCanonical | notOnCurve
def Bls12381.G1.decompress : ByteArray → Except CompressError Bls12381.G1Proj  -- 48 bytes
def Bls12381.G2.decompress : ByteArray → Except CompressError Bls12381.G2Proj  -- 96 bytes
def Bls12381.G1.keyValidate (b : ByteArray) : Bool                             -- R9

-- ECDSA
inductive SignatureError | notOnCurve | malformed | recoveredInfinity | invalid
def Secp256k1.b : Secp256k1.Fq
def Secp256k1.recover (r s : U256) (v : Bool) (msgHash : Hash32)
    : Except SignatureError Bytes64                      -- X‖Y (R10)
def P256.a P256.b : P256.Fq
def P256.curve : Weierstrass P256.Fq
def P256.isOnCurve (x y : U256) : Bool                   -- R3, literal formula
def P256.verify (r s x y : U256) (msgHash : Hash32) : Except SignatureError Unit  -- R11
```

`SignatureError` is local because `ethereum/exceptions.py` (`InvalidSignatureError`) belongs to
`EthBlock`/`EthFork`; callers map it. Recovery returns EthBase.Bytes64. Compressed codecs accept ByteArray and validate their exact size; fixed output widths use the D2 types.

## 6. Data structures

| Type | Representation | Model | Abstraction | Invariant | Persistence | Complexity |
|---|---|---|---|---|---|---|
| `Proj F` | three field elements, homogeneous (`py_ecc`) | `Affine F` restricted to curve points; Mathlib `W.Point` | `toAffine` (`z = 0 ↦ infinity`, else `(x/z, y/z)`) | `z = 0 ∨ isOnCurve` | immutable value | `add` ≈ 12M + 2S, `double` ≈ 7M + 5S (py_ecc formulas) [I]; one `inv0` per `toAffine` |
| `Affine F` | inductive | itself | identity | on curve | immutable | — |
| scalar mult. | recursion on bits of `n` | `n • P` | — | — | — | `O(log n)` group ops; subgroup check ≈ 255 doublings |
| MSM | **executable:** dispatch on `k`. Below a small threshold (to be measured; the EIP-2537 discount table starts at no discount for `k = 1`), sum independent double-and-add scalar multiplications. Otherwise **Pippenger's bucket method**: split each 256-bit scalar (EIP-2537 scalars are *not* reduced mod `r`) into windows of `c` bits, `c ≈ ⌊log₂ k⌋` (tuned by measurement), accumulate points into `2^c − 1` buckets per window, combine each window by a running sum, then combine windows by `c` doublings. *Reference:* the list fold `Σ mᵢ • Pᵢ` | `Σ mᵢ • Pᵢ` | executable = reference (refinement obligation [F]: for **every admissible window width `c ≥ 1`** and every list of 256-bit scalars, `msm c hc xs = msmReference (xs.map (·.toNat))`; this covers the final partial window of `256 − c·(⌈256/c⌉ − 1)` bits and the small-input path) | `k ≥ 1` | — | Pippenger `O(k · 256 / c + 2^c · 256 / c)` group ops; naive `O(k · 256)`. EIP-2537's gas schedule states MSMs "must be performed by Pippenger's algorithm to have a speedup that results in a discount over naive implementation" ([EIP-2537](https://eips.ethereum.org/EIPS/eip-2537#gas-schedule)) |
| compressed bytes | `ByteArray` (48/96) | curve point or error | `decompress` | size | immutable | one `sqrt` |

The initial choice follows `py_ecc` so that differential debugging can compare intermediate
triples (D7 "projective internally"). cryptography-specs uses Jacobian coordinates
(`Bls/G1.lean:23–25`) [V], and Mathlib has both `Projective` and `Jacobian` point types with
`AddCommGroup` instances (`AlgebraicGeometry/EllipticCurve/Projective/Point.lean:572`,
`Jacobian/Point.lean:588`) [V: Mathlib at CompPoly's pin v4.34.0]. Switching coordinates is a
representation replacement: only `toAffine`-commuting equations are re-proved.

## 7. Contract and laws

Per operation (commuting equations, under the invariant; stated for every curve instance):
- [C] `isOnCurve P ↔ toAffine P ∈ W` (with `∞` always on the curve).
- [C] `toAffine (neg P) = −toAffine P`; `toAffine (double P) = 2 • toAffine P`;
  `toAffine (add P Q) = toAffine P + toAffine Q`; invariant preserved by all three (cf.
  cryptography-specs `Proofs/Bls/G1Group.lean` `toPoint_add`, `valid_add` for Jacobian G1 [V]).
- [C] `toAffine (mulNat P n) = n • toAffine P`; `toAffine (msm l) = Σ (m • toAffine P)`.
- [C] `inSubgroup r P ↔ r • toAffine P = 0`; with `r` prime, `↔ toAffine P ∈ ⟨G⟩` given `#E = h·r`
  and `r ∤ h` [I: needs group orders].
- [C] `toXY P = (0, 0)` iff `P` is infinity, for BN254 and BLS12-381 (because `(0, 0)` is not on
  those curves) — needed by the EVM decoders' "all-zero means infinity" rule.
- [C] `mapToCurveG1 u` is on `E` and `clearCofactorG1` maps `E(Fq)` into G1; same for G2.
- [C] `decompress (compress P) = .ok P'` with `toAffine P' = toAffine P` for valid `P`; projective representatives need not be equal. `decompress` is total (cryptography-specs has
  `uncompress_compress` for G1 [V]).
- [C] `recover r s v e = .ok Q → ECDSA.verify (decodePublicKey Q) e r s` and the parity of the recovered `R.y` is `v`. Completeness requires a recovery-compatible signature: nonzero in-range `r,s`, a nonzero signing nonce, and the ephemeral point's `x = r < n`, since a Bool recovery id cannot select the `x = r + n` branch. Honest signing alone is insufficient for this converse.
- [C] `P256.verify r s x y e = .ok () ↔ FIPS186.verify (x, y) e (r, s)` on inputs that pass the
  `p256verify` prechecks.
- [T] all functions total (bit recursion; fixed isogeny degrees).
- [R] ZisK bridge: for affine inputs with `x₁ ≠ x₂`, `toXY (add P Q) = curveAdd q x₁ y₁ x₂ y₂`;
  for `y ≠ 0`, `toXY (double P) = curveDbl q x y` (`ZiskAccel.lean:413`, `:420`), for secp256k1,
  BN254 and BLS12-381 G1.
- [S] (statements only, in `EthCurveMathlib`/`EthSecurity`): ECDSA existential unforgeability for
  secp256k1 and P-256 is an *assumption*; the spec proves nothing about it.

**Derived laws** used by `EthPairing` and `EthPrecompiles`: the group structure on the model,
`n • P = (n mod r) • P` on the order-`r` subgroup, and "decode, operate, encode" results are
representation-independent.

### Informal correctness argument

**Claim.** On valid inputs, point operations refine the affine group model, and external encodings, maps and ECDSA operations reproduce their specified observations and rejection cases.

**Premises.** EthField laws, nonsingularity, the exact curve/twist parameters and subgroup facts, and the recovery-compatible signature domain where recovery completeness is claimed.

**Argument.** For homogeneous coordinates the equation is Y²Z = X³ + aXZ² + bZ³. Split addition into infinity, inverse, doubling and ordinary cases; after normalisation each formula gives the corresponding affine result. Bit induction lifts addition correspondence to scalar multiplication. Equality and decompression compare affine points, not raw projective coordinates. Compressed decoding checks flags, canonical x, the square root and sign in reference order, with a separate infinity case. SSWU and the isogeny require their exact constants and sign choice; cofactor clearing then establishes subgroup membership. The mapToCurve functions intentionally stop before clearing; the EVM wrappers clear exactly once. ECDSA verification follows the standard scalar equation. Boolean recovery parity selects x = r and therefore does not prove completeness for signatures needing x = r + n.

**Open obligations.** Formula identities, subgroup orders, SSWU sign/exception cases and compiled dependency error behaviour remain obligations. An on-curve/subgroup result alone does not prove the byte-exact mapping required by EIP-2537.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthField`
- **Used by:** `EthPairing`; `EthPrecompiles` (transitively, for ECRECOVER, ECADD/ECMUL,
  EIP-2537 and P256VERIFY); `EthCurveMathlib`. **Also needed by** transaction sender recovery
  (`transactions.py:907–912`, O5 public-key check `:916–934`) and EIP-7702 authority recovery
  (`vm/eoa_delegation.py:155`), through the applied D26 dependency: `EthVmRunner` imports `EthCurve` directly, and `EthBlock` reaches it transitively (D26, accepted 2026-09-28).
- **Seams.** Consumes `EthField` laws only (never limbs). Guarantees invariant preservation for inputs satisfying the stated validity premises, and that ECDSA functions are total on all `U256` inputs.

## 9. Open decisions

- **D7** (curve coordinates): homogeneous projective, following `py_ecc`, is the initial choice;
  Jacobian (cryptography-specs, EFD) is a representation replacement. Needs the pairing/MSM
  benchmarks named in D7.
- **D15**: cryptography-specs supplies Lean BLS12-381 G1/G2 and G2 hash-to-curve, but no G1 SSWU
  (11-isogeny), no BN254, no secp256k1/P-256; its toolchain is v4.29.1 [V].
- **D6** (provisional): fast fields for scalar multiplication. The width is settled (carry-preserving
  `Wide8`/`W12`, `EthField` §6; DECISIONS Q39). A Montgomery backend prototype measured `Wide8` at about 20–35×
  slower than native ecrecover, and located the remaining gap here, in curve-level algorithms:
  Shamir/Straus for `u₁G + u₂R`, wNAF with a precomputed `G` table, GLV for secp256k1
  (`EthField` §6).
- **D12**: all three deliverables — executable (this spec), correctness (`EthCurveMathlib`),
  security (ECDSA assumptions stated in `EthCurveMathlib`/`EthSecurity`).
- **D18** (accepted): EIP-2537's MSM gas discount assumes a Pippenger-class algorithm, so naive
  MSM (k independent scalar multiplications) is **not performance-appropriate** by default. It is
  allowed only with a recorded D18 justification, using the `k = 128` pair case as the reproducer.
  The preferred executable is Pippenger, with naive MSM as the legible reference and an equality
  proof.
- Reuse conditions for cryptography-specs (NEW-CRYPTO-8): DECISIONS Q45, with D15.
- secp256k1 recovery for `EthBlock` and the EIP-7702 authority check (NEW-CRYPTO-1): resolved by
  D26 (accepted), DECISIONS Q38.
- **Open: specification basis for third-party signature libraries** (NEW-CRYPTO-4, DECISIONS B13/Q41):
  scheduled, not settled. A compiled prototype of the interfaces kept `secp256k1Recover` as a leaf, so it did not
  decide the recovery/verification basis.

## 10. Gaps

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **API alignment** (§8): the dependency now reaches `EthCurve`; recovery uses `Bool` parity and `Bytes64`, with explicit conversions in the block and runner adapters.
- **libsecp256k1 and OpenSSL not read.** R10's "infinity result → error" and "e reduced mod n",
  and all of R11's verification steps, are inferred from standards and a handful of empirical
  probes, not from the pinned binaries' sources. `spec256k1` ships only a compiled `.so`.
- **P-256 group law** needs `a ≠ 0` formulas that `py_ecc` does not provide; nothing is chosen.
- **Group orders unproved.** Cofactor-1 for BN254 G1 and secp256k1/P-256, `#E(Fq) = h₁·r` and
  the G2 twist orders for BLS12-381 are standard facts with no Lean proof and **no known proof
  strategy** in Mathlib (no point-counting or CM machinery). `r • G = ∞` for generators is
  checkable by computation (cryptography-specs `Proofs/Bls/G1Order.lean` does it for BLS12-381 G1
  [V]).
- **SSWU and isogeny constants** (11-isogeny for G1, 3-isogeny for G2) are not yet transcribed;
  cryptography-specs has only the G2 3-isogeny (`Bls/HashToCurve.lean:139–206`) [V].
- **`h_eff` cofactor clearing vs. RFC 9380's `clear_cofactor_bls12381_g2` (ψ-based)**: EELS/py_ecc
  use plain multiplication by `h_eff`; cryptography-specs uses the ψ endomorphism (`HashToCurve.lean:224–245`)
  [V]. They should agree on `E'(Fq2)` [I: RFC 9380 states `h_eff` multiplication is equivalent];
  unproved.
- **`Fp2` square-root choice** for `G2.decompress` is unspecified beyond `py_ecc`; only the trusted
  setup constant uses it.
- **Recursion-depth host limits (O12):** `py_ecc` `multiply` recurses once per scalar bit (636 for
  `H_EFF_G2`) inside an EVM call stack. The guest-process recursion limit is **100,000**, because
  `py_ecc/__init__.py:13` raises it (`ethereum/__init__.py:29–30` alone sets 12,288) [V; also observed by running the pinned EELS guest]. Whether any reachable call depth can turn this into `RecursionError` (which is not an
  `ExceptionalHalt` and would escape to the block-level handler) is unverified; see
  `STFSpec/informal/DISCREPANCIES.md` DISC-001.
- **EEST coverage is thin** for ECRECOVER edge cases (only `frontier/precompiles` and
  `stPreCompiledContracts2`), and `ported_static/stZeroKnowledge` (BN254) exists in the EEST sources
  but is **absent** from the zkevm fixture corpus [V: fixture index vs. `tests/ported_static/`].
- **ECDSA security statements** have no owner beyond "stated as assumptions"; VCV-io has no
  ECDSA/EC definitions [V: a case-insensitive grep of VCV-io at `f5119c6` finds no secp256k1, ECDSA or Weierstrass curves].
