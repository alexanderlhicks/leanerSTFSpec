# `EthField`: prime fields, extension towers and modular arithmetic

*Status: informal specification, draft. Date: 2026-09-29. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: Montgomery backend results in §6 and D6 · gate: [REVIEW §3](../REVIEW.md) · decisions: D6, D15, D18, D21, D25, D26 · questions: Q39, Q45.*

Tags used below: **[V]** verified by reading the pinned source or running the pinned dependency
(venv `esvenv`, versions as in `reference.toml`); **[I]** inference, not yet checked.

## 1. Purpose

`EthField` provides the finite-field arithmetic that the precompiles and signature checks need:
the prime fields of BN254, BLS12-381, secp256k1 and P-256 (base and scalar fields), the quadratic,
sextic and dodecic extensions used by BN254 and BLS12-381 G2 and pairings, and plain `Nat`
modular exponentiation for MODEXP. It is layer L0 (ARCHITECTURE §2) and sits directly on
`EthBase`. It replaces the field classes of the Python dependency `py_ecc` (`FQ`, `FQ2`, `FQ12`,
`prime_field_inv`) and the `int` arithmetic inside `crypto/elliptic_curve.py`. It holds no EVM
semantics and no curve or pairing logic. Its public contract is **model-based** (D25): each field
type has a stable observer to `Nat`, operation laws stated through that observer, and, in the
Mathlib partner `EthFieldMathlib`, a ring isomorphism to `ZMod p` or to the corresponding extension.

## 2. Requirements

**R1. Moduli.** The library must define these moduli exactly [V: constants read from the pinned
sources]:

| Name | Value source | Use |
|---|---|---|
| `Bn254.q` (base) | `py_ecc/fields/field_properties.py` `"bn128"` | EIP-196/197 coordinates |
| `Bn254.r` (scalar) | `py_ecc/optimized_bn128/optimized_curve.py:17` | subgroup check |
| `Bls12381.q` (base, 381 bit) | `field_properties.py` `"bls12_381"` | EIP-2537, KZG |
| `Bls12381.r` (scalar) | `crypto/kzg.py:59` (`BLS_MODULUS`), `optimized_bls12_381` `curve_order` | KZG field elements, subgroup check |
| `Secp256k1.p`, `.n` | `crypto/elliptic_curve.py:18`, `:21` | ecrecover, tx signatures |
| `P256.p`, `.n` | `crypto/elliptic_curve.py:82`, `:79` | P256VERIFY |

The four base-field moduli (BN254 `q`, BLS12-381 `q`, secp256k1 `p`, P-256 `p`) are all
≡ 3 (mod 4), so square roots are `x^((p+1)/4)` [V: evaluated with Python; to become a `#guard`].
Scalar-field square roots are never needed.

**R2. Canonical elements.** A field element must always be a canonical residue in `[0, p)`.
Construction from an arbitrary `Nat` must reduce (`py_ecc` `FQ.__init__` reduces with `%`,
`optimized_field_elements.py:57–64` [V]). *Checked* construction (`ofNat?`) must reject `n ≥ p`;
every EVM decoder uses the checked form (for example `alt_bn128.py:68–71`,
`bls12_381/__init__.py:451`, `crypto/kzg.py:103`).

**R3. Inverse of zero.** `inv0 0 = 0` and `a / 0 = 0`. This is observable: `py_ecc`'s
`prime_field_inv` returns 0 for 0 (`py_ecc/utils.py:21–39`, "inv0(0) == 0" per the hash-to-curve
draft) [V], and `normalize` of the point at infinity divides by `z = 0`, which is how the
precompiles produce the all-zero encoding of infinity (`optimized_curve.py:146–150`) [V: `normalize`
of `P + (−P)` and of `0·P` gives `(0, 0)` for BN254]. Any representation must preserve this.

**R4. Extension conventions.** `Fp2 = Fp[i]/(i² + 1)` for both BN254 and BLS12-381
(`fq2_modulus_coeffs = (1, 0)`) [V]. The element `c0 + c1·i` is stored as `(c0, c1)`; the EVM
byte orders differ per EIP and are handled by `EthPrecompiles` (BN254 puts the imaginary part
first, `alt_bn128.py:124–125`; BLS12-381 puts `c0` first, `bls12_381/__init__.py:479–487`) [V].
`py_ecc` realises `Fp12` as a flat degree-12 extension, `w¹² − 18w⁶ + 82` (BN254) and
`w¹² − 2w⁶ + 2` (BLS12-381) [V]. These equal `(w⁶ − ξ)(w⁶ − ξ̄)` with `ξ = 9 + i` and `ξ = 1 + i`
respectively, so the tower `Fp2 → Fp6 = Fp2[v]/(v³ − ξ) → Fp12 = Fp6[w]/(w² − v)` is isomorphic
[I: algebra checked by hand; the explicit isomorphism must be written and tested]. The spec may
use the tower (as ethereum/cryptography-specs does) because **no `Fp6`/`Fp12` value is ever
EVM-observable**: pairings are observed only through the boolean "product equals one"
(`EthPairing` R3). `Fp2` values *are* observable (G2 coordinates), so the `Fp2` convention is
normative.

**R5. `sgn0` and square roots.** `sgn0` on `Fp` and `Fp2` must follow RFC 9380 §4.1
(`py_ecc` `FQ.sgn0`, `FQ2.sgn0`, `optimized_field_elements.py:205`, `:436`) [V: definitions
read], because SSWU in `bls12_map_fp_to_g1`/`bls12_map_fp2_to_g2` chooses the sign of `y` by it,
and that choice is observable in the output point. Square-root functions return `none` on
non-residues; which root they return is **not** normative on its own (callers fix the sign), but
`Fp2.sqrt?` must be total and deterministic.

**R6. Euler criterion.** `secp256k1_recover` first rejects `r` when
`pow(r³ + 7, (p − 1)/2, p) ≠ 1` (`crypto/elliptic_curve.py:47–56`) [V]. `EthField` provides
`isSquare` / `legendre` with the exact Python meaning: a zero argument gives `0`, which is `≠ 1`,
so it is rejected. (For secp256k1 `x³ + 7 ≡ 0` has no solution, because the group order is prime
and so there is no 2-torsion [I]; the check is kept literally anyway.)

**R7. MODEXP arithmetic.** `powMod b e m` must equal Python `pow(b, e, m)` for `m ≥ 1`,
including `pow(0, 0, m) = 1 % m` (so `0` when `m = 1`) [V: Python semantics]. MODEXP never calls
it with `m = 0` (`modexp.py:68–69` special-cases a zero modulus) [V]. Operand sizes are bounded
by 1024 bytes each (EIP-7823, `modexp.py:32–42`) [V], so `b`, `m < 2^8192` and `e < 2^8192`.
`powMod` must be total, structurally recursive on the exponent's bits, and must not materialise
`b^e`.

**R8. Byte conversions.** Fixed-width big-endian `toBytesBE (w : Nat) : F → ByteArray` and
checked `ofBytesBE? : ByteArray → Option F` (`int.from_bytes(…, "big")` then `< p`). Widths used:
32 (BN254, secp256k1, P-256, KZG scalars), 48 (BLS compressed), 64 (EIP-2537 padded Fp). For
64-byte EIP-2537 elements the top 16 bytes must be zero; this is implied by `c < q < 2^381`
(`bls12_381/__init__.py:449–452`) [V], so no separate padding check exists or is needed.

**R9. Totality and purity.** Every function is total, `partial`-free, `sorry`-free and uses no
`@[extern]`/`@[implemented_by]` (CONTRIBUTING §4). Exponentiation, inversion and square roots
recurse structurally on exponent bits or a fixed loop count.

**R10. Failure behaviour.** `EthField` never raises: invalid encodings are `none`, and every
arithmetic operation is total (R3). Outcome mapping (O8/O9) is done by `EthPrecompiles`.

## 3. EELS source map

Most of what this library specifies is *external* (`py_ecc` fields); the EELS items it owns are
the KZG scalar-field type and its decoder.

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `crypto/kzg.py::BLS_MODULUS` | 59 | `Bls12381.r` (alias `blsModulus`) | equals `py_ecc` `curve_order` for BLS12-381; a `#guard` checks equality with `point_evaluation.py:28` |
| `crypto/kzg.py::BLSFieldElement` | 42 | `Bls12381.Fr` | EELS subclasses `U256`; the spec uses the canonical field type, not a `U256` |
| `crypto/kzg.py::BYTES_PER_FIELD_ELEMENT` | 57 | `Bls12381.Fr.byteWidth = 32` | |
| `crypto/kzg.py::bytes_to_bls_field` | 96 | `Bls12381.Fr.ofBytesBE? : Bytes32 → Option Fr` | EELS `assert`s `< BLS_MODULUS`; the assertion becomes `none`, mapped by `EthPairing.verifyKzgProof` |

**External semantics.** This library must specify, as ordinary total Lean definitions:

- `py_ecc.fields.optimized_field_elements.FQ` (and the per-curve subclasses
  `optimized_bn128_FQ`, `optimized_bls12_381_FQ`, used through
  `py_ecc.optimized_bn128.optimized_curve.FQ` and
  `py_ecc.optimized_bls12_381.optimized_curve.FQ`, and in `crypto/kzg.py` as
  `py_ecc.fields.optimized_bls12_381_FQ`): residue arithmetic, `__eq__` against `int`, `__lt__`,
  division by `prime_field_inv`, `sgn0`.
- `FQ2`, `FQ12` (`py_ecc.optimized_bn128.optimized_curve.FQ2`/`FQ12`,
  `py_ecc.optimized_bls12_381.optimized_curve.FQ2`, `py_ecc.optimized_bls12_381.FQ12`,
  `py_ecc.fields.optimized_bls12_381_FQ2`/`FQ12`): as fields up to isomorphism (R4); `FQ2` exactly.
- `py_ecc.utils.prime_field_inv`: R3.
- `field_modulus`, `curve_order` constants (`py_ecc.optimized_bn128.optimized_curve.field_modulus`,
  `.curve_order`, and the BLS12-381 equivalents): R1.
- Python `pow(a, b, m)` on `int`/`U256` (`crypto/elliptic_curve.py:47`, `modexp.py:71`): R6, R7.
- `ethereum_types.numeric.U256`/`Uint` conversions at the boundary are `EthBase`'s.

## 4. Tests

- **EEST fixture areas** (indirect: fields are exercised only through precompiles and signatures):
  `byzantium/eip196_ec_add_mul`, `byzantium/eip197_ec_pairing`, `prague/eip2537_bls_12_381_precompiles`,
  `cancun/eip4844_blobs` (the `point_evaluation_precompile*` files), `osaka/eip7951_p256verify_precompiles`,
  `byzantium/eip198_modexp_precompile`, `osaka/eip7823_modexp_upper_bounds`,
  `osaka/eip7883_modexp_gas_increase`, `ported_static/stPreCompiledContracts2` (the `modexp_*`
  and `ecrecover*` tests), `frontier/precompiles`; and every fixture with a signed transaction
  (sender recovery), for secp256k1.
- **EELS unit tests:** none at e1a316a0 cover fields (`tests/json_loader/` has no crypto test) [V].
- **`core` `#guard` cases:**
  - typical: `mul`/`add`/`inv0` against hand-computed values per field; `(a * inv0 a) = 1` for
    sampled `a ≠ 0`; `Fp2` multiplication `(1 + 2i)(3 + 4i) = −5 + 10i` (the ZisK KAT);
  - edge: `inv0 0 = 0`; `ofNat? (p − 1) = some _`, `ofNat? p = none`, `ofNat? (2^256 − 1) = none`;
    `toBytesBE 64` has 16 leading zero bytes for BLS12-381; `powMod 0 0 1 = 0`,
    `powMod 0 0 5 = 1`, `powMod b e 1 = 0`; `isSquare 0 = false`, `isSquare 7` over secp256k1
    (`7` is a non-residue [V: Euler criterion evaluated with the pinned Python]);
  - adversarial: `sqrt?` on non-residues in `Fp` and `Fp2`; `powMod` with 8192-bit operands
    (timing budget); the tower isomorphism of R4 on random elements against the flat `py_ecc`
    representation (exported test vectors).
- **Differential checks (bug-finding only, CONTRIBUTING §1):** random operations against `py_ecc`
  (`FQ`, `FQ2`, `FQ12` under the R4 isomorphism) and Python `pow`; against CompPoly
  `BN254.Fast`/`BLS12_381.Fast` scalar fields; against the ZisK accelerator definitions
  `arith256Mod`/`complexMulL` (`riscv-zkvm` `RiscvZkvm/Rv64/ZiskAccel.lean:313`, `:489`).

## 5. Interface

All items are public unless marked internal. Namespaces `STFSpec.Field.*`.

```lean
-- modular exponentiation over Nat (MODEXP, Fermat inversion, Euler criterion)
def powMod (b e m : Nat) : Nat                         -- public; spec: b ^ e % m for m ≥ 1

-- a prime field, parameterised by its modulus
class FieldModulus (p : Nat) where
  one_lt : 1 < p               -- enough for the Nat reference; NOT enough for Montgomery (p = 2
                               -- satisfies it, but a power-of-two radix is not invertible mod 2)
  sqrtExp? : Option Nat        -- (p+1)/4 when p ≡ 3 mod 4, else none

-- LEGIBLE REFERENCE carrier (not the executable one): the Nat residue.
structure PrimeFieldRef (p : Nat) [FieldModulus p] where   -- NOT an abbrev (cf. D1)
  private mk ::
  val : Nat                                            -- internal field; use toNat
  isLt : val < p

-- EXECUTABLE carrier: a Montgomery residue in fixed limbs (§6). Exposes the same observers
-- (toNat, ofNat, …) and laws as PrimeFieldRef; the abstraction is α x̃ = x̃ · R⁻¹ mod p.
class MontgomeryParams (p : Nat) extends FieldModulus p where
  limbs : Nat                        -- L limbs of 32 bits: 8 for every p < 2^256, 12 for BLS12-381 q
  odd : p % 2 = 1                    -- R = 2^(32L) is invertible mod p only for odd p
  lt_radix : p < 2 ^ (32 * limbs)    -- the chosen carry-preserving CIOS backend needs only p < R
                                        -- (derived from bounded modulus limbs); CompPoly's current
                                        -- backend needed 2p < R because it drops a carry (see §6)
  limbs_bounded : ∀ x ∈ [modulusLimbs, rModP, r2ModP], x.Bounded   -- per-limb < 2^32 (as CompPoly)
  negInv_lt : negInv.toNat < 2 ^ 32
  negInv : UInt64                    -- −p⁻¹ mod 2^32
  negInv_spec : (negInv.toNat * p) % 2 ^ 32 = 2 ^ 32 - 1
  rModP r2ModP : Limbs               -- R mod p and R² mod p (for toMont), as limb constants
  rModP_spec : rModP.toNat = 2 ^ (32 * limbs) % p
  r2ModP_spec : r2ModP.toNat = 2 ^ (64 * limbs) % p

structure PrimeField (p : Nat) [MontgomeryParams p] where
  private mk ::
  mont : Limbs                       -- x̃ = x · R mod p
  bounded : mont.toNat < p

namespace PrimeField   -- the same observer API is provided by PrimeFieldRef
def toNat : PrimeField p → Nat                         -- stable observer: (α x̃).val
def ofNat (n : Nat) : PrimeField p                     -- reduces mod p
def ofNat? (n : Nat) : Option (PrimeField p)           -- none if n ≥ p
def zero one : PrimeField p
def add sub mul : PrimeField p → PrimeField p → PrimeField p
def neg : PrimeField p → PrimeField p
def inv0 : PrimeField p → PrimeField p                 -- inv0 0 = 0 (R3)
def div (a b : PrimeField p) : PrimeField p := mul a (inv0 b)
def pow : PrimeField p → Nat → PrimeField p
def isZero : PrimeField p → Bool
def legendre : PrimeField p → Int                      -- -1, 0, 1 (Euler criterion)
def isSquare (a : PrimeField p) : Bool := legendre a = 1
def sqrt? : PrimeField p → Option (PrimeField p)       -- requires sqrtExp? = some _
def sgn0 : PrimeField p → Bool                         -- RFC 9380 §4.1
def toBytesBE (w : Nat) : PrimeField p → ByteArray     -- left-padded to w bytes
def ofBytesBE? : ByteArray → Option (PrimeField p)     -- big-endian, checked
instance : Add, Sub, Neg, Mul, Div (via div), HPow _ Nat _, DecidableEq, Inhabited, Repr
end PrimeField

-- concrete fields (public)
def Bn254.q Bn254.r Bls12381.q Bls12381.r Secp256k1.p Secp256k1.n P256.p P256.n : Nat
abbrev Bn254.Fq := PrimeField Bn254.q      -- abbrev over the structure is fine: the
abbrev Bn254.Fr := PrimeField Bn254.r      -- structure is the abstraction barrier
abbrev Bls12381.Fq := PrimeField Bls12381.q
abbrev Bls12381.Fr := PrimeField Bls12381.r
abbrev Secp256k1.Fq := PrimeField Secp256k1.p
abbrev Secp256k1.Fn := PrimeField Secp256k1.n
abbrev P256.Fq := PrimeField P256.p
abbrev P256.Fn := PrimeField P256.n

-- quadratic extension F[i]/(i² − β); both curves use β = −1
class QuadNonResidue (F : Type) where beta : F
structure Fp2 (F : Type) [QuadNonResidue F] where
  c0 : F
  c1 : F
namespace Fp2
def add sub mul : Fp2 F → Fp2 F → Fp2 F
def sq : Fp2 F → Fp2 F
def neg conj inv0 : Fp2 F → Fp2 F
def mulByFp : F → Fp2 F → Fp2 F
def pow : Fp2 F → Nat → Fp2 F
def sgn0 : Fp2 F → Bool                        -- RFC 9380
def sqrt? : Fp2 F → Option (Fp2 F)             -- deterministic, total
def frobenius : Fp2 F → Fp2 F                  -- = conj for β = −1
end Fp2

-- tower (sextic over Fp2, quadratic over Fp6); ξ is a curve parameter
class SexticNonResidue (F) [QuadNonResidue F] where xi : Fp2 F
structure Fp6 (F) … where c0 c1 c2 : Fp2 F
structure Fp12 (F) … where c0 c1 : Fp6 F
-- add/sub/neg/mul/sq/inv0/pow/conj (unitary inverse)/frobenius^k (k < 12)/one/isOne
def Bn254.Fq2 Bn254.Fq12 Bls12381.Fq2 Bls12381.Fq12 : Type   -- instances ξ = 9+i, 1+i

-- internal
def Fp12.ofFlat : (Fin 12 → F) → Fp12 F     -- R4 isomorphism, for tests against py_ecc
def Fp12.toFlat : Fp12 F → (Fin 12 → F)
```

Names follow EELS/`py_ecc` in lowerCamelCase (`inv0` rather than `prime_field_inv`, because the
`0 ↦ 0` convention is the point). There is no `Div (Fin n)` pitfall: `PrimeField` is a
`structure`, so core's `Fin` division (Nat division, flagged in cryptography-specs `Bls/Fp.lean`)
can never be picked up.

## 6. Data structures

| Type | Representation (executable; reference in italics) | Model | Abstraction | Invariant | Persistence | Complexity |
|---|---|---|---|---|---|---|
| `PrimeField p` | **executable:** Montgomery residue `x̃ = x·R mod p` in fixed limbs, carry-preserving CIOS needing only `p < R`: `Wide8` (8×32-bit limbs in `UInt64`, `R = 2^256`) for every modulus `< 2^256`; `W12` (12×32, same template, `R = 2^384`) for BLS12-381 `q` (prototyped; not yet in the core or upstream). *Reference:* `val : Nat` with `val < p` | residues mod `p`; `ZMod p` in `EthFieldMathlib` | executable → reference: `α x̃ = x̃ · R⁻¹ mod p`; reference → model: `toNat` (core), `toZMod` (Mathlib) | executable: `Bounded x̃ ∧ x̃.toNat < p`; reference: `val < p` | immutable value; freely shareable | executable: CIOS Montgomery multiplication, add/sub with a conditional subtraction; reference: `Nat` arithmetic with `% p` |
| `Fp2 F` | two `F` | `F[i]/(i²−β)` | componentwise | components canonical | immutable | mul 3–4 `F`-muls (Karatsuba optional) |
| `Fp6 F`, `Fp12 F` | tower of `Fp2` | `Fp2[v]/(v³−ξ)`, `Fp6[w]/(w²−v)` | componentwise; `toFlat` for R4 | components canonical | immutable | `Fp12` mul ≈ 54 `Fp`-muls with Karatsuba [I] |
| `powMod` workspace | `Nat` accumulators | `b^e mod m` | — | `acc < m` | local | O(log e · M(log m)) |

**Montgomery backend premises (field backend only).** A modulus uses the Montgomery backend only if: `p` is odd; the radix capacity `R = 2^(32L)` satisfies `p < R` (for the chosen carry-preserving backend; see the limb table below); the constants' limbs are each below `2^32`, as is `negInv`; and the constants `negInv` (−p⁻¹ mod 2^32), `R mod p` and `R² mod p` are proved correct (the `MontgomeryParams` fields). These are premises of *this backend*. They do **not** restrict MODEXP, whose moduli are arbitrary (including even ones) and which uses `Nat` arithmetic (`EthPrecompiles`).

**Executable representation: Montgomery form (D6, D18).** The executable representation stores
`x̃ = x·R mod p` in fixed limbs, with `R = 2^256` for eight 32-bit limbs in `UInt64`s (`Wide8`)
and `R = 2^384` for twelve (`W12`). It is CompPoly's `Montgomery.Native64x8` (`Limbs8`, `mul` by
CIOS reduction, `rModModulus`, `r2ModModulus`, `montgomeryNegInv`;
`~/CompPoly/CompPoly/Fields/Montgomery/Native64x8Defs.lean`, zero imports [V]) **with its two
dropped carries restored** (the carry-preserving variant: `add` keeps the `addLimbs` carry, and
`mul` passes the head limb `t8` to the final `condSubWide`). CompPoly's
unmodified backend is valid only under `2p < R`.
Abstraction `α(x̃) = x̃ · R⁻¹ mod p`; invariant `Bounded x̃ ∧ x̃.toNat < p`. It sits behind the
*same* `PrimeField` observers and laws as the `Nat` reference: every executable operation commutes
with `α`. **Measured** (prototype, one secp256k1 k·G with conversions): the `Nat` reference is about 3–6.5× slower than `Wide8`, *not* orders of magnitude, and `Wide8` is about 20–35× slower than native ecrecover. So the remaining gap to the 10× target is algorithmic (Shamir/Straus, wNAF, GLV in `EthCurve`), not a matter of limb width. Performance suitability is to be confirmed by measurement that includes allocation,
conversions into and out of Montgomery form, and composition inside the tower and the pairing
(no checksum inside the timed loop; [REVIEW §7](../REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks) C1–C4), not by the algorithm's name alone. Status [V]:

- CompPoly has `Native64x8` instances only for the BN254 and BLS12-381 **scalar** fields
  (`CompPoly/Fields/BN254/Fast.lean`, `BLS12_381/Fast.lean`). The Montgomery prototype has
  decide-checked constants for all eight moduli (generated).
- **Resolved (prototype, 2026-09-29): the carry-preserving backend.** The results below were independently re-verified.
  - **Why CompPoly needed `2p < R`:** its eight-limb backend drops a carry in exactly two places, the top carry of `add` and the head limb `t8` of the CIOS accumulator (plus a third site in the divstep inverse). Fixing those with a carry-aware final subtraction `condSubWide` needs only `p < R`, the textbook CIOS bound.
  - **Result:** one template at two widths.

    | Modulus | Bits | Min limbs for `p < R` (chosen backend) | Min limbs for `2p < R` (CompPoly's current backend) |
    |---|---|---|---|
    | BN254 `q`, `r` | 254 | 8 | 8 |
    | BLS12-381 `r` | 255 | 8 | 8 |
    | secp256k1 `p`, `n`; P-256 `p`, `n` | 256 | **8** | 9 |
    | BLS12-381 `q` | 381 | 12 | 12 |

    The executable backends are **`Wide8`** (8 limbs, all seven moduli below 2^256) and **`W12`** (12 limbs, BLS12-381 `q`), generated from one template.
  - **Correctness:** checked against the `Nat` reference with 0 mismatches for all eight moduli.
  - **Proofs:** `mul_spec`, `mul_commutes`, `add_spec`, in core Lean with standard axioms only, no `sorry`. The premises are decide-proved instances depending on no axioms.
  - **Rejected alternatives:** a width-generic `Array UInt64` backend is the most legible but boxes every limb and is 22–36× slower end to end. Nine narrow limbs (keeping `2p < R`) is no faster, and needs a non-standard `R = 2^288`.
  - **Upstream:** in progress as CompPoly PR #389 (tracked in D6). The fix is a small CompPoly change (three call sites plus a weakened class field, `modulus_lt : modulus < 2^256`), or we vendor its zero-import Defs (D26: CompPoly requires Mathlib at package level).
- **BLS12-381 `q` (381 bits)** uses `W12` (12×32 limbs, the same carry-preserving template,
  `R = 2^384`, generated): 0 mismatches against the `Nat` reference, but its laws
  are not yet proved. It is not yet in the core or upstream.
- No extension-field Montgomery towers exist in CompPoly; its `Fields/Extension` is generic [I: not
  read in detail].

**No persistence concern.** Field elements are small immutable values; they never live inside
snapshotted state (ARCHITECTURE §5.0 does not apply).

## 7. Contract and laws

Per operation, the commuting equation with the `Nat` model (core) — stated once, proved once per
representation:

- [C] `(ofNat n).toNat = n % p`; `ofNat? n = some a ↔ n < p ∧ a.toNat = n`; `toNat` injective (ext).
- [C] `(a + b).toNat = (a.toNat + b.toNat) % p`; `(a − b).toNat = (a.toNat + p − b.toNat) % p`;
  `(−a).toNat = (p − a.toNat) % p`; `(a * b).toNat = a.toNat * b.toNat % p`.
- [C] `(a.pow e).toNat = a.toNat ^ e % p`; `powMod b e m = b ^ e % m` for `m ≥ 1`.
- [C] `inv0 0 = 0`; for prime `p` and `a ≠ 0`, `a * inv0 a = 1` (needs primality: Mathlib side).
- [C] `sqrt? a = some s → s * s = a`; for prime `p ≡ 3 mod 4`, `sqrt? a = none ↔ ¬ isSquare a ∧ a ≠ 0`.
- [C] `legendre` equals Python's `pow(a, (p−1)/2, p)` read as `{0, 1, p−1} ↦ {0, 1, −1}`.
- [C] `ofBytesBE? (toBytesBE w a) = some a` and `(toBytesBE w a).size = w` when `p ≤ 256^w`. Both laws require a sufficient width; left padding alone does not truncate an oversized value.
- [C] Extension fields: componentwise laws for `add`/`sub`/`neg`; `mul` law against the
  polynomial model; `Fp12.toFlat` is a ring isomorphism onto `py_ecc`'s flat representation (R4).
- [T] every definition total by structural recursion (no `partial`, cf. cryptography-specs'
  `partial def powNat` in `Bls/Fp2.lean:64`, `Bls/Fp12.lean:65`, which must not be copied).
- [F] each executable (Montgomery) operation commutes with `α` onto the `Nat` reference, so every
  law above holds for the executable representation. At limb level (proved for `Wide8.mul` in the
  prototype): `R · mul a b ≡ a · b (mod p)`, with the result bounded and `< p`; `mul` needs `a < p` and
  bounded limbs but not `b < p`. Observer form: `α (mul a b) = α a · α b mod p`.
- [R] bridge to ZisK: `(a * b + c).toNat = arith256Mod a.toNat b.toNat c.toNat p` for canonical
  inputs; `Fp2.mul` equals `complexMulL` on the accelerator wire format (for BN254, and BLS12-381
  via `Arith384Mod`/`complexMulL` with 6 limbs) (`ZiskAccel.lean:313`, `:489`).

**Derived laws** (in `EthFieldMathlib`, from `toZMod : PrimeField p ≃+* ZMod p`): field axioms,
Fermat, Euler's criterion, uniqueness of square roots up to sign. Callers (curves, pairings) use
the ring structure, never the `val` field.

### Informal correctness argument

**Claim.** Public field and tower operations commute with their residue-field models; encoding and square-root operations satisfy their stated, domain-qualified contracts.

**Premises.** Prime modulus for field laws, irreducibility/nonresidue facts for every tower layer, EthBase byte laws, and p ≤ 256^w for a w-byte encoding. The current modulus class's 1 < p alone does not establish a field.

**Argument.** Canonical reduction gives a unique representative in [0,p). Addition and multiplication preserve congruence, yielding their model equations. Inversion splits zero from nonzero; Fermat/Euclid supplies the nonzero inverse only under primality. Exponentiation maintains accumulator * base^remaining = original^exponent through each bit step. Tower multiplication reduces polynomial products by the declared defining polynomial; coefficient-wise equality then proves correspondence with the extension model. Square-root soundness is checked by squaring the returned value; completeness and the selected sign require the particular algorithm's hypotheses. Zero needs its own case because the reference's residue predicate and sqrt convention differ there. Encoding is positional evaluation with a range check, so reduction must not silently accept a noncanonical encoded field element.

**Open obligations.** Prime and irreducibility certificates, algorithm-specific sqrt completeness/sign laws, and public-operation bridges remain required. The Montgomery implementation must prove these same observer equations relative to the `Nat` reference.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthBase`
- **Used by:** `EthCurve` directly; `EthPairing` and `EthPrecompiles` transitively (MODEXP uses
  `powMod`; KZG decoders use `Bls12381.Fr.ofBytesBE?`). `EthFieldMathlib` (Mathlib bridge package).
- **Seams.** Consumes from `EthBase` only `ByteArray`/`Bytes32` and `U256.toNat`/`ofNat`
  conversions. Provides the `PrimeField` observer contract; guarantees every value is canonical.
  The runtime source for the fast path is CompPoly's zero-import `…Defs` in the
  carry-preserving variant (D6), not CompPoly's current `2p < R` code.
  Importing it must not pull in Mathlib (the D6 Lake check found that a `require` of CompPoly
  does), so vendoring with attribution or an upstream fix and split is still undecided.

## 9. Open decisions

- **D6** (provisional; field arithmetic source): the width is settled, a carry-preserving CIOS
  backend (`Wide8`/`W12`, `p < R`). Open: whether it is vendored from CompPoly's zero-import
  `Native64x8Defs` with the carry fix, or the same fix is upstreamed to a Mathlib-free CompPoly
  split. Local impact: only the representation of `PrimeField` changes; the laws of §7 do not.
- **D21** (accepted: banned): no `@[csimp]`. The Montgomery representation is used directly,
  as a representation replacement (like D1(b)) proved against the `ZMod p` model.
- **D18** (accepted): a `Nat`-only field with Fermat inversion is correct and complete, but it is
  **not performance-appropriate** for pairings (an earlier guess of "seconds per pairing" was an
  unmeasured estimate that predates the Montgomery prototype).
  So the executable representation is Montgomery, with the `Nat` form kept as the legible
  reference. Shipping the `Nat` form would need a D18 justification (legibility or drastic
  proof-friendliness) recorded in `STFSpec/informal/DEBT.md`.
- **D15**: if cryptography-specs' `Bls/Fp.lean` (`abbrev Fp := Fin modulus`) is reused, its
  `abbrev` must be wrapped in our `structure` to keep the abstraction barrier.
- **D1**: the boundary with `U256` (EVM inputs arrive as `U256`, converted via `toNat`).
- Fast-field plan (NEW-CRYPTO-2): width resolved, DECISIONS Q39 (Montgomery prototype); the source
  (vendor or upstream) remains with D6.

## 10. Gaps

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Montgomery backend not yet in the core.** `W12` (12×32, the same carry-preserving template,
  `R = 2^384`) serves BLS12-381 `q`, the hot field for EIP-2537 and KZG; it exists only in the
  Montgomery prototype, not in the core or upstream. Pairing and tower speed on it is unmeasured.
- **Montgomery obligations still open:** `sub`/`neg` laws under
  `q < 2^256`; all `W12` laws; the observer layer (`toMont`/`fromMont`) and the §7 [F] law for
  every operation; inversion. `Wide8` instances for all seven moduli below 2^256 exist in the
  prototype (CompPoly has only the BN254/BLS12-381 scalar fields [V]). CompPoly's divstep inverse
  (`Native64x8InvDefs.lean:168`) still drops the carry, so it is not valid for secp256k1/P-256
  until fixed; the prototype uses Fermat inversion.
- **Tower isomorphism unproved and untested** (R4): the explicit map between `py_ecc`'s flat
  `Fp12` and the tower is only a hand calculation; it is needed for differential tests of
  pairings, not for EVM outputs.
- **`sqrt?` on `Fp2`**: the algorithm (py_ecc uses `(q²+8)/16` exponent and eighth roots of unity,
  `point_compression.py:123`; RFC 9380 uses a different one) is unchosen; only its sign-fixed
  uses are normative, which must be checked at each call site (G2 decompression, SSWU).
- **`sgn0` for `Fp2`** is specified only by reference to RFC 9380 and `py_ecc`; not yet
  cross-checked against the EIP-2537 vectors.
- **Primality** of the eight moduli is a Mathlib-side obligation (Pratt certificates exist in
  CompPoly for BN254 `r`, BLS12-381 `r`, secp256k1 `p` and `n` [V], and in cryptography-specs for
  BLS12-381 `q` and `r` [V]; none found for BN254 `q` or P-256 `p`/`n` [I]); only `1 < p` is needed in the core.
- **Complexity bounds** are analytical; nothing is measured for `powMod` at 8192 bits or for
  `Fp12` multiplication in pure Lean.
- **Host behaviour of Python `pow`** is assumed to be exact bignum arithmetic; there is no
  host-dependent behaviour here, but this is not documented upstream.
- **Owner question:** whether `powMod` belongs here or in `EthBase` (it is non-prime modular
  arithmetic used by MODEXP). Kept here because `EthPrecompiles` already reaches `EthField`
  through `EthPairing`.
