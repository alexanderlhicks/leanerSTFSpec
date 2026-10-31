# `EthField`: prime fields, extension towers and modular arithmetic

*Status: informal specification, draft; reference carrier, basic residue arithmetic, natural powers, canonical sign, checked byte decoding and eight natural moduli supplied. Date: 2026-10-30. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
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
`py_ecc/fields/optimized_field_elements.py:57–64` [V]). *Checked* construction (`ofNat?`) must reject `n ≥ p`;
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
(`py_ecc` `FQ.sgn0`, `FQ2.sgn0`, `py_ecc/fields/optimized_field_elements.py:205`, `:436`) [V: definitions
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
| `crypto/kzg.py::BLS_MODULUS` | 59 | `Bls12381.r` (supplied constant; convenience alias open) | equals `py_ecc` `curve_order` for BLS12-381; a `#guard` checks equality with `point_evaluation.py:28` |
| `crypto/kzg.py::BLSFieldElement` | 42 | `Bls12381.Fr` | EELS subclasses `U256`; the spec uses the canonical field type, not a `U256` |
| `crypto/kzg.py::BYTES_PER_FIELD_ELEMENT` | 57 | `Bls12381.Fr.byteWidth = 32` | |
| `crypto/kzg.py::bytes_to_bls_field` | 96–104 | `PrimeFieldRef.ofBytesBE?` (reference helper supplied; concrete alias/consumer adapter open) | Conditional on typed 32-byte inputs and active assertions; optimized source retains noncanonical values. See the checked-reference slice below. |

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

### Supplied exact natural moduli

`STFSpec/Field/Moduli.lean`, reexported by `STFSpec.Field`, supplies exactly the eight
R1 constants below as `Nat`. These are pure values with no arguments, mutation,
queries or failure channel. The names distinguish coordinate/base moduli from
subgroup/scalar orders. No public law, instance, concrete field alias, convenience
alias, primality certificate, square-root metadata or Montgomery parameter is added.
The exact dependency is py-ecc 8.0.0 locked by EELS at
`e1a316a06fc3d3e0a5da36fdc78580811e9d8a36` (the current pin).

| Source / complete owning expression | Lean declaration and exact type | Meaning / deterministic control / status |
|---|---|---|
| py-ecc `py_ecc/fields/field_properties.py:24`, `bn128.field_modulus` | `Bn254.q : Nat` | Base modulus; full literal, 254 bits; **supplied** |
| py-ecc `py_ecc/optimized_bn128/optimized_curve.py:17–19`, `curve_order` | `Bn254.r : Nat` | Scalar order; full literal, 254 bits; **supplied** |
| py-ecc `py_ecc/fields/field_properties.py:29`, `bls12_381.field_modulus` | `Bls12381.q : Nat` | Base modulus; full literal, 381 bits; **supplied** |
| py-ecc `py_ecc/optimized_bls12_381/optimized_curve.py:17–19`, `curve_order`; EELS `src/ethereum/crypto/kzg.py:59–61`, `BLS_MODULUS`, and `src/ethereum/forks/amsterdam/vm/precompiled_contracts/point_evaluation.py:28` | `Bls12381.r : Nat` | Scalar order, all three source literals equal; 255 bits; **supplied** |
| EELS `src/ethereum/crypto/elliptic_curve.py:18–20`, `SECP256K1P` | `Secp256k1.p : Nat` | Base modulus; full literal, 256 bits; **supplied** |
| EELS `src/ethereum/crypto/elliptic_curve.py:21–23`, `SECP256K1N` | `Secp256k1.n : Nat` | Scalar order; full literal, 256 bits; **supplied** |
| EELS `src/ethereum/crypto/elliptic_curve.py:82–84`, `SECP256R1P` | `P256.p : Nat` | Base modulus; full literal, 256 bits; **supplied** |
| EELS `src/ethereum/crypto/elliptic_curve.py:79–81`, `SECP256R1N` | `P256.n : Nat` | Scalar order; full literal, 256 bits; **supplied** |

The dependency wheel is authenticated against the pinned `uv.lock`; source files
are bound to their actual pinned Git blobs and installed dependency members match
the locked wheel bytes. Static reading of the complete owning literal expressions
(including the U256/BLSFieldElement argument) does not execute original assignments,
classes or module initializers. These constants alone discharge no concrete-field,
primality, alias, precompile, backend, replacement, resource or C1–C4 gate.

### Supplied initial natural reference carrier

`STFSpec/Field/Reference.lean`, reexported by `STFSpec.Field`, supplies
`FieldModulus` and `PrimeFieldRef` with the initial five operations below and the
separate five-operation arithmetic slice that follows. The class has exactly
`one_lt : 1 < p` and unconstrained `sqrtExp? : Option Nat`. Every `p > 1` is admitted,
including 2, even composites and odd composites. Metadata is unread by this slice;
its presence does not assert that an exponent is correct. The structure uses the literal
private constructor; `val`/`isLt` projections remain internal by convention, not hidden.
Consumers use the fourteen observer laws in §7.

The dependency references below are py-ecc 8.0.0 at the lock pinned by `reference.toml`.
These synthetic parameter-class comparisons execute original optimized `FQ` methods;
they do not execute original EELS concrete-field globals. Natural inputs exclude the
source constructor's signed-integer and FQ-copy branches. No source exception or guest
handler is reached on this bounded, successfully constructed typed domain. Checked
construction is a mathematical helper required by R2, not an existing `FQ` method.

| Source / contract | Lean declaration and type (`[FieldModulus p]`, `p` inferred) | Domain, complete success/effects and ordered failure | Ordinary law | Deterministic controls / status |
|---|---|---|---|---|
| `py_ecc/fields/optimized_field_elements.py:190–191`, `FQ.__int__`; guided observer | `PrimeFieldRef.toNat : PrimeFieldRef p → Nat` | Every canonical element; return its natural residue, no mutation/query/failure | `toNat_lt`; `ext` | All canonical values below; **discharged** |
| `py_ecc/fields/optimized_field_elements.py:57–68`, `FQ.__init__` natural-input branch | `PrimeFieldRef.ofNat : Nat → PrimeFieldRef p` | Every Nat; return `n % p`; no mutation/query/failure | `toNat_ofNat` | `0,p−1,p,p+1,2p+3,2^4096+17`; **discharged** |
| R2 / §7 mathematical checked helper; no original helper execution | `PrimeFieldRef.ofNat? : Nat → Option (PrimeFieldRef p)` | First test `n < p`: return `some` with original value; otherwise `none`; no reduction, mutation or query; consumer owns any O8/O9 mapping | `ofNat?_eq_some_iff` | Same inputs; accept exactly `0,p−1`; **discharged** |
| `py_ecc/fields/optimized_field_elements.py:221–223`, `FQ.zero` | `PrimeFieldRef.zero : PrimeFieldRef p` | Every admitted modulus; canonical zero, pure, no failure | `toNat_zero` | All seven moduli and metadata choices; **discharged** |
| `py_ecc/fields/optimized_field_elements.py:217–219`, `FQ.one` | `PrimeFieldRef.one : PrimeFieldRef p` | Every admitted modulus; canonical one, pure, no failure | `toNat_one` | Same moduli/metadata; **discharged** |

Exactly three instance families are supplied: actual canonical `DecidableEq`,
`Inhabited` with zero default, and `Repr` of the canonical Nat. Dependency observations
are `FQ.__eq__` (`py_ecc/fields/optimized_field_elements.py:171–179`, field-to-field branch :172–173)
and `FQ.__repr__` (:187–188). Lean supplies no mixed-type equality instance; the
source comparison with raw integers is modelled separately by natural observation.
No BEq, order, coercion or numeric-literal notation is supplied. The arithmetic
slice adds exactly the four delegating operator instances below.

Private clients in `STFSpec/Conformance/Field/ReferenceCallerProofs.lean` derive checked
rejection iff, reducing roundtrip/idempotence, checked roundtrip/success preservation,
actual equality iff and zero/one recognition from only the six public laws. They quantify
over arbitrary modulus instances and elements without inspecting projections, metadata,
constructor equations or operation definitions. No primality/oddness/radix premise is used.

### Supplied basic natural-reference arithmetic

The same module supplies exactly five additional operations, five ordinary observer laws
and Add/Sub/Neg/Mul instances directly delegating to the respective named operation. These
are residue operations for every `p > 1`, including even and composite moduli, with arbitrary
unread `sqrtExp?`. They add no field hypothesis, runtime alias or algebra hierarchy.

| Source / contract | Lean declaration and type (`[FieldModulus p]`, `p` inferred) | Domain, complete success/effects and ordered failure | Ordinary law | Deterministic controls / status |
|---|---|---|---|---|
| `py_ecc/fields/optimized_field_elements.py:70–80`, `FQ.__add__`, constructor :57–68 | `PrimeFieldRef.add : PrimeFieldRef p → PrimeFieldRef p → PrimeFieldRef p` | Every canonical same-p pair; return `(a.toNat+b.toNat)%p`; pure, no query/mutation/failure | `toNat_add` | All small canonical pairs, boundary/reducing inputs and p9 asymmetric literal; **discharged** |
| `py_ecc/fields/optimized_field_elements.py:112–122`, `FQ.__sub__`, constructor :57–68 | `PrimeFieldRef.sub : PrimeFieldRef p → PrimeFieldRef p → PrimeFieldRef p` | Every canonical same-p pair; return `(a.toNat+p-b.toNat)%p`; the bound on b prevents natural truncation, matching signed remainder; pure, no query/mutation/failure | `toNat_sub` | All pair orderings; p5 (1,3) gives 3 rather than saturating 0; **discharged** |
| `py_ecc/fields/optimized_field_elements.py:184–185`, `FQ.__neg__`, constructor :57–68 | `PrimeFieldRef.neg : PrimeFieldRef p → PrimeFieldRef p` | Every canonical element; return `(p-a.toNat)%p`, including zero; pure, no query/mutation/failure | `toNat_neg` | Zero, one, p−1 and huge reducing inputs; **discharged** |
| `py_ecc/fields/optimized_field_elements.py:82–92`, `FQ.__mul__`, constructor :57–68 | `PrimeFieldRef.mul : PrimeFieldRef p → PrimeFieldRef p → PrimeFieldRef p` | Every canonical same-p pair; return `(a.toNat*b.toNat)%p`; pure, no query/mutation/failure | `toNat_mul` | All pairs; nonzero zero divisor 2×2 mod4=0; **discharged** |
| `py_ecc/fields/optimized_field_elements.py:171–175`, `FQ.__eq__` integer-zero comparison | `PrimeFieldRef.isZero : PrimeFieldRef p → Bool` | Every canonical element; return exactly `decide (a.toNat=0)`; pure, no query/mutation/failure | `isZero_eq` | True at zero and false at nonzero canonical values; **discharged** |

`isZero` is the guided Lean observer of original `a == 0`, not a dependency method named
`isZero`. The source mapping is restricted to successfully constructed canonical natural
same-modulus FQ operands. Mixed types, external signed constructor inputs, FQ copies,
cross-modulus objects, mutated objects, reflected methods and source exception branches are
outside this claim. Original negation retains its internal signed constructor argument.
Synthetic parameter classes are evidence-only, not original EELS concrete globals.

Private facade-only `ReferenceArithmeticCallerProofs.lean` clients demonstrate both named
and notation equations, all result ranges, both Boolean zero-recognition directions,
zero/self subtraction, zero negation, subtraction/addition and negation/addition cancellation,
and signed-Int subtraction/negation models. Clients use public laws and instance delegation,
never the carrier projections, constructor equations or semantic operation definitions.

### Supplied natural-reference powers

`STFSpec/Field/ReferencePower.lean`, reexported by `STFSpec.Field`, adds exactly
`PrimeFieldRef.pow`, its ordinary `toNat_pow` observer law and one directly delegating
`HPow (PrimeFieldRef p) Nat (PrimeFieldRef p)` instance. Every helper and derived law
is private. This reference-only operation admits every p>1, including 2 and even/odd
composites, every canonical base and every natural exponent. Square-root metadata is
arbitrary and unread. There is no primality, nonzero-base or exponent-bound premise.

| Source / contract | Lean declaration and exact type (`{p : Nat} [FieldModulus p]`) | Complete behavior / effects / ordered failure | Law / controls / status |
|---|---|---|---|
| py-ecc 8.0.0 `py_ecc/fields/optimized_field_elements.py:161–169`, `FQ.__pow__`; constructor :57–68 and multiplication :82–92 | `PrimeFieldRef.pow (a : PrimeFieldRef p) (e : Nat) : PrimeFieldRef p` | Return the canonical residue `a.toNat ^ e % p`; `0^0` is one; pure, no query/mutation/failure | `toNat_pow (a) (e) : (pow a e).toNat = a.toNat ^ e % p`; all-input ordinary proof and complete finite controls; **discharged** |
| §5 reference observer API and operator delegation | `PrimeFieldRef.toNat_pow (a : PrimeFieldRef p) (e : Nat)` and `HPow (PrimeFieldRef p) Nat (PrimeFieldRef p)` | The theorem is ordinary equality; notation delegates directly to `pow` | Private public-facade clients and named/notation controls; **discharged** |

The private positive-modulus natural worker halves the exponent, squares the returned
half-power modulo p, and multiplies by the reduced base on an odd bit. This rearranges
the source's equivalent square-base-before-recursion shape. Each product is reduced;
the implementation never constructs the unreduced natural power. The natural measure
strictly decreases at every recursive call; strong induction and natural modular
multiplication prove the full observer equation. No exponent is reduced modulo p,
p−1, an order or a machine width. The private worker's positivity premise follows
from the existing class bound and selects no public `powMod` zero-modulus completion.

Private `ReferencePowerCallerProofs.lean` clients import only the public Field facade.
They derive named/notation equations, canonical range, exponents zero/one, zero at
positive exponents, one at every exponent, square, exponent addition, product powers
and iterated powers from the public observer laws and delegation. An explicit symbolic
client quantifies over every `Option Nat` metadata value. No field/Euler/cancellation
assumption or equality between differently parameterized metadata instances is used.

### Supplied canonical natural-reference sign

`STFSpec/Field/ReferenceSign.lean`, reexported by `STFSpec.Field`, adds exactly
`PrimeFieldRef.sgn0` and its ordinary `sgn0_eq` observer law. This is R5's Fp
canonical-parity observer on the existing reference carrier and §5's same observer
API. Every admitted p>1, including 2 and even/odd composites, every canonical element
and arbitrary unread `sqrtExp? : Option Nat` are supported. No primality, oddness,
metadata coherence or additional proof argument is required.

| Source / contract | Lean declaration and exact type (`{p : Nat} [FieldModulus p]`) | Complete behavior / effects / ordered failure | Law / controls / status |
|---|---|---|---|
| py-ecc 8.0.0 `py_ecc/fields/optimized_field_elements.py:204–215`, optimized `FQ.sgn0`; constructor :57–68 and `__int__` :190–191 | `PrimeFieldRef.sgn0 (a : PrimeFieldRef p) : Bool` | Return exactly `decide (a.toNat % 2 = 1)`; canonical residue parity, pure Lean observer, no query/mutation/failure | `sgn0_eq`; exhaustive small canonical residues, wraps, p3/raw4 trap and adjacent large bit controls under all three metadata choices; **discharged** |
| R5 / §5 reference observer API / §7 model equation | `PrimeFieldRef.sgn0_eq (a : PrimeFieldRef p) : sgn0 a = decide (a.toNat % 2 = 1)` | Ordinary equality for every canonical element and arbitrary admitted instance | Private facade-only true/false, zero/one, reducing-constructor and arbitrary-metadata observer clients; **discharged** |

The original cached property's exact Python integer zero/one is compared to Lean
Bool explicitly as false→0 and true→1. The source first reduces the natural
constructor input: p3/raw4 has canonical residue one and sign true, although raw
four is even. The finite source claim covers successfully constructed fresh
optimized FQ objects, including the actual original BN254/BLS12-381 base classes.
Source cache entry/profile observations authenticate that property access; the pure
Lean API claims no mutable-cache effect correspondence. Signed/copy/mixed/mutated
source objects, ordinary/scalar/secp256k1/P256 named sign properties, Fp2 sign,
square roots, a negation-sign identity and an RFC-wide hierarchy are outside this slice.

Private `ReferenceSignCallerProofs.lean` imports only the Field facade and derives
both Boolean recognition directions, zero/one and reducing-constructor parity from
`sgn0_eq` and the public provider laws. Symbolic clients quantify over every metadata
value and compare Boolean observations of potentially different instance carriers
under a `toNat` equality premise; they never equate those carriers or inspect private
constructors, provider definitions or metadata. No algebra hierarchy or new instance
is added. The direct legible observer needs no alternate fast algorithm.

### Supplied checked natural-reference byte decoder

`STFSpec/Field/ReferenceDecode.lean`, reexported by `STFSpec.Field`, adds exactly
`PrimeFieldRef.ofBytesBE?` and its complete ordinary success iff. The public input
is `ByteArray`. Every finite length is admitted, with no width cap, reduction,
exception, mutation or query. Every p>1, including 2, even and odd composites,
and arbitrary unread square-root metadata is supported. The implementation composes
existing public `Bytes.ofByteArray`, unbounded `Uint.ofBeBytes` and `PrimeFieldRef.ofNat?`.

| Source / contract | Lean declaration and exact type (`{p : Nat} [FieldModulus p]`) | Domain, complete result and ordered failure | Ordinary law / controls / status |
|---|---|---|---|
| R2/R8/R10 mathematical helper; EELS `src/ethereum/crypto/kzg.py:96–104` conditionally on typed 32-byte, assertion-active inputs; `src/ethereum/forks/amsterdam/vm/precompiled_contracts/bls12_381/__init__.py:426–454` conditionally on exactly 64 bytes | `PrimeFieldRef.ofBytesBE? (b : ByteArray) : Option (PrimeFieldRef p)` | Interpret all bytes as a big-endian Nat n, then accept precisely n<p as `some` with original n; otherwise `none`; no consumer length guard or outcome adapter | `ofBytesBE?_eq_some_iff`; all-input ordinary proof and complete finite controls; **discharged** |
| R2/R8/R10 / §5 reference observer API | `PrimeFieldRef.ofBytesBE?_eq_some_iff (b) (a)` | `ofBytesBE? b = some a ↔ Uint.ofBeBytes (Bytes.ofByteArray b) < p ∧ a.toNat = Uint.ofBeBytes (Bytes.ofByteArray b)` (Base-qualified providers) | Ordinary iff, without a primality/width/metadata premise; **discharged** |

There is no original unbounded all-width field helper: generic checked semantics are
mathematical support. Normal KZG asserts range before the original U256-derived
BLSFieldElement constructor; optimized execution omits that assertion and returns four
noncanonical values in the finite corpus. Only admitted-value agreement is claimed
for optimized KZG, with all four actual differences retained. BLS first rejects lengths
other than 64, then decodes, then checks range before FQ construction. A wrong-width
zero may therefore be accepted by this generic helper while rejected by the original
consumer. The exact-width premises, original exception payloads and first consuming
handler/outcome mapping remain consumer-owned; no new guest fault or O row is supplied.

Private facade-only `ReferenceDecodeCallerProofs.lean` derives complete rejection iff,
successful original-value/range, equality for identical positional Nats, empty/all-zero
canonical zero, leading-zero preservation and metadata irrelevance of `Option.map toNat`.
Clients use public laws without unfolding foreign semantic definitions or inspecting
carrier projections. Differently parameterized carriers are never equated. Encoding,
paired roundtrip/size and undersized-width behavior remain open.

## 4. Tests

Private facade-only `ModuliCallerProofs.lean` checks all eight exact `Nat` types and
complete literal equalities by ordinary reflexivity. `ModuliGuards.lean` compares
all eight labelled full values, distinguishes every base/scalar pair, checks bit
lengths `254/254/381/255/256/256/256/256`, all values `>1` and `<2^384`, the seven
non-BLS-base values `<2^256`, and base/scalar residues `3`/`1` modulo four.
Complete interpreted and native facade-only observations independently agree with
all eight source-derived values, labels, bit lengths and mod-four residues.
These elementary finite checks establish no primality theorem or field instance.

The supplied reference slice has private full-result guards in
`STFSpec/Conformance/Field/ReferenceGuards.lean`: 42 input/modulus rows, each under
`none`, `some 0`, and `some (2^4096+17)` metadata (126 complete controls), plus all
6×6 actual equality matrices for each of the seven moduli under all three metadata
choices (756 pair entries). Moduli are 2, 3, 4, 9, 15, 17 and `2^127−1`; inputs
are `0,p−1,p,p+1,2p+3,2^4096+17`. Independent literal residues include 6 modulo 9
and 4294967313 modulo `2^127−1` for the huge input. Each row checks canonical range,
full optional checked value, actual equality with the canonical and shifted constructor,
next-residue inequality, zero/one recognition, complete default and canonical Nat Repr.
These are pure reference controls, not EEST execution, a field theorem or cost evidence.
Actual facade-importing `lake env lean --run` observations on 2026-10-29 match all
126 complete catalogue rows and 756 pairwise entries. For each metadata choice, the
42 shared FQ observations and 252 pairwise entries agree with the authenticated original
synthetic-class observations in normal and optimized CPython runs. Checked results and
arbitrary metadata remain mathematical/Lean-only controls; zero original checked-helper
executions are claimed. The target execution mode is interpreted, not a native cost run.

The arithmetic slice adds `ReferenceArithmeticGuards.lean`: all 649 ordered canonical
pairs for p=2,3,4,5,9,15,17 under three metadata choices (1,947 complete controls),
plus all 49 ordered pairs of `0,1,p−1,p,p+1,2p+3,2^4096+17` for each modulus and metadata
(1,029 controls). Each checks the named operations, signed-Int subtraction/negation,
operator delegation, zero recognition, canonical ranges and cancellation. Three additional
literal controls distinguish the p4 zero divisor, p5 wrapping subtraction and all four
p9 operations (2,4 gives add6/sub7/neg7/mul8).

On 2026-10-29, an independently frozen 2,005-row catalogue was replayed against original
locked py-ecc 8.0.0 in normal and optimized CPython modes. Its 19 contexts are seven complete
small-modulus contexts, ten larger synthetic contexts (257, 2^127−1 and the eight R1 values),
and the two actual original named BN254/BLS base FQ classes. R1 values bind by authenticated
source literals; synthetic scalar/secp/P256 contexts do not assert original named scalar
classes or execute EELS curve/KZG globals. Complete raw natural inputs, up to 8,192 bits,
enter original constructors unreduced, verified by actual constructor-entry receipts.

Facade-importing interpreted and native target runs each observe all 2,005 inputs under
`none`, `some 0` and `some (2^4096+17)` metadata: 6,015 complete target rows per execution
mode. Every ID/context/kind/modulus/raw input/canonical operand and add/sub/neg/mul/strict Bool
zero result, plus all four notation results, agrees with both complete original streams.
Each target run has 840 true and 5,175 false zero observations. The original wheel, pinned
EELS source/lock, loaded methods, interpreter and unchanged source/venv manifests were
independently authenticated; an owned-copy original replay repeats both whole streams.
These are finite reference-arithmetic correctness observations under the stated typed and
host-runtime premises, without a universal source theorem, cost or EEST/guest claim.

The power slice adds private `ReferencePowerGuards.lean` controls: 1,621 complete
raw-base/exponent rows, each under `none`, `some 0` and `some (2^4096+17)` metadata
(4,863 controls). Moduli are 2,3,4,5,6,8,9,15,17; bases are 0,1,p−1,p,p+1 and
2^4096+17, plus the explicit p4/base2/exponent4 nonunit witness.
Exponents include zero/one, adjacent bit boundaries through 255 bits,
and 2^256+1. Every row checks actual canonical base, full named and notation values
and range. The p4/base2/exponent4 result is zero; exponent reduction modulo p−1
would incorrectly give two. These finite controls supplement the universal proof.

On 2026-10-29, complete facade-importing interpreted and native target observations
each cover all 16,232 independently frozen source inputs under all three metadata
choices (48,696 rows per mode). All raw-base/exponent/id/context/kind/family/group/
label/modulus fields, metadata, actual canonical base and both named/notation residues
agree with both complete original normal/optimized streams and fresh whole-stream
original replays. The 22 contexts comprise 18 synthetic small-modulus classes across
ordinary and optimized FQ families and four actual original BN254/BLS12-381 base
classes. Ordinary FQ observations broaden finite evidence without adding an optimized
FQ contract. Only successfully constructed natural, same-class source operands are
claimed; no signed/mixed/mutated source domain is added.

The source packet, actual pinned Git blobs/modes, locked py-ecc 8.0.0 wheel members,
loaded original methods and Python runtime are authenticated; before/after source and
venv manifests agree. Strict parsed type identity rejects Bool-as-int equivalence.
Target results come from executing the facade API, separately in interpreted and
native modes; inputs contain no expected results. Kernel proof, finite source execution
and compiled observations remain distinct. Compiler/loader/core-runtime and exact
bignum assumptions remain explicit; original import raises the recursion limit.
These controls establish no universal Python host completion/resource result, cost,
precompile, guest or EEST conformance claim. The 16,232-input comparison, its frozen
catalogue, the original streams and the interpreted/native adapter are out of tree: no
harness or data for them is committed, so they are recorded observations that cannot
be reproduced from this repository. The in-tree checks are the 4,863 finite controls
and the public-law clients.

The sign slice adds private `ReferenceSignGuards.lean`: 315 complete
raw/canonical/Bool rows, each under `none`, `some 0` and `some (2^4096+17)` metadata
(945 controls). They exhaust canonical residues for p=2,3,4,5,6,8,9,15,17 and cover
zero, one, p−1, raw wraps, the p3/raw4 parity trap and adjacent bit boundaries through
2048 bits; four further rows check p−1 and p−2 in the BN254 and BLS12-381 base fields
through the public modulus constants. All Boolean outcomes are literal, and every other
expected residue is literal.

On 2026-10-30, fresh facade-importing interpreted and native target executions each
observe every one of the independently frozen 766 natural source inputs under all
three metadata choices (2,298 complete rows per mode). Complete id/context/kind/
family/group/label/p/raw input, metadata, canonical observation and explicitly encoded
Bool sign agree with both complete original normal/optimized streams and fresh
unchanged-producer replays. Eleven source contexts are the nine synthetic moduli
above and the actual original optimized BN254/BLS12-381 base classes. No generated
expected result is substituted for a target observation.

The frozen input-only stage predates original body/import/runtime observation.
Both source packets, actual pinned EELS Git blobs/modes, the locked py-ecc 8.0.0
wheel and installed members, original loaded methods and fresh owning-source
compilations, interpreter and source/venv identity are authenticated. Strict parsed
types reject Bool where a Nat is required. A fresh trust-zero, warnings-fatal closure
checks the leaf, facade and all old/new Field clients; separately generated C,
objects, archive, link and execution receipts bind the native observations to that
fresh source closure. Source host/runtime/core-primitive and compiler/loader
assumptions remain explicit: finite successful executions and the ordinary Lean
law establish no universal Python host/resource completion, C1–C4 cost, actual
curve/precompile composition, guest or EEST result. These sign comparisons, their
frozen inputs, the original streams and the interpreted/native adapter are out of tree:
nothing for them is committed, so they are recorded observations that cannot be
reproduced from this repository. The in-tree checks are the 945 controls and the
public-law clients.

The checked-decoder slice adds private `ReferenceDecodeGuards.lean` literal controls
and full facade-importing observations of the 762 independently frozen labelled rows
(665 distinct `(p, bytes)` inputs),
each under none, some 0 and some (2^4096+17) metadata (2,286 complete rows per mode).
Interpreted and fresh native observations compare complete IDs/groups/p/bytes/labels,
metadata and optional natural values against independent Horner and positional-sum
strict-admission models. Controls distinguish BE/LE, p−1/p/p+1, zero/one, some zero/none,
empty/leading zeros, asymmetric/reversed bytes and lengths 0/1/31/32/33/48/63/64/65/128/512,
long zero versus overflow, actual BLS q/r boundaries and p=2/3/4/9/17.

All 97 genuine original typed wrapper inputs (10 exact-32 KZG and 87 BLS byte inputs)
are retained from all four authenticated source streams and four fresh unchanged-producer
replays. The 665 generic-labelled rows make no original-call claim (97 of those same
inputs also have wrapper-labelled rows).
Normal KZG gives six successes and four empty-args AssertionErrors; optimized KZG gives
ten unreduced successes, four noncanonical. Target admission agrees with normal KZG;
optimized agreement is asserted only for n<p, and all four outside-domain differences
remain explicit. BLS gives four successes and 83 InvalidParameters: 77 length failures
precede decoding, and six of the ten 64-byte cases fail range. Full target/BLS comparison
requires exactly 64 bytes. Wrong-width original results and exception payloads are retained.

Source pin/blobs/modes, both locked dependency archives and static installed members,
original loaded methods/fresh compilation/dispatch, runtime and source/venv preservation
are authenticated. A fresh trust-zero warnings-fatal recursive provider/Field/client closure
and generated C, objects, archive, link and execution receipts bind native observations.
Strict external full-row parsing rejects malformed framing/schema/order/count, duplicate
keys, floats/nonfinite numbers and Bool-as-Nat/byte/metadata/Option values in normal and
optimized readers. These finite observations retain host bignum, loader/compiler/core
primitive and source-domain premises; they prove no universal source-host completion,
resource/cost/C1–C4, actual curve/precompile composition, guest or EEST claim. These
interpreted/native comparisons, the source streams and replays, and their authentication
are out of tree: nothing for them is committed, so they cannot be reproduced from this
repository. The in-tree checks are the literal guards and the public-law clients.

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
  sqrtExp? : Option Nat        -- (p+1)/4 when p ≡ 3 mod 4, else none (unenforced; unread here)

-- LEGIBLE REFERENCE carrier (not the executable one): the Nat residue.
structure PrimeFieldRef (p : Nat) [FieldModulus p] where   -- NOT an abbrev (cf. D1)
  private mk ::
  val : Nat                                            -- internal field; use toNat
  isLt : val < p

namespace PrimeFieldRef
-- Supplied reference carrier and basic residue arithmetic (other operations remain open).
def toNat : PrimeFieldRef p → Nat
def ofNat (n : Nat) : PrimeFieldRef p
def ofNat? (n : Nat) : Option (PrimeFieldRef p)
def zero one : PrimeFieldRef p
instance : DecidableEq (PrimeFieldRef p)
instance : Inhabited (PrimeFieldRef p)  -- zero
instance : Repr (PrimeFieldRef p)       -- canonical Nat
def add sub mul : PrimeFieldRef p → PrimeFieldRef p → PrimeFieldRef p
def neg : PrimeFieldRef p → PrimeFieldRef p
def isZero : PrimeFieldRef p → Bool
def pow : PrimeFieldRef p → Nat → PrimeFieldRef p
def sgn0 : PrimeFieldRef p → Bool  -- canonical toNat parity; ordinary sgn0_eq in §7
def ofBytesBE? : ByteArray → Option (PrimeFieldRef p)  -- checked, any finite length
instance : HPow (PrimeFieldRef p) Nat (PrimeFieldRef p)  -- direct pow delegation
instance : Add, Sub, Neg, Mul (PrimeFieldRef p)  -- direct named-operation delegation
end PrimeFieldRef

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

-- Exact Nat constants supplied; concrete field aliases below remain unimplemented.
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

The eight R1 constants are immutable ordinary `Nat` literals in a separate leaf;
no field representation or runtime backend is selected by supplying those values.

| Type | Representation (executable; reference in italics) | Model | Abstraction | Invariant | Persistence | Complexity |
|---|---|---|---|---|---|---|
| `PrimeField p` | **executable:** Montgomery residue `x̃ = x·R mod p` in fixed limbs, carry-preserving CIOS needing only `p < R`: `Wide8` (8×32-bit limbs in `UInt64`, `R = 2^256`) for every modulus `< 2^256`; `W12` (12×32, same template, `R = 2^384`) for BLS12-381 `q` (prototyped; not yet in the core or upstream). *Reference:* `val : Nat` with `val < p` | residues mod `p`; `ZMod p` in `EthFieldMathlib` | executable → reference: `α x̃ = x̃ · R⁻¹ mod p`; reference → model: `toNat` (core), `toZMod` (Mathlib) | executable: `Bounded x̃ ∧ x̃.toNat < p`; reference: `val < p` | immutable value; freely shareable | executable: CIOS Montgomery multiplication, add/sub with a conditional subtraction; reference: `Nat` arithmetic with `% p` (basic residue arithmetic and binary natural powers supplied; other operations open) |
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

**Supplied constant values.** The eight `Nat` definitions in §3 have their exact
source literals as transparent bodies. Their complete equalities and elementary
bounds are checked privately; no new authored public law or instance is supplied.
Primality, square-root metadata and concrete-field/backend contracts remain open.

**Supplied reference-only laws (discharged).** In namespace `PrimeFieldRef`, with
`{p : Nat} [FieldModulus p]`, exactly fourteen ordinary public laws are supplied:

- `toNat_lt (a) : a.toNat < p`.
- `toNat_ofNat (n) : (ofNat (p := p) n).toNat = n % p`.
- `ofNat?_eq_some_iff (n) (a) : ofNat? (p := p) n = some a ↔ n < p ∧ a.toNat = n`.
- `ext {a b} (h : a.toNat = b.toNat) : a = b`.
- `toNat_zero : (zero : PrimeFieldRef p).toNat = 0`.
- `toNat_one : (one : PrimeFieldRef p).toNat = 1`.
- `toNat_add (a b) : (add a b).toNat = (a.toNat + b.toNat) % p`.
- `toNat_sub (a b) : (sub a b).toNat = (a.toNat + p - b.toNat) % p`.
- `toNat_neg (a) : (neg a).toNat = (p - a.toNat) % p`.
- `toNat_mul (a b) : (mul a b).toNat = (a.toNat * b.toNat) % p`.
- `isZero_eq (a) : isZero a = decide (a.toNat = 0)`.
- `toNat_pow (a) (e) : (pow a e).toNat = a.toNat ^ e % p`.
- `sgn0_eq (a) : sgn0 a = decide (a.toNat % 2 = 1)`.
- `ofBytesBE?_eq_some_iff (b) (a) : ofBytesBE? b = some a ↔
  STFSpec.Base.Uint.ofBeBytes (STFSpec.Base.Bytes.ofByteArray b) < p ∧
  a.toNat = STFSpec.Base.Uint.ofBeBytes (STFSpec.Base.Bytes.ofByteArray b)`.

These require only `1 < p`, retain arbitrary metadata and have no global simp
attributes. Range follows canonical construction; reduction is remainder; checked
admission branches once on range; canonical residues determine equality. Zero and one
use `1 < p`. These facts prove the carrier slice. Arithmetic construction reduces the
corresponding natural expression, so its observer equations follow directly from the
reducing constructor. Canonical bounds make subtraction/negation agree with signed
modular arithmetic. The Boolean equation determines both outcomes. Binary halving plus
modular multiplication proves the power equation on every Nat exponent; its canonical
construction gives range and `0^0 = one`. The canonical sign equation directly decides
oddness of the observation; it does not read metadata. These results assert no field for
composites or sign-change-under-negation law. Composing the public byte
ingress/unbounded decoder with checked construction gives the complete decoder iff; its
private consequences require no width or metadata hypothesis.

**Remaining contracts (unimplemented for the executable `PrimeField` API).** Per operation, the commuting equation with the `Nat` model (core) — stated once, proved once per
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

**Open obligations.** The reference carrier, basic residue arithmetic, natural powers
  canonical sign and checked byte decoding above are discharged; inverse/Euler/sqrt,
  public powMod, encoding and executable-reference bridges stay open. Prime and
  irreducibility certificates, algorithm-specific sqrt completeness/sign laws, and
  public-operation bridges remain required. The Montgomery implementation must prove
  these same observer equations relative to the `Nat` reference.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthBase`
- **Used by:** `EthCurve` directly; `EthPairing` and `EthPrecompiles` transitively (MODEXP uses
  `powMod`; KZG decoders use `Bls12381.Fr.ofBytesBE?`). `EthFieldMathlib` (Mathlib bridge package).
- **Seams.** Consumes the public `Bytes.ofByteArray`/`Uint.ofBeBytes` providers for the
  supplied reference decoder; prospective consumers also use `ByteArray`/`Bytes32`
  and `U256.toNat`/`ofNat` conversions. Provides the `PrimeField` observer contract; guarantees every value is canonical.
  The runtime source for the fast path is CompPoly's zero-import `…Defs` in the
  carry-preserving variant (D6), not CompPoly's current `2p < R` code.
  Importing it must not pull in Mathlib (the D6 Lake check found that a `require` of CompPoly
  does), so vendoring with attribution or an upstream fix and split is still undecided.

## 9. Open decisions

Supplying the eight natural moduli, reference-only binary powers, canonical sign and
checked byte decoding makes no D6 source choice and requires no D18 performance
exception; executable representations and their costs remain open.

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
  reference. The designated reference slice supplied in §3 has no production aliases or
  callers and needs no performance exception. Shipping the `Nat` form as the executable
  representation would need a D18 justification (legibility or drastic
  proof-friendliness) recorded in `STFSpec/informal/DEBT.md`.
- **D15**: if cryptography-specs' `Bls/Fp.lean` (`abbrev Fp := Fin modulus`) is reused, its
  `abbrev` must be wrapped in our `structure` to keep the abstraction barrier.
- **D1**: the boundary with `U256` (EVM inputs arrive as `U256`, converted via `toNat`).
- Fast-field plan (NEW-CRYPTO-2): width resolved, DECISIONS Q39 (Montgomery prototype); the source
  (vendor or upstream) remains with D6.

## 10. Gaps

- **Bounded supplied status.** §3/§7 discharge the reference carrier's initial five
  operations/six laws/three instance families and basic add/sub/neg/mul/isZero, five
  observer laws and four delegating operator instances, plus natural pow/toNat_pow and
  its delegating HPow instance, plus canonical sgn0/sgn0_eq and checked
  ofBytesBE?/ofBytesBE?_eq_some_iff; private controls and
  clients cover those slices. The eight exact R1 natural moduli are supplied separately;
  concrete-field instances/aliases, convenience aliases, byte encoding and paired
  roundtrip/size laws, powMod, inverse, Euler/sqrt, towers, executable
  PrimeField/Montgomery and their bridges remain unimplemented. No D6 source choice,
  primality/Mathlib result, replacement/C1–C4 measurement, whole-module, precompile,
  signature, guest or EEST readiness claim follows.

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
