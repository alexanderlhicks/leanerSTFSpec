# `EthPairing`: BN254 and BLS12-381 pairings, pairing checks and KZG verification

*Status: informal specification, draft. Date: 2026-09-29. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F16 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D6, D7, D12, D15, D18, D21 · questions: B13/Q40/Q42, Q39, Q44, Q45.*

Tags: **[V]** verified against pinned source or by running the pinned dependency; **[I]**
inference, not yet checked. Line numbers without a path refer to `src/ethereum/crypto/kzg.py`;
`py_ecc` paths are relative to `site-packages/py_ecc/` (py-ecc 8.0.0).

## 1. Purpose

`EthPairing` defines the reduced Tate-style (optimal ate) pairings of BN254 and BLS12-381, the
multi-pairing **check** "the product of pairings equals one" used by ECPAIRING (EIP-197) and
BLS12_PAIRING_CHECK (EIP-2537), and single-point KZG proof verification (`verify_kzg_proof`,
EIP-4844) with its input validation. It is layer L0 (ARCHITECTURE §2), the top of the crypto
stack, used only by `EthPrecompiles`. Per the isolation rule (ARCHITECTURE §5.2) no opcode proof depends on it.
Its public contract is a **predicate**: callers observe pairings only through `pairingCheck` and
`verifyKzgProof`, which lets the internal pairing algorithm change freely (R3).

## 2. Requirements

**R1. BN254 pairing** (`optimized_bn128/optimized_pairing.py:228–243`) [V]:
`pairing(Q, P)` with `Q ∈ E'(Fq2)`, `P ∈ E(Fq)`, argument order (G2, G1). It raises `ValueError`
if either point is off its curve (callers have already checked, `alt_bn128.py:80`, `:134`), returns
`FQ12.one()` if either is infinity, and otherwise runs the optimal-ate Miller loop on the untwisted
`Q` (loop count `29793968203157093288 = 6u + 2`, signed-digit encoding with `±1`, two Frobenius
correction lines `Q₁`, `−Q₂`) followed by `f^((q¹² − 1)/r)` as a plain exponentiation.

**R2. BLS12-381 pairing** (`optimized_bls12_381/optimized_pairing.py:183–246`) [V]: same
interface; Miller loop over `|x| = 0xd201000000010000` (binary, no `−1` digits, no Frobenius
lines, no conjugation for the negative sign of `x`); `f = f_num / f_den`; final exponentiation by
the easy part (`p⁶ − 1`, `p² + 1` via Frobenius tables) and then `^((q⁴ − q² + 1)/r)`. Because the
sign of `x` is ignored, `py_ecc`'s value may be the inverse of the textbook optimal ate pairing
[I]; R3 makes this unobservable.

**R3. Observability and admissible pairings.** The EVM observes pairings **only** through:
- ECPAIRING: `∏ᵢ pairing(Qᵢ, Pᵢ) = 1` (each factor fully reduced, `alt_bn128.py:220–237`) [V];
- BLS12_PAIRING_CHECK: the same over BLS12-381 (`bls12_381_pairing.py:50–70`) [V];
- KZG: `final_exponentiate(ML(Q₁, P₁) · ML(Q₂, P₂)) = 1`, one final exponentiation of the product
  of Miller loops (`:115–124`) [V].

Every point reaching these checks is in the order-`r` subgroups G1 and G2 (subgroup checks in
`alt_bn128.py:227–230`, `bls12_381_pairing.py:57`, `:62`; `KeyValidate` for KZG, R6; fixed
generators; the setup constant, R7). If `e` and `e'` are non-degenerate bilinear maps
`G1 × G2 → μ_r` with `G1`, `G2` cyclic of prime order `r`, then `e' = e^c` for some `c` coprime to
`r` [I: standard; to be proved in `EthPairingMathlib`], so `∏ e'(Pᵢ, Qᵢ) = 1 ↔ ∏ e(Pᵢ, Qᵢ) = 1`.
**Subject to Q40 and after proving these premises for both the reference and replacement, the spec may use a different non-degenerate bilinear pairing** (for example
cryptography-specs' tower-based optimal ate, or a version with the sign fix), provided the
pairing-check functions are stated and proved as predicates. Reproducing `py_ecc`'s exact `Fq12`
values is *not* required, but it is useful for differential debugging.

**R4. Infinity.** A pair with either point at infinity contributes `1` (R1, R2). The empty input
is handled by the caller (ECPAIRING accepts it and returns 1; EIP-2537 rejects it before
pairing).

**R5. `verify_kzg_proof(commitment, z, y, proof)`** (`:127–149`) must:
1. assert the four byte lengths `48, 32, 32, 48` (`:139–142`); always true from
   `point_evaluation`, which slices a 192-byte input (`point_evaluation.py:44–51`) [V];
2. validate the commitment (`bytes_to_kzg_commitment`, `:88–93`), then `z` and `y`
   (`bytes_to_bls_field`, `:96–104`, owned by `EthField`), then the proof (`:107–112`); argument
   evaluation order is commitment, z, y, proof, and **all failures are `AssertionError`s**, which
   the caller maps to one error (`point_evaluation.py:59–62`), so the order is unobservable;
3. compute (`verify_kzg_proof_impl`, `:152–176`)
   `X − z := [τ]G2 + [(r − z) mod r]G2`, `P − y := C + [(r − y) mod r]G1`, and return
   `FE(ML(−G2, P − y) · ML(X − z, π)) = 1`, i.e. `e(C − [y]G1, −G2) · e(π, [τ − z]G2) = 1`.

**R6. G1 validation for KZG** (`validate_kzg_g1`, `:77–85`) [V]: accept iff the 48 bytes equal
`G1_POINT_AT_INFINITY = 0xc0 ‖ 0⁴⁷` exactly, or `KeyValidate` succeeds (`EthCurve` R9:
decompresses, is not infinity, is in G1). Hence the only accepted infinity encoding is the
canonical one; `0xe0…` and non-zero-padded infinity encodings are rejected.

**R7. Trusted-setup constant.** `[τ]G2 = signature_to_G2(KZG_SETUP_G2_MONOMIAL_1)` (`:62`,
`:164`), decompressed from the 96-byte hex constant on every call, without a subgroup check [V].
The spec defines it as a constant `G2` point with a `#guard`/theorem that it equals the
decompression of the EELS bytes, and records that its subgroup membership and its agreement with
the ceremony's `g2_monomial[1]` are *setup assumptions*, not checked by EELS.

**R8. Totality.** Miller loops iterate over fixed digit lists; exponentiations recurse on bits;
nothing is `partial` (contrast cryptography-specs `partial def millerLoop`,
`Bls/Pairing.lean:130` [V]). `verifyKzgProof` returns `Except KzgError Bool`: `.error` exactly
where EELS raises, `.ok false` where the pairing check fails.

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `crypto/kzg.py::KZGCommitment` | 30 | `Kzg.KZGCommitment` (validated: bytes + decoded point) | EELS type is unvalidated `Bytes48`; validation by R6 |
| `crypto/kzg.py::KZGProof` | 36 | `Kzg.KZGProof` | as above |
| `crypto/kzg.py::BYTES_PER_COMMITMENT` | 55 | `Kzg.bytesPerCommitment = 48` | |
| `crypto/kzg.py::BYTES_PER_PROOF` | 56 | `Kzg.bytesPerProof = 48` | |
| `crypto/kzg.py::G1_POINT_AT_INFINITY` | 58 | `Kzg.g1PointAtInfinity : ByteArray` | `0xc0 ‖ 0⁴⁷` |
| `crypto/kzg.py::KZG_SETUP_G2_MONOMIAL_1` | 62 | `Kzg.setupG2Monomial1Bytes`, `Kzg.tauG2 : Bls12381.G2Proj` | R7 |
| `crypto/kzg.py::validate_kzg_g1` | 77 | `Kzg.validateKzgG1 : ByteArray → Except KzgError Bls12381.G1Proj` | R6 |
| `crypto/kzg.py::bytes_to_kzg_commitment` | 88 | `Kzg.bytesToKzgCommitment` | |
| `crypto/kzg.py::bytes_to_kzg_proof` | 107 | `Kzg.bytesToKzgProof` | |
| `crypto/kzg.py::pairing_check` | 115 | `Bls12381.pairingCheckMiller : (G1Proj × G2Proj) → (G1Proj × G2Proj) → Bool` | one final exponentiation |
| `crypto/kzg.py::verify_kzg_proof` | 127 | `Kzg.verifyKzgProof : ByteArray → ByteArray → ByteArray → ByteArray → Except KzgError Bool` | R5 |
| `crypto/kzg.py::verify_kzg_proof_impl` | 152 | `Kzg.verifyKzgProofImpl : KZGCommitment → Bls12381.Fr → Bls12381.Fr → KZGProof → Bool` | |

The KZG items owned elsewhere: the versioned-hash items (need SHA-256) are in `EthPrecompiles`;
the scalar-field items are in `EthField`; the point-type aliases are in `EthCurve`.

**External semantics** to specify:
- `py_ecc.optimized_bn128.optimized_pairing.pairing` (R1) — as a pairing satisfying R3;
- `py_ecc.optimized_bls12_381.pairing` and
  `py_ecc.optimized_bls12_381.optimized_pairing.{pairing, final_exponentiate}` (R2, R5);
- `py_ecc.optimized_bls12_381.FQ12` / `py_ecc.fields.optimized_bls12_381_FQ12` `one()` and
  equality (via `EthField`);
- `py_ecc.optimized_bls12_381.{add, multiply, neg}`, `optimized_curve.{G1, G2}` (via `EthCurve`);
- `py_ecc.bls.G2ProofOfPossession.KeyValidate`, `g2_primitives.{pubkey_to_G1, signature_to_G2}`
  (via `EthCurve` R9).

## 4. Tests

- **EEST fixture areas:** `byzantium/eip197_ec_pairing` (11 files: `ecpairing/{valid,invalid,fail,gas}`,
  `ecpairing_fuzzed/{positive,negative,invalid_g1_point,invalid_g2_point,invalid_g2_subgroup}`),
  `prague/eip2537_bls_12_381_precompiles/bls12_pairing/*` (6 files including `valid_multi_inf`,
  `invalid_multi_inf`), `bls12_variable_length_input_contracts/*pairing*`,
  `cancun/eip4844_blobs/point_evaluation_precompile/{valid_inputs,invalid_inputs,external_vectors,call_opcode_types,tx_entry_point}.json`
  and `point_evaluation_precompile_gas/*`. `external_vectors` are the go-kzg-4844 vectors
  (`tests/cancun/eip4844_blobs/point_evaluation_vectors/go_kzg_4844_verify_kzg_proof.json`) [V].
- **EELS unit tests:** none for pairings or KZG at e1a316a0 [V].
- **`core` `#guard` cases** (F16: a `#guard` or `decide` cannot evaluate a term that reaches a `sorry` leaf, so each guard runs only once the pairing and curve operations it reaches are implemented):
  - typical: `pairingCheck [(G1, G2), (−G1, G2)] = true`; `pairingCheck [(G1, G2)] = false`
    (non-degeneracy sample); `e(aP, bQ) = e(P, Q)^{ab}` for small `a, b`; the go-kzg vectors
    and the EIP-2537 `pairing_check_bls.json`/`fail-pairing_check_bls.json` vectors;
  - edge: empty list; pairs with infinity on either side; all pairs infinity; KZG with
    commitment `= proof = ∞`, `y = 0`, any `z` (the zero polynomial; must be `true`);
    `z = r − 1`, `y = 0`; `tauG2` equals the decompressed setup bytes;
  - adversarial: KZG commitment/proof that is on the curve but outside G1; non-canonical infinity
    encodings; `z = r`, `y = 2^256 − 1`; a Miller-loop input where a line denominator vanishes
    (`linefunc` vertical-line branch, `optimized_pairing.py:131–146`).
- **Differential checks (bug-finding):** predicate-level against `py_ecc` for random subgroup
  points and random multi-pairings (and exact `Fq12` values if the `py_ecc` algorithm is
  mirrored); against cryptography-specs `Bls/Pairing.lean` `pairingCheck` and `Kzg/Core.lean`
  `verifyKzgProof`; against c-kzg (`ckzg` 2.1.5 is in `uv.lock` but not imported by `src/` [V,
  reference.toml]) for `verify_kzg_proof`.

## 5. Interface

Public unless marked internal. Namespaces `STFSpec.Pairing.*`.

```lean
namespace Bn254
def millerLoop : G2Proj → G1Proj → Fq12                 -- internal
def finalExponentiate : Fq12 → Fq12                      -- executable: easy part + hard part (§6)
def finalExponentiateReference : Fq12 → Fq12             -- legible reference: f ^ ((q^12 - 1) / r)
def pairing (Q : G2Proj) (P : G1Proj) : Fq12             -- 1 if either is infinity
def pairingCheck : List (G1Proj × G2Proj) → Bool         -- ∏ pairing Qᵢ Pᵢ = 1 (empty → true)
end Bn254

namespace Bls12381
def millerLoop : G2Proj → G1Proj → Fq12                 -- internal
def finalExponentiate : Fq12 → Fq12                      -- executable: easy part + hard part (§6)
def finalExponentiateReference : Fq12 → Fq12             -- legible reference: plain power
def pairingReference (Q : G2Proj) (P : G1Proj) : Fq12    -- exact value, for raw-value consumers
def pairing (Q : G2Proj) (P : G1Proj) : Fq12
def pairingCheck : List (G1Proj × G2Proj) → Bool
def pairingCheckMiller (a b : G1Proj × G2Proj) : Bool    -- EELS kzg.pairing_check shape
end Bls12381

namespace Kzg
def bytesPerCommitment bytesPerProof : Nat               -- 48
def g1PointAtInfinity : ByteArray                        -- 0xc0 ‖ 0^47
def setupG2Monomial1Bytes : ByteArray                    -- 96 bytes, from EELS hex
def tauG2 : Bls12381.G2Proj                              -- R7
inductive KzgError | badLength (what : String) | invalidG1 (e : CompressError) | notInSubgroup
                   | infinityNotCanonical | fieldElementTooLarge
structure KZGCommitment where                            -- validated
  bytes : ByteArray
  point : Bls12381.G1Proj
  -- invariant (proof field or separate predicate): validateKzgG1 bytes = .ok point
structure KZGProof where bytes : ByteArray; point : Bls12381.G1Proj
def validateKzgG1 : ByteArray → Except KzgError Bls12381.G1Proj
def bytesToKzgCommitment : ByteArray → Except KzgError KZGCommitment
def bytesToKzgProof : ByteArray → Except KzgError KZGProof
def verifyKzgProofImpl : KZGCommitment → Bls12381.Fr → Bls12381.Fr → KZGProof → Bool
def verifyKzgProof (commitment z y proof : ByteArray) : Except KzgError Bool
end Kzg
```

`CompressError` and the point types come from `EthCurve`; `Bls12381.Fr.ofBytesBE?` from
`EthField`. Storing the decoded point in `KZGCommitment` avoids EELS's second decompression
(`pubkey_to_G1` at `:168`, `:174`); the invariant makes this unobservable.

## 6. Data structures

| Type | Representation | Model | Abstraction | Invariant | Persistence | Complexity |
|---|---|---|---|---|---|---|
| `Fq12` accumulators | tower (`EthField`) | `Fq12` field | `EthField` | canonical | immutable, local | Miller loop BN254 ≈ 64 iterations (+2 Frobenius lines), BLS12-381 63 iterations; each an `Fq12` squaring, a line evaluation and a multiplication |
| Miller state `(T, f_num, f_den)` | `G2Proj`, two `Fq12` (py_ecc keeps a separate denominator) | `f_{s,Q}(P)` up to `Fq*` factors killed by the final exponentiation | — | `T = s'·Q` for the processed prefix `s'` | local | inversion only once at the end |
| final exponentiation | **executable:** (1) **easy part** `f^((q⁶−1)(q²+1))`, computed as `conj(f) · f⁻¹` followed by a `q²`-Frobenius and a multiplication; (2) **hard part** `(q⁴ − q² + 1)/r`, computed by the curve family's decomposition in the curve parameter `u`: for BLS12-381, Hayashida, Hayasaka & Teruya, [ePrint 2020/875](https://eprint.iacr.org/2020/875); for BN254, Scott et al., [ePrint 2008/490](https://eprint.iacr.org/2008/490). Squarings inside the hard part use cyclotomic squaring (Granger & Scott, [ePrint 2009/565](https://eprint.iacr.org/2009/565)). *Reference:* the plain power `f^((q¹²−1)/r)` | `f^((q¹²−1)/r)` | exact-chain equality; a fixed-power chain requires the Q40 predicate replacement gate below | — | — | reference: BN254 plain exponent ≈ 2 794 bits [V: arithmetic]; executable: a few hundred `Fq12`/cyclotomic operations [I] |
| `KZGCommitment`, `KZGProof` | bytes + decoded point | point in G1 | `point` | `validateKzgG1 bytes = .ok point` | immutable | one decompression + subgroup check (≈ 255 doublings) each |
| `tauG2` | constant | a G2 point | — | on curve; in G2 (assumed, R7) | shared constant | computed once (or a literal) |

Legibility and performance (D18, D21, `CONTRIBUTING.md` §4): the executable
`finalExponentiate` is the two-part algorithm in the table, and the plain power is kept beside it
as the legible reference. `@[csimp]` is banned.

**Domain and observation contracts.**
- **Zero.** `f = 0` lies outside the multiplicative group, and so outside the cyclotomic subgroup. The executable handles it explicitly *before* the easy part: `finalExponentiate 0 = 0`, matching the reference (`0^e = 0` for `e > 0`). The two-part algorithm (inversion, cyclotomic squaring) is applied only to `f ≠ 0`. Valid pairing inputs never produce a zero Miller-loop output [I], but the function must be total and correct on every `Fq12`.
- **Target subgroup.** For `f ≠ 0`, the reference result lies in `μ_r = {x | x^r = 1}`, since `(f^((q¹²−1)/r))^r = f^(q¹²−1) = 1`. The predicate argument below relies on that membership.
- **Raw pairing values.** Consumers that need the *value* of a pairing, as opposed to the check "the product equals one", use `pairingReference`/`finalExponentiateReference`, which are always exact. The executable `pairing`/`finalExponentiate` are guaranteed only as the applicability conditions state.

**Applicability conditions** (implementer to verify against the cited papers):
1. **Cyclotomic squaring** is valid only on elements of the cyclotomic subgroup, that is, *after* the easy part. It must never be applied to a raw Miller-loop output.
2. **Exact or a fixed power.** Some published hard-part chains compute a fixed power `c` of the exact result to avoid a division in the exponent decomposition; check which the chosen chain does. If it is a power, `c` must be a **single constant, independent of the input**, with `gcd(c, r) = 1`.
   - **Exact:** the refinement obligation [F] is executable = reference.
   - **Fixed power:** the executable is *not* equal to the reference. It is a proposed replacement, subject to Q40, because the working public contract is the pairing-*check* predicate (R3: "the product equals one"; NEW-CRYPTO-3, DECISIONS B13). The obligation is then that the predicate agrees, via `x^c = 1 ↔ x = 1` in a group of order `r` when `gcd(c, r) = 1`. Any consumer of raw pairing values must use the reference.
3. **Performance** is to be confirmed by measurement, including allocation and tower conversions, with no checksum inside the timed loop ([REVIEW §7](../REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks) C1–C4), not by the algorithm's name alone.

## 7. Contract and laws

- [C] `pairingCheck l = true ↔ ∏_{(P,Q) ∈ l} pairing Q P = 1` (definition), and
  `pairingCheckMiller a b = pairingCheck [a, b]` (final exponentiation is a monoid
  homomorphism).
- [C] **Bilinearity and non-degeneracy** of `pairing` on `G1 × G2` (in `EthPairingMathlib`):
  `pairing (b • Q) (a • P) = pairing Q P ^ (a·b)` and `pairing Q₀ P₀ ≠ 1` for the generators;
  `pairing Q P ^ r = 1`.
- [C] **Predicate independence** (R3): for any other non-degenerate bilinear `e'`, the two
  `pairingCheck`s agree on subgroup inputs. This is the law that lets the implementation be
  replaced (ARCHITECTURE §4, replacement procedure) and lets consumers state pairing results without naming
  the Miller loop.
- [C] `verifyKzgProof c z y π = .ok b ↔` every input validates, and then
  `b ↔ e(C − [y]G1, G2) = e(π, [τ − z]G2)` (rearranged from R5 by bilinearity).
- [C] **KZG completeness**: if `C = [p(τ)]G1`, `y = p(z)` and `π = [(p(X) − y)/(X − z)](τ)·G1`,
  then `verifyKzgProof` returns `.ok true` (needs bilinearity and the setup assumption that the
  G1 powers used by the committer and `tauG2` share `τ`).
- [T] total, fixed iteration counts.
- [F] `finalExponentiate` ≡ `finalExponentiateReference` if the chosen hard-part chain is exact; otherwise agreement of the pairing-check predicate (applicability condition 2, §6). Tower ≡ flat `Fq12` (EthField R4).
- [S] (statements, `EthPairingMathlib`/`EthSecurity`): KZG evaluation binding under the
  `q`-SDH assumption with `q = 4096` (`FIELD_ELEMENTS_PER_BLOB`), for a setup whose `τ` is unknown
  to the adversary (the ceremony's 1-of-n honesty). Nothing is claimed for EIP-2537 or EIP-197
  beyond mathematical correctness.

**Derived laws** used by `EthPrecompiles`: "pairing check of a list is invariant under
permutation, under removing pairs with infinity, and under `(P, Q), (−P, Q) ↦ []`".

### Informal correctness argument

**Claim.** The default pairing/KZG implementation reproduces the pinned algorithms and their accepted byte-level inputs. Replacing its pairing convention preserves the product-equals-one predicate only under the additional pairing laws below.

**Premises.** Valid curve/subgroup inputs, EthField and EthCurve laws, exact Miller-loop constants/twists, and, for convention independence, bilinearity and nondegeneracy on the same cyclic prime-order groups.

**Argument.** Maintain the Miller-loop invariant relating the processed scalar prefix, its current curve point and accumulated line-function numerator/denominator. Doubling, addition and the terminal Frobenius lines extend that prefix according to the pinned algorithm. Final exponentiation branches on the chosen hard-part chain. **Exact chain:** the executable equals the reference exponent in the target field (value refinement), and multiplication preservation follows from exponentiation. **Fixed-power chain** (`c` constant, `gcd(c, r) = 1`): the executable equals `reference^c`, so only the *predicate* refines: for `f ≠ 0` both results lie in `μ_r`, where `x ↦ x^c` is a bijection fixing `1`, so `executable f = 1 ↔ reference f = 1`. `f = 0` is handled separately, before either part. This proves algorithm correspondence separately from bilinearity. If both pairings are bilinear and nondegenerate, choose generators: their values are primitive r-th roots differing by a nonzero exponent c modulo r. Every product for one convention is the c-th power of the other, hence equals one exactly when the other does. KZG completeness follows from p(τ) − p(z) = (τ−z)q(τ) and the pairing equation, after decoding, subgroup and setup checks. That identity establishes completeness, not KZG binding security.

**Open obligations.** The Miller invariant and concrete bilinearity/group-order proofs have no completed Lean proof route. Tests cannot discharge the convention-independence premises. Alternative pairings must remain unavailable until predicate equivalence is proved.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthCurve`
- **Used by:** `EthPrecompiles` (ECPAIRING, BLS12_PAIRING_CHECK, POINT_EVALUATION);
  `EthPairingMathlib`; `EthSecurity` (KZG assumptions: the D12 (iii) statements live there, DECISIONS Q44).
- **Seams.** Consumes `EthCurve`'s point types, group laws and `EthCurve.Bls12381.G1.keyValidate`,
  and `EthField`'s `Fq12` and `Fr` decoding. Guarantees the predicate contract R3; callers must
  pass only subgroup points to `pairingCheck` (the precondition under which R3 holds) —
  `EthPrecompiles` discharges it by its subgroup checks.

## 9. Open decisions

- **D15** (BLS12-381/KZG reference): cryptography-specs has a Lean BLS12-381 pairing and KZG, but
  on Lean v4.29.1 with Mathlib required at package level, with `partial def millerLoop` and
  `partial def powNat` (`Bls/Pairing.lean:130`, `Bls/Fp2.lean:64`, `Bls/Fp12.lean:65`), `get!`
  and a `KzgM` monad that loads the whole trusted setup (`Kzg/Core.lean:153–168`) [V]; its proof
  library uses `native_decide` (banned here, CONTRIBUTING §4) in `Proofs/Bls/Compress.lean:319`
  [V]. Adoption requires vendoring and rewriting those parts.
- **D6**, **D7**: field and coordinate representations dominate pairing cost. The field width is
  settled (carry-preserving `W12` for BLS12-381 `q`, `Wide8` for BN254 `q`; DECISIONS Q39, `EthField` §6).
- **D12** (accepted): (ii) bilinearity/KZG completeness in `EthPairingMathlib`; (iii) the KZG binding statement in `EthSecurity` (DECISIONS Q44).
- **D18** (accepted), **D21** (accepted): plain-power final exponentiation is kept only as the legible
  reference; it is not performance-appropriate as the executable definition. The executable
  definition is the easy/hard-part algorithm. Exact chains require equality to the reference; a fixed-power replacement requires Q40 to be settled and its predicate equivalence proved (§6).
- **Open: pairing contract as a predicate** (R3; NEW-CRYPTO-3, DECISIONS B13/Q40): scheduled, not
  settled. B13 recommends the predicate, and this spec is written to it.
- **Open: trusted-setup provenance** (NEW-CRYPTO-5, DECISIONS B13/Q42): scheduled, not settled. R7's
  pinned constant, `#guard`-checked against the EELS bytes, is the working choice; the alternative
  is a check against the ceremony transcript (cryptography-specs `Kzg/TrustedSetupData.lean`).
- Reuse conditions for cryptography-specs (NEW-CRYPTO-8): DECISIONS Q45, with D15.

## 10. Gaps

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **No pairing theory in Mathlib** [V: no pairing development under `AlgebraicGeometry/EllipticCurve`
  at v4.34.0]. Bilinearity and non-degeneracy of a Miller-loop pairing have **no known proof
  strategy** within current Mathlib (no divisors on curves, no Weil reciprocity). Until then,
  [C] results that need them (predicate independence, KZG completeness) are conditional on an
  explicit unproved hypothesis; tests provide evidence but cannot discharge it.
- **No BN254 Lean reference** anywhere (cryptography-specs is BLS12-381 only; CompPoly has only
  the BN254 scalar field) [V]. BN254 Miller loop, twist, Frobenius constants are all to be written.
- **`py_ecc` BLS12-381 sign convention** (R2) is inferred, not checked; it matters only for
  exact-value differential tests.
- **Speed is unmeasured.** The "seconds per pairing" guess for a pure-Lean `Nat` pairing
  is not a measurement and predates the Montgomery backend
  (`EthField` §6); no pairing has been timed on `Wide8`/`W12`. EIP-2537, EIP-197 and point-evaluation fixtures may dominate
  conformance runtime (the number of pairings in the corpus has not been counted).
- **Setup assumptions** (R7) are unstated upstream: EELS never checks `[τ]G2 ∈ G2` or consistency
  with the G1 setup; KZG completeness needs both.
- **KZG binding proof**: the `q`-SDH reduction is not formalised anywhere we know of in Lean;
  VCV-io has no KZG or pairing-group definitions [V: grep of VCV-io at `f5119c6`]. The statement is
  `EthSecurity`'s (DECISIONS Q44).
- **Coverage:** EEST exercises ECPAIRING with 11 fixture files and no `ported_static/stZeroKnowledge*`
  (present in EEST sources, absent from the zkevm corpus) [V]; no fixture targets the Miller-loop
  vertical-line branch or the `P ≠ ∞, Q = ∞` mixed case explicitly [I: not searched inside files].
- **`linefunc` degenerate branches** (`optimized_pairing.py:137–146`) are reachable only for
  special `R, Q` relations during the loop [I]; whether they occur for subgroup inputs is unproved.
