# `EthFieldMathlib`: field arithmetic is ring arithmetic in `ZMod p` and its extensions

*Status: informal specification, draft. Date: 2026-09-29. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: Montgomery backend results in `EthField` §6 and D6 · gate: [REVIEW §3](../REVIEW.md) · decisions: D6, D12, D21, D25, D26, P4 · questions: Q39, Q45.*

## 1. Purpose

`EthFieldMathlib` is the Mathlib bridge for `EthField` (Mathlib bridge package `STFSpecMathlib/`, root
`STFSpecMathlib.Field`; ARCHITECTURE §3 "outside the core package"). It proves that every
`EthField` prime field is isomorphic as a ring to `ZMod p`, that the `Fp2`/`Fp6`/`Fp12` towers are
fields isomorphic to the intended extensions, and that `powMod`, `inv0`, `sqrt?`, `legendre` and
`sgn0` have their mathematical meanings. It is the (ii) "mathematical correctness" deliverable of
D12 for the field layer, and the base on which `EthCurveMathlib` and `EthPairingMathlib` rest.
It contains no executable code.

## 2. Requirements

- Every theorem is about the **public** `EthField` API (observers and operations), never about
  its private fields, so that a Montgomery representation (D6) re-proves only the core's
  commuting equations and this library survives unchanged (ARCHITECTURE §4).
- Primality of the eight moduli (`EthField` R1) must be proved without `native_decide`
  (CONTRIBUTING §4). CompPoly's Pratt certificates (`CompPoly/Fields/PrattCertificate.lean`) are
  a model. D26 records that a text scan of CompPoly at `96e4b3d` found no `native_decide` in
  `PrattCertificate.lean` or the per-field certificates, so check the axioms
  (`#print axioms`) at the commit to be reused before relying on either reading. cryptography-specs proves BLS12-381 `q` prime "kernel-checked without
  `native_decide`" (`Proofs/Bls/FpZMod.lean:31`, `:446`) [V].
- The irreducibility of `X² + 1` over each base field (`q ≡ 3 mod 4`), of `X³ − ξ` over `Fp2`,
  and of `X² − v` over `Fp6` must be proved, or the towers identified with `GaloisField q k`.
- Release theorems are `sorry`-free, including dependencies; axioms limited to `propext`,
  `Quot.sound`, `Classical.choice` (CONTRIBUTING §4).

## 3. EELS source map

None: this proof library claims no EELS items (all field items are claimed by `EthField`).

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| none | — | — | proof-only library |

**External semantics:** none beyond `EthField`'s; the theorems justify that the `EthField`
definitions of `py_ecc` field behaviour (`FQ`, `FQ2`, `FQ12`, `prime_field_inv`) are field
operations.

## 4. Tests

- No EEST fixtures or `#guard`s (nothing executable). Evidence is `lake build` of `STFSpecMathlib/` with
  `--wfail` and the declaration check (P4).
- Regression: each theorem is instantiated on all eight fields (a missing instance is a build
  failure).

## 5. Interface

Lean-like theorem signatures (all public):

```lean
theorem Bn254.q_prime : Nat.Prime Bn254.q          -- and r, Bls12381.q/r, Secp256k1.p/n, P256.p/n
def PrimeField.toZMod [Fact p.Prime] : PrimeField p ≃+* ZMod p
theorem PrimeField.toZMod_toNat (a) : (toZMod a).val = a.toNat
theorem PrimeField.toZMod_inv0 (a) : toZMod (a.inv0) = (toZMod a)⁻¹          -- 0⁻¹ = 0 in ZMod
theorem PrimeField.toZMod_div (a b) : toZMod (a / b) = toZMod a / toZMod b
theorem PrimeField.toZMod_pow (a n) : toZMod (a.pow n) = toZMod a ^ n
theorem PrimeField.sqrt?_spec [p % 4 = 3] (a) :
    (∃ s, a.sqrt? = some s ∧ s * s = a) ∨ (a.sqrt? = none ∧ ¬ IsSquare (toZMod a))
theorem PrimeField.legendre_eq (a) : a.legendre = legendreSym p (toZMod a).val   -- Euler's criterion
theorem powMod_eq (b e m) (h : 0 < m) : powMod b e m = b ^ e % m
instance : Field (PrimeField p)        -- transported along toZMod
def Fp2.toAdjoin : Bn254.Fq2 ≃+* AdjoinRoot (X ^ 2 + 1 : Polynomial (ZMod Bn254.q))
instance : Field Bn254.Fq2 ; instance : Field Bn254.Fq12   -- and for BLS12-381
theorem Fp12.toFlat_ringHom : …        -- EthField R4: tower ≃ py_ecc flat representation
theorem Fp2.sgn0_spec, Fp2.sqrt?_spec  -- RFC 9380 meaning
-- optional, if D6 reuses CompPoly's bridge: FastField.ringEquiv ∘ … commutes with PrimeField
-- observers. CompPoly proves it under its class field `2 * p < 2^256`; for the carry-preserving
-- backend it must be re-proved under `p < R`, or proved directly for Wide8/W12 (EthField §6)
```

## 6. Data structures

None new. Models used: `ZMod p` (prime fields), `AdjoinRoot`/`GaloisField p k` (extensions).
Abstraction maps: `PrimeField.toZMod`, `Fp2.toAdjoin`, `Fp12` tower maps. No persistence or
complexity questions (proof-only).

## 7. Contract and laws

- [C] `toZMod` is a ring isomorphism for each prime modulus; all `EthField` §7 commuting
  equations lift to field identities.
- [C] `inv0` agrees with Mathlib's `Inv` on `ZMod p` (which has `0⁻¹ = 0`), so `py_ecc`'s
  `prime_field_inv(0) = 0` is exactly Mathlib's convention.
- [C] Towers are fields; `Fp12` has `q¹²` elements; `toFlat` is a ring isomorphism.
- [C] Euler's criterion, square-root correctness for `q ≡ 3 mod 4`, uniqueness up to sign.
- [C] `powMod` correctness (all `m ≥ 1`, not only primes).
- [F] (if D6 attaches Montgomery) `FastField.ringEquiv` (CompPoly `BLS12_381/Fast.lean:61–62`,
  `BN254/Fast.lean:60`) [V] composes with `toZMod` to give the same isomorphism. As proved
  upstream it assumes `2p < R`; the chosen carry-preserving backend needs it re-proved under
  `p < R` (carry-fixed), or proved for `Wide8`/`W12` directly (`EthField` §6).
- [S] none.

### Informal correctness argument

**Claim.** The public concrete operations transport to Mathlib's prime/extension-field models without depending on their private representation.

**Premises.** EthField commuting equations, prime and irreducibility certificates, and compatible pinned Mathlib constructions.

**Argument.** First construct a bijection between canonical residues and ZMod p. Prove that zero, one, addition, negation and multiplication commute with it, then transport the ring structure; do not assume a Field instance to establish the operation equations needed to build that instance. Primality gives the inverse law for nonzero values, with inv0 handled separately. For towers, evaluate coefficient tuples in the quotient/extension model; irreducibility supplies the field structure and basis uniqueness supplies injectivity. Induction transports exponentiation and the algorithm-specific square-root soundness facts. This order avoids circular use of field laws. Downstream curve proofs consume the bridge through public equations, so changing residues to limbs or changing tower layout affects this bridge rather than every group theorem.

**Open obligations.** Supply the certificates, tower isomorphisms and sqrt completeness/sign proof. Computational checks used as certificates must be kernel-checkable and satisfy the repository declaration check; native_decide or an assumed irreducibility axiom cannot discharge them.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthField`.
- VCV-io is not imported here; it enters only the security package `STFSpecSecurity/` (P4).
- Imports `EthField` (core) and Mathlib v4.34.0 (`STFSpecMathlib/lakefile.toml`); possibly CompPoly for
  Pratt certificates and `FastField` (D6), which already pins Mathlib v4.34.0 @`5ed29652`, as VCV-io `f5119c6` does [V].
- **Used by:** `EthCurveMathlib`, `EthPairingMathlib`; `EthSecurity` indirectly.
- **Seams:** relies only on `EthField`'s public API and its core commuting equations.

## 9. Open decisions

- **D6** (provisional; width settled by the Montgomery prototype, DECISIONS Q39): whether CompPoly's `FastField.ringEquiv` is reused (re-proved under `p < R`) or our own bridge is proved for `Wide8`/`W12`.
- **D12**: this is part of deliverable (ii).
- **D21** (accepted: banned): no `@[csimp]`. The equation between an executable field (Montgomery) and
  its reference is an ordinary, axiom-clean theorem, proved here or in the core.
- **D25**: model-based; `ZMod p` is the model.
- **P4**: lives in the Mathlib bridge package `STFSpecMathlib/`.

## 10. Gaps

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Primality certificates** for BN254 `q`, P-256 `p`/`n` are not known to exist in Lean [I];
  CompPoly covers BN254 `r`, BLS12-381 `r` and secp256k1 `p`/`n` [V: files read], cryptography-specs
  covers BLS12-381 `q` and `r` [V]. D26 records no `native_decide` tactic use in CompPoly at `96e4b3d`
  (a text scan; an axiom check at the reused commit decides); reusing either source also means a dependency or vendoring
  decision (D26, Q45).
- **Irreducibility proofs** for the tower polynomials (`X³ − ξ` over `Fp2`) are not written
  anywhere we know of; a `GaloisField` identification needs cardinality arguments.
- **cryptography-specs' proofs use `native_decide`** in some files (for example
  `Proofs/Bls/Compress.lean:319`, `Proofs/Xmss/Blake2s.lean`) [V]; those cannot be imported as-is.
- **Toolchain mismatch:** cryptography-specs is on Lean v4.29.1 / Mathlib v4.29.1 [V]; our
  proofs are on v4.34.0.
- **`sgn0`/`Fp2.sqrt?`** specifications depend on which algorithm `EthField` chooses (open there).
