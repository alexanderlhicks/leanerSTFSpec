# `EthPairingMathlib`: pairing laws and KZG correctness

*Status: informal specification, draft. Date: 2026-09-29. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: gate: [REVIEW §3](../REVIEW.md) · decisions: D12, D15, D18, P4 · questions: B13/Q40, Q44, Q45.*

## 1. Purpose

`EthPairingMathlib` (Mathlib bridge package `STFSpecMathlib/`, root `STFSpecMathlib.Pairing`) proves the laws that make
`EthPairing`'s predicate contract meaningful: the final exponentiation is a homomorphism,
pairing checks are products of pairings, pairings are bilinear and non-degenerate on the order-`r`
subgroups, any two such pairings give the same check (so the implementation may change), and
KZG single-point verification is complete. The KZG binding statement of D12 deliverable (iii)
belongs to `EthSecurity` (DECISIONS Q44), stated over the models defined here.

## 2. Requirements

- Laws are stated over `EthPairing`'s public functions (`pairing`, `pairingCheck`,
  `verifyKzgProof`) and `EthCurveMathlib`'s point model; the Miller loop is not exposed to
  callers.
- **Bilinearity/non-degeneracy** may enter first as an explicit hypothesis
  (`IsNondegBilinear (pairing)`), so that downstream theorems are conditional and honest about it
  (CONTRIBUTING §4: conditional theorems list their hypotheses and the bridge that discharges each).
- No axioms; no `native_decide`.

## 3. EELS source map

None: this proof library claims no EELS items.

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| none | — | — | proof-only library |

**External semantics:** justifies `EthPairing`'s treatment of `py_ecc` `pairing` and
`final_exponentiate` (EthPairing R3).

## 4. Tests

No executable tests. Computational facts (`pairing G2 G1 ^ r = 1`, `pairing G2 G1 ≠ 1`, the
trusted-setup constant decompresses to a curve point) are proved by evaluation if feasible, else
left as `#guard`s in the core with a stated gap. Build with `--wfail`; declaration check.

## 5. Interface

```lean
def IsNondegBilinear (e : G1 → G2 → μ r) : Prop
theorem finalExp_mul : finalExponentiate (a * b) = finalExponentiate a * finalExponentiate b
theorem pairingCheck_iff : pairingCheck l ↔ (l.map fun (P, Q) => pairing Q P).prod = 1
theorem pairingCheckMiller_eq : pairingCheckMiller a b = pairingCheck [a, b]
theorem pairing_pow_r : (pairing Q P) ^ r = 1                 -- on subgroup inputs
theorem bn254_pairing_nondegBilinear : IsNondegBilinear Bn254.pairing        -- GAP (hypothesis first)
theorem bls12381_pairing_nondegBilinear : IsNondegBilinear Bls12381.pairing  -- GAP
theorem check_independent (he he' : IsNondegBilinear e, e') (hl : ∀ x ∈ l, InSubgroups x) :
    check e l ↔ check e' l
theorem verifyKzgProof_iff : verifyKzgProof c z y π = .ok b ↔ Valid… ∧ (b ↔ e (C - y•G1) G2 = e π (tauG2 - z•G2))
theorem kzg_complete (hsetup : SetupConsistent τ) (p : Polynomial Fr) (z) :
    verifyKzgProof (commit p) z (p.eval z) (prove p z) = .ok true
-- (iii) statements (q-SDH, KZG evaluation binding) are EthSecurity's (DECISIONS Q44)
```

## 6. Data structures

None new. Models: `μ r ⊆ Fq12ˣ` (`rootsOfUnity`), the order-`r` subgroups of the Mathlib point
groups from `EthCurveMathlib`, `Polynomial Fr` for KZG. `SetupConsistent τ` is a predicate on the
setup (G1 powers and `tauG2` share `τ`).

## 7. Contract and laws

- [C] `finalExp_mul`, `pairingCheck_iff`, `pairingCheckMiller_eq`: elementary, no pairing theory
  needed.
- [C] `check_independent`: from bilinearity and non-degeneracy of both maps on cyclic groups of
  prime order (`e' = e^c`, `c` a unit mod `r`). This is the theorem that licenses the
  replacement of the pairing algorithm (EthPairing R3).
- [C] Bilinearity and non-degeneracy of the concrete Miller-loop pairings: hypothesis first,
  then (long term) proof.
- [C] KZG completeness under `SetupConsistent`.
- [F] executable final exponentiation ≡ the plain-power reference (or, for a fixed-power chain, agreement of the pairing-check predicate; `EthPairing` §6); tower `Fq12` ≡ flat (from `EthFieldMathlib`).
- [S] none here. KZG evaluation binding from `q`-SDH (`q = 4096`) with an unknown `τ` (ceremony
  1-of-n honesty) is stated in `EthSecurity` (DECISIONS Q44); its proof is optional and probably
  VCV-io-based.

### Informal correctness argument

**Claim.** Under established group/field and concrete pairing laws, pairing conventions give the same product check and honest KZG openings satisfy the executable equation.

**Premises.** EthCurveMathlib bridges; cyclic prime-order source groups; bilinearity and nondegeneracy of each concrete pairing; compatible trusted setup and valid encodings.

**Argument.** Choose source generators and let ζ be their pairing value. Nondegeneracy gives order r; bilinearity writes every pairing as ζ^(ab). A second nondegenerate pairing has generator value ζ^c with c nonzero modulo r. Multiplication of pairings therefore transforms by a bijective exponentiation, proving equality-to-one independence. Final exponentiation's multiplicative law follows from the field power law. For KZG, evaluation of the commitment and quotient at τ gives p(τ)−p(z)=(τ−z)q(τ); bilinearity turns this into the verified pairing equation. All decoding, infinity and subgroup premises come from the concrete callers and cannot be omitted from the theorem.

**Open obligations.** Concrete Miller-loop bilinearity and nondegeneracy remain the central missing proofs; this argument does not supply them. Group order, setup consistency and accepted encoding proofs are also outstanding. Computational pairing checks support fidelity but do not establish these universally quantified premises.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthPairing`, `EthCurveMathlib` (the direct proof imports in `STFSpec/informal/contracts.toml`).
- VCV-io is not imported here; it enters only the security package `STFSpecSecurity/` (P4).
- Imports `EthPairing` (core), `EthCurveMathlib` (which brings `EthFieldMathlib` transitively), Mathlib v4.34.0.
- **Used by:** consumers proving precompile outputs (ECPAIRING, BLS12_PAIRING_CHECK,
  POINT_EVALUATION), `EthSecurity`.
- **Seams:** relies on `EthPairing`'s predicate contract; discharges `EthPairing`'s R3 claim.

## 9. Open decisions

- **D12** (accepted): (ii) here; (iii) statements and game proofs in `EthSecurity` (DECISIONS Q44).
- **D15**: cryptography-specs has KZG proofs (`Proofs/Kzg/*.lean`: evaluation, barycentric,
  domain) [V: file names] but no pairing bilinearity; reuse needs the toolchain and
  `native_decide` issues resolved (DECISIONS Q45).
- **D18**: none directly.
- **Open:** pairing contract as a predicate (NEW-CRYPTO-3): DECISIONS B13 (Q40), scheduled, not settled; this library is written to the predicate B13 recommends.
- Owner of the (iii) statements (NEW-CRYPTO-7): resolved, DECISIONS Q44 (`EthSecurity`).

## 10. Gaps

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **No pairing theory in Mathlib** (no Weil/Tate pairing, no divisors or Weil reciprocity on
  elliptic curves) [V: none found under `AlgebraicGeometry/EllipticCurve` at v4.34.0]. Proving
  bilinearity of an optimal-ate Miller loop has **no known strategy** short of building that
  theory; it may stay a hypothesis for a long time.
- **Non-degeneracy by computation** (`pairing G2 G1 ≠ 1`) is a large kernel evaluation in `Fq12`;
  feasibility without `native_decide` is unknown.
- **`SetupConsistent`** cannot be checked from the EELS constant alone; it is a ceremony
  assumption, and EELS does not check `tauG2 ∈ G2` (EthPairing R7).
- **`q`-SDH/KZG binding** has no Lean formalisation we know of; VCV-io lacks pairing groups
  [V: grep of VCV-io at `f5119c6`].
- The (iii) statements are `EthSecurity`'s (DECISIONS Q44), which has not started; until it does, nothing states KZG binding.
