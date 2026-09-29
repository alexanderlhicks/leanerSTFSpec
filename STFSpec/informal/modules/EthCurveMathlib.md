# `EthCurveMathlib`: curve operations are the elliptic-curve group law; ECDSA correctness

*Status: informal specification, draft. Date: 2026-09-29. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: gate: [REVIEW §3](../REVIEW.md) · decisions: D7, D12, D15, D26, P4 · questions: Q44, Q45.*

## 1. Purpose

`EthCurveMathlib` (Mathlib bridge package `STFSpecMathlib/`, root `STFSpecMathlib.Curve`) proves that `EthCurve`'s executable
operations implement the elliptic-curve group law of Mathlib's `WeierstrassCurve` for each
Ethereum curve, that scalar multiplication, MSM, subgroup checks, the BLS12-381 compressed codec
and the SSWU maps mean what their names say, and that ECDSA recovery (secp256k1) and verification
(P-256) are correct with respect to the ECDSA equations. It is D12 deliverable (ii) for curves. The
security statements of deliverable (iii) belong to `EthSecurity` (DECISIONS Q44); this library
supplies only the model-level predicates (`Ecdsa.verifies`) they are stated over.

## 2. Requirements

- Model: Mathlib `WeierstrassCurve.Affine.Point` with its `AddCommGroup` instance
  (`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:807`), and the `Projective`/`Jacobian`
  point types for coordinate bridges (`Projective/Point.lean:572`, `Jacobian/Point.lean:588`)
  [V: Mathlib at v4.34.0 as pinned by CompPoly].
- One commuting theorem per `EthCurve` operation (ARCHITECTURE §4), stated through
  `EthCurve.Proj.toAffine`, so a coordinate change (D7) re-proves only these.
- The precedent is cryptography-specs' Jacobian G1 development (`Proofs/Bls/G1Group.lean`:
  `toPoint_add`, `valid_add`, `toPoint_mulNat`; `Proofs/Bls/G1Order.lean`; `Proofs/Bls/Compress.lean`
  `uncompress_compress`) [V]; the same shape must cover BN254 G1/G2, BLS12-381 G2, secp256k1 and
  P-256.
- Security statements are **hypotheses or definitions**, never axioms (CONTRIBUTING §4).

## 3. EELS source map

None: this proof library claims no EELS items.

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| none | — | — | proof-only library |

**External semantics:** justifies `EthCurve`'s definitions of `py_ecc` curve functions,
`spec256k1` recovery and OpenSSL P-256 verification against the standards (SEC 1 v2, FIPS 186-5,
RFC 9380).

## 4. Tests

No executable tests. Kernel-checked facts that are also computations (generator on curve,
`r • G = 0` for each generator, `decompress (compress G) = G`) are proved by `decide`-free
evaluation (`norm_num`/`reduce_mod_char` style, as cryptography-specs `G1Order.lean` does) [V].
Build with `--wfail`; declaration check.

## 5. Interface

```lean
def Curve.toMathlib (W : EthCurve.Weierstrass F) : WeierstrassCurve (ZModOrField F)
def Proj.toPoint (P : Proj F) (h : Valid P) : (W.toMathlib).Point
theorem toPoint_add (hP hQ) : toPoint (add P Q) = toPoint P + toPoint Q
theorem toPoint_double, toPoint_neg, toPoint_mulNat : toPoint (mulNat P n) = n • toPoint P
theorem toPoint_msm : toPoint (msm c hc l) = (l.map fun (P, m) => m.toNat • toPoint P).sum  -- every c ≥ 1
theorem inSubgroup_iff : inSubgroup r P ↔ r • toPoint P = 0
theorem generator_order : addOrderOf (toPoint gen) = r            -- per curve
theorem cofactor_one_bn254 : ∀ P : (Bn254 G1 curve).Point, r • P = 0   -- GAP: needs #E = r
theorem toXY_eq_zero_iff : toXY P = (0, 0) ↔ toPoint P = 0             -- BN254, BLS12-381
theorem decompress_compress, decompress_spec, keyValidate_iff           -- BLS12-381 R9
theorem mapFpToG1_mem : toPoint (mapFpToG1 u) ∈ Bls12381.G1Subgroup   -- includes exactly one clearing
theorem mapFp2ToG2_mem : toPoint (mapFp2ToG2 u) ∈ Bls12381.G2Subgroup
theorem recover_sound : Secp256k1.recover r s v e = .ok q → Ecdsa.verifies secp256k1 q e r s
theorem recover_complete (hc : RecoveryCompatible k e r s v) :
    Ecdsa.honestSig k e = (r, s, v) → recover r s v e = .ok (pub k)
theorem p256_verify_iff : P256.verify r s x y e = .ok () ↔ Ecdsa.verifies p256 (x, y) e r s
-- (iii) statements (EUF-CMA advantage, ECDSA security assumptions) are EthSecurity's (DECISIONS Q44)
```

## 6. Data structures

None new. Models: Mathlib Weierstrass points; `Ecdsa.verifies` as a predicate on the model
(defined here, following FIPS 186-5 §6.4.2, with `e = int(hash)` and no truncation for 256-bit
orders). Abstraction: `Proj.toPoint` under `Valid` (the `EthCurve` invariant).

## 7. Contract and laws

- [C] Group-law commuting equations for `add`, `double`, `neg`, `mulNat`, `msm`; invariant
  preservation (`Valid (add P Q)`).
- [C] `inSubgroup` meaning; `generator_order`.
- [C] Codec: `decompress` total, inverse of compression on valid points, rejects exactly the
  cases of `EthCurve` R9; `x = 0` points rejected by flags are exactly order-3 points
  (hence the agreement claim in `EthCurve` R9).
- [C] SSWU/isogeny: image on the target curve; `h_eff` clearing lands in the order-`r`
  subgroup; agreement with the ψ-based G2 clearing if cryptography-specs' version is used.
- [C] ECDSA: soundness and completeness of recovery; P-256 verification equivalence; the
  `mod n` comparison of `R.x`.
- [R] ZisK: affine `curveAdd`/`curveDbl` equal the Mathlib group law under their preconditions
  (`x₁ ≠ x₂`, `y ≠ 0`).
- [S] none here. ECDSA EUF-CMA for secp256k1 (transaction authentication) and P-256
  (P256VERIFY) is stated in `EthSecurity` (DECISIONS Q44), over `Ecdsa.verifies`; the precompile
  spec does not depend on it.

### Informal correctness argument

**Claim.** Valid concrete points and public operations map to the intended mathematical elliptic-curve groups, supporting the qualified subgroup, mapping and ECDSA laws.

**Premises.** EthFieldMathlib bridges; nonsingularity; concrete formula correspondence; certified subgroup orders and relevant cofactor facts.

**Argument.** Normalise a valid projective point to the affine model, mapping z=0 to infinity. This identifies equivalent coordinates without demanding equality of representations. Case analysis of public add/double/neg equations proves preservation of this map; scalar-bit induction proves multiplication correspondence. Transfer the group laws through these equations rather than unfolding limbs or coordinates in callers. A prime claimed order and a nonzero generator with rG=0 establish that generator's order; they do not establish the entire curve's point count or every cofactor claim. Mapping proofs additionally show the exact SSWU/isogeny sign and then the once-cleared subgroup property. Signature completeness is restricted to the documented recovery-compatible domain.

**Open obligations.** Finish concrete formula bridges, point counting/subgroup certificates, compression and mapping correspondence, and ECDSA library acceptance/error alignment. Subgroup membership tested by multiplication is executable; its identification with the advertised prime-order subgroup still requires the mathematical group facts.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthCurve`, `EthFieldMathlib`.
- VCV-io is not imported here; it enters only the security package `STFSpecSecurity/` (P4).
- Imports `EthCurve` (core), `EthFieldMathlib`, Mathlib v4.34.0.
- **Used by:** `EthPairingMathlib` (subgroup facts), `EthSecurity` (states its signature assumptions over `Ecdsa.verifies`),
  consumers proving precompile results.
- **Seams:** uses only `EthCurve`'s public operations and invariant.

## 9. Open decisions

- **D7**: the coordinate system determines which Mathlib bridge (`Projective` or `Jacobian`) is
  used.
- **D12** (accepted): (ii) proofs here; (iii) statements in `EthSecurity` (DECISIONS Q44).
- **D15**: reuse of cryptography-specs' G1 proofs (toolchain v4.29.1; `native_decide` in some
  files); conditions in DECISIONS Q45.
- Owner of the D12 (iii) statements (NEW-CRYPTO-7): resolved, DECISIONS Q44 (`EthSecurity`).

## 10. Gaps

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Group orders:** `#E(Fq)` for BN254 G1, secp256k1, P-256, and the twist orders for G2 have
  **no known proof strategy** in Mathlib (no point counting, no CM theory). Every "cofactor 1" or
  "subgroup check redundant" law is therefore conditional. Computation-only facts
  (`r • G = 0`) are provable.
- **General-`a` formulas** for P-256 are not yet defined in `EthCurve`, so their proofs have no
  target.
- **ECDSA over Mathlib** is not formalised anywhere we know of; `Ecdsa.verifies` must be written.
- **SSWU/isogeny correctness** requires checking the isogeny polynomials (RFC 9380 Appendix E);
  plausible by computation in `Polynomial (ZMod q)` but unestimated.
- **libsecp256k1/OpenSSL** are specified by standards; that their observed behaviour matches is
  evidence from tests only.
- **ECDSA security** proofs are out of scope (assumptions only); VCV-io has no EC/ECDSA
  definitions [V: a case-insensitive grep of VCV-io at `f5119c6` finds no secp256k1, ECDSA or Weierstrass curves].
