/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Bounded structural public-law clients

Library `EthConformance`: private arbitrary-input clients of exactly the five structural laws.
Spec guidance: `STFSpec/informal/modules/EthState.md` §7.4.
-/

namespace STFSpec.Conformance.StructuralCallerProofs

open STFSpec.Base STFSpec.State

private theorem clauses (σ : MathState) (d : BlockDiff) :
    BlockDiff.StructuralPremises σ d ↔
      (∀ a : Address, d.accountChanges[a]? = some none → a ∈ d.storageClears) ∧
      (∀ a : Address, d.storageChanges[a]?.isSome = true → (σ.apply d).account? a ≠ none) :=
  BlockDiff.structuralPremises_iff σ d

private theorem deletion (σ : MathState) (d : BlockDiff)
    (hp : BlockDiff.StructuralPremises σ d) (a : Address)
    (hd : d.accountChanges[a]? = some none) : a ∈ d.storageClears :=
  BlockDiff.structuralPremises_storage_clear σ d hp a hd

private theorem patch (σ : MathState) (d : BlockDiff)
    (hp : BlockDiff.StructuralPremises σ d) (a : Address)
    (hs : d.storageChanges[a]?.isSome = true) : (σ.apply d).account? a ≠ none :=
  BlockDiff.structuralPremises_account_present σ d hp a hs

private theorem preservation (σ : MathState) (d : BlockDiff)
    (hwf : MathState.WF σ) (hp : BlockDiff.StructuralPremises σ d) :
    MathState.WF (σ.apply d) := MathState.wf_apply_of_structuralPremises σ d hwf hp

private theorem metadata (σ : MathState) (d e : BlockDiff)
    (ha : d.accountChanges = e.accountChanges) (hs : d.storageChanges = e.storageChanges)
    (hc : d.codeChanges = e.codeChanges) (hcl : d.storageClears = e.storageClears) :
    BlockDiff.StructuralPremises σ d ↔ BlockDiff.StructuralPremises σ e :=
  BlockDiff.structuralPremises_congr_effects σ d e ha hs hc hcl

end STFSpec.Conformance.StructuralCallerProofs
