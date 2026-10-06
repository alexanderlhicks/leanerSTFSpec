/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.Apply

/-!
# Bounded structural preservation

Library `EthState`: the two sufficient raw diff premises and conditional preservation of
the three structural `MathState.WF` clauses. Replay metadata, history and code are separate.
Spec guidance: `STFSpec/informal/modules/EthState.md` §7.4.
-/

namespace STFSpec.State

open Base

namespace BlockDiff

/-- Every deletion clears storage; every raw storage patch has a present post-account.
Empty patches and zero writes count. This imposes no initial-state or metadata invariant. -/
def StructuralPremises (σ : MathState) (d : BlockDiff) : Prop :=
  (∀ a : Address, d.accountChanges[a]? = some none → a ∈ d.storageClears) ∧
  (∀ a : Address, d.storageChanges[a]?.isSome = true → (σ.apply d).account? a ≠ none)

/-- The structural premises consist exactly of their two raw clauses. -/
theorem structuralPremises_iff (σ : MathState) (d : BlockDiff) :
    StructuralPremises σ d ↔
      (∀ a : Address, d.accountChanges[a]? = some none → a ∈ d.storageClears) ∧
      (∀ a : Address, d.storageChanges[a]?.isSome = true → (σ.apply d).account? a ≠ none) :=
  Iff.rfl

/-- A raw deletion tombstone requires clear membership. -/
theorem structuralPremises_storage_clear (σ : MathState) (d : BlockDiff)
    (hp : StructuralPremises σ d) (a : Address)
    (hd : d.accountChanges[a]? = some none) : a ∈ d.storageClears := hp.1 a hd

/-- A raw storage-change address requires a present post-account, even for an empty patch. -/
theorem structuralPremises_account_present (σ : MathState) (d : BlockDiff)
    (hp : StructuralPremises σ d) (a : Address)
    (hs : d.storageChanges[a]?.isSome = true) : (σ.apply d).account? a ≠ none := hp.2 a hs

end BlockDiff

namespace MathState

private theorem post_slot_nonzero (σ : MathState) (d : BlockDiff) (hwf : WF σ)
    (a : Address) (slots : Std.ExtTreeMap Bytes32 U256)
    (hs : (σ.apply d).storage[a]? = some slots) (k : Bytes32) (v : U256)
    (hk : slots[k]? = some v) : v ≠ U256.zero := by
  have hpost : ((σ.apply d).storage[a]?).bind (fun out ↦ out[k]?) = some v := by
    simp only [hs, Option.bind_some, hk]
  cases hq : (d.storageChanges[a]?).bind (fun writes ↦ writes[k]?) with
  | none =>
    rw [apply_storage_slot_of_no_write σ d a k hq] at hpost
    by_cases hcl : a ∈ d.storageClears
    · simp [hcl] at hpost
    · simp only [hcl, ite_false] at hpost
      cases hi : σ.storage[a]? with
      | none => simp [hi] at hpost
      | some initial =>
        simp only [hi, Option.bind_some] at hpost
        exact wf_storage_value_ne_zero σ a initial k v hwf hi hpost
  | some value =>
    by_cases hz : value = U256.zero
    · subst value
      rw [apply_storage_slot_of_write_zero σ d a k hq] at hpost
      contradiction
    · rw [apply_storage_slot_of_write_ne_zero σ d a k value hq hz] at hpost
      exact (Option.some.inj hpost) ▸ hz

private theorem post_inner_nonempty (σ : MathState) (d : BlockDiff) (hwf : WF σ)
    (a : Address) (slots : Std.ExtTreeMap Bytes32 U256)
    (hs : (σ.apply d).storage[a]? = some slots) : slots.isEmpty = false := by
  rw [apply_storage_lookup] at hs
  cases hsc : d.storageChanges[a]? with
  | none =>
    simp only [hsc] at hs
    by_cases hcl : a ∈ d.storageClears
    · simp [hcl] at hs
    · simp only [hcl, ite_false] at hs
      exact wf_storage_nonempty σ a slots hwf hs
  | some writes =>
    simp only [hsc] at hs
    let out := writes.foldl (fun out k v ↦
      if v = U256.zero then out.erase k else out.insert k v)
      ((if a ∈ d.storageClears then none else σ.storage[a]?).getD ∅)
    change (if out.isEmpty then none else some out) = some slots at hs
    by_cases he : out.isEmpty = true
    · simp only [he, ite_true] at hs
      contradiction
    · simp only [he] at hs
      rw [← Option.some.inj hs]
      exact Bool.eq_false_iff.mpr he

private theorem post_account_present (σ : MathState) (d : BlockDiff) (hwf : WF σ)
    (hp : BlockDiff.StructuralPremises σ d) (a : Address)
    (slots : Std.ExtTreeMap Bytes32 U256) (hs : (σ.apply d).storage[a]? = some slots) :
    (σ.apply d).account? a ≠ none := by
  cases hsc : d.storageChanges[a]? with
  | some writes =>
    exact BlockDiff.structuralPremises_account_present σ d hp a (by simp [hsc])
  | none =>
    have hcl : a ∉ d.storageClears := by
      intro hc
      rw [apply_storage_of_clear_no_writes σ d a hc hsc] at hs
      contradiction
    rw [apply_storage_of_untouched σ d a hsc hcl] at hs
    rw [apply_account?_eq]
    cases hac : d.accountChanges[a]? with
    | none => exact wf_storage_account_present σ a slots hwf hs
    | some replacement =>
      cases replacement with
      | none => exact False.elim (hcl (BlockDiff.structuralPremises_storage_clear σ d hp a hac))
      | some account => simp

/-- Initial structural WF and the two raw structural premises preserve exactly structural WF. -/
theorem wf_apply_of_structuralPremises (σ : MathState) (d : BlockDiff)
    (hwf : WF σ) (hp : BlockDiff.StructuralPremises σ d) : WF (σ.apply d) := by
  apply (wf_iff (σ.apply d)).mpr
  refine ⟨post_slot_nonzero σ d hwf, post_inner_nonempty σ d hwf, ?_⟩
  intro a slots hs
  have ha := post_account_present σ d hwf hp a slots hs
  rw [← account?_eq_lookup]
  cases h : (σ.apply d).account? a with
  | none => exact False.elim (ha h)
  | some account => rfl

end MathState

namespace BlockDiff

/-- Equal four effect fields preserve the predicate regardless of all replay metadata. -/
theorem structuralPremises_congr_effects (σ : MathState) (d e : BlockDiff)
    (ha : d.accountChanges = e.accountChanges) (hs : d.storageChanges = e.storageChanges)
    (hc : d.codeChanges = e.codeChanges) (hcl : d.storageClears = e.storageClears) :
    StructuralPremises σ d ↔ StructuralPremises σ e := by
  rw [structuralPremises_iff, structuralPremises_iff,
    MathState.apply_congr_effects σ d e ha hs hc hcl, ha, hs, hcl]

end BlockDiff

end STFSpec.State
