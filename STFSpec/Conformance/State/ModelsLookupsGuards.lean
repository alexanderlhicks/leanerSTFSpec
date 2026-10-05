/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.ModelsLookups

/-!
# Lookup agreement positive and negative guards

Library `EthConformance`: private ordinary proofs over arbitrary records and raw states.
Supplied test callbacks exercise successes and errors, without a universal Prop decider.
Provider and container reasoning uses only public laws.
Spec guidance: `STFSpec/informal/modules/EthState.md` R8/§4/§5.
-/

namespace STFSpec.Conformance.State.ModelsLookupsGuards

open STFSpec.Base STFSpec.State

private def failed (e : WitnessError)
    (root : BlockDiff → Id (Except WitnessError Hash32)) : PreState Id :=
  PreState.mk (fun _ ↦ .error e) (fun _ _ ↦ .error e) (fun _ ↦ .error e) root

private theorem errors_vacuous (consts : HashConsts) (σ : MathState) (e : WitnessError)
    (root : BlockDiff → Id (Except WitnessError Hash32)) :
    ModelsLookups consts (failed e root) σ := by
  unfold ModelsLookups failed
  rw [PreState.getAccount?_mk, PreState.getStorage_mk, PreState.getCode_mk]
  refine ⟨?_, ?_, ?_⟩
  · intro a o h
    cases h
  · intro a k v h
    cases h
  · intro h code hc
    cases hc

-- Exact successful answers at any raw state; missing code is a supplied error.
private def answers (consts : HashConsts) (σ : MathState) (e : WitnessError)
    (root : BlockDiff → Id (Except WitnessError Hash32)) : PreState Id :=
  PreState.mk (fun a ↦ .ok (σ.account? a)) (fun a k ↦ .ok (σ.storageAt a k))
    (fun h ↦ match σ.code? consts h with
      | none => .error e
      | some code => .ok code) root

private theorem exact_answers (consts : HashConsts) (σ : MathState) (e : WitnessError)
    (root : BlockDiff → Id (Except WitnessError Hash32)) :
    ModelsLookups consts (answers consts σ e root) σ := by
  unfold ModelsLookups answers
  rw [PreState.getAccount?_mk, PreState.getStorage_mk, PreState.getCode_mk]
  refine ⟨?_, ?_, ?_⟩
  · intro a o ha
    exact Except.ok.inj ha
  · intro a k v hs
    exact Except.ok.inj hs
  · intro h code hc
    cases he : σ.code? consts h with
    | none => simp only [he] at hc; cases hc
    | some bytes =>
      simp only [he] at hc
      exact congrArg some (Except.ok.inj hc)

-- These positive witnesses retain complete successful values, including account absence.
example (consts : HashConsts) (σ : MathState) (e : WitnessError) (a : Address)
    (o : Option Account) (ha : σ.accounts[a]? = o)
    (root : BlockDiff → Id (Except WitnessError Hash32)) :
    ModelsLookups consts (answers consts σ e root) σ ∧
      (answers consts σ e root).getAccount? a = .ok o := by
  refine ⟨exact_answers _ _ _ _, ?_⟩
  unfold answers
  rw [PreState.getAccount?_mk, MathState.account?_eq_lookup, ha]

example (consts : HashConsts) (σ : MathState) (e : WitnessError) (a : Address)
    (k : Bytes32) (hn : σ.storage[a]? = none)
    (root : BlockDiff → Id (Except WitnessError Hash32)) :
    ModelsLookups consts (answers consts σ e root) σ ∧
      (answers consts σ e root).getStorage a k = .ok U256.zero := by
  refine ⟨exact_answers _ _ _ _, ?_⟩
  unfold answers
  rw [PreState.getStorage_mk, MathState.storageAt_of_storage_none σ a k hn]

-- Arbitrary code includes empty and nonempty byte arrays; a raw miss is a supplied error.
example (consts : HashConsts) (σ : MathState) (e : WitnessError) (h : Hash32)
    (code : ByteArray) (hh : h ≠ consts.emptyCodeHash) (hs : σ.code[h]? = some code)
    (root : BlockDiff → Id (Except WitnessError Hash32)) :
    ModelsLookups consts (answers consts σ e root) σ ∧
      (answers consts σ e root).getCode h = .ok code := by
  refine ⟨exact_answers _ _ _ _, ?_⟩
  unfold answers
  rw [PreState.getCode_mk, MathState.code?_of_ne σ consts h hh, hs]

example (consts : HashConsts) (σ : MathState) (e : WitnessError) (h : Hash32)
    (hh : h ≠ consts.emptyCodeHash) (hn : σ.code[h]? = none)
    (root : BlockDiff → Id (Except WitnessError Hash32)) :
    ModelsLookups consts (answers consts σ e root) σ ∧
      (answers consts σ e root).getCode h = .error e := by
  refine ⟨exact_answers _ _ _ _, ?_⟩
  unfold answers
  rw [PreState.getCode_mk, MathState.code?_of_ne σ consts h hh, hn]

private theorem wrong_account (consts : HashConsts) (ps : PreState Id) (σ : MathState)
    (a : Address) (o : Option Account) (ha : ps.getAccount? a = .ok o)
    (hne : σ.account? a ≠ o) : ¬ ModelsLookups consts ps σ :=
  fun hm ↦ hne (hm.1 a o ha)

private theorem wrong_storage (consts : HashConsts) (ps : PreState Id) (σ : MathState)
    (a : Address) (k : Bytes32) (v : U256) (hs : ps.getStorage a k = .ok v)
    (hne : σ.storageAt a k ≠ v) : ¬ ModelsLookups consts ps σ :=
  fun hm ↦ hne (hm.2.1 a k v hs)

private theorem wrong_code (consts : HashConsts) (ps : PreState Id) (σ : MathState)
    (h : Hash32) (code : ByteArray) (hc : ps.getCode h = .ok code)
    (hne : σ.code? consts h ≠ some code) : ¬ ModelsLookups consts ps σ :=
  fun hm ↦ hne (hm.2.2 h code hc)

-- Absence and exact present empty-account answers remain different.
example (consts : HashConsts) (ps : PreState Id) (σ : MathState) (a : Address)
    (ha : σ.accounts[a]? = none) (hp : ps.getAccount? a = .ok (some (emptyAccount consts))) :
    ¬ ModelsLookups consts ps σ := by
  apply wrong_account consts ps σ a _ hp
  rw [MathState.account?_eq_lookup, ha]
  intro he
  cases he

example (consts : HashConsts) (ps : PreState Id) (σ : MathState) (a : Address)
    (ha : σ.accounts[a]? = some (emptyAccount consts)) (hp : ps.getAccount? a = .ok none) :
    ¬ ModelsLookups consts ps σ := by
  apply wrong_account consts ps σ a _ hp
  rw [MathState.account?_eq_lookup, ha]
  intro he
  cases he

-- Zero, nonzero and orphan raw storage all admit complete agreeing providers.
example (consts : HashConsts) (a : Address) (k : Bytes32) (v : U256) (e : WitnessError)
    (root : BlockDiff → Id (Except WitnessError Hash32)) :
    let σ : MathState := ⟨∅,
      (∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert a
        ((∅ : Std.ExtTreeMap Bytes32 U256).insert k v), ∅⟩
    ModelsLookups consts (answers consts σ e root) σ ∧
      σ.account? a = none ∧ σ.storageAt a k = v := by
  dsimp only
  refine ⟨exact_answers _ _ _ _, ?_, ?_⟩
  · rw [MathState.account?_eq_lookup, Std.ExtTreeMap.getElem?_empty]
  · exact MathState.storageAt_of_slot_some _ a k _ v
      Std.ExtTreeMap.getElem?_insert_self Std.ExtTreeMap.getElem?_insert_self

example (consts : HashConsts) (a : Address) (k : Bytes32) (e : WitnessError)
    (root : BlockDiff → Id (Except WitnessError Hash32)) :
    let σ : MathState := ⟨∅,
      (∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert a ∅, ∅⟩
    ModelsLookups consts (answers consts σ e root) σ ∧ σ.storageAt a k = U256.zero := by
  dsimp only
  refine ⟨exact_answers _ _ _ _, ?_⟩
  exact MathState.storageAt_of_slot_none _ a k ∅
    Std.ExtTreeMap.getElem?_insert_self Std.ExtTreeMap.getElem?_empty

example (consts : HashConsts) (ps : PreState Id) (σ : MathState) (a : Address)
    (k : Bytes32) (v : U256) (hn : σ.storage[a]? = none)
    (hp : ps.getStorage a k = .ok v) (hv : v ≠ U256.zero) :
    ¬ ModelsLookups consts ps σ := by
  apply wrong_storage consts ps σ a k v hp
  rw [MathState.storageAt_of_storage_none σ a k hn]
  exact Ne.symm hv

example (consts : HashConsts) (ps : PreState Id) (σ : MathState) (a : Address)
    (k : Bytes32) (slots : Std.ExtTreeMap Bytes32 U256) (stored wrong : U256)
    (hs : σ.storage[a]? = some slots) (hk : slots[k]? = some stored)
    (hp : ps.getStorage a k = .ok wrong) (hne : stored ≠ wrong) :
    ¬ ModelsLookups consts ps σ := by
  apply wrong_storage consts ps σ a k wrong hp
  rw [MathState.storageAt_of_slot_some σ a k slots stored hs hk]
  exact hne

-- The supplied reserved hash bypasses hidden raw bytes, for every constants record.
example (consts : HashConsts) (hidden : ByteArray) (e : WitnessError)
    (root : BlockDiff → Id (Except WitnessError Hash32)) :
    let σ : MathState := ⟨∅, ∅,
      (∅ : Std.ExtTreeMap Hash32 ByteArray).insert consts.emptyCodeHash hidden⟩
    ModelsLookups consts (answers consts σ e root) σ ∧
      σ.code[consts.emptyCodeHash]? = some hidden ∧
      σ.code? consts consts.emptyCodeHash = some ByteArray.empty := by
  dsimp only
  exact ⟨exact_answers _ _ _ _, Std.ExtTreeMap.getElem?_insert_self,
    MathState.code?_empty _ consts⟩

example (consts : HashConsts) (ps : PreState Id) (σ : MathState) (code : ByteArray)
    (hc : ps.getCode consts.emptyCodeHash = .ok code) (hne : code ≠ ByteArray.empty) :
    ¬ ModelsLookups consts ps σ := by
  apply wrong_code consts ps σ _ code hc
  rw [MathState.code?_empty]
  exact fun he ↦ hne (Option.some.inj he).symm

example (consts : HashConsts) (ps : PreState Id) (σ : MathState) (h : Hash32)
    (code : ByteArray) (hh : h ≠ consts.emptyCodeHash) (hn : σ.code[h]? = none)
    (hp : ps.getCode h = .ok code) : ¬ ModelsLookups consts ps σ := by
  apply wrong_code consts ps σ h code hp
  rw [MathState.code?_of_ne σ consts h hh, hn]
  intro he
  cases he

example (consts : HashConsts) (ps : PreState Id) (σ : MathState) (h : Hash32)
    (code wrong : ByteArray) (hh : h ≠ consts.emptyCodeHash)
    (hs : σ.code[h]? = some code) (hp : ps.getCode h = .ok wrong) (hne : code ≠ wrong) :
    ¬ ModelsLookups consts ps σ := by
  apply wrong_code consts ps σ h wrong hp
  rw [MathState.code?_of_ne σ consts h hh, hs]
  exact fun he ↦ hne (Option.some.inj he)

-- Selective errors do not excuse a wrong successful observer elsewhere.
example (consts : HashConsts) (a : Address) (k : Bytes32) (v : U256)
    (e : WitnessError) (hv : v ≠ U256.zero)
    (root : BlockDiff → Id (Except WitnessError Hash32)) :
    let ps := PreState.mk (m := Id) (fun _ ↦ .error e) (fun _ _ ↦ .ok v)
      (fun _ ↦ .error e) root
    ¬ ModelsLookups consts ps (MathState.mk ∅ ∅ ∅) := by
  dsimp only
  apply wrong_storage consts _ _ a k v
  · rw [PreState.getStorage_mk]
  · rw [MathState.storageAt_of_storage_none _ a k Std.ExtTreeMap.getElem?_empty]
    exact Ne.symm hv

private def reservedOnly (consts : HashConsts) (e : WitnessError)
    (root : BlockDiff → Id (Except WitnessError Hash32)) : PreState Id :=
  PreState.mk (fun _ ↦ .error e) (fun _ _ ↦ .error e)
    (fun h ↦ if h = consts.emptyCodeHash then .ok ByteArray.empty else .error e) root

private theorem reserved_agrees (consts : HashConsts) (σ : MathState) (e : WitnessError)
    (root : BlockDiff → Id (Except WitnessError Hash32)) :
    ModelsLookups consts (reservedOnly consts e root) σ := by
  unfold ModelsLookups reservedOnly
  rw [PreState.getAccount?_mk, PreState.getStorage_mk, PreState.getCode_mk]
  refine ⟨?_, ?_, ?_⟩
  · intro a o h
    cases h
  · intro a k v h
    cases h
  · intro h code hc
    split at hc
    · rename_i hh
      subst h
      rw [MathState.code?_empty]
      exact congrArg some (Except.ok.inj hc)
    · cases hc

-- A provider agreeing at one record need not agree at a different reserved hash.
example (consts other : HashConsts) (e : WitnessError)
    (hne : consts.emptyCodeHash ≠ other.emptyCodeHash)
    (root : BlockDiff → Id (Except WitnessError Hash32)) :
    let σ := MathState.mk ∅ ∅ ∅
    ModelsLookups consts (reservedOnly consts e root) σ ∧
      ¬ ModelsLookups other (reservedOnly consts e root) σ := by
  dsimp only
  refine ⟨reserved_agrees _ _ _ _, ?_⟩
  apply wrong_code other _ _ consts.emptyCodeHash ByteArray.empty
  · unfold reservedOnly
    rw [PreState.getCode_mk]
    simp
  · rw [MathState.code?_of_ne _ other _ hne, Std.ExtTreeMap.getElem?_empty]
    intro he
    cases he

-- Always-error callbacks include errors at the reserved hash, independent of arbitrary roots.
example (consts : HashConsts) (σ : MathState) (e : WitnessError) (r : Hash32) :
    ModelsLookups consts (failed e (fun _ ↦ .ok r)) σ ∧
      ModelsLookups consts (failed e (fun _ ↦ .error e)) σ ∧
      (failed e (fun _ ↦ .ok r)).getCode consts.emptyCodeHash = .error e := by
  refine ⟨errors_vacuous _ _ _ _, errors_vacuous _ _ _ _, ?_⟩
  unfold failed
  rw [PreState.getCode_mk]

end STFSpec.Conformance.State.ModelsLookupsGuards
