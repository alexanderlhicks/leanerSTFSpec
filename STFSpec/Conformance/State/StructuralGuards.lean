/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Structural premises and finite counterexamples

Library `EthConformance`: private symbolic omission proofs and complete raw finite guards.
The predicate stays logical; no decision procedure enumerates its address or slot domains.
Spec guidance: `STFSpec/informal/modules/EthState.md` §4/§7.4.
-/

namespace STFSpec.Conformance.StructuralGuards

open STFSpec.Base STFSpec.State

private theorem single_lookup {K V : Type} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
    [DecidableEq K] (key other : K) (value : V) :
    ((∅ : Std.ExtTreeMap K V).insert key value)[other]? =
      if key = other then some value else none := by
  rw [Std.ExtTreeMap.getElem?_insert]
  simp only [Std.compare_eq_iff_eq, Std.ExtTreeMap.getElem?_empty]

private def raw (a : Address) (account : Option Account) (slots : Std.ExtTreeMap Bytes32 U256)
    (code : Std.ExtTreeMap Hash32 ByteArray) : MathState :=
  ⟨account.elim ∅ (fun x ↦ (∅ : Std.ExtTreeMap Address Account).insert a x),
    (∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert a slots, code⟩

private def diff (ac : Std.ExtTreeMap Address (Option Account))
    (sc : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (cl : Std.ExtTreeSet Address) (cc : Std.ExtTreeMap Hash32 ByteArray := ∅) : BlockDiff :=
  ⟨ac, [], sc, [], ∅, cc, cl⟩

private theorem raw_wf (a : Address) (account : Account) (k : Bytes32) (v : U256)
    (hv : v ≠ U256.zero) (code : Std.ExtTreeMap Hash32 ByteArray) :
    MathState.WF (raw a (some account) ((∅ : Std.ExtTreeMap Bytes32 U256).insert k v) code) := by
  apply (MathState.wf_iff _).mpr
  dsimp only [raw, Option.elim]
  refine ⟨?_, ?_, ?_⟩
  · intro b slots hs j w hj
    rw [single_lookup] at hs
    split at hs
    · cases hs
      rw [single_lookup] at hj
      split at hj
      · cases hj
        exact hv
      · contradiction
    · contradiction
  · intro b slots hs
    rw [single_lookup] at hs
    split at hs
    · cases hs
      exact Std.ExtTreeMap.isEmpty_eq_false_iff.mpr Std.ExtTreeMap.insert_ne_empty
    · contradiction
  · intro b slots hs
    rw [single_lookup] at hs
    split at hs
    · rename_i hab
      subst b
      simp
    · contradiction

private theorem no_effects_premises (σ : MathState) :
    BlockDiff.StructuralPremises σ (diff ∅ ∅ ∅) := by
  apply (BlockDiff.structuralPremises_iff _ _).mpr
  constructor <;> intro a ha <;> simp [diff] at ha

private theorem no_effects_apply (σ : MathState) : σ.apply (diff ∅ ∅ ∅) = σ :=
  MathState.apply_of_no_changes σ _ rfl rfl rfl rfl

-- Omitting only deletion-to-clear leaves an orphan, even from a WF state.
private theorem deletion_omission (a : Address) (account : Account) (k : Bytes32) (v : U256)
    (hv : v ≠ U256.zero) (code : Std.ExtTreeMap Hash32 ByteArray) :
    let σ := raw a (some account) ((∅ : Std.ExtTreeMap Bytes32 U256).insert k v) code
    let d := diff ((∅ : Std.ExtTreeMap Address (Option Account)).insert a none) ∅ ∅
    MathState.WF σ ∧
      (∀ b : Address, d.storageChanges[b]?.isSome = true → (σ.apply d).account? b ≠ none) ∧
      ¬BlockDiff.StructuralPremises σ d ∧ ¬MathState.WF (σ.apply d) ∧
      (σ.apply d).account? a = none ∧
      (σ.apply d).storage[a]? = some ((∅ : Std.ExtTreeMap Bytes32 U256).insert k v) := by
  dsimp only
  have hd :
      (diff ((∅ : Std.ExtTreeMap Address (Option Account)).insert a none) ∅ ∅).accountChanges[a]? =
        some none := Std.ExtTreeMap.getElem?_insert_self
  have hcl :
      a ∉ (diff ((∅ : Std.ExtTreeMap Address (Option Account)).insert a none)
        ∅ ∅).storageClears := by
    simp [diff]
  have he := MathState.apply_storage_of_deleted_account_without_clear
    (raw a (some account) ((∅ : Std.ExtTreeMap Bytes32 U256).insert k v) code)
    (diff ((∅ : Std.ExtTreeMap Address (Option Account)).insert a none) ∅ ∅) a hd
    (by simp [diff]) hcl
  have hs :
      (raw a (some account) ((∅ : Std.ExtTreeMap Bytes32 U256).insert k v) code).storage[a]? =
        some ((∅ : Std.ExtTreeMap Bytes32 U256).insert k v) :=
    Std.ExtTreeMap.getElem?_insert_self
  rw [hs] at he
  refine ⟨raw_wf a account k v hv code, ?_, ?_, ?_, he⟩
  · simp [diff]
  · intro hp
    exact hcl (BlockDiff.structuralPremises_storage_clear _ _ hp a hd)
  · intro hw
    exact MathState.wf_storage_account_present _ a _ hw he.2 he.1

-- Omitting only post-account presence admits nonzero orphan writes.
private theorem account_omission (a : Address) (k : Bytes32) (v : U256) (hv : v ≠ U256.zero) :
    let σ : MathState := ⟨∅, ∅, ∅⟩
    let d := diff ∅ ((∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert a
      ((∅ : Std.ExtTreeMap Bytes32 U256).insert k v)) ∅
    MathState.WF σ ∧ (∀ b : Address, d.accountChanges[b]? = some none → b ∈ d.storageClears) ∧
      ¬BlockDiff.StructuralPremises σ d ∧ ¬MathState.WF (σ.apply d) ∧
      ((σ.apply d).storage[a]?).bind (fun slots ↦ slots[k]?) = some v := by
  dsimp only
  have ha : ((MathState.mk ∅ ∅ ∅).apply
      (diff ∅ ((∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert a
        ((∅ : Std.ExtTreeMap Bytes32 U256).insert k v)) ∅)).account? a = none := by
    rw [MathState.apply_account?_eq]
    simp [diff, MathState.account?_eq_lookup]
  have hs := MathState.apply_storage_slot_of_write_ne_zero (MathState.mk ∅ ∅ ∅)
    (diff ∅ ((∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert a
      ((∅ : Std.ExtTreeMap Bytes32 U256).insert k v)) ∅) a k v (by simp [diff]) hv
  refine ⟨MathState.wf_empty, ?_, ?_, ?_, hs⟩
  · simp [diff]
  · intro hp
    exact BlockDiff.structuralPremises_account_present _ _ hp a (by simp [diff]) ha
  · intro hw
    cases ho : ((MathState.mk ∅ ∅ ∅).apply
        (diff ∅ ((∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert a
          ((∅ : Std.ExtTreeMap Bytes32 U256).insert k v)) ∅)).storage[a]? with
    | none => simp [ho] at hs
    | some slots => exact MathState.wf_storage_account_present _ a slots hw ho ha

-- Raw patch presence counts even if it has no slots or contains only a zero.
private theorem absent_account_patch (a : Address) (writes : Std.ExtTreeMap Bytes32 U256) :
    ¬BlockDiff.StructuralPremises (MathState.mk ∅ ∅ ∅)
      (diff ∅ ((∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert a writes) ∅) := by
  intro hp
  apply BlockDiff.structuralPremises_account_present _ _ hp a (by simp [diff])
  rw [MathState.apply_account?_eq]
  simp [diff, MathState.account?_eq_lookup]

private theorem malformed_unchanged (σ : MathState) (hn : ¬MathState.WF σ) :
    BlockDiff.StructuralPremises σ (diff ∅ ∅ ∅) ∧ ¬MathState.WF (σ.apply (diff ∅ ∅ ∅)) := by
  rw [no_effects_apply]
  exact ⟨no_effects_premises σ, hn⟩

private theorem initial_zero (a : Address) (account : Account) (k : Bytes32) :
    let σ := raw a (some account) ((∅ : Std.ExtTreeMap Bytes32 U256).insert k U256.zero) ∅
    BlockDiff.StructuralPremises σ (diff ∅ ∅ ∅) ∧ ¬MathState.WF (σ.apply (diff ∅ ∅ ∅)) := by
  apply malformed_unchanged
  intro hw
  exact MathState.wf_storage_value_ne_zero _ a _ k U256.zero hw
    Std.ExtTreeMap.getElem?_insert_self Std.ExtTreeMap.getElem?_insert_self rfl

private theorem initial_empty (a : Address) (account : Account) :
    let σ := raw a (some account) ∅ ∅
    BlockDiff.StructuralPremises σ (diff ∅ ∅ ∅) ∧ ¬MathState.WF (σ.apply (diff ∅ ∅ ∅)) := by
  apply malformed_unchanged
  intro hw
  have he := MathState.wf_storage_nonempty _ a ∅ hw Std.ExtTreeMap.getElem?_insert_self
  simp at he

private theorem initial_orphan (a : Address) (k : Bytes32) (v : U256) :
    let σ := raw a none ((∅ : Std.ExtTreeMap Bytes32 U256).insert k v) ∅
    BlockDiff.StructuralPremises σ (diff ∅ ∅ ∅) ∧ ¬MathState.WF (σ.apply (diff ∅ ∅ ∅)) := by
  apply malformed_unchanged
  intro hw
  apply MathState.wf_storage_account_present _ a _ hw Std.ExtTreeMap.getElem?_insert_self
  rw [MathState.account?_eq_lookup]
  simp [raw]

-- Arbitrary account values and code/maps remain admissible; a replacement supplies presence.
private theorem replacement_premises (σ : MathState) (a : Address) (account : Account)
    (writes : Std.ExtTreeMap Bytes32 U256) (cl : Std.ExtTreeSet Address)
    (cc : Std.ExtTreeMap Hash32 ByteArray) :
    BlockDiff.StructuralPremises σ
      (diff ((∅ : Std.ExtTreeMap Address (Option Account)).insert a (some account))
        ((∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert a writes) cl cc) := by
  apply (BlockDiff.structuralPremises_iff _ _).mpr
  dsimp only [diff]
  constructor
  · intro b hb
    rw [single_lookup] at hb
    split at hb <;> simp at hb
  · intro b hb
    rw [single_lookup] at hb
    split at hb
    · rename_i hab
      subst b
      rw [MathState.apply_account?_eq]
      simp
    · simp at hb

private def a : Address := Address.ofNat (2 ^ 152 + 17)
private def other : Address := Address.ofNat (2 ^ 160 - 1)
private def k : Bytes32 := FixedBytes.ofNat (2 ^ 248 + 9)
private def j : Bytes32 := FixedBytes.ofNat (2 ^ 256 - 1)
private def account : Account := ⟨2 ^ 1024 + 17, U256.max, Hash32.ofBytes32 j⟩
private def code : Std.ExtTreeMap Hash32 ByteArray :=
  (∅ : Std.ExtTreeMap Hash32 ByteArray).insert HashConsts.literals.emptyCodeHash
    (Bytes.ofList [0, 128, 255, 0]).toByteArray
private def slots : Std.ExtTreeMap Bytes32 U256 :=
  (∅ : Std.ExtTreeMap Bytes32 U256).insert k U256.one
private def parent : MathState := raw a (some account) slots code
private def replacement (writes : Std.ExtTreeMap Bytes32 U256) (clear : Bool) : BlockDiff :=
  diff ((∅ : Std.ExtTreeMap Address (Option Account)).insert a (some account))
    ((∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert a writes)
    (if clear then (∅ : Std.ExtTreeSet Address).insert a else ∅) code
private def deletion (clear : Bool) : BlockDiff :=
  diff ((∅ : Std.ExtTreeMap Address (Option Account)).insert a none) ∅
    (if clear then (∅ : Std.ExtTreeSet Address).insert a else ∅)
private def observe (σ : MathState) :=
  (σ.accounts.toList.map (fun (b, x) ↦
    (b.toBytes.toList, x.nonce, x.balance.toNat, x.codeHash.toBytes.toList)),
   σ.storage.toList.map (fun (b, inner) ↦
    (b.toBytes.toList, inner.toList.map
      (fun kv : Bytes32 × U256 ↦ (kv.1.toBytes.toList, kv.2.toNat)))),
   σ.code.toList.map (fun (h, bytes) ↦ (h.toBytes.toList, bytes.toList)))

private theorem replacement_wf (writes : Std.ExtTreeMap Bytes32 U256) (clear : Bool) :
    MathState.WF (parent.apply (replacement writes clear)) :=
  MathState.wf_apply_of_structuralPremises parent _
    (raw_wf a account k U256.one (by decide) code)
    (replacement_premises parent a account writes _ code)

private theorem create_before_write :
    MathState.WF ((MathState.mk ∅ ∅ ∅).apply (replacement slots false)) :=
  MathState.wf_apply_of_structuralPremises _ _ MathState.wf_empty
    (replacement_premises _ a account slots _ code)

private theorem empty_and_zero_raw_presence :
    ¬BlockDiff.StructuralPremises (MathState.mk ∅ ∅ ∅)
      (diff ∅ ((∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert a ∅) ∅) ∧
    ¬BlockDiff.StructuralPremises (MathState.mk ∅ ∅ ∅)
      (diff ∅ ((∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert a
        ((∅ : Std.ExtTreeMap Bytes32 U256).insert k U256.zero)) ∅) :=
  ⟨absent_account_patch a ∅, absent_account_patch a _⟩

-- Complete account/storage/code observations, including optional inner-map distinctions.
#guard observe (parent.apply (diff ∅ ∅ ∅)) == observe parent
#guard (parent.apply (deletion false)).account? a = none
#guard (parent.apply (deletion false)).storage[a]?.map (fun inner ↦ inner.toList) =
  some slots.toList
#guard (parent.apply (deletion true)).storage[a]? = none
#guard observe (parent.apply (replacement ∅ false)) == observe parent
#guard (parent.apply (replacement ∅ true)).storage[a]? = none
#guard (parent.apply (replacement ((∅ : Std.ExtTreeMap Bytes32 U256).insert k U256.zero)
  false)).storage[a]? = none
#guard ((parent.apply (replacement ((∅ : Std.ExtTreeMap Bytes32 U256).insert j U256.max)
  true)).storage[a]?).map (fun inner ↦ inner.toList) =
  some [ (j, U256.max) ]
#guard ((parent.apply (replacement ((∅ : Std.ExtTreeMap Bytes32 U256).insert j U256.max)
  false)).storage[a]?).map (fun inner ↦ inner.toList) = some [(k, U256.one), (j, U256.max)]
#guard ((MathState.mk ∅ ∅ ∅).apply (replacement slots false)).account? a = some account
#guard ((MathState.mk ∅ ∅ ∅).apply (replacement slots false)).storage[a]?.map
  (fun inner ↦ inner.toList) = some slots.toList
#guard ((MathState.mk ∅ ∅ ∅).apply
  (diff ∅ ((∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert a ∅)
    ∅)).storage[a]? = none
#guard ((MathState.mk ∅ ∅ ∅).apply
  (diff ∅ ((∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert a
    ((∅ : Std.ExtTreeMap Bytes32 U256).insert k U256.zero)) ∅)).storage[a]? = none

private def strangeMetadata (d : BlockDiff) : BlockDiff :=
  { d with
    accountOrder := [other, a, a]
    storageAddressOrder := [a, other, other]
    storageSlotOrder := ((∅ : Std.ExtTreeMap Address (List Bytes32)).insert a []).insert
      other [j, k, k] }
private theorem metadata_invariance (σ : MathState) (d : BlockDiff) :
    BlockDiff.StructuralPremises σ d ↔ BlockDiff.StructuralPremises σ (strangeMetadata d) :=
  BlockDiff.structuralPremises_congr_effects σ d _ rfl rfl rfl rfl
#guard observe (parent.apply (strangeMetadata (replacement slots true))) ==
  observe (parent.apply (replacement slots true))

-- Deletion clearing is sufficient, yet deletion of an account with no storage needs no clear.
private theorem delete_clear : MathState.WF (parent.apply (deletion true)) := by
  apply MathState.wf_apply_of_structuralPremises _ _
    (raw_wf a account k U256.one (by decide) code)
  apply (BlockDiff.structuralPremises_iff _ _).mpr
  constructor
  · intro b hb
    change ((∅ : Std.ExtTreeMap Address (Option Account)).insert a none)[b]? = some none at hb
    rw [single_lookup] at hb
    split at hb
    · rename_i hab
      subst b
      simp [deletion, diff]
    · contradiction
  · simp [deletion, diff]

private theorem sufficient_not_necessary :
    let σ : MathState := ⟨(∅ : Std.ExtTreeMap Address Account).insert a account, ∅, code⟩
    MathState.WF (σ.apply (deletion false)) ∧
      ¬BlockDiff.StructuralPremises σ (deletion false) := by
  dsimp only
  constructor
  · apply (MathState.wf_iff _).mpr
    have hs := MathState.apply_storage_of_no_changes
      (MathState.mk ((∅ : Std.ExtTreeMap Address Account).insert a account) ∅ code)
      (deletion false) rfl rfl
    simp [hs]
  · intro hp
    have hc := BlockDiff.structuralPremises_storage_clear _ _ hp a
      Std.ExtTreeMap.getElem?_insert_self
    simp [deletion, diff] at hc

end STFSpec.Conformance.StructuralGuards
