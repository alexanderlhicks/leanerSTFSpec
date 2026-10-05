/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.MathState
import STFSpec.State.BlockDiff

/-!
# Mathematical block diff application

Library `EthState`: raw finite-map application, with local zero deletion and touched-map pruning.
EELS `src/ethereum/state_mpt.py:133–161`; replay metadata and backend failures remain separate.
Spec guidance: `STFSpec/informal/modules/EthState.md`.
-/

namespace STFSpec.State.MathState

open Base

private theorem list_fold_lookup {α β γ δ : Type} [DecidableEq α]
    (f : β → α → γ → β) (observe : β → α → Option δ)
    (update : γ → Option δ → Option δ)
    (step : ∀ out key value a, observe (f out key value) a =
      if key = a then update value (observe out a) else observe out a)
    (entries : List (α × γ)) (distinct : entries.Pairwise (fun x y ↦ x.1 ≠ y.1))
    (base : β) (a : α) :
    observe (entries.foldl (fun out kv ↦ f out kv.1 kv.2) base) a =
      match entries.find? (fun kv ↦ decide (kv.1 = a)) with
      | Option.none => observe base a
      | Option.some kv => update kv.2 (observe base a) := by
  induction entries generalizing base with
  | nil => rfl
  | cons kv rest ih =>
    obtain ⟨hne, hrest⟩ := List.pairwise_cons.mp distinct
    rw [List.foldl_cons, ih hrest]
    by_cases hk : kv.1 = a
    · have hn : rest.find? (fun p ↦ decide (p.1 = a)) = none := by
        apply List.find?_eq_none.mpr
        intro p hp
        simp only [decide_eq_true_eq]
        intro ha
        exact hne p hp (hk.trans ha.symm)
      simp [hk, hn, step]
    · simp [hk, step]

private theorem map_fold_lookup {α β γ : Type} [Ord α] [DecidableEq α]
    [Std.TransOrd α] [Std.LawfulEqOrd α]
    (f : Std.ExtTreeMap α β → α → γ → Std.ExtTreeMap α β)
    (update : γ → Option β → Option β)
    (step : ∀ out key value a, (f out key value)[a]? =
      if key = a then update value out[a]? else out[a]?)
    (writes : Std.ExtTreeMap α γ) (base : Std.ExtTreeMap α β) (a : α) :
    (writes.foldl f base)[a]? =
      match writes[a]? with
      | Option.none => base[a]?
      | Option.some value => update value base[a]? := by
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  have hd : writes.toList.Pairwise (fun x y ↦ x.1 ≠ y.1) := by
    simpa only [Std.LawfulEqCmp.compare_eq_iff_eq] using
      Std.ExtTreeMap.distinct_keys_toList (t := writes)
  rw [list_fold_lookup f (fun out key ↦ out[key]?) update step writes.toList hd]
  have hp : (fun kv : α × γ ↦ decide (kv.1 = a)) =
      (fun kv ↦ compare kv.1 a == Ordering.eq) := by
    funext kv
    apply Bool.eq_iff_iff.mpr
    simp
  rw [hp]
  cases hw : writes[a]? with
  | none =>
    have hn : a ∉ writes := by simp [Std.ExtTreeMap.mem_iff_isSome_getElem?, hw]
    rw [Std.ExtTreeMap.find?_toList_eq_none_iff_not_mem.mpr hn]
  | some value =>
    have hm : a ∈ writes := by simp [Std.ExtTreeMap.mem_iff_isSome_getElem?, hw]
    have hs : writes.toList.find? (compare ·.1 a == Ordering.eq) = some (a, value) :=
      Std.ExtTreeMap.find?_toList_eq_some_iff_getKey?_eq_some_and_getElem?_eq_some.mpr
        ⟨Std.ExtTreeMap.getKey?_eq_some hm, hw⟩
    rw [hs]

private theorem erase_list_lookup {α β : Type} [Ord α] [DecidableEq α]
    [Std.TransOrd α] [Std.LawfulEqOrd α]
    (keys : List α) (base : Std.ExtTreeMap α β) (a : α) :
    (keys.foldl (fun out key ↦ out.erase key) base)[a]? =
      if a ∈ keys then none else base[a]? := by
  induction keys generalizing base with
  | nil => simp
  | cons key rest ih =>
    rw [List.foldl_cons, ih]
    simp only [List.mem_cons, Std.ExtTreeMap.getElem?_erase,
      Std.LawfulEqCmp.compare_eq_iff_eq]
    by_cases hk : key = a
    · simp [hk]
    · by_cases hr : a ∈ rest
      · simp [hr]
      · simp [hr, hk, Ne.symm hk]

private theorem clear_fold_lookup (clears : Std.ExtTreeSet Address)
    (base : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256 compare)) (a : Address) :
    (clears.foldl (fun out key ↦ out.erase key) base)[a]? =
      if a ∈ clears then none else base[a]? := by
  rw [Std.ExtTreeSet.foldl_eq_foldl_toList, erase_list_lookup]
  simp only [Std.ExtTreeSet.mem_toList]

private def writeAccount (out : Std.ExtTreeMap Address Account) (a : Address)
    (replacement : Option Account) : Std.ExtTreeMap Address Account :=
  match replacement with
  | Option.none => out.erase a
  | Option.some account => out.insert a account

private def writeSlot (out : Std.ExtTreeMap Bytes32 U256 compare) (k : Bytes32) (v : U256) :
    Std.ExtTreeMap Bytes32 U256 compare :=
  if v = U256.zero then out.erase k else out.insert k v

private def writeStorage (out : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256 compare))
    (a : Address) (writes : Std.ExtTreeMap Bytes32 U256 compare) :
    Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256 compare) :=
  let slots := writes.foldl writeSlot (out[a]?.getD ∅)
  if slots.isEmpty then out.erase a else out.insert a slots

/-- Apply raw changes: clear storage, replace/delete accounts, write/prune touched storage,
then overwrite all raw code. EELS `src/ethereum/state_mpt.py:133–161`. -/
def apply (σ : MathState) (d : BlockDiff) : MathState :=
  let cleared := d.storageClears.foldl (fun out a ↦ out.erase a) σ.storage
  let accounts := d.accountChanges.foldl writeAccount σ.accounts
  let storage := d.storageChanges.foldl writeStorage cleared
  let code := d.codeChanges.foldl (fun out h bytes ↦ out.insert h bytes) σ.code
  ⟨accounts, storage, code⟩

private theorem account_fold_lookup (writes : Std.ExtTreeMap Address (Option Account))
    (base : Std.ExtTreeMap Address Account) (a : Address) :
    (writes.foldl writeAccount base)[a]? =
      match writes[a]? with
      | Option.none => base[a]?
      | Option.some replacement => replacement := by
  have he := map_fold_lookup writeAccount (fun replacement _ ↦ replacement)
    (fun out key replacement query ↦ by
      cases replacement <;>
        simp [writeAccount, Std.ExtTreeMap.getElem?_erase, Std.ExtTreeMap.getElem?_insert])
    writes base a
  cases hw : writes[a]? <;> simpa only [hw] using he

private theorem slot_fold_lookup (writes : Std.ExtTreeMap Bytes32 U256 compare)
    (base : Std.ExtTreeMap Bytes32 U256 compare) (k : Bytes32) :
    (writes.foldl writeSlot base)[k]? =
      match writes[k]? with
      | Option.none => base[k]?
      | Option.some value => if value = U256.zero then none else some value := by
  have he := map_fold_lookup writeSlot (fun value _ ↦
    if value = U256.zero then none else some value)
    (fun out key value query ↦ by
      by_cases hv : value = U256.zero <;>
        simp [writeSlot, hv, Std.ExtTreeMap.getElem?_erase, Std.ExtTreeMap.getElem?_insert])
    writes base k
  cases hw : writes[k]? <;> simpa only [hw] using he

private theorem storage_fold_lookup
    (writes : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256 compare))
    (base : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256 compare)) (a : Address) :
    (writes.foldl writeStorage base)[a]? =
      (writes[a]?).elim base[a]? (fun (slots : Std.ExtTreeMap Bytes32 U256 compare) ↦
        let out := slots.foldl writeSlot (base[a]?.getD ∅)
        if out.isEmpty then none else some out) := by
  have he := map_fold_lookup writeStorage
    (fun (slots : Std.ExtTreeMap Bytes32 U256 compare) old ↦
      let out := slots.foldl writeSlot (old.getD ∅)
      if out.isEmpty then none else some out)
    (fun out key slots query ↦ by
      by_cases hk : key = query
      · subst key
        simp only [writeStorage, ite_true]
        split <;> simp
      · simp only [writeStorage, hk, ite_false]
        split <;>
          simp [Std.ExtTreeMap.getElem?_erase, Std.ExtTreeMap.getElem?_insert, hk])
    writes base a
  cases hw : writes[a]? <;> simpa only [hw, Option.elim] using he

private theorem code_fold_lookup (writes : Std.ExtTreeMap Hash32 ByteArray)
    (base : Std.ExtTreeMap Hash32 ByteArray) (h : Hash32) :
    (writes.foldl (fun out key bytes ↦ out.insert key bytes) base)[h]? =
      match (writes[h]? : Option ByteArray) with
      | Option.none => base[h]?
      | Option.some bytes => some bytes := by
  have he := map_fold_lookup (fun out key bytes ↦ out.insert key bytes)
    (fun bytes _ ↦ some bytes)
    (fun out key bytes query ↦ by simp [Std.ExtTreeMap.getElem?_insert]) writes base h
  cases hw : writes[h]? <;> simpa only [hw] using he

/-- Account changes preserve absence, exact replacements and explicit deletion markers. -/
theorem apply_accounts_lookup (σ : MathState) (d : BlockDiff) (a : Address) :
    (σ.apply d).accounts[a]? =
      match d.accountChanges[a]? with
      | Option.none => σ.accounts[a]?
      | Option.some replacement => replacement :=
  account_fold_lookup d.accountChanges σ.accounts a

/-- Account observation after application is the exact change or original observation. -/
theorem apply_account?_eq (σ : MathState) (d : BlockDiff) (a : Address) :
    (σ.apply d).account? a =
      match d.accountChanges[a]? with
      | Option.none => σ.account? a
      | Option.some replacement => replacement := apply_accounts_lookup σ d a

/-- Complete optional storage maps retain clear-before-write and actual-empty local pruning. -/
theorem apply_storage_lookup (σ : MathState) (d : BlockDiff) (a : Address) :
    (σ.apply d).storage[a]? =
      match d.storageChanges[a]? with
      | Option.none => if a ∈ d.storageClears then none else σ.storage[a]?
      | Option.some writes =>
        let out := writes.foldl (fun out k v ↦
          if v = U256.zero then out.erase k else out.insert k v)
          ((if a ∈ d.storageClears then none else σ.storage[a]?).getD ∅)
        if out.isEmpty then none else some out := by
  change (d.storageChanges.foldl writeStorage
    (d.storageClears.foldl (fun out key ↦ out.erase key) σ.storage))[a]? = _
  rw [storage_fold_lookup, clear_fold_lookup]
  cases d.storageChanges[a]? <;> rfl

/-- Raw code changes overwrite complete bytes even at a reserved hash. -/
theorem apply_code_lookup (σ : MathState) (d : BlockDiff) (h : Hash32) :
    (σ.apply d).code[h]? =
      match d.codeChanges[h]? with
      | Option.none => σ.code[h]?
      | Option.some bytes => some bytes := code_fold_lookup d.codeChanges σ.code h

/-- Code observation retains the caller's reserved-hash bypass after the raw update. -/
theorem apply_code?_eq (σ : MathState) (d : BlockDiff) (consts : HashConsts) (h : Hash32) :
    (σ.apply d).code? consts h =
      if h = consts.emptyCodeHash then some ByteArray.empty else
        match d.codeChanges[h]? with
        | Option.none => σ.code[h]?
        | Option.some bytes => some bytes := by
  simp only [code?, apply_code_lookup]


private theorem pruned_slot_lookup (slots : Std.ExtTreeMap Bytes32 U256 compare) (k : Bytes32) :
    ((if slots.isEmpty then none else some slots).bind (fun out ↦ out[k]?)) = slots[k]? := by
  by_cases he : slots.isEmpty = true
  · have hz : slots = ∅ := Std.ExtTreeMap.isEmpty_iff.mp he
    simp [hz]
  · simp [he]

private theorem default_slots_lookup (old : Option (Std.ExtTreeMap Bytes32 U256 compare))
    (k : Bytes32) : (old.getD ∅)[k]? = old.bind (fun slots ↦ slots[k]?) := by
  cases old <;> simp

private theorem applied_slot_lookup (σ : MathState) (d : BlockDiff) (a : Address) (k : Bytes32) :
    ((σ.apply d).storage[a]?).bind (fun slots ↦ slots[k]?) =
      match (d.storageChanges[a]?).bind (fun writes ↦ writes[k]?) with
      | none => if a ∈ d.storageClears then none else
          (σ.storage[a]?).bind (fun slots ↦ slots[k]?)
      | some value => if value = U256.zero then none else some value := by
  rw [apply_storage_lookup]
  cases hw : d.storageChanges[a]? with
  | none =>
    simp only [Option.bind_none]
    by_cases hc : a ∈ d.storageClears <;> simp [hc]
  | some writes =>
    simp only [Option.bind_some]
    rw [pruned_slot_lookup]
    change (writes.foldl writeSlot
      ((if a ∈ d.storageClears then none else σ.storage[a]?).getD ∅))[k]? = _
    rw [slot_fold_lookup]
    cases hk : writes[k]? with
    | none =>
      simp only
      rw [default_slots_lookup]
      by_cases hc : a ∈ d.storageClears <;> simp [hc]
    | some value => simp only

/-- Visible storage uses slot writes first, then clear suppression, then the original state. -/
theorem apply_storageAt_eq (σ : MathState) (d : BlockDiff) (a : Address) (k : Bytes32) :
    (σ.apply d).storageAt a k =
      match (d.storageChanges[a]?).bind (fun writes ↦ writes[k]?) with
      | none => if a ∈ d.storageClears then U256.zero else σ.storageAt a k
      | some value => value := by
  rw [storageAt_eq_lookup, applied_slot_lookup]
  cases hq : (d.storageChanges[a]?).bind (fun writes ↦ writes[k]?) with
  | none =>
    simp only
    by_cases hc : a ∈ d.storageClears <;> simp [hc, storageAt_eq_lookup]
  | some value =>
    simp only
    by_cases hv : value = U256.zero <;> simp [hv]

/-- With no account changes the complete original account map is retained. -/
theorem apply_accounts_of_no_changes (σ : MathState) (d : BlockDiff)
    (hac : d.accountChanges = ∅) : (σ.apply d).accounts = σ.accounts := by
  apply Std.ExtTreeMap.ext_getElem?
  intro a
  rw [apply_accounts_lookup]
  simp [hac]

/-- With no storage changes or clears the complete original storage map is retained. -/
theorem apply_storage_of_no_changes (σ : MathState) (d : BlockDiff)
    (hsc : d.storageChanges = ∅) (hcl : d.storageClears = ∅) :
    (σ.apply d).storage = σ.storage := by
  apply Std.ExtTreeMap.ext_getElem?
  intro a
  rw [apply_storage_lookup]
  simp [hsc, hcl]

/-- With no code changes the complete original raw code map is retained. -/
theorem apply_code_of_no_changes (σ : MathState) (d : BlockDiff)
    (hcc : d.codeChanges = ∅) : (σ.apply d).code = σ.code := by
  apply Std.ExtTreeMap.ext_getElem?
  intro h
  rw [apply_code_lookup]
  simp [hcc]

/-- No effect fields means exact raw identity, for arbitrary states and metadata. -/
theorem apply_of_no_changes (σ : MathState) (d : BlockDiff)
    (hac : d.accountChanges = ∅) (hsc : d.storageChanges = ∅)
    (hcc : d.codeChanges = ∅) (hcl : d.storageClears = ∅) : σ.apply d = σ :=
  ext (apply_accounts_of_no_changes σ d hac) (apply_storage_of_no_changes σ d hsc hcl)
    (apply_code_of_no_changes σ d hcc)

/-- Equal effect fields give equal mathematical states irrespective of all replay metadata. -/
theorem apply_congr_effects (σ : MathState) (d e : BlockDiff)
    (hac : d.accountChanges = e.accountChanges) (hsc : d.storageChanges = e.storageChanges)
    (hcc : d.codeChanges = e.codeChanges) (hcl : d.storageClears = e.storageClears) :
    σ.apply d = σ.apply e := by
  simp only [apply, hac, hsc, hcc, hcl]

/-- Untouched addresses retain whole optional raw inner maps, including malformed entries. -/
theorem apply_storage_of_untouched (σ : MathState) (d : BlockDiff) (a : Address)
    (hsc : d.storageChanges[a]? = none) (hcl : a ∉ d.storageClears) :
    (σ.apply d).storage[a]? = σ.storage[a]? := by
  rw [apply_storage_lookup]
  simp [hsc, hcl]

/-- Account deletion without storage effects leaves storage unchanged at that address. -/
theorem apply_storage_of_deleted_account_without_clear (σ : MathState) (d : BlockDiff)
    (a : Address) (hac : d.accountChanges[a]? = some none)
    (hsc : d.storageChanges[a]? = none) (hcl : a ∉ d.storageClears) :
    (σ.apply d).account? a = none ∧ (σ.apply d).storage[a]? = σ.storage[a]? := by
  constructor
  · rw [apply_account?_eq]
    simp [hac]
  · exact apply_storage_of_untouched σ d a hsc hcl

/-- A clear with no address writes removes that complete storage entry. -/
theorem apply_storage_of_clear_no_writes (σ : MathState) (d : BlockDiff) (a : Address)
    (hcl : a ∈ d.storageClears) (hsc : d.storageChanges[a]? = none) :
    (σ.apply d).storage[a]? = none := by
  rw [apply_storage_lookup]
  simp [hsc, hcl]

/-- An empty write map still prunes an actually empty post-clear base at its touched address. -/
theorem apply_storage_of_empty_writes (σ : MathState) (d : BlockDiff) (a : Address)
    (hsc : d.storageChanges[a]? = some (∅ : Std.ExtTreeMap Bytes32 U256 compare)) :
    (σ.apply d).storage[a]? =
      let base := (if a ∈ d.storageClears then none else σ.storage[a]?).getD ∅
      if base.isEmpty then none else some base := by
  rw [apply_storage_lookup]
  have he : (∅ : Std.ExtTreeMap Bytes32 U256 compare).toList = [] :=
    Std.ExtTreeMap.toList_eq_nil_iff.mpr rfl
  simp only [hsc, Std.ExtTreeMap.foldl_eq_foldl_toList, he, List.foldl_nil]

/-- An explicit zero write erases its raw slot rather than storing zero. -/
theorem apply_storage_slot_of_write_zero (σ : MathState) (d : BlockDiff)
    (a : Address) (k : Bytes32)
    (hq : (d.storageChanges[a]?).bind (fun writes ↦ writes[k]?) = some U256.zero) :
    ((σ.apply d).storage[a]?).bind (fun slots ↦ slots[k]?) = none := by
  rw [applied_slot_lookup]
  simp [hq]

/-- A nonzero write stores exactly its value, independently of account existence and clears. -/
theorem apply_storage_slot_of_write_ne_zero (σ : MathState) (d : BlockDiff)
    (a : Address) (k : Bytes32) (v : U256)
    (hq : (d.storageChanges[a]?).bind (fun writes ↦ writes[k]?) = some v)
    (hv : v ≠ U256.zero) :
    ((σ.apply d).storage[a]?).bind (fun slots ↦ slots[k]?) = some v := by
  rw [applied_slot_lookup]
  simp [hq, hv]

/-- An unwritten slot retains its exact optional raw value unless the address was cleared. -/
theorem apply_storage_slot_of_no_write (σ : MathState) (d : BlockDiff) (a : Address)
    (k : Bytes32) (hq : (d.storageChanges[a]?).bind (fun writes ↦ writes[k]?) = none) :
    ((σ.apply d).storage[a]?).bind (fun slots ↦ slots[k]?) =
      if a ∈ d.storageClears then none else (σ.storage[a]?).bind (fun slots ↦ slots[k]?) := by
  rw [applied_slot_lookup]
  simp [hq]

end STFSpec.State.MathState
