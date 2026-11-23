/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.TxState

/-!
# Transaction storage clear

Library `EthState`. See `STFSpec/informal/modules/EthState.md` R16.
-/

namespace STFSpec.State

open Base

private abbrev StorageReads := Std.HashSet (Address × Bytes32)

private def observePending (a : Address) (reads : StorageReads)
    (patch : Std.ExtTreeMap Bytes32 U256) : StorageReads :=
  patch.foldl (fun seen key _ ↦ seen.insert (a, key)) reads

private def clearRevertible (r : TxRevertible) (a : Address) : TxRevertible :=
  { r with
    storageWrites := r.storageWrites.erase a
    storageAddressOrder := r.storageAddressOrder.erase a
    storageSlotOrder := r.storageSlotOrder.erase a
    storageClears := r.storageClears.insert a }

private def clearedState {m : Type → Type} (t : TxState m) (a : Address) : TxState m :=
  let reads := match t.rev.storageWrites[a]? with
    | none => t.obs.storageReads
    | some patch => observePending a t.obs.storageReads patch
  { t with rev := clearRevertible t.rev a, obs.storageReads := reads }

private def clearStateLinear {m : Type → Type} (t : TxState m) (a : Address) : TxState m :=
  -- Take ownership of the read set before the fold so it can reuse exclusive buckets.
  let ⟨block, rev, ⟨accountReads, storageReads, codeReads, createdAccounts⟩⟩ := t
  let reads := match rev.storageWrites[a]? with
    | none => storageReads
    | some patch => observePending a storageReads patch
  ⟨block, clearRevertible rev a, ⟨accountReads, reads, codeReads, createdAccounts⟩⟩

private theorem clearStateLinear_eq {m : Type → Type} (t : TxState m) (a : Address) :
    clearStateLinear t a = clearedState t a := by
  rcases t with ⟨block, rev, obs⟩
  rcases obs with ⟨accountReads, storageReads, codeReads, createdAccounts⟩
  rfl

/-- Convert the target's pending slot keys to reads, drop its patch and mark a clear.
Implements EELS `src/ethereum/forks/amsterdam/state_tracker.py:528–549`.
An explicit zero write contributes its key. The action returns through one underlying
`pure` without calling a provider. -/
def destroyStorage {m : Type → Type} [Monad m] (a : Address) : StateM m Unit :=
  fun t ↦ ExceptT.mk (pure (.ok ((), clearStateLinear t a)))

private theorem run_destroyStorage {m : Type → Type} [Monad m] (t : TxState m) (a : Address) :
    ((destroyStorage a).run t).run = pure (.ok ((), clearedState t a)) := by
  change (pure (Except.ok ((), clearStateLinear t a)) : m (Except StateError (Unit × TxState m))) = _
  rw [clearStateLinear_eq]

private theorem storageReads_of_missing {m : Type → Type} (t : TxState m) (a : Address)
    (h : t.rev.storageWrites[a]? = none) :
    (clearedState t a).obs.storageReads = t.obs.storageReads := by
  simp only [clearedState, h]

private theorem storageReads_of_present {m : Type → Type} (t : TxState m) (a : Address)
    (patch : Std.ExtTreeMap Bytes32 U256) (h : t.rev.storageWrites[a]? = some patch) :
    (clearedState t a).obs.storageReads = observePending a t.obs.storageReads patch := by
  simp only [clearedState, h]

private theorem mem_observeKeys (reads : StorageReads) (a b : Address) (k : Bytes32)
    (keys : List Bytes32) :
    (b, k) ∈ keys.foldl (fun seen key ↦ seen.insert (a, key)) reads ↔
      (b, k) ∈ reads ∨ b = a ∧ k ∈ keys := by
  induction keys generalizing reads with
  | nil => simp
  | cons key rest ih =>
    rw [List.foldl_cons, ih, Std.HashSet.mem_insert]
    simp only [beq_iff_eq, Prod.mk.injEq, List.mem_cons]
    grind

private theorem mem_observePending (reads : StorageReads) (a b : Address) (k : Bytes32)
    (patch : Std.ExtTreeMap Bytes32 U256) :
    (b, k) ∈ observePending a reads patch ↔ (b, k) ∈ reads ∨ b = a ∧ k ∈ patch := by
  rw [observePending, Std.ExtTreeMap.foldl_eq_foldl_keys, mem_observeKeys]
  simp

private theorem storageReads_mem {m : Type → Type} (t : TxState m) (a b : Address)
    (k : Bytes32) :
    (b, k) ∈ (clearedState t a).obs.storageReads ↔
      (b, k) ∈ t.obs.storageReads ∨ b = a ∧
        (∃ patch, t.rev.storageWrites[a]? = some patch ∧ k ∈ patch) := by
  cases h : t.rev.storageWrites[a]? with
  | none => simp [storageReads_of_missing t a h]
  | some patch =>
    rw [storageReads_of_present t a patch h, mem_observePending]
    simp

private theorem storage_updates {m : Type → Type} (t : TxState m) (a : Address) :
    let r := (clearedState t a).rev
    r.storageWrites = t.rev.storageWrites.erase a ∧
      r.storageAddressOrder = t.rev.storageAddressOrder.erase a ∧
      r.storageSlotOrder = t.rev.storageSlotOrder.erase a ∧
      r.storageClears = t.rev.storageClears.insert a :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem target_cleared {m : Type → Type} (t : TxState m) (a : Address) :
    let r := (clearedState t a).rev
    r.storageWrites[a]? = none ∧ r.storageSlotOrder[a]? = none ∧ a ∈ r.storageClears := by
  simp [clearedState, clearRevertible]

private theorem storageAddressOrder_preserved {m : Type → Type} (t : TxState m) (a : Address)
    (wf : t.rev.storageAddressOrder.WF)
    (agrees : t.rev.storageAddressOrder.Agrees t.rev.storageWrites) :
    let r := (clearedState t a).rev
    r.storageAddressOrder.WF ∧ r.storageAddressOrder.Agrees r.storageWrites :=
  ⟨t.rev.storageAddressOrder.wf_erase a wf,
    t.rev.storageAddressOrder.agrees_erase_erase t.rev.storageWrites a agrees⟩

private theorem frames {m : Type → Type} (t : TxState m) (a : Address) :
    let next := clearedState t a
    next.block = t.block ∧ next.rev.accountWrites = t.rev.accountWrites ∧
      next.rev.accountOrder = t.rev.accountOrder ∧ next.rev.codeWrites = t.rev.codeWrites ∧
      next.rev.transient = t.rev.transient ∧ next.obs.accountReads = t.obs.accountReads ∧
      next.obs.codeReads = t.obs.codeReads ∧ next.obs.createdAccounts = t.obs.createdAccounts :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end STFSpec.State
