/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.AccountOptional
import STFSpec.State.WriteOrder

/-!
# Transaction storage writes

Library `EthState`. The account read admits a write to the transaction overlay.
The write retains zeros and a prior clear.
Spec guidance: `STFSpec/informal/modules/EthState.md` R15, R29 and §7.
-/

namespace STFSpec.State

open Base

private def recordStorage (r : TxRevertible) (a : Address) (k : Bytes32) (v : U256) :
    TxRevertible :=
  let slots := r.storageWrites[a]?.getD ∅
  let order := r.storageSlotOrder[a]?.getD WriteOrder.empty
  { r with
    storageWrites := r.storageWrites.insert a (slots.insert k v)
    storageAddressOrder := r.storageAddressOrder.record a
    storageSlotOrder := r.storageSlotOrder.insert a (order.record k) }

/-- Read the current optional account before writing the slot. On presence,
record the complete word using the returned transaction, including an explicit
zero. Preserve the read's exact error and fail on successful absence.
EELS `src/ethereum/forks/amsterdam/state_tracker.py:457–481` at the pin. -/
def setStorage {m : Type → Type} [Monad m] (a : Address) (k : Bytes32) (v : U256) :
    StateM m Unit := fun t ↦ ExceptT.mk do
  match ← ((getAccountOptional a).run t).run with
  | .error error => pure (.error error)
  | .ok (none, _) => pure (.error .storageOnMissingAccount)
  | .ok (some _, readState) =>
    pure (.ok ((), { readState with rev := recordStorage readState.rev a k v }))

private theorem setStorage_action {m : Type → Type} [Monad m] (t : TxState m)
    (a : Address) (k : Bytes32) (v : U256) :
    ((setStorage a k v).run t).run = (do
      match ← ((getAccountOptional a).run t).run with
      | .error error => pure (.error error)
      | .ok (none, _) => pure (.error .storageOnMissingAccount)
      | .ok (some _, readState) =>
        pure (.ok ((), { readState with rev := recordStorage readState.rev a k v }))) := rfl

private theorem setStorage_of_present (t readState : TxState Id) (a : Address) (k : Bytes32)
    (v : U256) (account : Account)
    (read : ((getAccountOptional a).run t).run = .ok (some account, readState)) :
    ((setStorage a k v).run t).run =
      .ok ((), { readState with rev := recordStorage readState.rev a k v }) := by
  rw [setStorage_action, read]
  rfl

private theorem recordedAddressOrder (r : TxRevertible) (a : Address) (k : Bytes32) (v : U256)
    (wf : r.storageAddressOrder.WF)
    (agrees : r.storageAddressOrder.Agrees r.storageWrites) :
    (recordStorage r a k v).storageAddressOrder.WF ∧
      (recordStorage r a k v).storageAddressOrder.Agrees (recordStorage r a k v).storageWrites :=
  ⟨r.storageAddressOrder.wf_record a wf,
    r.storageAddressOrder.agrees_record_insert r.storageWrites a
      ((r.storageWrites[a]?.getD ∅).insert k v) agrees⟩

private theorem recordedSlotOrder (r : TxRevertible) (a : Address) (k : Bytes32) (v : U256)
    (wf : (r.storageSlotOrder[a]?.getD WriteOrder.empty).WF)
    (agrees : (r.storageSlotOrder[a]?.getD WriteOrder.empty).Agrees (r.storageWrites[a]?.getD ∅)) :
    ((recordStorage r a k v).storageSlotOrder[a]?.getD WriteOrder.empty).WF ∧
      ((recordStorage r a k v).storageSlotOrder[a]?.getD WriteOrder.empty).Agrees
        ((recordStorage r a k v).storageWrites[a]?.getD ∅) := by
  simp only [recordStorage, Std.ExtTreeMap.getElem?_insert_self, Option.getD_some]
  exact ⟨WriteOrder.wf_record _ _ wf, WriteOrder.agrees_record_insert _ _ _ _ agrees⟩

private def slotAt (r : TxRevertible) (a : Address) (k : Bytes32) : Option U256 :=
  r.storageWrites[a]?.bind fun slots ↦ slots[k]?

private theorem slotAt_recordStorage
    (r : TxRevertible) (a b : Address) (k j : Bytes32) (v : U256) :
    slotAt (recordStorage r a k v) b j = if a = b ∧ k = j then some v else slotAt r b j := by
  by_cases sameAddress : a = b
  · subst b
    simp only [slotAt, recordStorage, Std.ExtTreeMap.getElem?_insert_self, Option.bind_some,
      Std.ExtTreeMap.getElem?_insert, Std.compare_eq_iff_eq, true_and]
    cases r.storageWrites[a]? <;> simp
  · simp only [slotAt, recordStorage, Std.ExtTreeMap.getElem?_insert, Std.compare_eq_iff_eq,
      sameAddress, ↓reduceIte, false_and]

private theorem viewStorage {m : Type → Type} (σ : MathState) (t : TxState m)
    (a : Address) (k : Bytes32) :
    (t.view σ).storageAt a k = match slotAt t.rev a k with
    | none => if a ∈ t.rev.storageClears then U256.zero else (t.block.view σ).storageAt a k
    | some value => value := by
  rw [TxState.view, MathState.apply_storageAt_eq]
  rfl

private theorem recordedView {m : Type → Type} (σ : MathState) (t : TxState m)
    (a b : Address) (k j : Bytes32) (v : U256) :
    ({ t with rev := recordStorage t.rev a k v }.view σ).storageAt b j =
      if a = b ∧ k = j then v else (t.view σ).storageAt b j := by
  rw [viewStorage, viewStorage]
  change (match slotAt (recordStorage t.rev a k v) b j with
    | none => if b ∈ t.rev.storageClears then U256.zero else (t.block.view σ).storageAt b j
    | some value => value) = _
  rw [slotAt_recordStorage]
  by_cases same : a = b ∧ k = j <;> simp [same]

private theorem setStorage_view (σ : MathState) (t readState : TxState Id)
    (a b : Address) (k j : Bytes32) (v : U256) (account : Account)
    (read : ((getAccountOptional a).run t).run = .ok (some account, readState)) :
    ((setStorage a k v).run t).run.map (fun result ↦ (result.2.view σ).storageAt b j) =
      .ok (if a = b ∧ k = j then v else (t.view σ).storageAt b j) := by
  obtain ⟨sameBlock, sameRev, _⟩ := getAccountOptional_frames t a (some account) readState read
  rw [setStorage_of_present t readState a k v account read]
  change (Except.ok (({ readState with rev := recordStorage readState.rev a k v }.view σ).storageAt
    b j) : Except StateError U256) = _
  rw [recordedView, viewStorage, sameRev, sameBlock, ← viewStorage]

end STFSpec.State
