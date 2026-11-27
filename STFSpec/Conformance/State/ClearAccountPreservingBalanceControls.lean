/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Balance-preserving account clear controls

Library `EthConformance`. Verify the ordered R16 and R18 actions, their
exact result and the complete local State effects. See EthState §§4/7.5.
-/

namespace STFSpec.Conformance.State.ClearAccountPreservingBalanceControls
open STFSpec.Base STFSpec.State

private theorem literal_action {m : Type → Type} [Monad m] (t : TxState m) (a : Address) :
    ((clearAccountPreservingBalance a).run t).run =
      (((destroyStorage a).run t).run >>= ExceptT.bindCont
        (fun pair : Unit × TxState m ↦
          match pair with
          | (_, next) =>
            (modifyState a (fun account ↦ .ok ⟨0, account.balance, t.block.consts.emptyCodeHash⟩)).run next)) :=
  rfl

private theorem after_first_clear (t next : TxState Id) (a : Address)
    (cleared : ((destroyStorage a).run t).run = .ok ((), next)) :
    ((clearAccountPreservingBalance a).run t).run =
      ((modifyState a (fun account ↦ .ok ⟨0, account.balance, t.block.consts.emptyCodeHash⟩)).run next).run := by
  rw [literal_action, cleared]
  rfl

private theorem after_provider_error (t next : TxState Id) (a : Address)
    (cleared : ((destroyStorage a).run t).run = .ok ((), next)) (error : StateError)
    (failed : ((modifyState a (fun account ↦ .ok ⟨0, account.balance, t.block.consts.emptyCodeHash⟩)).run next).run =
      .error error) :
    ((clearAccountPreservingBalance a).run t).run = .error error :=
  (after_first_clear t next a cleared).trans failed

private theorem cleared_empty (consts : HashConsts) (account : Account) :
    (⟨0, account.balance, consts.emptyCodeHash⟩ : Account) = emptyAccount consts ↔ account.balance = U256.zero := by
  constructor
  · intro same
    exact congrArg Account.balance same
  · intro zero
    exact Account.ext rfl zero rfl

private theorem restore_after_clear (t next : TxState Id) (a : Address)
    (succeeded : ((clearAccountPreservingBalance a).run t).run = .ok ((), next)) :
    (((do clearAccountPreservingBalance a; restoreTxState (copyTxState t)) : StateM Id Unit).run t).run =
      .ok ((), { next with rev := t.rev }) := by
  change ExceptT.bindCont (fun pair : Unit × TxState Id ↦
    match pair with
    | (_, state) => (restoreTxState (copyTxState t)).run state)
    ((clearAccountPreservingBalance a).run t).run = _
  rw [succeeded]
  rfl

private def target := Address.ofNat (2 ^ 159 + 47)
private def sibling := Address.ofNat 47
private def zeroKey : Bytes32 := FixedBytes.ofNat (2 ^ 255 + 53)
private def fundedKey : Bytes32 := FixedBytes.ofNat (2 ^ 255 + 59)
private def emptyHash := Hash32.ofBytes32 (FixedBytes.ofNat 61)
private def installedHash := Hash32.ofBytes32 (FixedBytes.ofNat 67)
private def consts : HashConsts := ⟨emptyHash, installedHash, emptyHash, installedHash⟩

private abbrev Slots := Std.ExtTreeMap Bytes32 U256

private def entry (prior : Option Account) (pending : Bool) : TxState Id :=
  let provider : PreState Id :=
    ⟨fun _ ↦ .ok none, fun _ _ ↦ .error (.missing .leaf),
      fun _ ↦ .error (.missing .leaf), fun _ ↦ .error (.missing .leaf)⟩
  let block := BlockState.new provider consts
  let tx := TxState.new { block with oldestAncestorOffset := some 71 }
  let accounts := tx.rev.accountWrites.insert sibling (some ⟨13, U256.ofNat 17, installedHash⟩)
  let records := prior.elim accounts (fun value ↦ accounts.insert target (some value))
  let order := tx.rev.accountOrder.record sibling
  let patch := (∅ : Slots).insert zeroKey U256.zero |>.insert fundedKey (U256.ofNat 73)
  let slotOrder := (WriteOrder.empty.record zeroKey).record fundedKey
  { tx with
    rev := { tx.rev with
      accountWrites := records
      accountOrder := if prior.isSome then order.record target else order
      storageWrites := if pending then tx.rev.storageWrites.insert target patch |>.insert sibling patch
        else tx.rev.storageWrites.insert sibling patch
      storageClears := tx.rev.storageClears.insert sibling
      storageAddressOrder := if pending then (tx.rev.storageAddressOrder.record target).record sibling
        else tx.rev.storageAddressOrder.record sibling
      storageSlotOrder := if pending then tx.rev.storageSlotOrder.insert target slotOrder |>.insert sibling slotOrder
        else tx.rev.storageSlotOrder.insert sibling slotOrder
      codeWrites := tx.rev.codeWrites.insert installedHash (ByteArray.mk #[0, 128, 255])
      transient := tx.rev.transient.insert (target, zeroKey) (U256.ofNat 79) }
    obs := { tx.obs with
      accountReads := tx.obs.accountReads.insert sibling
      storageReads := tx.obs.storageReads.insert (sibling, fundedKey)
      codeReads := tx.obs.codeReads.insert installedHash
      createdAccounts := tx.obs.createdAccounts.insert target } }

private def expected (t : TxState Id) (value : Option Account) (pending : Bool) : TxState Id :=
  let reads := t.obs.storageReads
  { t with
    rev := { t.rev with
      accountWrites := t.rev.accountWrites.insert target value
      accountOrder := t.rev.accountOrder.record target
      storageWrites := t.rev.storageWrites.erase target
      storageClears := t.rev.storageClears.insert target
      storageAddressOrder := t.rev.storageAddressOrder.erase target
      storageSlotOrder := t.rev.storageSlotOrder.erase target }
    obs := { t.obs with
      accountReads := t.obs.accountReads.insert target
      storageReads := if pending then (reads.insert (target, zeroKey)).insert (target, fundedKey) else reads } }

private def orderModel {K : Type} [Ord K] [Std.TransOrd K] (order : WriteOrder K) (key : K → Nat) :=
  (order.next, order.positions.toList.map (fun (k, index) ↦ (key k, index)),
    order.keysByPosition.toList.map (fun (index, k) ↦ (index, key k)))

private def cell (a : Address) (key : Bytes32) := (a.toNat, key.toNat)

private def overlayModel (t : TxState Id) :=
  (t.rev.accountWrites.toList.map (fun (a, value) ↦
    (a.toNat, value.map (fun (v : Account) ↦ (v.nonce, v.balance.toNat, v.codeHash.toNat)))),
  orderModel t.rev.accountOrder Address.toNat,
  t.rev.storageWrites.toList.map (fun (a, patch) ↦
    (a.toNat, patch.toList.map (fun ((k, v) : Bytes32 × U256) ↦ (k.toNat, v.toNat)))),
  t.rev.storageClears.toList.map Address.toNat,
  orderModel t.rev.storageAddressOrder Address.toNat,
  t.rev.storageSlotOrder.toList.map (fun (a, o) ↦ (a.toNat, orderModel o FixedBytes.toNat)),
  t.rev.codeWrites.toList.map (fun (h, bytes) ↦ (h.toNat, bytes.data.toList)),
  t.rev.transient.toList.map (fun ((a, k), v) ↦ (cell a k, v.toNat)),
  t.obs.accountReads.toList.map Address.toNat,
  t.obs.storageReads.toList.map (fun (a, k) ↦ cell a k),
  t.obs.codeReads.toList.map Hash32.toNat,
  t.obs.createdAccounts.toList.map Address.toNat,
  t.block.oldestAncestorOffset)

private def success (prior result : Option Account) (pending : Bool) : Bool :=
  let before := entry prior pending
  let want := expected before result pending
  match ((clearAccountPreservingBalance target).run before).run with
  | .error _ => false
  | .ok ((), after) =>
    overlayModel after == overlayModel want &&
      match ((restoreTxState (copyTxState before)).run after).run with
      | .ok ((), restored) => overlayModel restored == overlayModel { want with rev := before.rev }
      | .error _ => false

private abbrev ReadTrace := StateT (List Nat) Id

private def providerFailure : Bool :=
  let key := Hash32.ofBytes32 (FixedBytes.ofNat (2 ^ 255 + 101))
  let supplier : PreState ReadTrace :=
    ⟨fun a visited ↦ (.error (.missing (.node key)), visited ++ [a.toNat]),
      fun _ _ ↦ pure (.error (.missing .leaf)), fun _ ↦ pure (.error (.missing .leaf)),
      fun _ ↦ pure (.error (.missing .leaf))⟩
  let block := BlockState.new supplier consts
  let raw := entry none true
  let before : TxState ReadTrace := ⟨block, raw.rev, raw.obs⟩
  match (((clearAccountPreservingBalance target).run before).run).run [] with
  | (.error (.witness (.missing (.node item))), calls) => item == key && calls == [target.toNat]
  | _ => false

#guard success (some ⟨2 ^ 270 + 103, U256.max, installedHash⟩) (some ⟨0, U256.max, emptyHash⟩) true
#guard success (some ⟨103, U256.zero, installedHash⟩) none true
#guard success (some ⟨0, U256.ofNat 109, emptyHash⟩) (some ⟨0, U256.ofNat 109, emptyHash⟩) false
#guard success none none true
#guard success none none false
#guard providerFailure

end STFSpec.Conformance.State.ClearAccountPreservingBalanceControls
