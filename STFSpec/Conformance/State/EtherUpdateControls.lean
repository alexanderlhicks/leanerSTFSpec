/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Ether transfer and credit controls

Library `EthConformance`. These clients exercise the State facade using complete
transaction overlays and an observed provider. See EthState §§4/7.5.
-/

namespace STFSpec.Conformance.State.EtherUpdateControls
open STFSpec.Base STFSpec.State

private def sender := Address.ofNat 11
private def recipient := Address.ofNat 29
private def other := Address.ofNat 37
private def zeroKey : Bytes32 := FixedBytes.ofNat 13
private def fundedKey : Bytes32 := FixedBytes.ofNat 17
private def emptyCode := Hash32.ofBytes32 (FixedBytes.ofNat 59)
private def nonemptyCode := Hash32.ofBytes32 (FixedBytes.ofNat 61)
private def consts : HashConsts := ⟨emptyCode, emptyCode, emptyCode, emptyCode⟩

private def account (nonce balance : Nat) : Account :=
  ⟨nonce, U256.ofNat balance, if nonce = 0 then emptyCode else nonemptyCode⟩

private abbrev Slots := Std.ExtTreeMap Bytes32 U256

private def entry (fromAccount toAccount : Option Account) : TxState Id :=
  let provider : PreState Id :=
    ⟨fun _ ↦ .ok none, fun _ _ ↦ .error (.missing .leaf),
      fun _ ↦ .error (.missing .leaf), fun _ ↦ .error (.missing .leaf)⟩
  let block := BlockState.new provider consts
  let tx := TxState.new { block with oldestAncestorOffset := some 73 }
  let accounts := tx.rev.accountWrites.insert other (some (account 17 71))
  let accounts := fromAccount.elim accounts (fun value ↦ accounts.insert sender (some value))
  let accounts := toAccount.elim accounts (fun value ↦ accounts.insert recipient (some value))
  let patch := (∅ : Slots).insert zeroKey U256.zero |>.insert fundedKey (U256.ofNat 43)
  let slotOrder := (WriteOrder.empty.record zeroKey).record fundedKey
  { tx with
    rev := { tx.rev with
      accountWrites := accounts
      accountOrder := tx.rev.accountOrder.record other
      storageWrites := tx.rev.storageWrites.insert sender patch |>.insert recipient patch |>.insert other patch
      storageClears := tx.rev.storageClears.insert other
      storageAddressOrder := ((tx.rev.storageAddressOrder.record sender).record recipient).record other
      storageSlotOrder := tx.rev.storageSlotOrder.insert sender slotOrder
        |>.insert recipient slotOrder |>.insert other slotOrder
      codeWrites := tx.rev.codeWrites.insert nonemptyCode (ByteArray.mk #[0, 128, 255])
      transient := tx.rev.transient.insert (other, fundedKey) (U256.ofNat 53) }
    obs := { tx.obs with
      accountReads := tx.obs.accountReads.insert other
      storageReads := tx.obs.storageReads.insert (other, fundedKey)
      codeReads := tx.obs.codeReads.insert nonemptyCode
      createdAccounts := tx.obs.createdAccounts.insert other } }

private def touch (t : TxState Id) (a : Address) (value : Option Account) : TxState Id :=
  let rev := { t.rev with
    accountWrites := t.rev.accountWrites.insert a value
    accountOrder := t.rev.accountOrder.record a }
  let obs := { t.obs with accountReads := t.obs.accountReads.insert a }
  if value.isSome then { t with rev, obs }
  else
    { t with
      rev := { rev with
        storageWrites := rev.storageWrites.erase a
        storageClears := rev.storageClears.insert a
        storageAddressOrder := rev.storageAddressOrder.erase a
        storageSlotOrder := rev.storageSlotOrder.erase a }
      obs := { obs with storageReads := (obs.storageReads.insert (a, zeroKey)).insert (a, fundedKey) } }

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

private def check (op : StateM Id Unit) (before expected : TxState Id) : Bool :=
  match (op.run before).run with
  | .error _ => false
  | .ok ((), actual) => overlayModel actual == overlayModel expected

private def nonemptyTransfer : Bool :=
  let before := entry (some (account 7 47)) (some (account 9 101))
  let expected := touch (touch before sender (some (account 7 28))) recipient (some (account 9 120))
  check (moveEther sender recipient (U256.ofNat 19)) before expected

private def selfTransfer : Bool :=
  let before := entry (some (account 0 31)) none
  let expected := touch (touch before sender none) sender (some (account 0 31))
  check (moveEther sender sender (U256.ofNat 31)) before expected

private def zeroTransfer : Bool :=
  let before := entry none none
  check (moveEther sender recipient U256.zero) before (touch (touch before sender none) recipient none)

private def absentCredit : Bool :=
  let before := entry none none
  check (createEther recipient (U256.ofNat 31)) before (touch before recipient (some (account 0 31))) &&
    check (createEther recipient U256.zero) before (touch before recipient none)

private def maximumCredit : Bool :=
  let before := entry none (some (account 23 (U256.max.toNat - 1)))
  let expected := touch before recipient (some (account 23 U256.max.toNat))
  check (createEther recipient (U256.ofNat 1)) before expected &&
    match ((createEther recipient (U256.ofNat 2)).run before).run with
    | .error .balanceOverflow => true
    | _ => false

private abbrev ReadTrace := StateT (List Nat) Id

private def transferFault (enough : Bool) : Bool :=
  let provider : PreState ReadTrace :=
    ⟨fun a state ↦
      let value := if a = sender then account 7 (if enough then 1 else 0) else account 13 U256.max.toNat
      (.ok (some value), state ++ [a.toNat]),
      fun _ _ ↦ pure (.error (.missing .leaf)), fun _ ↦ pure (.error (.missing .leaf)),
      fun _ ↦ pure (.error (.missing .leaf))⟩
  let before := TxState.new (BlockState.new provider consts)
  match (((moveEther sender recipient (U256.ofNat 1)).run before).run).run [] with
  | (.error .balanceUnderflow, reads) => !enough && reads == [sender.toNat]
  | (.error .balanceOverflow, reads) => enough && reads == [sender.toNat, recipient.toNat]
  | _ => false

#guard nonemptyTransfer
#guard selfTransfer
#guard zeroTransfer
#guard absentCredit
#guard maximumCredit
#guard transferFault false
#guard transferFault true

end STFSpec.Conformance.State.EtherUpdateControls
