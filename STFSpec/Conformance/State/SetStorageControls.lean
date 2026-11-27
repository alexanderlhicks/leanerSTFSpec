/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Transaction storage write controls

Library `EthConformance`. These State facade clients check R15 account
admission, provider effects, and the complete transaction and order updates.
Spec guidance: `STFSpec/informal/modules/EthState.md` §4.
-/

namespace STFSpec.Conformance.State.SetStorageControls

open STFSpec.Base STFSpec.State

private def target := Address.ofNat 11
private def sibling := Address.ofNat 17
private def later := Address.ofNat 5
private def slot : Bytes32 := FixedBytes.ofNat 19
private def oldSlot : Bytes32 := FixedBytes.ofNat 23
private def hash := Hash32.ofBytes32 (FixedBytes.ofNat 29)
private def retainedHash := Hash32.ofBytes32 (FixedBytes.ofNat 31)
private def consts : HashConsts := ⟨hash, retainedHash, hash, retainedHash⟩
private def blank := emptyAccount consts
private def account : Account := ⟨43, U256.ofNat 47, retainedHash⟩
private def fault : WitnessError := .malformed (.node retainedHash)

private inductive Event where
  | account (a : Address)
  | storage
  | code
  | root
  deriving BEq

private abbrev Observing := StateT (List Event) Id

private def observe {α : Type} (event : Event) (value : α) : Observing α :=
  fun prior ↦ pure (value, prior ++ [event])

private def provider (answer : Except WitnessError (Option Account)) : PreState Observing :=
  ⟨fun a ↦ observe (.account a) answer, fun _ _ ↦ observe .storage (.error fault),
    fun _ ↦ observe .code (.error fault), fun _ ↦ observe .root (.error fault)⟩

private abbrev Slots := Std.ExtTreeMap Bytes32 U256

private def slots : Slots := (∅ : Slots).insert oldSlot (U256.ofNat 53)

private def block (answer : Except WitnessError (Option Account))
    (patch : Option (Option Account)) : BlockState Observing :=
  let b := BlockState.new (provider answer) consts
  { b with
    accountWrites := match patch with
      | some value => b.accountWrites.insert target value
      | none => b.accountWrites
    storageWrites := b.storageWrites.insert target (slots.insert slot (U256.ofNat 59))
    storageAddressOrder := b.storageAddressOrder.record target
    storageSlotOrder := b.storageSlotOrder.insert target
      ((WriteOrder.empty.record oldSlot).record slot)
    oldestAncestorOffset := some 61
    accountReads := b.accountReads.insert later }

private def transaction (answer : Except WitnessError (Option Account))
    (txPatch blockPatch : Option (Option Account)) : TxState Observing :=
  let t := TxState.new (block answer blockPatch)
  { t with
    rev := { t.rev with
      accountWrites := match txPatch with
        | some value => (t.rev.accountWrites.insert sibling (some account)).insert target value
        | none => t.rev.accountWrites.insert sibling (some account)
      accountOrder := t.rev.accountOrder.record sibling
      storageWrites := (t.rev.storageWrites.insert sibling slots).insert target slots
      storageAddressOrder := (t.rev.storageAddressOrder.record sibling).record target
      storageSlotOrder := t.rev.storageSlotOrder.insert sibling (WriteOrder.empty.record oldSlot)
        |>.insert target (WriteOrder.empty.record oldSlot)
      storageClears := t.rev.storageClears.insert target
      codeWrites := t.rev.codeWrites.insert hash (ByteArray.mk #[0, 128, 255])
      transient := t.rev.transient.insert (target, slot) (U256.ofNat 67) }
    obs := { t.obs with
      accountReads := t.obs.accountReads.insert sibling
      storageReads := t.obs.storageReads.insert (sibling, oldSlot)
      codeReads := t.obs.codeReads.insert retainedHash
      createdAccounts := t.obs.createdAccounts.insert target } }

private def run (t : TxState Observing) (a : Address) (k : Bytes32) (v : U256)
    (events : List Event) :=
  Id.run <| (((setStorage a k v).run t).run).run events

private def expectedFirstSlot (t : TxState Observing) (reads : Std.HashSet Address) :
    TxState Observing :=
  { t with
    obs.accountReads := reads
    rev := { t.rev with
      storageWrites := t.rev.storageWrites.insert target (slots.insert slot U256.zero)
      storageSlotOrder := t.rev.storageSlotOrder.insert target
        ((WriteOrder.empty.record oldSlot).record slot) } }

private def orderEntries {K : Type} [Ord K] [Std.TransOrd K] (order : WriteOrder K)
    (toNat : K → Nat) :=
  (order.next, order.positions.toList.map (fun (k, p) ↦ (toNat k, p)),
    order.keysByPosition.toList.map (fun (p, k) ↦ (p, toNat k)))

private def accountEntries (writes : Std.ExtTreeMap Address (Option Account)) :=
  writes.toList.map (fun (a, value) ↦ (a.toNat, value.map fun (account : Account) ↦
    (account.nonce, account.balance.toNat, account.codeHash.toNat)))

private def slotEntries (values : Slots) :=
  values.toList.map (fun (k, value) ↦ (FixedBytes.toNat k, U256.toNat value))

private def storageEntries (writes : Std.ExtTreeMap Address Slots) :=
  writes.toList.map (fun (a, values) ↦ (a.toNat, slotEntries values))

private def slotOrderEntries (orders : Std.ExtTreeMap Address (WriteOrder Bytes32)) :=
  orders.toList.map (fun (a, order) ↦ (a.toNat, orderEntries order FixedBytes.toNat))

private def codeEntries (writes : Std.ExtTreeMap Hash32 ByteArray) :=
  writes.toList.map (fun (h, code) ↦ (h.toNat, code.data.toList))

private def cell (key : Address × Bytes32) := (key.1.toNat, key.2.toNat)

private def sameBlockFields (b expected : BlockState Observing) : Bool :=
  (b.consts.emptyCodeHash, b.consts.emptyTrieRoot, b.consts.emptyOmmerHash,
    b.consts.transferTopic) ==
      (expected.consts.emptyCodeHash, expected.consts.emptyTrieRoot,
        expected.consts.emptyOmmerHash, expected.consts.transferTopic) &&
  accountEntries b.accountWrites == accountEntries expected.accountWrites &&
  orderEntries b.accountOrder Address.toNat == orderEntries expected.accountOrder Address.toNat &&
  storageEntries b.storageWrites == storageEntries expected.storageWrites &&
  orderEntries b.storageAddressOrder Address.toNat ==
    orderEntries expected.storageAddressOrder Address.toNat &&
  slotOrderEntries b.storageSlotOrder == slotOrderEntries expected.storageSlotOrder &&
  codeEntries b.codeWrites == codeEntries expected.codeWrites &&
  b.storageClears.toList == expected.storageClears.toList &&
  b.accountReads.toList == expected.accountReads.toList &&
  b.storageReads.toList == expected.storageReads.toList &&
  b.codeReads.toList == expected.codeReads.toList &&
  b.oldestAncestorOffset == expected.oldestAncestorOffset

private def sameRevertible (r expected : TxRevertible) : Bool :=
  accountEntries r.accountWrites == accountEntries expected.accountWrites &&
  orderEntries r.accountOrder Address.toNat == orderEntries expected.accountOrder Address.toNat &&
  storageEntries r.storageWrites == storageEntries expected.storageWrites &&
  orderEntries r.storageAddressOrder Address.toNat ==
    orderEntries expected.storageAddressOrder Address.toNat &&
  slotOrderEntries r.storageSlotOrder == slotOrderEntries expected.storageSlotOrder &&
  codeEntries r.codeWrites == codeEntries expected.codeWrites &&
  r.storageClears.toList == expected.storageClears.toList &&
  r.transient.toList.map (fun (key, value) ↦ (cell key, value.toNat)) ==
    expected.transient.toList.map (fun (key, value) ↦ (cell key, value.toNat))

private def sameObservations (obs expected : TxObs) : Bool :=
  obs.accountReads.toList == expected.accountReads.toList &&
  obs.storageReads.toList == expected.storageReads.toList &&
  obs.codeReads.toList == expected.codeReads.toList &&
  obs.createdAccounts.toList == expected.createdAccounts.toList

private def success (t : TxState Observing) (a : Address) (k : Bytes32) (v : U256)
    (events : List Event) (expected : TxState Observing) (expectedEvents : List Event) : Bool :=
  match run t a k v events with
  | (.ok ((), next), actualEvents) =>
    sameBlockFields next.block expected.block && sameRevertible next.rev expected.rev &&
      sameObservations next.obs expected.obs && actualEvents == expectedEvents
  | (.error _, _) => false

private def absent (t : TxState Observing) (v : U256)
    (events expectedEvents : List Event) : Bool :=
  match run t target slot v events with
  | (.error .storageOnMissingAccount, actualEvents) => actualEvents == expectedEvents
  | _ => false

-- The present empty transaction account suppresses the conflicting block tombstone
-- and the provider. Storage zero stays in the complete overlay after the prior clear.
#guard
  let t := transaction (.error fault) (some (some blank)) (some none)
  success t target slot U256.zero [.root]
    (expectedFirstSlot t (t.obs.accountReads.insert target)) [.root]

#guard absent (transaction (.ok (some account)) (some none) (some (some account)))
  (U256.ofNat 71) [] []

#guard
  let t := transaction (.error fault) none (some (some account))
  success t target slot U256.zero [.code]
    (expectedFirstSlot t ((t.obs.accountReads.insert target).insert target)) [.code]

#guard absent (transaction (.ok (some account)) none (some none)) U256.zero [] []

#guard
  let t := transaction (.ok (some blank)) none none
  success t target slot U256.zero [.storage]
    (expectedFirstSlot t ((t.obs.accountReads.insert target).insert target))
    [.storage, .account target]

#guard absent (transaction (.ok none) none none) U256.zero [.code] [.code, .account target]

#guard
  let t := transaction (.error fault) none none
  match run t target slot (U256.ofNat 73) [.storage, .root] with
  | (.error (.witness (.malformed (.node h))), events) =>
    h == retainedHash && events == [.storage, .root, .account target]
  | _ => false

#guard
  let t := transaction (.error fault) (some (some blank)) none
  let value := U256.ofNat 79
  success t target oldSlot value [] { t with
    obs.accountReads := t.obs.accountReads.insert target
    rev.storageWrites := t.rev.storageWrites.insert target (slots.insert oldSlot value) } []

#guard
  let t := transaction (.ok (some blank)) none none
  let value := U256.ofNat 83
  success t later slot value [] { t with
    obs.accountReads := (t.obs.accountReads.insert later).insert later
    rev := { t.rev with
      storageWrites := t.rev.storageWrites.insert later ((∅ : Slots).insert slot value)
      storageAddressOrder := t.rev.storageAddressOrder.record later
      storageSlotOrder := t.rev.storageSlotOrder.insert later (WriteOrder.empty.record slot) }
  } [.account later]

#guard
  let initial := transaction (.error fault) (some (some blank)) none
  let t := { initial with rev.storageSlotOrder := initial.rev.storageSlotOrder.erase target }
  success t target slot U256.zero [] { t with
    obs.accountReads := t.obs.accountReads.insert target
    rev := { t.rev with
      storageWrites := t.rev.storageWrites.insert target (slots.insert slot U256.zero)
      storageSlotOrder := t.rev.storageSlotOrder.insert target (WriteOrder.empty.record slot) }
  } []

#guard ((WriteOrder.empty.record oldSlot).record slot).toList == [oldSlot, slot]
#guard (((WriteOrder.empty.record sibling).record target).record later).toList ==
  [sibling, target, later]

end STFSpec.Conformance.State.SetStorageControls
