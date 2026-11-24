/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Transaction account modification controls

Library `EthConformance`. These clients check the ordered actions and complete
transaction results through the State facade. See EthState §§4/7.
-/

namespace STFSpec.Conformance.State.ModifyStateControls
open STFSpec.Base STFSpec.State

private def writeAndCheck {m : Type → Type} [Monad m] (a : Address)
    (updated : Account) : StateM m Unit := do
  setAccount a (some updated)
  if ← accountExistsAndIsEmpty a then
    destroyAccount a

private theorem literal_run {m : Type → Type} [Monad m]
    (t : TxState m) (a : Address) (update : Account → Except StateError Account) :
    ((modifyState a update).run t).run = (do
      match ← ((getAccount a).run t).run with
      | .error error => pure (.error error)
      | .ok (account, next) =>
        match update account with
        | .error error => pure (.error error)
        | .ok updated => ((writeAndCheck a updated).run next).run) := rfl

private theorem provider_error (t : TxState Id) (a : Address)
    (update : Account → Except StateError Account) (error : WitnessError)
    (txMiss : t.rev.accountWrites[a]? = none)
    (blockMiss : t.block.accountWrites[a]? = none)
    (provider : t.block.preState.getAccount? a = .error error) :
    ((modifyState a update).run t).run = .error (.witness error) := by
  rw [literal_run, getAccount_error t a error txMiss blockMiss provider]
  rfl

private theorem callback_error (t next : TxState Id) (a : Address) (account : Account)
    (update : Account → Except StateError Account) (error : StateError)
    (read : ((getAccount a).run t).run = .ok (account, next))
    (failed : update account = .error error) :
    ((modifyState a update).run t).run = .error error := by
  rw [literal_run, read]
  change (match update account with
    | .error err => Except.error err
    | .ok updated => ((writeAndCheck a updated).run next).run) = _
  rw [failed]

private def written {m : Type → Type} (t : TxState m) (a : Address) (v : Account) : TxState m :=
  { t with
    rev.accountWrites := t.rev.accountWrites.insert a (some v)
    rev.accountOrder := t.rev.accountOrder.record a }

private def observed {m : Type → Type} (t : TxState m) (a : Address) (v : Account) : TxState m :=
  { written t a v with obs.accountReads := t.obs.accountReads.insert a }

private theorem second_read {m : Type → Type} [Monad m] (t : TxState m)
    (a : Address) (v : Account) :
    ((getAccountOptional a).run (written t a v)).run = pure (.ok (some v, observed t a v)) := by
  apply getAccountOptional_of_tx
  change (t.rev.accountWrites.insert a (some v))[a]? = some (some v)
  simp

private theorem callback_success (t next : TxState Id) (a : Address)
    (account updated : Account) (update : Account → Except StateError Account) (isEmpty : Bool)
    (read : ((getAccount a).run t).run = .ok (account, next))
    (accepted : update account = .ok updated)
    (checked : ((accountExistsAndIsEmpty a).run (written next a updated)).run =
      .ok (isEmpty, observed next a updated)) :
    ((modifyState a update).run t).run =
      if isEmpty then
        ((destroyAccount a).run (observed next a updated)).run
      else
        .ok ((), observed next a updated) := by
  rw [literal_run, read]
  change (match update account with
    | .error err => Except.error err
    | .ok updated => ((writeAndCheck a updated).run next).run) = _
  rw [accepted]
  change ExceptT.bindCont (fun pair : Bool × TxState Id ↦
    match pair with
    | (isEmpty, after) => ((if isEmpty then destroyAccount a else pure ()).run after))
    ((accountExistsAndIsEmpty a).run (written next a updated)).run = _
  rw [checked]
  cases isEmpty <;> rfl

private theorem restored_after_update (t next : TxState Id) (a : Address)
    (update : Account → Except StateError Account)
    (succeeded : ((modifyState a update).run t).run = .ok ((), next)) :
    (((do modifyState a update; restoreTxState (copyTxState t)) : StateM Id Unit).run t).run =
      .ok ((), { next with rev := t.rev }) := by
  change ExceptT.bindCont (fun pair : Unit × TxState Id ↦
    match pair with
    | (_, state) => (restoreTxState (copyTxState t)).run state)
    ((modifyState a update).run t).run = _
  rw [succeeded]
  rfl

private def target := Address.ofNat 29
private def other := Address.ofNat 11
private def zeroKey : Bytes32 := FixedBytes.ofNat 17
private def fundedKey : Bytes32 := FixedBytes.ofNat 13
private def testHash := Hash32.ofBytes32 (FixedBytes.ofNat 59)
private def consts : HashConsts := ⟨testHash, testHash, testHash, testHash⟩
private def funded : Account := ⟨0, U256.ofNat 101, testHash⟩
private def alternateHash : Account := ⟨0, U256.zero, Hash32.ofBytes32 (FixedBytes.ofNat 61)⟩

private def provider (answer : Except WitnessError (Option Account)) : PreState Id :=
  ⟨fun _ ↦ answer, fun _ _ ↦ .error (.missing .leaf),
    fun _ ↦ .error (.missing .leaf), fun _ ↦ .error (.missing .leaf)⟩

private abbrev SlotMap := Std.ExtTreeMap Bytes32 U256

private def entry (answer : Except WitnessError (Option Account))
    (prior : Option Account) : TxState Id :=
  let block := BlockState.new (provider answer) consts
  let tx := TxState.new { block with
    storageClears := block.storageClears.insert other
    oldestAncestorOffset := some 67 }
  let patch := (∅ : SlotMap).insert fundedKey (U256.ofNat 23) |>.insert zeroKey U256.zero
  let entries := prior.elim tx.rev.accountWrites (fun account ↦ tx.rev.accountWrites.insert target (some account))
  let order := if prior.isSome then tx.rev.accountOrder.record target else tx.rev.accountOrder
  { tx with
    rev := { tx.rev with
      accountWrites := entries.insert other (some alternateHash)
      accountOrder := order.record other
      storageWrites := tx.rev.storageWrites.insert target patch |>.insert other patch
      storageAddressOrder := (tx.rev.storageAddressOrder.record target).record other
      storageSlotOrder := (tx.rev.storageSlotOrder.insert target
        ((WriteOrder.empty.record zeroKey).record fundedKey)).insert other (WriteOrder.empty.record zeroKey)
      storageClears := tx.rev.storageClears.insert other
      codeWrites := tx.rev.codeWrites.insert testHash (ByteArray.mk #[0, 128, 255])
      transient := tx.rev.transient.insert (target, zeroKey) (U256.ofNat 71) }
    obs := { tx.obs with
      accountReads := tx.obs.accountReads.insert other
      storageReads := tx.obs.storageReads.insert (other, fundedKey)
      codeReads := tx.obs.codeReads.insert testHash
      createdAccounts := tx.obs.createdAccounts.insert target } }

private def orderModel {K : Type} [Ord K] [Std.TransOrd K] (r : WriteOrder K) (key : K → Nat) :=
  (r.next, r.positions.toList.map (fun (k, p) ↦ (key k, p)),
    r.keysByPosition.toList.map (fun (p, k) ↦ (p, key k)))

private def accountModel (a : Account) := (a.nonce, a.balance.toNat, a.codeHash.toNat)
private def cell (a : Address) (k : Bytes32) := (a.toNat, k.toNat)
private def slotsModel (patch : SlotMap) :=
  patch.toList.map (fun (key, value) ↦ (key.toNat, value.toNat))

private def sameState (a b : TxState Id) : Bool :=
  let accounts := fun (t : TxState Id) ↦
    t.rev.accountWrites.toList.map (fun (a, value) ↦ (a.toNat, value.map accountModel))
  let storage := fun (t : TxState Id) ↦
    t.rev.storageWrites.toList.map (fun (a, slots) ↦ (a.toNat, slotsModel slots))
  let slotOrders := fun (t : TxState Id) ↦
    t.rev.storageSlotOrder.toList.map (fun (a, order) ↦ (a.toNat, orderModel order FixedBytes.toNat))
  let transient := fun (t : TxState Id) ↦
    t.rev.transient.toList.map (fun ((a, k), v) ↦ (cell a k, v.toNat))
  let code := fun (t : TxState Id) ↦
    t.rev.codeWrites.toList.map (fun (hash, bytes) ↦ (hash.toNat, bytes.data.toList))
  let storageReads := fun (t : TxState Id) ↦
    t.obs.storageReads.toList.map (fun (a, k) ↦ cell a k)
  accounts a == accounts b &&
    orderModel a.rev.accountOrder Address.toNat == orderModel b.rev.accountOrder Address.toNat &&
    storage a == storage b &&
    orderModel a.rev.storageAddressOrder Address.toNat == orderModel b.rev.storageAddressOrder Address.toNat &&
    slotOrders a == slotOrders b &&
    a.rev.storageClears.toList.map Address.toNat == b.rev.storageClears.toList.map Address.toNat &&
    transient a == transient b && code a == code b &&
    a.obs.accountReads.toList.map Address.toNat == b.obs.accountReads.toList.map Address.toNat &&
    storageReads a == storageReads b &&
    a.obs.codeReads.toList.map Hash32.toNat == b.obs.codeReads.toList.map Hash32.toNat &&
    a.obs.createdAccounts.toList.map Address.toNat == b.obs.createdAccounts.toList.map Address.toNat &&
    a.block.oldestAncestorOffset == b.block.oldestAncestorOffset &&
    a.block.storageClears.toList.map Address.toNat == b.block.storageClears.toList.map Address.toNat &&
    a.block.consts.emptyCodeHash.toNat == b.block.consts.emptyCodeHash.toNat

private def expectedState (before : TxState Id) (updated : Option Account) : TxState Id :=
  let read := { before.obs with accountReads := before.obs.accountReads.insert target }
  let written := { before.rev with
    accountWrites := before.rev.accountWrites.insert target updated
    accountOrder := before.rev.accountOrder.record target }
  if updated.isSome then { before with rev := written, obs := read }
  else
    { before with
      rev := { written with
        storageWrites := before.rev.storageWrites.erase target
        storageAddressOrder := before.rev.storageAddressOrder.erase target
        storageSlotOrder := before.rev.storageSlotOrder.erase target
        storageClears := before.rev.storageClears.insert target }
      obs := { read with storageReads := (read.storageReads.insert (target, fundedKey)).insert (target, zeroKey) } }

private def successControl (prior : Option Account) (update : Account → Except StateError Account)
    (updated : Option Account) : Bool :=
  let before := entry (.ok none) prior
  let expected := expectedState before updated
  match ((modifyState target update).run before).run with
  | .error _ => false
  | .ok (_, after) =>
    let snapshot := ((restoreTxState (copyTxState before)).run after).run
    sameState after expected &&
      snapshot.toOption.any (fun ((), restored) ↦ sameState restored { expected with rev := before.rev })

private def providerControl : Bool :=
  let before := entry (.error (.missing (.node testHash))) none
  match ((modifyState target (fun _ ↦ .error .balanceOverflow)).run before).run with
  | .error (.witness (.missing (.node h))) => h.toNat == testHash.toNat
  | _ => false

private def callbackControl : Bool :=
  let before := entry (.ok none) none
  let update := fun current ↦
    if current = emptyAccount consts then Except.error StateError.storageOnMissingAccount
    else Except.error StateError.balanceOverflow
  match ((modifyState target update).run before).run with
  | .error .storageOnMissingAccount => true
  | _ => false

#guard providerControl
#guard callbackControl
#guard successControl none Except.ok none
#guard successControl (some funded) (fun _ ↦ .ok (emptyAccount consts)) none
#guard successControl (some funded) (fun _ ↦ .ok alternateHash) (some alternateHash)
#guard successControl none (fun _ ↦ .ok funded) (some funded)

end STFSpec.Conformance.State.ModifyStateControls
