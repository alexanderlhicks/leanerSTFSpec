/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Transaction code installation controls

Library `EthConformance`. These clients check the R21 action through the State
facade. See EthState §§4/7.5.
-/

namespace STFSpec.Conformance.State.SetCodeControls
open STFSpec.Base STFSpec.State

private def stageCode {m : Type → Type} (t : TxState m)
    (code : ByteArray) (hash : Hash32) : TxState m :=
  if hash = t.block.consts.emptyCodeHash then t
  else { t with rev.codeWrites := t.rev.codeWrites.insert hash code }

private theorem literal_run {m : Type → Type} [Monad m] (t : TxState m)
    (a : Address) (code : ByteArray) (hash : Hash32) :
    ((setCode a code hash).run t).run =
      ((modifyState a (fun account ↦ .ok { account with codeHash := hash })).run
        (stageCode t code hash)).run := rfl

private theorem empty_hash {m : Type → Type} (t : TxState m)
    (code : ByteArray) (hash : Hash32) (empty : hash = t.block.consts.emptyCodeHash) :
    stageCode t code hash = t := by
  simp [stageCode, empty]

private theorem staged_lookup {m : Type → Type} (t : TxState m)
    (code : ByteArray) (hash key : Hash32) :
    (stageCode t code hash).rev.codeWrites[key]? =
      if hash ≠ t.block.consts.emptyCodeHash ∧ key = hash then some code
      else t.rev.codeWrites[key]? := by
  by_cases empty : hash = t.block.consts.emptyCodeHash
  · rw [empty_hash t code hash empty]
    simp [empty]
  · by_cases sameKey : key = hash
    · simp [stageCode, empty, sameKey]
    · have distinct : compare hash key ≠ .eq := fun h ↦
        sameKey (Std.LawfulEqOrd.compare_eq_iff_eq.mp h).symm
      simp [stageCode, empty, sameKey, Std.ExtTreeMap.getElem?_insert, distinct]

private theorem staged_frame {m : Type → Type} (t : TxState m)
    (code : ByteArray) (hash : Hash32) :
    let next := stageCode t code hash
    next.block = t.block ∧ next.obs = t.obs ∧
      { next.rev with codeWrites := t.rev.codeWrites } = t.rev := by
  dsimp only
  unfold stageCode
  split <;> exact ⟨rfl, rfl, rfl⟩

private theorem restored_after_install (t next : TxState Id) (a : Address)
    (code : ByteArray) (hash : Hash32)
    (succeeded : ((setCode a code hash).run t).run = .ok ((), next)) :
    (((do setCode a code hash; restoreTxState (copyTxState t)) : StateM Id Unit).run t).run =
      .ok ((), { next with rev := t.rev }) := by
  change ExceptT.bindCont (fun pair : Unit × TxState Id ↦
    match pair with
    | (_, state) => (restoreTxState (copyTxState t)).run state)
    ((setCode a code hash).run t).run = _
  rw [succeeded]
  rfl

private def target := Address.ofNat 29
private def other := Address.ofNat 11
private def zeroKey : Bytes32 := FixedBytes.ofNat 17
private def retainedKey : Bytes32 := FixedBytes.ofNat 13
private def emptyHash := Hash32.ofBytes32 (FixedBytes.ofNat 59)
private def installedHash := Hash32.ofBytes32 (FixedBytes.ofNat 61)
private def priorHash := Hash32.ofBytes32 (FixedBytes.ofNat 67)
private def retainedCode := ByteArray.mk #[0, 128, 255]
private def newCode := ByteArray.mk #[96, 0, 255, 0]
private def consts : HashConsts := ⟨emptyHash, priorHash, installedHash, emptyHash⟩
private def funded : Account := ⟨3, U256.ofNat 101, priorHash⟩

private def provider (answer : Except WitnessError (Option Account)) : PreState Id :=
  ⟨fun _ ↦ answer, fun _ _ ↦ .error (.missing .leaf),
    fun _ ↦ .error (.missing .leaf), fun _ ↦ .error (.missing .leaf)⟩

private def entry (answer : Except WitnessError (Option Account)) : TxState Id :=
  let block := BlockState.new (provider answer) consts
  let tx := TxState.new { block with oldestAncestorOffset := some 31 }
  let slots : Std.ExtTreeMap Bytes32 U256 := (∅ : Std.ExtTreeMap Bytes32 U256)
    |>.insert zeroKey U256.zero
    |>.insert retainedKey (U256.ofNat 37)
  { tx with
    rev := { tx.rev with
      accountWrites := tx.rev.accountWrites.insert other (some funded)
      accountOrder := tx.rev.accountOrder.record other
      storageWrites := tx.rev.storageWrites.insert target slots |>.insert other slots
      storageAddressOrder := (tx.rev.storageAddressOrder.record target).record other
      storageSlotOrder := tx.rev.storageSlotOrder.insert target
        ((WriteOrder.empty.record zeroKey).record retainedKey)
      storageClears := tx.rev.storageClears.insert other
      codeWrites := tx.rev.codeWrites.insert emptyHash retainedCode
        |>.insert installedHash retainedCode |>.insert priorHash retainedCode
      transient := tx.rev.transient.insert (target, zeroKey) (U256.ofNat 71) }
    obs := { tx.obs with
      accountReads := tx.obs.accountReads.insert other
      storageReads := tx.obs.storageReads.insert (other, retainedKey)
      codeReads := tx.obs.codeReads.insert priorHash
      createdAccounts := tx.obs.createdAccounts.insert target } }

private def orderModel {K : Type} [Ord K] [Std.TransOrd K] (order : WriteOrder K) (key : K → Nat) :=
  (order.next, order.positions.toList.map (fun (k, p) ↦ (key k, p)),
    order.keysByPosition.toList.map (fun (p, k) ↦ (p, key k)))

private def accountModel (a : Account) := (a.nonce, a.balance.toNat, a.codeHash.toNat)
private def cell (a : Address) (k : Bytes32) := (a.toNat, k.toNat)

private def observed (t : TxState Id) :=
  (t.obs.accountReads.toList.map Address.toNat,
    t.obs.storageReads.toList.map (fun (a, k) ↦ cell a k),
    t.obs.codeReads.toList.map Hash32.toNat, t.obs.createdAccounts.toList.map Address.toNat)

private def slotValues (slots : Std.ExtTreeMap Bytes32 U256) : List (Nat × Nat) :=
  slots.toList.map (fun (key, value) ↦ (key.toNat, value.toNat))

private def written (t : TxState Id) :=
  (t.rev.accountWrites.toList.map (fun (a, v) ↦ (a.toNat, v.map accountModel)),
    orderModel t.rev.accountOrder Address.toNat,
    t.rev.storageWrites.toList.map (fun (a, slots) ↦ (a.toNat, slotValues slots)),
    orderModel t.rev.storageAddressOrder Address.toNat,
    t.rev.storageSlotOrder.toList.map (fun (a, order) ↦ (a.toNat, orderModel order FixedBytes.toNat)),
    t.rev.storageClears.toList.map Address.toNat,
    t.rev.codeWrites.toList.map (fun (hash, bytes) ↦ (hash.toNat, bytes.data.toList)),
    t.rev.transient.toList.map (fun ((a, k), v) ↦ (cell a k, v.toNat)))

private def expectedState (before : TxState Id) (code : ByteArray)
    (hash : Hash32) (account : Option Account) : TxState Id :=
  let accountReads := before.obs.accountReads.insert target
  let rev := { before.rev with
    accountWrites := before.rev.accountWrites.insert target account
    accountOrder := before.rev.accountOrder.record target
    codeWrites := if hash == emptyHash then before.rev.codeWrites
      else before.rev.codeWrites.insert hash code }
  if account.isSome then
    { before with rev := rev, obs.accountReads := accountReads }
  else
    { before with
      rev := { rev with
        storageWrites := rev.storageWrites.erase target
        storageAddressOrder := rev.storageAddressOrder.erase target
        storageSlotOrder := rev.storageSlotOrder.erase target
        storageClears := rev.storageClears.insert target }
      obs := { before.obs with
        accountReads
        storageReads := before.obs.storageReads.insert (target, zeroKey)
          |>.insert (target, retainedKey) } }

private def successControl (prior : Option Account) (code : ByteArray)
    (hash : Hash32) (account : Option Account) : Bool :=
  let before := entry (.ok prior)
  let expected := expectedState before code hash account
  match ((setCode target code hash).run before).run with
  | .error _ => false
  | .ok ((), after) =>
    let snapshot := ((restoreTxState (copyTxState before)).run after).run
    written after == written expected && observed after == observed expected &&
      after.block.oldestAncestorOffset == before.block.oldestAncestorOffset &&
      snapshot.toOption.any (fun ((), restored) ↦
        written restored == written before && observed restored == observed expected)

private def providerControl (code : ByteArray) (hash : Hash32) : Bool :=
  let before := entry (.error (.missing (.node priorHash)))
  match ((setCode target code hash).run before).run with
  | .error (.witness (.missing (.node key))) => key.toNat == priorHash.toNat
  | _ => false

#guard successControl none ByteArray.empty emptyHash none
#guard successControl (some funded) ByteArray.empty emptyHash (some { funded with codeHash := emptyHash })
#guard successControl none newCode installedHash (some ⟨0, U256.zero, installedHash⟩)
#guard successControl (some funded) newCode installedHash (some { funded with codeHash := installedHash })
#guard successControl none newCode emptyHash none
#guard successControl (some funded) ByteArray.empty installedHash (some { funded with codeHash := installedHash })
#guard providerControl ByteArray.empty emptyHash
#guard providerControl newCode installedHash

end STFSpec.Conformance.State.SetCodeControls
