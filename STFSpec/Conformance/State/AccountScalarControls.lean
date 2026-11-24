/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Account balance and nonce controls

Library `EthConformance`. Verify the scalar callbacks through State and
exercise their complete transaction effects. See EthState §§4/7.5.
-/

namespace STFSpec.Conformance.State.AccountScalarControls
open STFSpec.Base STFSpec.State

private theorem balance_action {m : Type → Type} [Monad m] (t : TxState m)
    (a : Address) (amount : U256) :
    ((setAccountBalance a amount).run t).run =
      ((modifyState a (fun account ↦ .ok ⟨account.nonce, amount, account.codeHash⟩)).run t).run :=
  rfl

private theorem nonce_action {m : Type → Type} [Monad m] (t : TxState m) (a : Address) :
    ((incrementNonce a).run t).run =
      ((modifyState a (fun account ↦ .ok ⟨account.nonce + 1, account.balance, account.codeHash⟩)).run t).run :=
  rfl

private theorem balance_empty (consts : HashConsts) (account : Account) (amount : U256) :
    ({ account with balance := amount } : Account) = emptyAccount consts ↔
      account.nonce = 0 ∧ amount = U256.zero ∧ account.codeHash = consts.emptyCodeHash := by
  constructor
  · intro same
    exact ⟨congrArg Account.nonce same, congrArg Account.balance same, congrArg Account.codeHash same⟩
  · rintro ⟨nonce, balance, hash⟩
    exact Account.ext nonce balance hash

private theorem nonce_nonempty (consts : HashConsts) (account : Account) :
    ({ account with nonce := account.nonce + 1 } : Account) ≠ emptyAccount consts := by
  intro same
  have nonce := congrArg Account.nonce same
  rw [emptyAccount_nonce] at nonce
  simp at nonce

private theorem lookup_failure (t : TxState Id) (a : Address) (amount : U256)
    (error : WitnessError)
    (txMiss : t.rev.accountWrites[a]? = none)
    (blockMiss : t.block.accountWrites[a]? = none)
    (provider : t.block.preState.getAccount? a = .error error) :
    ((setAccountBalance a amount).run t).run = .error (.witness error) ∧
      ((incrementNonce a).run t).run = .error (.witness error) := by
  have read := getAccount_error t a error txMiss blockMiss provider
  have run {m : Type → Type} [Monad m] (entry : TxState m)
      (update : Account → Except StateError Account) :
      ((modifyState a update).run entry).run = (do
        match ← ((getAccount a).run entry).run with
        | .error problem => pure (.error problem)
        | .ok (account, next) =>
          match update account with
          | .error problem => pure (.error problem)
          | .ok updated =>
            (((do
              setAccount a (some updated)
              if ← accountExistsAndIsEmpty a then destroyAccount a) : StateM m Unit).run next).run) :=
    rfl
  have failed (update : Account → Except StateError Account) :
      ((modifyState a update).run t).run = .error (.witness error) := by
    rw [run t update, read]
    rfl
  exact ⟨failed _, failed _⟩

private theorem restored_after_scalar (action : StateM Id Unit) (t next : TxState Id)
    (succeeded : (action.run t).run = .ok ((), next)) :
    (((do action; restoreTxState (copyTxState t)) : StateM Id Unit).run t).run =
      .ok ((), { next with rev := t.rev }) := by
  change ExceptT.bindCont (fun pair : Unit × TxState Id ↦
    match pair with
    | (_, state) => (restoreTxState (copyTxState t)).run state)
    (action.run t).run = _
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

private def entry (prior : Option Account) : TxState Id :=
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
      storageWrites := tx.rev.storageWrites.insert target patch |>.insert sibling patch
      storageClears := tx.rev.storageClears.insert sibling
      storageAddressOrder := (tx.rev.storageAddressOrder.record target).record sibling
      storageSlotOrder := tx.rev.storageSlotOrder.insert target slotOrder |>.insert sibling slotOrder
      codeWrites := tx.rev.codeWrites.insert installedHash (ByteArray.mk #[0, 128, 255])
      transient := tx.rev.transient.insert (target, zeroKey) (U256.ofNat 79) }
    obs := { tx.obs with
      accountReads := tx.obs.accountReads.insert sibling
      storageReads := tx.obs.storageReads.insert (sibling, fundedKey)
      codeReads := tx.obs.codeReads.insert installedHash
      createdAccounts := tx.obs.createdAccounts.insert target } }

private def expected (t : TxState Id) (value : Option Account) : TxState Id :=
  let rev := { t.rev with
    accountWrites := t.rev.accountWrites.insert target value
    accountOrder := t.rev.accountOrder.record target }
  let obs := { t.obs with accountReads := t.obs.accountReads.insert target }
  if value.isSome then { t with rev, obs }
  else
    { t with
      rev := { rev with
        storageWrites := rev.storageWrites.erase target
        storageClears := rev.storageClears.insert target
        storageAddressOrder := rev.storageAddressOrder.erase target
        storageSlotOrder := rev.storageSlotOrder.erase target }
      obs := { obs with storageReads := (obs.storageReads.insert (target, zeroKey)).insert (target, fundedKey) } }

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

private def success (op : StateM Id Unit) (prior result : Option Account) : Bool :=
  let before := entry prior
  let want := expected before result
  match (op.run before).run with
  | .error _ => false
  | .ok ((), after) =>
    overlayModel after == overlayModel want &&
      match ((restoreTxState (copyTxState before)).run after).run with
      | .ok ((), restored) => overlayModel restored == overlayModel { want with rev := before.rev }
      | .error _ => false

private abbrev ReadTrace := StateT (List Nat) Id

private def failedProvider : Bool :=
  let key := Hash32.ofBytes32 (FixedBytes.ofNat (2 ^ 255 + 83))
  let provider : PreState ReadTrace :=
    ⟨fun a visited ↦ (.error (.missing (.node key)), visited ++ [a.toNat]),
      fun _ _ ↦ pure (.error (.missing .leaf)), fun _ ↦ pure (.error (.missing .leaf)),
      fun _ ↦ pure (.error (.missing .leaf))⟩
  let before := TxState.new (BlockState.new provider consts)
  let failed := fun (action : StateM ReadTrace Unit) ↦
    match (((action.run before).run).run []) with
    | (.error (.witness (.missing (.node item))), calls) => item == key && calls == [target.toNat]
    | _ => false
  failed (setAccountBalance target U256.max) && failed (incrementNonce target)

#guard success (setAccountBalance target U256.zero) (some ⟨0, U256.ofNat 89, emptyHash⟩) none
#guard success (setAccountBalance target U256.zero) none none
#guard success (setAccountBalance target U256.max) none (some ⟨0, U256.max, emptyHash⟩)
#guard success (setAccountBalance target U256.zero)
  (some ⟨0, U256.ofNat 89, installedHash⟩) (some ⟨0, U256.zero, installedHash⟩)
#guard success (setAccountBalance target U256.zero)
  (some ⟨2 ^ 270 + 97, U256.ofNat 89, emptyHash⟩) (some ⟨2 ^ 270 + 97, U256.zero, emptyHash⟩)
#guard success (incrementNonce target) none (some ⟨1, U256.zero, emptyHash⟩)
#guard success (incrementNonce target)
  (some ⟨2 ^ 64 - 1, U256.max, installedHash⟩) (some ⟨2 ^ 64, U256.max, installedHash⟩)
#guard success (incrementNonce target)
  (some ⟨2 ^ 256 - 1, U256.zero, emptyHash⟩) (some ⟨2 ^ 256, U256.zero, emptyHash⟩)
#guard failedProvider

end STFSpec.Conformance.State.AccountScalarControls
