/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions
import STFSpec.Fork.Amsterdam
import STFSpec.State.BlockInitialization
import STFSpec.State.TransactionInitialization

/-!
# SELFBALANCE controls

Library `EthConformance`. The public facade cases preserve the complete
frame and observe the actual backing account actions.
-/

namespace STFSpec.Conformance.Vm.Instructions.SelfBalanceControls
open STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private def addr (n : Nat) := Address.ofNat n
private def hash (n : Nat) := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def target := addr 71
private def fault : WitnessError := .missing (.node (hash 181))
private abbrev Reads := StateT (List Nat) Id

private inductive Lookup
  | tx
  | block
  | provider

private inductive Outcome
  | fault
  | denied
  | overflow
  | success
deriving BEq

private def blockEnv : BlockEnvironment :=
  ⟨U64.ofNat 11, 13, #[hash 17, hash 19], addr 23, 29, 31,
    U256.ofNat 37, FixedBytes.ofNat 41, U64.ofNat 43, hash 47, U64.ofNat 53⟩

private def txEnv : TransactionEnvironment :=
  ⟨addr 59, addr 61, true, Bytes.ofList [0, 128, 0], U256.ofNat 67, 71, 73,
    79, 83, 89, ∅, ∅, #[], #[], some 0, some (hash 97)⟩

private def context (price : Nat) (static : Bool) : FrameCtx :=
  let costs := { STFSpec.Fork.Amsterdam.gasCosts with
    warmAccess := 13
    coldAccountAccess := 17
    opcodeSelfBalance := price
    veryLow := 97 }
  ⟨⟨costs, ⟨0, 7, 2 ^ 300 + 11, 13⟩, ⟨7, 0, 2 ^ 301 + 17⟩⟩,
    blockEnv, txEnv, addr 101, target, U256.max, Bytes.ofList [255, 0, 128],
    some (addr 0), Bytes.ofList [0x47], validJumpDestinations (Bytes.ofList [91, 0, 91]),
    1024, by decide, true, static, false, addr 107⟩

private def stackOf (words : List Nat) : Stack :=
  words.reverse.foldl (fun s n ↦ (s.push (U256.ofNat n)).toOption.getD s) Stack.empty

private def frame (gas : Nat) (warm : Bool) (words : List Nat) : Frame :=
  let addrs : AddrSet := (∅ : AddrSet).insert (addr 1)
  let entry : Log := ⟨addr 256, #[hash 256, hash 1, hash 256], Bytes.ofList [255, 0, 128]⟩
  ⟨2 ^ 256 + 13, stackOf words, Memory.empty.expand 32 (by decide), ⟨gas, 101, 2, -17, 5, 11⟩,
    .concat (.leaf [entry]) (.concat .empty (.leaf [entry])),
    (∅ : AddrSet).insert (addr 256), Bytes.ofList [0, 255, 128, 0],
    if warm then addrs.insert target else addrs,
    ((∅ : SlotSet).insert (addr 1, FixedBytes.ofNat 256)).insert (addr 256, FixedBytes.ofNat 1)⟩

private def frameModel (f : Frame) :=
  (f.pc, f.stack.toList.map U256.toNat, f.memory.toBytes,
    (f.gasMeter.gasLeft, f.gasMeter.stateGasLeft, f.gasMeter.stateGasBaseline,
      f.gasMeter.refundCounter, f.gasMeter.stateGasSpilled, f.gasMeter.stateGasCommittedSpill),
    f.logs.toList.map (fun log ↦
      (log.address.toNat, log.topics.toList.map Hash32.toNat, log.data.toList)),
    f.accountsToDelete.toList.map Address.toNat, f.returnData.toList,
    f.accessedAddresses.toList.map Address.toNat,
    f.accessedStorageKeys.toList.map (fun (a, k) ↦ (a.toNat, k.toNat)))

private def provider (answer : Except WitnessError (Option Account)) : PreState Reads :=
  ⟨fun a ↦ do
    modify (· ++ [a.toNat])
    pure (if a = target then answer else .error fault),
    fun _ _ ↦ pure (.ok (U256.ofNat 109)),
    fun _ ↦ pure (.ok (ByteArray.mk #[0, 255, 128])),
    fun _ ↦ pure (.ok (hash 113))⟩

private def world (layer : Lookup) (answer : Except WitnessError (Option Account)) : VmWorld Reads :=
  let initial := BlockState.new (provider answer) ⟨hash 127, hash 131, hash 137, hash 139⟩
  let block := { initial with
    accountWrites := initial.accountWrites.insert (addr 149) none
    accountOrder := initial.accountOrder.record (addr 149)
    oldestAncestorOffset := some (2 ^ 290 + 167) }
  let block := match layer with
    | .block => { block with
      accountWrites := block.accountWrites.insert target (answer.toOption.join)
      accountOrder := block.accountOrder.record target }
    | _ => block
  let tx := TxState.new block
  let tx := match layer with
    | .tx => { tx with
      rev.accountWrites := tx.rev.accountWrites.insert target (answer.toOption.join)
      rev.accountOrder := tx.rev.accountOrder.record target }
    | _ => tx
  ⟨{ tx with
    rev.transient := tx.rev.transient.insert (addr 181, FixedBytes.ofNat 191) (U256.ofNat 193)
    obs := { tx.obs with
      accountReads := tx.obs.accountReads.insert (addr 197)
      storageReads := tx.obs.storageReads.insert (addr 199, FixedBytes.ofNat 201)
      codeReads := tx.obs.codeReads.insert (hash 203)
      createdAccounts := tx.obs.createdAccounts.insert (addr 205) } }⟩

private def accountFields (account : Account) := (account.nonce, account.balance.toNat, account.codeHash.toNat)

private def accountWrites (entries : Std.ExtTreeMap Address (Option Account)) :
    List (Nat × Option (Nat × Nat × Nat)) :=
  entries.toList.map (fun (a, v) ↦ (a.toNat, v.map accountFields))

private def worldModel (w : VmWorld Reads) :=
  let tx := w.tx
  (accountWrites tx.block.accountWrites, tx.block.accountOrder.toList.map Address.toNat,
    tx.block.oldestAncestorOffset, tx.block.consts.emptyCodeHash.toNat,
    accountWrites tx.rev.accountWrites, tx.rev.accountOrder.toList.map Address.toNat,
    tx.rev.storageWrites.toList.length, tx.rev.storageClears.toList.length,
    tx.rev.transient.toList.map (fun ((a,k), v) ↦ (a.toNat, k.toNat, v.toNat)),
    tx.obs.accountReads.toList.map Address.toNat,
    tx.obs.storageReads.toList.map (fun (a,k) ↦ (a.toNat,k.toNat)),
    tx.obs.codeReads.toList.map Hash32.toNat, tx.obs.createdAccounts.toList.map Address.toNat)


private def check (price gas : Nat) (enteredWarm static : Bool) (words : List Nat)
    (layer : Lookup) (answer : Except WitnessError (Option Account))
    (expected : Outcome) (value : Nat) (expectedCalls : List Nat) : Bool :=
  let before := frame gas enteredWarm words
  let input := world layer answer
  let (result, calls) := (((selfBalance (context price static) before).run input).run).run []
  let paid := { before with gasMeter := { before.gasMeter with gasLeft := gas - price } }
  let observed := { input with tx.obs.accountReads := input.tx.obs.accountReads.insert target }
  calls == expectedCalls &&
    match result with
    | .error (.state (.witness (.missing (.node key)))) =>
      expected == .fault && key.toNat == (hash 181).toNat
    | .ok (.halt after .outOfGas, out) =>
      expected == .denied && frameModel after == frameModel before && worldModel out == worldModel input
    | .ok (.halt after .stackOverflow, out) =>
      expected == .overflow && frameModel after == frameModel paid && worldModel out == worldModel observed
    | .ok (.continue after, out) =>
      let want := { paid with pc := before.pc + 1, stack := stackOf (value :: words) }
      expected == .success && frameModel after == frameModel want && worldModel out == worldModel observed
    | _ => false

private def top : Nat := U256.max.toNat
private def account (n : Nat) : Option Account := some ⟨3, U256.ofNat n, hash 307⟩

#guard check 5 4 false true (List.range 1024) .provider (.error fault) .denied 0 []
#guard check 5 5 false false [] .provider (.ok none) .success 0 [71]
#guard check 5 5 false true (List.range 1023) .tx (.ok (account top)) .success top []
#guard check 5 19 true false [23, 33] .block (.ok (account 83)) .success 83 []
#guard check 5 5 false true (List.range 1024) .tx (.ok (account 73)) .overflow 0 []
#guard check 5 5 true true (List.range 1024) .provider (.ok none) .overflow 0 [71]
#guard check 5 37 true false (List.range 1024) .provider (.error fault) .fault 0 [71]
#guard check 5 5 false false [17] .provider (.ok (account (2 ^ 255))) .success (2 ^ 255) [71]
#guard check 0 0 false true [] .block (.ok (account 11)) .success 11 []
#guard check 9 8 true false [17] .tx (.ok (account 101)) .denied 0 []
#guard check 9 9 true false [17] .tx (.ok (account 101)) .success 101 []

end STFSpec.Conformance.Vm.Instructions.SelfBalanceControls
