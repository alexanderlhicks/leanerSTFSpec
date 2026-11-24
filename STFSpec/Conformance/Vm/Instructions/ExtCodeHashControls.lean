/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions
import STFSpec.Fork.Amsterdam
import STFSpec.State.BlockInitialization
import STFSpec.State.TransactionInitialization

/-!
# EXTCODEHASH controls

Library `EthConformance`. The public facade clients check warmth, payment,
the account comparison and hash word, and the unchanged frame and transaction fields.
-/

namespace STFSpec.Conformance.Vm.Instructions.ExtCodeHashControls
open STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private def addr (n : Nat) := Address.ofNat n
private def hash (n : Nat) := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def target := addr 71
private def operand := U256.ofNat (2 ^ 255 + 2 ^ 161 + 71)
private def fault : WitnessError := .missing (.node (hash 181))
private abbrev Reads := StateT (List Nat) Id

private def blockEnv : BlockEnvironment :=
  ⟨U64.ofNat 11, 13, #[hash 17, hash 19], addr 23, 29, 31,
    U256.ofNat 37, FixedBytes.ofNat 41, U64.ofNat 43, hash 47, U64.ofNat 53⟩

private def txEnv : TransactionEnvironment :=
  ⟨addr 59, addr 61, true, Bytes.ofList [0, 128, 0], U256.ofNat 67, 71, 73,
    79, 83, 89, ∅, ∅, #[], #[], some 0, some (hash 97)⟩

private def context (warmPrice coldPrice : Nat) (static : Bool) : FrameCtx :=
  let costs := { STFSpec.Fork.Amsterdam.gasCosts with
    warmAccess := warmPrice
    coldAccountAccess := coldPrice
    veryLow := 97 }
  ⟨⟨costs, ⟨0, 7, 2 ^ 300 + 11, 13⟩, ⟨7, 0, 2 ^ 301 + 17⟩⟩,
    blockEnv, txEnv, addr 101, addr 103, U256.max, Bytes.ofList [255, 0, 128],
    some (addr 0), Bytes.ofList [0x31], validJumpDestinations (Bytes.ofList [91, 0, 91]),
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
    fun _ ↦ do
      modify (· ++ [2 ^ 160])
      pure (.error (.missing (.code (hash 127)))),
    fun _ ↦ pure (.ok (hash 113))⟩

private def world {m : Type → Type} (pre : PreState m) (entry : Option (Option Account)) :
    VmWorld m :=
  let initial := BlockState.new pre ⟨hash 127, hash 131, hash 137, hash 139⟩
  let block := { initial with
    accountWrites := initial.accountWrites.insert (addr 149) none
    accountOrder := initial.accountOrder.record (addr 149)
    oldestAncestorOffset := some (2 ^ 290 + 167) }
  let tx := TxState.new block
  let writes := entry.elim tx.rev.accountWrites (tx.rev.accountWrites.insert target)
  let order := if entry.isSome then tx.rev.accountOrder.record target else tx.rev.accountOrder
  ⟨{ tx with
    rev := { tx.rev with
      accountWrites := writes
      accountOrder := order
      transient := tx.rev.transient.insert (addr 181, FixedBytes.ofNat 191) (U256.ofNat 193) }
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

private def denied (warmPrice coldPrice gas : Nat) (warm : Bool)
    (words : List Nat) (expected : ExceptionalHalt) : Bool :=
  let entry := frame gas warm words
  let input := world (provider (.error fault)) none
  let (result, calls) := (((extcodehash (context warmPrice coldPrice false) entry).run input).run).run []
  match result with
  | .ok (.halt after reason, out) =>
    let want := { entry with
      stack := stackOf words.tail
      accessedAddresses := if words.isEmpty then entry.accessedAddresses else
        entry.accessedAddresses.insert target }
    let correctFault := match reason, expected with
      | .stackUnderflow, .stackUnderflow | .outOfGas, .outOfGas => true
      | _, _ => false
    correctFault && calls.isEmpty && frameModel after == frameModel want &&
      worldModel out == worldModel input
  | _ => false

private def paid (warmPrice coldPrice gas : Nat) (warm static : Bool) (rest : List Nat)
    (answer : Option Account) (entry : Option (Option Account)) (expectedWord : Nat) : Bool :=
  let before := frame gas warm (operand.toNat :: rest)
  let input := world (provider (.ok answer)) entry
  let (result, calls) := (((extcodehash (context warmPrice coldPrice static) before).run input).run).run []
  match result with
  | .ok (.continue after, out) =>
    let price := if warm then warmPrice else coldPrice
    let wanted := { before with
      pc := before.pc + 1
      stack := stackOf (expectedWord :: rest)
      gasMeter := { before.gasMeter with gasLeft := gas - price }
      accessedAddresses := before.accessedAddresses.insert target }
    let expected := { input with tx.obs.accountReads := input.tx.obs.accountReads.insert target }
    let callsExpected := if entry.isSome then [] else [target.toNat]
    calls == callsExpected && frameModel after == frameModel wanted &&
      worldModel out == worldModel expected
  | _ => false

private def failedProvider : Bool :=
  let before := frame 91 false [operand.toNat, 23]
  let input := world (provider (.error fault)) none
  let (result, calls) := (((extcodehash (context 107 91 true) before).run input).run).run []
  match result with
  | .error (.state (.witness (.missing (.node key)))) =>
    key.toNat == (hash 181).toNat && calls == [target.toNat]
  | _ => false

private def outerFailure : Bool :=
  let unavailable : PreState Option := ⟨fun _ ↦ none, fun _ _ ↦ none, fun _ ↦ none, fun _ ↦ none⟩
  let input := world unavailable none
  let cfg := context 13 17 false
  let before := frame 17 false [operand.toNat]
  match ((extcodehash cfg before).run input).run with
  | none => true
  | some _ => false

private def fullHash := hash
  0xff00927f05408b00d10cfa71adf002ff44e200307d99081100c2ff7e6b004911

#guard denied 13 17 0 false [] .stackUnderflow
#guard denied 13 17 12 true [operand.toNat, 23] .outOfGas
#guard denied 103 7 6 false [operand.toNat, 31] .outOfGas
#guard paid 13 17 17 false true [23] none none 0
#guard paid 13 17 13 true false [23] (some ⟨0, U256.zero, hash 127⟩) none 0
#guard paid 13 17 19 false false [23] (some ⟨0, U256.max, hash 127⟩) none 127
#guard paid 13 17 19 false false [23] (some ⟨7, U256.zero, hash 127⟩) none 127
#guard paid 13 17 13 true false [23] none (some (some ⟨0, U256.zero, fullHash⟩)) fullHash.toNat
#guard paid 0 31 0 true true (List.range 1023) (some ⟨0, U256.zero, fullHash⟩) none fullHash.toNat
#guard paid 103 7 7 false false [] (some ⟨0, U256.zero, hash 31⟩) (some none) 0
#guard failedProvider
#guard outerFailure

end STFSpec.Conformance.Vm.Instructions.ExtCodeHashControls
