/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Fork.Amsterdam
import STFSpec.Vm.Instructions
import STFSpec.State

/-!
# Standalone TSTORE checks

Library `EthConformance`. Check the handler's failure order, frame result and
precise write using the public Instructions, Core and State facades.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Instructions.TstoreChecks

open STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private abbrev Trace := StateT (List Nat) Id
private abbrev Entry := Nat × Nat × Nat

private structure Case where
  name : String
  static : Bool
  operands : List Nat
  gas : Nat
  price : Nat
  prior : Option Nat
  status : String
  expectedStack : List Nat
  expectedGas : Nat
  expectedSlot : Option Nat

private def key : Nat := 2 ^ 255 + 11
private def value : Nat := 2 ^ 256 - 1
private def owner : Address := Address.ofNat (2 ^ 159 + 5)
private def other : Address := Address.ofNat 5
private def slot (n : Nat) : Bytes32 := FixedBytes.ofNat n
private def hash (n : Nat) : Hash32 := Hash32.ofBytes32 (slot n)

private def cases : List Case :=
  [⟨"static-empty", true, [], 0, 100, some 3, "static", [], 0, some 3⟩,
   ⟨"static-full", true, [41, value, key], 101, 100, some 3, "static", [key, value, 41], 101, some 3⟩,
   ⟨"first-pop-fails", false, [], 0, 100, some 3, "underflow", [], 0, some 3⟩,
   ⟨"second-pop-fails", false, [key], 0, 100, some 3, "underflow", [], 0, some 3⟩,
   ⟨"charge-fails", false, [41, value, key], 99, 100, some 3, "out-of-gas", [41], 99, some 3⟩,
   ⟨"exact-charge-set", false, [41, value, key], 100, 100, some 3, "continue", [41], 0, some value⟩,
   ⟨"surplus-charge-erase", false, [41, 0, key], 101, 100, some 3, "continue", [41], 1, none⟩,
   ⟨"absent-insert", false, [value, key], 120, 100, none, "continue", [], 20, some value⟩,
   ⟨"absent-erase", false, [0, key], 100, 100, none, "continue", [], 0, none⟩,
   ⟨"explicit-zero-erase", false, [0, key], 100, 100, some 0, "continue", [], 0, none⟩,
   ⟨"zero-price", false, [value, key], 0, 0, some 3, "continue", [], 0, some value⟩,
   ⟨"price-seven", false, [value, key], 8, 7, some 3, "continue", [], 1, some value⟩,
   ⟨"price-seven-fails", false, [value, key], 6, 7, some 3, "out-of-gas", [], 6, some 3⟩]

private def context (c : Case) : FrameCtx :=
  let schedule := STFSpec.Fork.Amsterdam.vmConfig
  let costs := { schedule.costs with opcodeTstore := c.price }
  let block : BlockEnvironment :=
    ⟨U64.ofNat 11, 13, #[hash 17, hash 19], Address.ofNat 23, 29, 31,
      U256.ofNat 37, slot 41, U64.ofNat 43, hash 47, U64.ofNat 53⟩
  let tx : TransactionEnvironment :=
    ⟨other, Address.ofNat 61, true, Bytes.ofList [0, 128, 0], U256.ofNat 67, 71, 73,
      79, 83, 89, ∅, ∅, #[], #[], some 0, some (hash 97)⟩
  ⟨{ schedule with costs := costs }, block, tx, other, owner, U256.max, Bytes.ofList [255, 0, 128],
    some other, Bytes.ofList [92], validJumpDestinations (Bytes.ofList [91, 0, 91]),
    7, by decide, true, c.static, false, Address.ofNat 107⟩

private def frame (c : Case) (stack : Stack) : Frame :=
  let log : Log := ⟨other, #[hash 256, hash 1, hash 256], Bytes.ofList [255, 0, 128]⟩
  ⟨31, stack, Memory.empty.expand 32 (by decide), ⟨c.gas, 13, 17, -19, 23, 29⟩,
    .concat (.leaf [log]) (.leaf [log]), (∅ : AddrSet).insert other, Bytes.ofList [0, 255, 128],
    (∅ : AddrSet).insert owner, (∅ : SlotSet).insert (owner, slot key)⟩

private def called {α : Type} (tag : Nat) : Trace (Except WitnessError α) := do
  modify (tag :: ·)
  pure (.error (.missing (.node (hash tag))))

private def entries (selected : Option Nat) : List Entry :=
  [(other.toNat, key, 7), (owner.toNat, 11, 5)] ++
    (selected.toList.map (fun word ↦ (owner.toNat, key, word)))

private def world (c : Case) : VmWorld Trace :=
  let provider : PreState Trace :=
    ⟨fun _ ↦ called 1, fun _ _ ↦ called 2, fun _ ↦ called 3, fun _ ↦ called 4⟩
  let block := BlockState.new provider ⟨hash 107, hash 109, hash 113, hash 127⟩
  let transient : Std.ExtTreeMap (Address × Bytes32) U256 :=
    (entries c.prior).foldl (fun map (a, k, v) ↦
      map.insert (Address.ofNat a, slot k) (U256.ofNat v)) ∅
  let tombstone := (∅ : Std.ExtTreeMap Address (Option Account)).insert other none
  let order : WriteOrder Address :=
    ⟨0, (∅ : Std.ExtTreeMap Address Nat).insert other 4,
      (∅ : Std.ExtTreeMap Nat Address).insert 6 owner⟩
  let clears := (∅ : Std.ExtTreeSet Address).insert owner
  let rev : TxRevertible := ⟨tombstone, order, ∅, WriteOrder.empty, ∅, ∅, clears, transient⟩
  let obs : TxObs := ⟨(∅ : Std.HashSet Address).insert other,
    (∅ : Std.HashSet (Address × Bytes32)).insert (other, slot 11),
    (∅ : Std.HashSet Hash32).insert (hash 29), (∅ : Std.HashSet Address).insert other⟩
  ⟨⟨{ block with oldestAncestorOffset := some (2 ^ 190) }, rev, obs⟩⟩

private def status {ctx : FrameCtx} (result : StepResult ctx) : Option (String × Frame) :=
  match result with
  | .continue next => some ("continue", next)
  | .halt next .writeInStaticContext => some ("static", next)
  | .halt next .stackUnderflow => some ("underflow", next)
  | .halt next .outOfGas => some ("out-of-gas", next)
  | _ => none

private def otherFrame (before after : Frame) : Bool :=
  let logs (f : Frame) := f.logs.toList.map (fun l ↦ (l.address, l.topics, l.data))
  after.memory.toBytes == before.memory.toBytes && logs after == logs before &&
    after.returnData == before.returnData &&
    after.accountsToDelete.toList == before.accountsToDelete.toList &&
    after.accessedAddresses.toList == before.accessedAddresses.toList &&
    after.accessedStorageKeys.toList == before.accessedStorageKeys.toList

private def otherGas (meter : GasMeter) : Bool :=
  meter.stateGasLeft == 13 && meter.stateGasBaseline == 17 && meter.refundCounter == -19 &&
    meter.stateGasSpilled == 23 && meter.stateGasCommittedSpill == 29

private def otherWorld (before after : VmWorld Trace) : Bool :=
  let rev := after.tx.rev
  let old := before.tx.rev
  let obs := after.tx.obs
  let earlier := before.tx.obs
  after.tx.block.oldestAncestorOffset == before.tx.block.oldestAncestorOffset &&
    rev.accountWrites.toList == old.accountWrites.toList &&
    rev.accountOrder.next == old.accountOrder.next &&
    rev.accountOrder.positions.toList == old.accountOrder.positions.toList &&
    rev.accountOrder.keysByPosition.toList == old.accountOrder.keysByPosition.toList &&
    rev.storageClears.contains owner &&
    obs.accountReads.toList == earlier.accountReads.toList &&
    obs.storageReads.toList == earlier.storageReads.toList &&
    obs.codeReads.toList == earlier.codeReads.toList &&
    obs.createdAccounts.toList == earlier.createdAccounts.toList

private def observe (c : Case) : Option (String × List Nat × Nat × Nat × List Entry) := do
  let stack ← (c.operands.foldlM (fun (s : Stack) n ↦ s.push (U256.ofNat n)) Stack.empty).toOption
  let before := frame c stack
  let original := world c
  let (result, calls) := (((tstore (context c) before).run original).run).run []
  let .ok (step, written) := result | none
  let (outcome, after) ← status step
  if !calls.isEmpty || !otherFrame before after || !otherGas after.gasMeter ||
      !otherWorld original written then
    none
  else
    let observed := written.tx.rev.transient.toList.map fun ((a, k), v) ↦
      (a.toNat, k.toNat, v.toNat)
    return (outcome, after.stack.toList.map U256.toNat, after.gasMeter.gasLeft, after.pc, observed)

#guard cases.all (fun c ↦ observe c == some
  (c.status, c.expectedStack, c.expectedGas,
    if c.status == "continue" then 32 else 31, entries c.expectedSlot))

end STFSpec.Conformance.Vm.Instructions.TstoreChecks
