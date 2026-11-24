/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Fork.Amsterdam
import STFSpec.State
import STFSpec.Vm.Instructions

/-!
# Standalone SLOAD controls

Library `EthConformance`. Observe slot warmth, current storage precedence
and the order of exceptional halts and provider calls through the public facades.
-/

namespace STFSpec.Conformance.Vm.Instructions.SloadControls

open STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private abbrev Query := Address × Bytes32
private abbrev Reads := StateT (List Query) Id

private inductive Layer where
  | transactionSlot
  | transactionClear
  | blockSlot
  | blockClear
  | provider
  | fault
  deriving BEq

private inductive Outcome where
  | underflow
  | denied
  | fault
  | read (value : Nat)

private structure Case where
  warm : Bool
  gas : Nat
  warmPrice : Nat
  coldPrice : Nat
  depth : Nat
  layer : Layer
  outcome : Outcome

private def target : Address := Address.ofNat (2 ^ 159 + 5)
private def other : Address := Address.ofNat 7
private def key : Nat := 2 ^ 239 + 2 ^ 135 + 255
private def slot : Bytes32 := FixedBytes.ofNat key
private def otherSlot : Bytes32 := FixedBytes.ofNat 19
private def hash (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def sentinel : Query := (other, otherSlot)
private def marker : Hash32 := hash 23

private def context (c : Case) : FrameCtx :=
  let config := STFSpec.Fork.Amsterdam.vmConfig
  let costs := { config.costs with warmAccess := c.warmPrice, coldStorageAccess := c.coldPrice }
  let block : BlockEnvironment :=
    ⟨U64.ofNat 11, 13, #[hash 17, hash 19], Address.ofNat 23, 29, 31,
      U256.ofNat 37, FixedBytes.ofNat 41, U64.ofNat 43, hash 47, U64.ofNat 53⟩
  let tx : TransactionEnvironment :=
    ⟨other, Address.ofNat 61, true, Bytes.ofList [0, 128, 0], U256.ofNat 67, 71, 73,
      79, 83, 89, ∅, ∅, #[], #[], some 0, some (hash 97)⟩
  ⟨{ config with costs := costs }, block, tx, other, target, U256.max,
    Bytes.ofList [255, 0, 128], some other, Bytes.ofList [84],
    validJumpDestinations (Bytes.ofList [91, 0, 91]), 7, by decide, true, true, false,
    Address.ofNat 107⟩

private def frame (c : Case) (stack : Stack) : Frame :=
  let log : Log := ⟨other, #[hash 256, hash 1, hash 256], Bytes.ofList [255, 0, 128]⟩
  let slots := (∅ : SlotSet).insert sentinel
  ⟨2 ^ 260 + 31, stack, Memory.empty.expand 32 (by decide), ⟨c.gas, 13, 17, -19, 23, 29⟩,
    .concat (.leaf [log]) (.leaf [log]), (∅ : AddrSet).insert other, Bytes.ofList [0, 255, 128],
    (∅ : AddrSet).insert other, if c.warm then slots.insert (target, slot) else slots⟩

private def putSlot (v : U256) : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256) :=
  (∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert target
    ((∅ : Std.ExtTreeMap Bytes32 U256).insert slot v)

private def cleared : Std.ExtTreeSet Address := (∅ : Std.ExtTreeSet Address).insert target

private def storageProvider (layer : Layer) (a : Address) (k : Bytes32) :
    Reads (Except WitnessError U256) := do
  modify ((a, k) :: ·)
  if layer == .provider && a == target && k == slot then pure (.ok (U256.ofNat 37))
  else pure (.error (.missing (.node marker)))

private def world (c : Case) : VmWorld Reads :=
  let bad {α : Type} : Reads (Except WitnessError α) := do
    modify (sentinel :: ·)
    pure (.error (.missing .leaf))
  let provider : PreState Reads := ⟨fun _ ↦ bad, storageProvider c.layer, fun _ ↦ bad, fun _ ↦ bad⟩
  let block := BlockState.new provider ⟨hash 107, hash 109, hash 113, hash 127⟩
  let block := { block with
    storageWrites := if c.layer == .blockSlot || c.layer == .transactionClear then
      putSlot U256.max else ∅
    storageClears := if c.layer == .blockSlot || c.layer == .blockClear then cleared else ∅
    codeWrites := block.codeWrites.insert marker ⟨#[0, 255]⟩
    oldestAncestorOffset := some 3 }
  let t := TxState.new block
  ⟨{ t with
    rev.storageWrites := if c.layer == .transactionSlot then putSlot U256.zero else ∅
    rev.storageClears := if c.layer == .transactionSlot || c.layer == .transactionClear then
      cleared else ∅
    rev.transient := t.rev.transient.insert sentinel U256.max
    obs.accountReads := t.obs.accountReads.insert other
    obs.storageReads := t.obs.storageReads.insert sentinel
    obs.codeReads := t.obs.codeReads.insert marker
    obs.createdAccounts := t.obs.createdAccounts.insert other }⟩

private def frameFields (before after : Frame) : Bool :=
  let logs (f : Frame) := f.logs.toList.map (fun l ↦ (l.address, l.topics, l.data))
  let old := before.gasMeter
  let gas := after.gasMeter
  after.memory.toBytes == before.memory.toBytes && logs after == logs before &&
    after.returnData == before.returnData &&
    after.accountsToDelete.toList == before.accountsToDelete.toList &&
    after.accessedAddresses.toList == before.accessedAddresses.toList &&
    gas.stateGasLeft == old.stateGasLeft && gas.stateGasBaseline == old.stateGasBaseline &&
    gas.refundCounter == old.refundCounter && gas.stateGasSpilled == old.stateGasSpilled &&
    gas.stateGasCommittedSpill == old.stateGasCommittedSpill

private def hasSlots (warmed : Bool) (slots : SlotSet) : Bool :=
  slots.contains sentinel && slots.contains (target, slot) == warmed &&
    slots.toList.length == (if warmed then 2 else 1)

private def stateFields (before after : VmWorld Reads) (didRead : Bool) : Bool :=
  let old := before.tx
  let new := after.tx
  new.obs.storageReads.contains sentinel && new.obs.storageReads.contains (target, slot) == didRead &&
    new.obs.storageReads.toList.length == (if didRead then 2 else 1) &&
    new.obs.accountReads.toList == old.obs.accountReads.toList &&
    new.obs.codeReads.toList == old.obs.codeReads.toList &&
    new.obs.createdAccounts.toList == old.obs.createdAccounts.toList &&
    new.rev.transient.toList == old.rev.transient.toList &&
    new.rev.storageWrites.toList.map (fun (a, slots) ↦ (a, slots.toList)) ==
      old.rev.storageWrites.toList.map (fun (a, slots) ↦ (a, slots.toList)) &&
    new.rev.storageClears.toList == old.rev.storageClears.toList &&
    new.block.storageClears.toList == old.block.storageClears.toList &&
    new.block.codeWrites.toList == old.block.codeWrites.toList &&
    new.block.oldestAncestorOffset == old.block.oldestAncestorOffset

private def check (c : Case) : Bool := Id.run do
  let rest := List.replicate (c.depth - 1) 9
  let entryStack := if c.depth == 0 then [] else key :: rest
  let .ok stack := entryStack.reverse.foldlM (fun (s : Stack) word ↦ s.push (U256.ofNat word))
      Stack.empty | return false
  let entry := frame c stack
  let start := world c
  let (result, queries) := (((sload (context c) entry).run start).run).run []
  let frameAt (next : Frame) (words : List Nat) (gas pc : Nat) (warmed : Bool) :=
    frameFields entry next && next.stack.toList.map U256.toNat == words &&
      next.gasMeter.gasLeft == gas && next.pc == pc && hasSlots warmed next.accessedStorageKeys
  match c.outcome, result with
  | .underflow, .ok (.halt next .stackUnderflow, after) =>
    return queries.isEmpty && frameAt next [] c.gas entry.pc c.warm && stateFields start after false
  | .denied, .ok (.halt next .outOfGas, after) =>
    return queries.isEmpty && frameAt next rest c.gas entry.pc true && stateFields start after false
  | .fault, .error (.state (.witness (.missing (.node h)))) =>
    return queries == [(target, slot)] && h == marker
  | .read value, .ok (.continue next, after) =>
    let price := if c.warm then c.warmPrice else c.coldPrice
    let expected := if c.layer == .provider then [(target, slot)] else []
    return queries == expected && frameAt next (value :: rest) (c.gas - price) (entry.pc + 1) true &&
      stateFields start after true
  | _, _ => return false

#guard check ⟨false, 0, 100, 2100, 0, .fault, .underflow⟩
#guard check ⟨true, 99, 100, 2100, 3, .fault, .denied⟩
#guard check ⟨false, 2099, 100, 2100, 3, .fault, .denied⟩
#guard check ⟨false, 2100, 100, 2100, 1024, .transactionSlot, .read 0⟩
#guard check ⟨true, 100, 100, 2100, 1, .transactionClear, .read 0⟩
#guard check ⟨false, 2107, 100, 2100, 3, .blockSlot, .read (2 ^ 256 - 1)⟩
#guard check ⟨true, 103, 100, 2100, 3, .blockClear, .read 0⟩
#guard check ⟨true, 108, 100, 2100, 3, .provider, .read 37⟩
#guard check ⟨false, 2100, 100, 2100, 3, .fault, .fault⟩
#guard check ⟨false, 0, 17, 0, 1024, .provider, .read 37⟩
#guard check ⟨true, 16, 17, 0, 1024, .fault, .denied⟩
#guard check ⟨true, 0, 0, 19, 1024, .blockSlot, .read (2 ^ 256 - 1)⟩

end STFSpec.Conformance.Vm.Instructions.SloadControls
