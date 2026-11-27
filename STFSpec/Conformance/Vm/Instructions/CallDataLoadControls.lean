/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Fork.Amsterdam
import STFSpec.State.BlockInitialization
import STFSpec.State.TransactionInitialization
import STFSpec.Vm.Instructions

/-!
# Standalone CALLDATALOAD controls

Library `EthConformance`. Check the selected price, full offset, padded
input and complete frame update through the Instructions facade.
-/

namespace STFSpec.Conformance.Vm.Instructions.CallDataLoadControls
open STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private def addr (n : Nat) : Address := Address.ofNat n
private def hash (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)

private def context (price : Nat) (data : Bytes) : FrameCtx :=
  let config := STFSpec.Fork.Amsterdam.vmConfig
  let costs := { config.costs with opcodeCallDataLoad := price, veryLow := 113 }
  let block : BlockEnvironment :=
    ⟨U64.ofNat 11, 13, #[hash 17, hash 19], addr 23, 29, 31, U256.ofNat 37,
      FixedBytes.ofNat 41, U64.ofNat 43, hash 47, U64.ofNat 53⟩
  let tx : TransactionEnvironment :=
    ⟨addr 59, addr 61, true, Bytes.ofList [0, 128, 0], U256.ofNat 67, 71, 73,
      79, 83, 89, (∅ : AddrSet).insert (addr 91),
      (∅ : SlotSet).insert (addr 93, FixedBytes.ofNat 95), #[], #[], some 0, some (hash 97)⟩
  ⟨{ config with costs := costs }, block, tx, addr 101, addr 103, U256.max,
    data, some (addr 0), Bytes.ofList [0x35],
    validJumpDestinations (Bytes.ofList [91, 0, 91]), 7, by decide, true, true, false, addr 107⟩

private def frame (gas : Nat) (stack : Stack) : Frame :=
  let log : Log := ⟨addr 109, #[hash 256, hash 1, hash 256], Bytes.ofList [255, 0, 128]⟩
  ⟨2 ^ 261 + 117, stack, Memory.empty.expand 32 (by decide), ⟨gas, 13, 17, -19, 23, 29⟩,
    .concat (.leaf [log]) (.leaf [log]), (∅ : AddrSet).insert (addr 123), Bytes.ofList [0, 255, 128],
    (∅ : AddrSet).insert (addr 129), (∅ : SlotSet).insert (addr 131, FixedBytes.ofNat 137)⟩

private def world : VmWorld Option :=
  let unavailable : PreState Option := ⟨fun _ ↦ none, fun _ _ ↦ none, fun _ ↦ none, fun _ ↦ none⟩
  let block := BlockState.new unavailable ⟨hash 139, hash 149, hash 151, hash 157⟩
  let t := TxState.new { block with oldestAncestorOffset := some 163 }
  ⟨{ t with
    rev.transient := t.rev.transient.insert (addr 167, FixedBytes.ofNat 173) (U256.ofNat 179)
    obs.accountReads := t.obs.accountReads.insert (addr 181)
    obs.storageReads := t.obs.storageReads.insert (addr 191, FixedBytes.ofNat 193)
    obs.codeReads := t.obs.codeReads.insert (hash 197)
    obs.createdAccounts := t.obs.createdAccounts.insert (addr 199) }⟩

private def frameModel (f : Frame) :=
  let m := f.gasMeter
  (f.pc, f.stack.toList.map U256.toNat, f.memory.toBytes, f.logs.toList.map
    (fun l ↦ (l.address.toNat, l.topics.toList.map Hash32.toNat, l.data.toList)),
    f.accountsToDelete.toList.map Address.toNat, f.returnData.toList,
    f.accessedAddresses.toList.map Address.toNat,
    f.accessedStorageKeys.toList.map (fun (a, k) ↦ (a.toNat, k.toNat)),
    m.gasLeft, m.stateGasLeft, m.stateGasBaseline, m.refundCounter,
    m.stateGasSpilled, m.stateGasCommittedSpill)

private def worldModel (w : VmWorld Option) :=
  let t := w.tx
  (t.block.oldestAncestorOffset, t.block.consts.emptyCodeHash.toNat,
    t.rev.transient.toList.map (fun ((a,k), v) ↦ (a.toNat, k.toNat, v.toNat)),
    t.obs.accountReads.toList.map Address.toNat,
    t.obs.storageReads.toList.map (fun (a,k) ↦ (a.toNat, k.toNat)),
    t.obs.codeReads.toList.map Hash32.toNat,
    t.obs.createdAccounts.toList.map Address.toNat)

private def stackOf (words : List Nat) : Except ExceptionalHalt Stack :=
  words.reverse.foldlM (fun (stack : Stack) n ↦ stack.push (U256.ofNat n)) Stack.empty

private inductive Outcome where
  | underflow
  | denied
  | paid (word : Nat)

private def check (price gas : Nat) (data : Bytes)
    (words : List Nat) (outcome : Outcome) : Bool := Id.run do
  let .ok stack := stackOf words | return false
  let before := frame gas stack
  let actual := ((calldataload (context price data) before).run world).run
  match outcome, actual with
  | .underflow, some (.ok (.halt after .stackUnderflow, w)) =>
    return frameModel after == frameModel before && worldModel w == worldModel world
  | .denied, some (.ok (.halt after .outOfGas, w)) =>
    let .ok tail := stackOf words.tail | return false
    return frameModel after == frameModel { before with stack := tail } && worldModel w == worldModel world
  | .paid word, some (.ok (.continue after, w)) =>
    let .ok next := stackOf (word :: words.tail) | return false
    return frameModel after == frameModel { before with
      pc := before.pc + 1, stack := next, gasMeter.gasLeft := gas - price } &&
      worldModel w == worldModel world
  | _, _ => return false

private def input : Bytes :=
  Bytes.ofList ((List.range 36).map (fun i ↦ UInt8.ofNat (i * 19 + 0xa1)))

#guard check 61 17 input [] .underflow
#guard check 59 58 input [0, 23, 37] .denied
#guard check 3 3 input [0, 41] (.paid 0xa1b4c7daed001326394c5f728598abbed1e4f70a1d304356697c8fa2b5c8dbee)
#guard check 3 5 input [4, 43] (.paid 0xed001326394c5f728598abbed1e4f70a1d304356697c8fa2b5c8dbee0114273a)
#guard check 3 3 input [5, 47] (.paid 0x1326394c5f728598abbed1e4f70a1d304356697c8fa2b5c8dbee0114273a00)
#guard check 3 3 input [34] (.paid 0x273a000000000000000000000000000000000000000000000000000000000000)
#guard check 3 3 input [35] (.paid 0x3a00000000000000000000000000000000000000000000000000000000000000)
#guard check 3 3 input [36] (.paid 0)
#guard check 3 3 Bytes.empty [1] (.paid 0)
#guard check 3 8 input [2 ^ 256 - 1] (.paid 0)
#guard check 3 3 input [2 ^ 200 + 5] (.paid 0)
#guard check 3 3 input (5 :: List.replicate 1023 53) (.paid 0x1326394c5f728598abbed1e4f70a1d304356697c8fa2b5c8dbee0114273a00)
#guard check 0 0 (Bytes.ofList [0, 128, 0, 255]) [0] (.paid 0x008000ff00000000000000000000000000000000000000000000000000000000)
#guard check (2 ^ 269 + 23) (2 ^ 269 + 23) input [4] (.paid 0xed001326394c5f728598abbed1e4f70a1d304356697c8fa2b5c8dbee0114273a)

end STFSpec.Conformance.Vm.Instructions.CallDataLoadControls
