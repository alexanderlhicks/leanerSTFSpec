/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions
import STFSpec.Fork.Amsterdam

/-!
# Byte-size word controls

Library `EthConformance`. Distinct lengths, prices and the current return buffer
exercise the complete frame through the Instructions facade.
See `STFSpec/informal/modules/EthVmInstructions.md` §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.SizeWordControls
open STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private def addr (n : Nat) := Address.ofNat n
private def hash (n : Nat) := Hash32.ofBytes32 (FixedBytes.ofNat n)

private def blockEnv : BlockEnvironment :=
  ⟨U64.ofNat 11, 13, #[hash 17, hash 19], addr 23, 29, 31,
    U256.ofNat 37, FixedBytes.ofNat 41, U64.ofNat 43, hash 47, U64.ofNat 53⟩

private def txEnv : TransactionEnvironment :=
  ⟨addr 59, addr 61, true, Bytes.ofList [0, 128, 0], U256.ofNat 67, 71, 73,
    79, 83, 89, ∅, ∅, #[], #[], some 0, some (hash 97)⟩

private def bytes (count salt : Nat) : Bytes :=
  Bytes.generate count (fun i ↦ UInt8.ofNat (i * 73 + salt))

private def context (prices : Nat × Nat × Nat) (sizes : Nat × Nat) : FrameCtx :=
  let (callPrice, codePrice, returnPrice) := prices
  let code := bytes sizes.2 61
  let costs := { STFSpec.Fork.Amsterdam.gasCosts with
    opcodeCallDataSize := callPrice, opcodeCodeSize := codePrice,
    opcodeReturnDataSize := returnPrice, opcodeGasPrice := 71, opcodeBaseFee := 73 }
  ⟨⟨costs, ⟨0, 7, 2 ^ 300 + 11, 13⟩, ⟨7, 0, 2 ^ 301 + 17⟩⟩,
    blockEnv, txEnv, addr 101, addr 103, U256.max, bytes sizes.1 31,
    some (addr 0), code, validJumpDestinations (Bytes.ofList [91]),
    1024, by decide, true, true, false, addr 107⟩

private def world : VmWorld Id :=
  let pre : PreState Id := ⟨fun _ ↦ .ok none, fun _ _ ↦ .ok (U256.ofNat 109),
    fun _ ↦ .ok (ByteArray.mk #[0, 255, 128]), fun _ ↦ .ok (hash 113)⟩
  let block : BlockState Id :=
    ⟨pre, ⟨hash 127, hash 131, hash 137, hash 139⟩,
      (∅ : Std.ExtTreeMap Address (Option Account)).insert (addr 149) none,
      ⟨157, ∅, ∅⟩, ∅, ⟨163, ∅, ∅⟩, ∅, ∅, ∅, ∅, ∅, ∅,
      some (2 ^ 290 + 167)⟩
  let rev : TxRevertible :=
    ⟨∅, ⟨173, ∅, ∅⟩, ∅, ⟨179, ∅, ∅⟩, ∅, ∅, ∅,
      (∅ : Std.ExtTreeMap (Address × Bytes32) U256).insert
        (addr 181, FixedBytes.ofNat 191) (U256.ofNat 193)⟩
  let obs : TxObs :=
    ⟨(∅ : Std.HashSet Address).insert (addr 197), ∅, ∅,
      (∅ : Std.HashSet Address).insert (addr 199)⟩
  ⟨⟨block, rev, obs⟩⟩

private def expanded : Memory := Memory.empty.expand 32 (by decide)

private theorem expanded_size : expanded.size = 32 := by
  rw [← Memory.length_toBytes, expanded, Memory.toBytes_expand, Memory.toBytes_empty]
  rfl

private def memory : Memory := expanded.write 2 (Bytes.ofList [0, 128, 255, 1]) (by
  right
  rw [expanded_size]
  decide)

private def frame (pc gas : Nat) (stack : Stack) : Frame :=
  let entry : Log := ⟨addr 256, #[hash 256, hash 1, hash 256], Bytes.ofList [255, 0, 128]⟩
  ⟨pc, stack, memory, ⟨gas, 101, 2, -17, 5, 11⟩,
    .concat (.leaf [entry]) (.concat .empty (.leaf [entry])),
    (∅ : AddrSet).insert (addr 256), Bytes.ofList [0, 255, 128, 0],
    (∅ : AddrSet).insert (addr 1),
    ((∅ : SlotSet).insert (addr 1, FixedBytes.ofNat 256)).insert (addr 256, FixedBytes.ofNat 1)⟩

private def frameModel (f : Frame) :=
  (f.pc, f.stack.toList.map U256.toNat, f.memory.toBytes,
    (f.gasMeter.gasLeft, f.gasMeter.stateGasLeft, f.gasMeter.stateGasBaseline,
      f.gasMeter.refundCounter, f.gasMeter.stateGasSpilled, f.gasMeter.stateGasCommittedSpill),
    f.logs.toList.map (fun l ↦
      (l.address.toNat, l.topics.toList.map Hash32.toNat, l.data.toList)),
    f.accountsToDelete.toList.map Address.toNat, f.returnData.toList,
    f.accessedAddresses.toList.map Address.toNat,
    f.accessedStorageKeys.toList.map (fun (a, k) ↦ (a.toNat, k.toNat)))

private def worldModel (w : VmWorld Id) :=
  let tx := w.tx
  let storage := ((tx.block.preState.getStorage (addr 1) (FixedBytes.ofNat 2)).toOption).map
    U256.toNat
  (tx.block.accountOrder.next, tx.block.storageAddressOrder.next,
    tx.rev.accountOrder.next, tx.rev.storageAddressOrder.next,
    tx.block.oldestAncestorOffset, tx.block.consts.emptyCodeHash.toNat,
    storage, tx.obs.createdAccounts.contains (addr 199), tx.obs.accountReads.contains (addr 197))

private def stackOf (words : List Nat) : Option Stack :=
  words.reverse.foldlM (fun stack word ↦ (stack.push (U256.ofNat word)).toOption) Stack.empty

private def check (action : Handler Id) (prices : Nat × Nat × Nat) (sizes : Nat × Nat)
    (returnSize actualPrice gas count : Nat) (expected : Except ExceptionalHalt Nat) : Bool := Id.run do
  let words := (List.range count).map (· + 283)
  let some stack := stackOf words | return false
  let pc := 2^269 + 19
  let start := { frame pc gas stack with returnData := bytes returnSize 91 }
  let run := ((action (context prices sizes) start).run world).run
  match expected, run with
  | .error .outOfGas, .ok (.halt after .outOfGas, retained) =>
    return frameModel after == frameModel start && worldModel retained == worldModel world
  | .error .stackOverflow, .ok (.halt after .stackOverflow, retained) =>
    let paid := { start with gasMeter.gasLeft := gas - actualPrice }
    return frameModel after == frameModel paid && worldModel retained == worldModel world
  | .ok size, .ok (.continue after, retained) =>
    let some pushed := stackOf (size :: words) | return false
    let complete := { start with pc := pc + 1, stack := pushed, gasMeter.gasLeft := gas - actualPrice }
    return frameModel after == frameModel complete && worldModel retained == worldModel world
  | _, _ => return false

#guard check calldatasize (3, 5, 7) (258, 513) 259 3 2 1024 (.error .outOfGas)
#guard check calldatasize (3, 5, 7) (258, 513) 259 3 3 1024 (.error .stackOverflow)
#guard check calldatasize (3, 5, 7) (258, 513) 259 3 11 1023 (.ok 258)
#guard check calldatasize (0, 5, 7) (0, 513) 259 0 0 0 (.ok 0)

#guard check codesize (3, 5, 7) (258, 513) 259 5 4 1024 (.error .outOfGas)
#guard check codesize (3, 5, 7) (258, 513) 259 5 5 1024 (.error .stackOverflow)
#guard check codesize (3, 5, 7) (258, 513) 259 5 11 1023 (.ok 513)
#guard check codesize (3, 2^278 + 19, 7) (258, 0) 259 (2^278 + 19) (2^278 + 19) 0 (.ok 0)

#guard check returndatasize (3, 5, 7) (258, 513) 259 7 6 1024 (.error .outOfGas)
#guard check returndatasize (3, 5, 7) (258, 513) 259 7 7 1024 (.error .stackOverflow)
#guard check returndatasize (3, 5, 7) (258, 513) 259 7 11 1023 (.ok 259)
#guard check returndatasize (3, 5, 7) (258, 513) 0 7 11 1023 (.ok 0)
#guard check returndatasize (3, 5, 7) (258, 513) 513 7 11 1023 (.ok 513)

private def callSignature {m : Type → Type} [Monad m] : Handler m := calldatasize
private def codeSignature {m : Type → Type} [Monad m] : Handler m := codesize
private def returnSignature {m : Type → Type} [Monad m] : Handler m := returndatasize

end STFSpec.Conformance.Vm.Instructions.SizeWordControls
