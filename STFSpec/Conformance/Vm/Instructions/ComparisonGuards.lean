/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions
import STFSpec.Fork.Amsterdam

/-!
# ISZERO controls

Library `EthConformance`. These guards observe all frame fields, the exception
or continuation and selected world values. See
`STFSpec/informal/modules/EthVmInstructions.md` §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.ComparisonGuards
open STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private def addr (n : Nat) := Address.ofNat n
private def hash (n : Nat) := Hash32.ofBytes32 (FixedBytes.ofNat n)

private def blockEnv : BlockEnvironment :=
  ⟨U64.ofNat 11, 13, #[hash 17, hash 19], addr 23, 29, 31,
    U256.ofNat 37, FixedBytes.ofNat 41, U64.ofNat 43, hash 47, U64.ofNat 53⟩

private def txEnv : TransactionEnvironment :=
  ⟨addr 59, addr 61, true, Bytes.ofList [0, 128, 0], U256.ofNat 67, 71, 73,
    79, 83, 89, ∅, ∅, #[], #[], some 0, some (hash 97)⟩

private def context (price : Nat) : FrameCtx :=
  let costs := { STFSpec.Fork.Amsterdam.gasCosts with
    opcodeIsZero := price
    opcodeAdd := 2 ^ 301 + 17 }
  ⟨⟨costs, ⟨0, 7, 2 ^ 300 + 11, 13⟩, ⟨7, 0, 2 ^ 301 + 17⟩⟩,
    blockEnv, txEnv, addr 101, addr 103, U256.max, Bytes.ofList [255, 0, 128],
    some (addr 0), Bytes.ofList [96, 91, 255],
    validJumpDestinations (Bytes.ofList [91, 0, 91]),
    1024, by decide, true, true, false, addr 107⟩

private def world : VmWorld Id :=
  let pre : PreState Id := ⟨fun _ ↦ .ok none, fun _ _ ↦ .ok (U256.ofNat 109),
    fun _ ↦ .ok (ByteArray.mk #[0, 255, 128]), fun _ ↦ .ok (hash 113)⟩
  let block : BlockState Id :=
    ⟨pre, ⟨hash 127, hash 131, hash 137, hash 139⟩,
      (∅ : Std.ExtTreeMap Address (Option Account)).insert (addr 149) none,
      ⟨157, ∅, ∅⟩, ∅, ⟨163, ∅, ∅⟩, ∅, ∅, ∅, ∅, ∅, ∅, some (2 ^ 290 + 167)⟩
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
    f.logs.toList.map (fun l ↦ (l.address.toNat, l.topics.toList.map Hash32.toNat, l.data.toList)),
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

private def stackOf : List Nat → Option Stack
  | [] => some Stack.empty
  | word :: remaining => do
    let stack ← stackOf remaining
    (stack.push (U256.ofNat word)).toOption

private def runCase (price gas pc : Nat) (input expected : List Nat)
    (expectedHalt : Option ExceptionalHalt) : Bool := Id.run do
  let some inputStack := stackOf input | return false
  let some expectedStack := stackOf expected | return false
  let incoming := frame pc gas inputStack
  let desired := match expectedHalt with
    | some _ => frame pc gas expectedStack
    | none => frame (pc + 1) (gas - price) expectedStack
  let result := ((isZero (context price) incoming).run world).run
  match result, expectedHalt with
  | .ok (.halt after .stackUnderflow, retained), some .stackUnderflow
  | .ok (.halt after .outOfGas, retained), some .outOfGas
  | .ok (.continue after, retained), none =>
    return frameModel after == frameModel desired && worldModel retained == worldModel world
  | _, _ => return false

#guard runCase 3 0 0 [] [] (some .stackUnderflow)
#guard runCase 0 0 0 [] [] (some .stackUnderflow)
#guard runCase 3 2 11 [0, 2 ^ 256 - 1] [2 ^ 256 - 1] (some .outOfGas)
#guard runCase 3 3 11 [0, 2 ^ 256 - 1] [1, 2 ^ 256 - 1] none
#guard runCase 0 0 (2 ^ 300 + 17) [2 ^ 256 - 1] [0] none
#guard runCase (2 ^ 300 + 3) (2 ^ 300 + 3) 0 [0] [1] none
#guard runCase (2 ^ 300 + 3) (2 ^ 300 + 2) 0 [0] [] (some .outOfGas)
#guard runCase 3 5 0
  (0 :: List.replicate 1023 (2 ^ 256 - 1)) (1 :: List.replicate 1023 (2 ^ 256 - 1)) none

end STFSpec.Conformance.Vm.Instructions.ComparisonGuards
