/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Fork.Amsterdam
import STFSpec.Vm.Instructions

/-!
# MCOPY controls

Library `EthConformance`. Exercise complete stack, charge and overlapping memory effects through
the Instructions facade.
See `STFSpec/informal/modules/EthVmInstructions.md` §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.MemoryCopyControls

open STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private def addr (n : Nat) := Address.ofNat n
private def hash (n : Nat) := Hash32.ofBytes32 (FixedBytes.ofNat n)

private def blockEnv : BlockEnvironment :=
  ⟨U64.ofNat 11, 13, #[hash 17, hash 19], addr 23, 29, 31,
    U256.ofNat 37, FixedBytes.ofNat 41, U64.ofNat 43, hash 47, U64.ofNat 53⟩

private def txEnv : TransactionEnvironment :=
  ⟨addr 59, addr 61, true, Bytes.ofList [0, 128, 0], U256.ofNat 67, 71, 73,
    79, 83, 89, ∅, ∅, #[], #[], some 0, some (hash 97)⟩

private def context (base perWord memoryWord seed : Nat) : FrameCtx :=
  let costs := { STFSpec.Fork.Amsterdam.gasCosts with
    opcodeMcopyBase := base, opcodeCopyPerWord := perWord, memoryPerWord := memoryWord,
    zero := seed, opcodeCallDataCopyBase := 223, opcodeCodeCopyBase := 227 }
  ⟨⟨costs, ⟨0, 7, 2 ^ 300 + 11, 13⟩, ⟨7, 0, 2 ^ 301 + 17⟩⟩,
    blockEnv, txEnv, addr 101, addr 103, U256.max, Bytes.ofList [255, 0, 128],
    some (addr 0), Bytes.ofList [0, 255], validJumpDestinations (Bytes.ofList [91]),
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

private def makeMemory (values : List UInt8) : Memory :=
  let data := Bytes.ofList values
  let padded := Memory.empty.expand (ceil32 data.size) (ceil32_mod_eq_zero _)
  padded.write 0 data (Or.inr (by
    have size : padded.size = ceil32 data.size := by
      rw [← Memory.length_toBytes, Memory.toBytes_expand, Memory.toBytes_empty,
        List.nil_append, List.length_replicate]
    rw [size, Nat.zero_add]
    exact le_ceil32 _))

private def frame (gas : Nat) (stack : Stack) (memory : Memory) : Frame :=
  let entry : Log := ⟨addr 256, #[hash 256, hash 1, hash 256], Bytes.ofList [255, 0, 128]⟩
  ⟨2^277+139, stack, memory, ⟨gas, 2^283 + 163, 2^273 + 39, -17, 5, 11⟩,
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

private inductive Expected where
  | underflow
  | denied
  | success (memory : List UInt8)

private def controls (prices : Nat × Nat × Nat × Nat) (initial : List UInt8)
    (words : List Nat) (grant spent : Nat) (expected : Expected) : Bool := Id.run do
  let (base, perWord, memoryWord, seed) := prices
  let some stack := stackOf words | return false
  let some rest := stackOf (words.drop 3) | return false
  let entry := frame grant stack (makeMemory initial)
  let popped := { entry with stack := rest }
  let result := (((mcopy : Handler Id) (context base perWord memoryWord seed) entry).run world).run
  match result, expected with
  | .ok (.halt after .stackUnderflow, retained), .underflow =>
    return frameModel after == frameModel popped && worldModel retained == worldModel world
  | .ok (.halt after .outOfGas, retained), .denied =>
    return frameModel after == frameModel popped && worldModel retained == worldModel world
  | .ok (.continue after, retained), .success bytes =>
    let paid := { popped with
      pc := entry.pc + 1
      gasMeter := { entry.gasMeter with gasLeft := grant - spent }
      memory := makeMemory bytes }
    return frameModel after == frameModel paid && worldModel retained == worldModel world
  | _, _ => return false

private def prices : Nat × Nat × Nat × Nat := (17, 11, 13, 7)
private def original : List UInt8 := (List.range 32).map (fun n ↦ UInt8.ofNat (41 + 7*n))
private def limit : Nat := 2^256 - 1
private def wide : Nat := 2^269+151

#guard controls prices original [] 0 0 .underflow
#guard controls prices original [38] 0 0 .underflow
#guard controls prices original [38, 27] 0 0 .underflow

#guard controls prices original [7, 2, 10, 91] 35 35
  (.success (original.take 7 ++ [55, 62, 69, 76, 83, 90, 97, 104, 111, 118] ++ original.drop 17))
#guard controls prices original [2, 7, 10, 91] 42 35
  (.success (original.take 2 ++ [90, 97, 104, 111, 118, 125, 132, 139, 146, 153] ++ original.drop 12))
#guard controls prices original [7, 7, 10, 91] 35 35 (.success original)
#guard controls prices original [39, 1, 6, 91] 48 48
  (.success (original ++ List.replicate 7 0 ++ [48, 55, 62, 69, 76, 83] ++ List.replicate 19 0))
#guard controls prices original [7, 29, 7, 91] 48 48
  (.success (original.take 7 ++ [244, 251, 2, 0, 0, 0, 0] ++ original.drop 14 ++ List.replicate 32 0))

#guard controls prices original [limit, limit, 0, 91] 24 24 (.success original)
#guard controls (0, 11, 13, 0) original [limit, limit, 0, 91] 0 0 (.success original)
#guard controls prices original [limit, 4, 2, 91] 99 0 .denied
#guard controls prices original [4, limit, 2, 91] 99 0 .denied

#guard controls (wide, 11, 13, 7) original [7, 7, 10, 91] (wide + 17) 0 .denied
#guard controls (wide, 11, 13, 7) original ([7, 7, 10] ++ List.range 1021) (wide + 18) (wide + 18)
  (.success original)

end STFSpec.Conformance.Vm.Instructions.MemoryCopyControls
