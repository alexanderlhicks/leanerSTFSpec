/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Fork.Amsterdam
import STFSpec.Vm.Instructions

/-!
# LOG0 through LOG4 controls

Library `EthConformance`. Exercise complete stack, charge, memory and log effects through
the Instructions facade.
See `STFSpec/informal/modules/EthVmInstructions.md` §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.LogOpcodeControls

open STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private def addr (n : Nat) := Address.ofNat n
private def hash (n : Nat) := Hash32.ofBytes32 (FixedBytes.ofNat n)

private def blockEnv : BlockEnvironment :=
  ⟨U64.ofNat 11, 13, #[hash 17, hash 19], addr 23, 29, 31,
    U256.ofNat 37, FixedBytes.ofNat 41, U64.ofNat 43, hash 47, U64.ofNat 53⟩

private def txEnv : TransactionEnvironment :=
  ⟨addr 59, addr 61, true, Bytes.ofList [0, 128, 0], U256.ofNat 67, 71, 73,
    79, 83, 89, ∅, ∅, #[], #[], some 0, some (hash 97)⟩

private def context (static free : Bool) : FrameCtx :=
  let price := fun n : Nat ↦ if free then 0 else n
  let costs := { STFSpec.Fork.Amsterdam.gasCosts with
    opcodeLogBase := price 19, opcodeLogDataPerByte := price 7, opcodeLogTopic := price 23,
    memoryPerWord := price 11, zero := price 31 }
  ⟨⟨costs, ⟨0, 7, 2 ^ 300 + 11, 13⟩, ⟨7, 0, 2 ^ 301 + 17⟩⟩,
    blockEnv, txEnv, addr 101, addr 103, U256.max, Bytes.ofList [255, 0, 128],
    some (addr 0), Bytes.ofList [0, 255], validJumpDestinations (Bytes.ofList [91]),
    1024, by decide, true, static, false, addr 107⟩

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

private def memory : Memory := expanded.write 29 (Bytes.ofList [73, 128, 255]) (by
  right
  rw [expanded_size]
  decide)

private def frame (pc gas : Nat) (stack : Stack) : Frame :=
  let entry : Log := ⟨addr 256, #[hash 256, hash 1, hash 256], Bytes.ofList [255, 0, 128]⟩
  ⟨pc, stack, memory, ⟨gas, 2^279 + 67, 2^273 + 39, -17, 5, 11⟩,
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
  | static
  | success (data : List UInt8)

private def topicWord (i : Nat) : Nat := 2^(248+i) + 159 + 13*i

private def check (n : Fin 5) (static free : Bool) (words : List Nat) (grant spent growth : Nat)
    (expected : Expected) (initial : Memory := memory) : Bool := Id.run do
  let some original := stackOf words | return false
  let some rest := stackOf (words.drop (2 + n.val)) | return false
  let entry := { frame (2^271 + 83) grant original with memory := initial }
  let cfg := context static free
  let action : Handler Id := logN n
  let result := ((action cfg entry).run world).run
  if aligned : growth % 32 = 0 then
    let popped := { entry with stack := rest }
    let paid := { popped with
      memory := entry.memory.expand growth aligned
      gasMeter := { entry.gasMeter with gasLeft := grant - spent } }
    match result, expected with
    | .ok (.halt after .stackUnderflow, retained), .underflow =>
      return frameModel after == frameModel popped && worldModel retained == worldModel world
    | .ok (.halt after .outOfGas, retained), .denied =>
      return frameModel after == frameModel popped && worldModel retained == worldModel world
    | .ok (.halt after .writeInStaticContext, retained), .static =>
      return frameModel after == frameModel paid && worldModel retained == worldModel world
    | .ok (.continue after, retained), .success data =>
      let topics := ((words.drop 2).take n.val).map hash
      let log : Log := ⟨cfg.currentTarget, topics.toArray, Bytes.ofList data⟩
      let want := { paid with pc := entry.pc + 1, logs := .leaf (entry.logs.toList ++ [log]) }
      return frameModel after == frameModel want && worldModel retained == worldModel world
    | _, _ => return false
  else
    return false

#guard (List.finRange 5).all (fun n ↦
  let words := [29, 7] ++ (List.range n.val).map topicWord
  (List.range (2 + n.val)).all (fun size ↦ check n true false (words.take size) 0 0 0 .underflow))

#guard (List.finRange 5).all (fun n ↦
  let words := [29, 7] ++ (List.range n.val).map topicWord ++ [93, 101]
  let spend := 110 + 23*n.val
  check n true false words (spend - 1) 0 0 .denied)

#guard (List.finRange 5).all (fun n ↦
  let words := [62, 4] ++ (List.range n.val).map topicWord ++ [93]
  let spend := 100 + 23*n.val
  check n true false words spend spend 64 .static)

#guard (List.finRange 5).all (fun n ↦
  let words := [29, 7] ++ (List.range n.val).map topicWord ++ [93, 95, 101]
  let spend := 110 + 23*n.val
  check n false false words (spend + 17) spend 32 (.success [73, 128, 255, 0, 0, 0, 0]))

#guard (List.finRange 5).all (fun n ↦
  let words := [2^256 - 1, 0] ++ (List.range n.val).map topicWord
  check n false true words 0 0 0 (.success []))

#guard check 4 true false ([2^256 - 1, 0] ++ (List.range 4).map topicWord) 142 142 0 .static
#guard check 4 true false ([2^256 - 1, 2] ++ (List.range 4).map topicWord ++ [97]) 142 0 0 .denied
#guard check 4 false false ([29, 3] ++ (List.range 4).map topicWord ++ List.range 1018)
  163 163 0 (.success [73, 128, 255])

private def largerMemory : Memory := Memory.empty.expand 64 (by decide)

private theorem largerMemory_size : largerMemory.size = 64 := by
  rw [← Memory.length_toBytes, largerMemory, Memory.toBytes_expand, Memory.toBytes_empty]
  rfl

private def widerWindow : Memory := largerMemory.write 61 (Bytes.ofList [201, 0, 103]) (by
  right
  rw [largerMemory_size]
  decide)

#guard check 0 true false [61, 18, 93] 187 187 32 .static widerWindow
#guard check 0 false false [61, 18, 93] 192 187 32
  (.success ([201, 0, 103] ++ List.replicate 15 0)) widerWindow

end STFSpec.Conformance.Vm.Instructions.LogOpcodeControls
