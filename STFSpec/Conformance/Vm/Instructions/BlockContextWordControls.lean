/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions
import STFSpec.Fork.Amsterdam

/-!
# Bounded block-context word controls

Library `EthConformance`. These guards compare whole frame observations and
sampled world values through the five public handlers.
See `STFSpec/informal/modules/EthVmInstructions.md` §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.BlockContextWordControls
open STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private def addr (n : Nat) := Address.ofNat n
private def hash (n : Nat) := Hash32.ofBytes32 (FixedBytes.ofNat n)

private def blockEnv : BlockEnvironment :=
  ⟨U64.ofNat 11, 13, #[hash 17, hash 19], addr 23, 29, 31,
    U256.ofNat 37, FixedBytes.ofNat 41, U64.ofNat 43, hash 47, U64.ofNat 53⟩

private def txEnv : TransactionEnvironment :=
  ⟨addr 59, addr 61, true, Bytes.ofList [0, 128, 0], U256.ofNat 67, 71, 73,
    79, 83, 89, ∅, ∅, #[], #[], some 0, some (hash 97)⟩

private inductive Instruction where
  | coinbase
  | timestamp
  | randao
  | chainId
  | slotNumber

private def mixedRandomness : Nat :=
  0x00f701008080a160ec8b28ff94c30073013c082ef6e64044bbc9ea9f4d0197ad

private def context (op : Instruction) (price : Nat) (high static : Bool) : FrameCtx :=
  let initial := { STFSpec.Fork.Amsterdam.gasCosts with
    opcodeCoinbase := 17, opcodeTimestamp := 19, opcodePrevRandao := 23,
    opcodeChainId := 29, opcodeSlotNum := 31 }
  let costs := match op with
    | .coinbase => { initial with opcodeCoinbase := price }
    | .timestamp => { initial with opcodeTimestamp := price }
    | .randao => { initial with opcodePrevRandao := price }
    | .chainId => { initial with opcodeChainId := price }
    | .slotNumber => { initial with opcodeSlotNum := price }
  let block := if high then
      { blockEnv with
        coinbase := addr (2^160 - 1), time := U256.max, prevRandao := FixedBytes.ofNat 0,
        chainId := U64.ofNat (2^64 - 1), slotNumber := U64.ofNat 0 }
    else
      { blockEnv with
        coinbase := addr 0x810012, time := U256.zero, prevRandao := FixedBytes.ofNat mixedRandomness,
        chainId := U64.ofNat 0x123457, slotNumber := U64.ofNat (2^64 - 1) }
  ⟨⟨costs, ⟨0, 7, 2 ^ 300 + 11, 13⟩, ⟨7, 0, 2 ^ 301 + 17⟩⟩,
    block, txEnv, addr 0x800011, addr 0xf7010080, U256.ofNat 247, Bytes.ofList [255, 0, 128],
    some (addr 0), Bytes.ofList [96, 91, 255],
    validJumpDestinations (Bytes.ofList [91, 0, 91]),
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

private def runCase (op : Instruction) (price gas : Nat) (high static : Bool) (input : List Nat)
    (expectedWord : Nat) (expectedHalt : Option ExceptionalHalt) : Bool := Id.run do
  let some inputStack := stackOf input | return false
  let pc := 2 ^ 274 + 41
  let incoming := frame pc gas inputStack
  let handler : Handler Id := match op with
    | .coinbase => coinbase
    | .timestamp => timestamp
    | .randao => prevRandao
    | .chainId => chainId
    | .slotNumber => slotNumber
  let result := ((handler (context op price high static) incoming).run world).run
  let sameFrameAndWorld (actual desired : Frame) (retained : VmWorld Id) : Bool :=
    frameModel actual == frameModel desired && worldModel retained == worldModel world
  match result, expectedHalt with
  | .ok (.halt after .outOfGas, retained), some .outOfGas =>
    return sameFrameAndWorld after incoming retained
  | .ok (.halt after .stackOverflow, retained), some .stackOverflow =>
    return sameFrameAndWorld after (frame pc (gas - price) inputStack) retained
  | .ok (.continue after, retained), none =>
    let some desiredStack := stackOf (expectedWord :: input) | return false
    return sameFrameAndWorld after (frame (pc + 1) (gas - price) desiredStack) retained
  | _, _ => return false

private def fullWords := (List.range 1024).map (fun i ↦ 0x520000 + 0x17 * i)
private def heavy := 2 ^ 275 + 29

#guard runCase .coinbase 2 1 false true fullWords 0 (some .outOfGas)
#guard runCase .coinbase 2 5 true false fullWords 0 (some .stackOverflow)
#guard runCase .coinbase 2 2 false true [] 0x810012 none
#guard runCase .coinbase 0 0 true false (fullWords.take 1023) (2^160 - 1) none
#guard runCase .timestamp 2 1 true false [] 0 (some .outOfGas)
#guard runCase .timestamp 0 0 false true fullWords 0 (some .stackOverflow)
#guard runCase .timestamp 7 23 true true [] (2^256 - 1) none
#guard runCase .timestamp heavy heavy false false [1, 3] 0 none
#guard runCase .randao heavy (heavy - 1) false true [5, 7] 0 (some .outOfGas)
#guard runCase .randao 2 2 true false fullWords 0 (some .stackOverflow)
#guard runCase .randao 2 2 false true [] mixedRandomness none
#guard runCase .randao 0 0 true false (fullWords.take 1023) 0 none
#guard runCase .chainId 2 1 true true fullWords 0 (some .outOfGas)
#guard runCase .chainId 2 4 false false fullWords 0 (some .stackOverflow)
#guard runCase .chainId 2 2 true true [] (2^64 - 1) none
#guard runCase .chainId heavy heavy false false [7] 0x123457 none
#guard runCase .slotNumber 2 1 false true fullWords 0 (some .outOfGas)
#guard runCase .slotNumber 2 2 true false fullWords 0 (some .stackOverflow)
#guard runCase .slotNumber 2 2 false true [7, 0] (2^64 - 1) none
#guard runCase .slotNumber heavy heavy true false [] 0 none

private theorem wideningPreservesU64 (word : U64) : (U256.ofNat word.toNat).toNat = word.toNat :=
  U256.toNat_ofNat_of_lt (Nat.lt_trans (U64.toNat_lt word) (by decide))

private theorem randomnessPreservesBytes (bytes : Bytes32) : (U256.ofBeBytes32 bytes).toBeBytes32 = bytes :=
  U256.toBeBytes32_ofBeBytes32 bytes

private def signatures {m : Type → Type} [Monad m] : List (Handler m) :=
  [coinbase, timestamp, prevRandao, chainId, slotNumber]

end STFSpec.Conformance.Vm.Instructions.BlockContextWordControls
