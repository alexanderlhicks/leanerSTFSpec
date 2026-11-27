/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions
import STFSpec.Fork.Amsterdam

/-!
# GASPRICE and BASEFEE controls

Library `EthConformance`. The guards observe complete frames, nominal faults and
sampled world values through both public handlers. See
`STFSpec/informal/modules/EthVmInstructions.md` §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.FeeWordControls
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
  | gasprice
  | baseFee

private def context (op : Instruction) (price fee : Nat) : FrameCtx :=
  let otherFee := 2 ^ 279 + 37
  let otherPrice := 313
  let initialCosts := STFSpec.Fork.Amsterdam.gasCosts
  let (block, tx, costs) := match op with
    | .gasprice =>
      ({ blockEnv with baseFeePerGas := otherFee }, { txEnv with effectiveGasPrice := fee },
        { initialCosts with opcodeGasPrice := price, opcodeBaseFee := otherPrice })
    | .baseFee =>
      ({ blockEnv with baseFeePerGas := fee }, { txEnv with effectiveGasPrice := otherFee },
        { initialCosts with opcodeGasPrice := otherPrice, opcodeBaseFee := price })
  ⟨⟨costs, ⟨0, 7, 2 ^ 300 + 11, 13⟩, ⟨7, 0, 2 ^ 301 + 17⟩⟩,
    block, tx, addr 101, addr 103, U256.max, Bytes.ofList [255, 0, 128],
    some (addr 0), Bytes.ofList [96, 91, 255],
    validJumpDestinations (Bytes.ofList [91, 0, 91]),
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

private inductive Outcome where
  | success
  | denied
  | full
  | conversionFault

private def runCase (op : Instruction) (price gas pc fee : Nat) (input : List Nat)
    (expected : Outcome) : Bool := Id.run do
  let some inputStack := stackOf input | return false
  let incoming := frame pc gas inputStack
  let ctx := context op price fee
  let handler : Handler Id := match op with
    | .gasprice => gasprice
    | .baseFee => baseFee
  let result := ((handler ctx incoming).run world).run
  let sameFrameAndWorld (actual desired : Frame) (retained : VmWorld Id) : Bool :=
    frameModel actual == frameModel desired && worldModel retained == worldModel world
  match result, expected with
  | .ok (.halt after .outOfGas, retained), .denied => return sameFrameAndWorld after incoming retained
  | .ok (.halt after .stackOverflow, retained), .full =>
    return sameFrameAndWorld after (frame pc (gas - price) inputStack) retained
  | .ok (.continue after, retained), .success =>
    let some desiredStack := stackOf (fee :: input) | return false
    return sameFrameAndWorld after (frame (pc + 1) (gas - price) desiredStack) retained
  | .error (.u256Overflow .gasPrice), .conversionFault =>
    return match op with | .gasprice => true | .baseFee => false
  | .error (.u256Overflow .baseFee), .conversionFault =>
    return match op with | .gasprice => false | .baseFee => true
  | _, _ => return false

private def both (price gas fee : Nat) (input : List Nat) (expected : Outcome) : Bool :=
  let pc := 2 ^ 272 + 41
  runCase .gasprice price gas pc fee input expected && runCase .baseFee price gas pc fee input expected

private def fullWords := (List.range 1024).map (fun i ↦ 0x520000 + 0x17 * i)
private def heavy := 2 ^ 275 + 29

#guard both 2 2 0 [] .success
#guard both 2 11 (2 ^ 256 - 1) (fullWords.take 1023) .success
#guard both 2 5 (2 ^ 256 - 1) fullWords .full
#guard both 2 2 (2 ^ 256) fullWords .conversionFault
#guard both 2 5 (2 ^ 256) [] .conversionFault
#guard both 2 1 (2 ^ 256 - 1) fullWords .denied
#guard both 2 1 (2 ^ 256 + 79) fullWords .denied
#guard both 0 0 (2 ^ 256) [0, 255] .conversionFault
#guard both 0 0 0x8100 [0, 255] .success
#guard both heavy heavy 0x8100 [1, 3] .success
#guard both heavy (heavy - 1) 0 [5, 7] .denied

private def gaspriceType {m : Type → Type} [Monad m] : Handler m := gasprice
private def baseFeeType {m : Type → Type} [Monad m] : Handler m := baseFee

end STFSpec.Conformance.Vm.Instructions.FeeWordControls
