/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Fork.Amsterdam
import STFSpec.Vm.Instructions

/-!
# Local copy controls

Library `EthConformance`. CALLDATACOPY and CODECOPY compare the complete
paid or halted frame through the Instructions facade.
See `STFSpec/informal/modules/EthVmInstructions.md` §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.LocalCopyControls

open STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private def addr (n : Nat) := Address.ofNat n
private def hash (n : Nat) := Hash32.ofBytes32 (FixedBytes.ofNat n)

private def blockEnv : BlockEnvironment :=
  ⟨U64.ofNat 11, 13, #[hash 17, hash 19], addr 23, 29, 31,
    U256.ofNat 37, FixedBytes.ofNat 41, U64.ofNat 43, hash 47, U64.ofNat 53⟩

private def txEnv : TransactionEnvironment :=
  ⟨addr 59, addr 61, true, Bytes.ofList [0, 128, 0], U256.ofNat 67, 71, 73,
    79, 83, 89, ∅, ∅, #[], #[], some 0, some (hash 97)⟩

private def config (callBase codeBase copyWord memoryWord seed : Nat) : VmConfig :=
  let costs := { STFSpec.Fork.Amsterdam.gasCosts with
    opcodeCallDataCopyBase := callBase, opcodeCodeCopyBase := codeBase,
    opcodeCopyPerWord := copyWord, memoryPerWord := memoryWord, zero := seed }
  ⟨costs, ⟨0, 7, 2 ^ 300 + 11, 13⟩, ⟨7, 0, 2 ^ 301 + 17⟩⟩

private def prices := config 17 29 11 5 7

private def context (cfg : VmConfig) : FrameCtx :=
  ⟨cfg, blockEnv, txEnv, addr 101, addr 103, U256.max,
    Bytes.ofList [0x11, 0, 0x21, 0xff], some (addr 0),
    Bytes.ofList [0x60, 0xff, 0x13], validJumpDestinations (Bytes.ofList [91]),
    1024, by decide, true, false, false, addr 107⟩

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

private def overwrite (atByte : Nat) (value : List UInt8) : List UInt8 :=
  if value.isEmpty then memory.toBytes else
    let previous := memory.toBytes
    let required := (atByte + value.length + 31) / 32 * 32
    let expanded := previous ++ List.replicate (required - previous.length) 0
    expanded.take atByte ++ value ++ expanded.drop (atByte + value.length)

private def check (action : Handler Id) (cfg : VmConfig) (budget paid : Nat)
    (words tail : List Nat) (expected : Except ExceptionalHalt (Nat × List UInt8)) : Bool := Id.run do
  let some stack := stackOf words | return false
  let some remaining := stackOf tail | return false
  let pc := 2^270 + 19
  let start := frame pc budget stack
  let result := ((action (context cfg) start).run world).run
  match result, expected with
  | .ok (.halt after .outOfGas, retained), .error .outOfGas
  | .ok (.halt after .stackUnderflow, retained), .error .stackUnderflow =>
    return frameModel after == frameModel (frame pc budget remaining) &&
      worldModel retained == worldModel world
  | .ok (.continue after, retained), .ok (atByte, value) =>
    return frameModel { after with memory := start.memory } == frameModel (frame (pc + 1) paid remaining) &&
      after.memory.toBytes == overwrite atByte value && worldModel retained == worldModel world
  | _, _ => return false

#guard check calldatacopy prices 0 0 [] [] (.error .stackUnderflow)
#guard check calldatacopy prices 0 0 [31] [] (.error .stackUnderflow)
#guard check codecopy prices 0 0 [31, 1] [] (.error .stackUnderflow)
#guard check calldatacopy prices 39 39 [31, 1, 3, 9] [9] (.error .outOfGas)
#guard check calldatacopy prices 40 0 [31, 1, 3, 9] [9] (.ok (31, [0, 0x21, 0xff]))
#guard check codecopy prices 48 1 [12, 1, 4, 12] [12] (.ok (12, [0xff, 0x13, 0, 0]))
#guard check calldatacopy prices 35 0 [20, 2^256 - 1, 4] [] (.ok (20, [0, 0, 0, 0]))
#guard check calldatacopy prices 24 0 [2^256 - 1, 2^256 - 1, 0] [] (.ok (2^256 - 1, []))
#guard check codecopy (config 31 0 99 101 0) 0 0 [2^256 - 1, 2^256 - 1, 0, 91] [91]
  (.ok (2^256 - 1, []))
#guard check codecopy prices 0 0 [2^256 - 1, 7, 1, 3] [3] (.error .outOfGas)
#guard check calldatacopy prices 0 0 [12, 7, 2^256 - 1, 3] [3] (.error .outOfGas)
#guard check codecopy (config 31 (2^258 + 13) 7 11 19) (2^258 + 39) 0 [1, 0, 1] [] (.ok (1, [0x60]))
#guard check codecopy prices 47 0 ([2, 2, 2] ++ List.range 1021) (List.range 1021)
  (.ok (2, [0x13, 0]))

private def calldataSignature {m : Type → Type} [Monad m] : Handler m := calldatacopy
private def codeSignature {m : Type → Type} [Monad m] : Handler m := codecopy

end STFSpec.Conformance.Vm.Instructions.LocalCopyControls
