/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions
import STFSpec.Fork.Amsterdam

/-!
# Bounded context-word controls

Library `EthConformance`. The guards observe the complete frame, the result tag and sampled world values.
The ordinary clients check the public local laws. See
`STFSpec/informal/modules/EthVmInstructions.md` §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.ContextWordControls
open STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private def addr (n : Nat) := Address.ofNat n
private def hash (n : Nat) := Hash32.ofBytes32 (FixedBytes.ofNat n)

private def blockEnv : BlockEnvironment :=
  ⟨U64.ofNat (2 ^ 64 - 1), 13, #[hash 17, hash 19], addr (2 ^ 159 + 47), 29, 31,
    U256.ofNat (2 ^ 200 + 99), FixedBytes.ofNat (2 ^ 255 + 173), U64.ofNat 43, hash 47,
    U64.ofNat (2 ^ 63 + 53)⟩

private def txEnv : TransactionEnvironment :=
  ⟨addr 59, addr 61, true, Bytes.ofList [0, 128, 0], U256.ofNat 67, 71, 73,
    79, 83, 89, ∅, ∅, #[], #[], some 0, some (hash 97)⟩

private def context : FrameCtx :=
  let costs := { STFSpec.Fork.Amsterdam.gasCosts with
    opcodeAddress := 11
    opcodeOrigin := 13
    opcodeCaller := 17
    opcodeCallValue := 19
    opcodeCoinbase := 23
    opcodeTimestamp := 29
    opcodePrevRandao := 31
    opcodeChainId := 37
    opcodeSlotNum := 41 }
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

private structure Expected where
  pc : Nat
  gas : Nat
  stack : List Nat
  fault : Option ExceptionalHalt

private def runCase (run : Handler Id) (ctx : FrameCtx) (gas pc : Nat)
    (words : List Nat) (expected : Expected) : Bool := Id.run do
  let some stack := stackOf words | return false
  let some desired := stackOf expected.stack | return false
  let expectedFrame := frameModel (frame expected.pc expected.gas desired)
  let result := ((run ctx (frame pc gas stack)).run world).run
  match result, expected.fault with
  | .ok (.halt after .outOfGas, retained), some .outOfGas
  | .ok (.halt after .stackOverflow, retained), some .stackOverflow
  | .ok (.continue after, retained), none =>
    return frameModel after == expectedFrame && worldModel retained == worldModel world
  | _, _ => return false

#guard runCase address context 10 17 [] ⟨17, 10, [], some .outOfGas⟩
#guard runCase address context 11 17 (List.replicate 1024 31)
  ⟨17, 0, List.replicate 1024 31, some .stackOverflow⟩
#guard runCase address context 12 (2 ^ 256 + 23) [7, 3]
  ⟨2 ^ 256 + 24, 1, [103, 7, 3], none⟩

#guard runCase origin context 12 17 [] ⟨17, 12, [], some .outOfGas⟩
#guard runCase origin context 13 17 (List.replicate 1024 31)
  ⟨17, 0, List.replicate 1024 31, some .stackOverflow⟩
#guard runCase origin context 14 (2 ^ 256 + 23) [7, 3]
  ⟨2 ^ 256 + 24, 1, [59, 7, 3], none⟩

#guard runCase caller context 16 17 [] ⟨17, 16, [], some .outOfGas⟩
#guard runCase caller context 17 17 (List.replicate 1024 31)
  ⟨17, 0, List.replicate 1024 31, some .stackOverflow⟩
#guard runCase caller context 18 (2 ^ 256 + 23) [7, 3]
  ⟨2 ^ 256 + 24, 1, [101, 7, 3], none⟩

#guard runCase callvalue context 18 17 [] ⟨17, 18, [], some .outOfGas⟩
#guard runCase callvalue context 19 17 (List.replicate 1024 31)
  ⟨17, 0, List.replicate 1024 31, some .stackOverflow⟩
#guard runCase callvalue context 20 (2 ^ 256 + 23) [7, 3]
  ⟨2 ^ 256 + 24, 1, [2 ^ 256 - 1, 7, 3], none⟩

#guard runCase coinbase context 22 17 [] ⟨17, 22, [], some .outOfGas⟩
#guard runCase coinbase context 23 17 (List.replicate 1024 31)
  ⟨17, 0, List.replicate 1024 31, some .stackOverflow⟩
#guard runCase coinbase context 24 (2 ^ 256 + 23) [7, 3]
  ⟨2 ^ 256 + 24, 1, [2 ^ 159 + 47, 7, 3], none⟩

#guard runCase timestamp context 28 17 [] ⟨17, 28, [], some .outOfGas⟩
#guard runCase timestamp context 29 17 (List.replicate 1024 31)
  ⟨17, 0, List.replicate 1024 31, some .stackOverflow⟩
#guard runCase timestamp context 30 (2 ^ 256 + 23) [7, 3]
  ⟨2 ^ 256 + 24, 1, [2 ^ 200 + 99, 7, 3], none⟩

#guard runCase prevRandao context 30 17 [] ⟨17, 30, [], some .outOfGas⟩
#guard runCase prevRandao context 31 17 (List.replicate 1024 31)
  ⟨17, 0, List.replicate 1024 31, some .stackOverflow⟩
#guard runCase prevRandao context 32 (2 ^ 256 + 23) [7, 3]
  ⟨2 ^ 256 + 24, 1, [2 ^ 255 + 173, 7, 3], none⟩

#guard runCase chainId context 36 17 [] ⟨17, 36, [], some .outOfGas⟩
#guard runCase chainId context 37 17 (List.replicate 1024 31)
  ⟨17, 0, List.replicate 1024 31, some .stackOverflow⟩
#guard runCase chainId context 38 (2 ^ 256 + 23) [7, 3]
  ⟨2 ^ 256 + 24, 1, [2 ^ 64 - 1, 7, 3], none⟩

#guard runCase slotNumber context 40 17 [] ⟨17, 40, [], some .outOfGas⟩
#guard runCase slotNumber context 41 17 (List.replicate 1024 31)
  ⟨17, 0, List.replicate 1024 31, some .stackOverflow⟩
#guard runCase slotNumber context 42 (2 ^ 256 + 23) [7, 3]
  ⟨2 ^ 256 + 24, 1, [2 ^ 63 + 53, 7, 3], none⟩

#guard runCase address context 10 17 (List.replicate 1024 31)
  ⟨17, 10, List.replicate 1024 31, some .outOfGas⟩

private def freeRandomness : FrameCtx :=
  { context with
    config := { context.config with costs := { context.config.costs with opcodePrevRandao := 0 } }
    blockEnv := { context.blockEnv with prevRandao := FixedBytes.ofNat 0 } }

#guard runCase prevRandao freeRandomness 0 17 [] ⟨18, 0, [0], none⟩

private def RunLaws {m : Type → Type} [Monad m] (handler : Handler m)
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (price : Nat) (word : U256) : Prop :=
  let run := ((handler ctx f).run w).run
  let paid := { f with gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - price } }
  (f.gasMeter.gasLeft < price → run = pure (Except.ok (.halt f .outOfGas, w))) ∧
  (price ≤ f.gasMeter.gasLeft → f.stack.size = 1024 →
    run = pure (Except.ok (.halt paid .stackOverflow, w))) ∧
  (price ≤ f.gasMeter.gasLeft → f.stack.size < 1024 →
    ∃ stack : Stack, f.stack.push word = .ok stack ∧ stack.toList = word :: f.stack.toList ∧
      run = pure (Except.ok (.continue { paid with pc := f.pc + 1, stack }, w)))

private def Accounting (f f' : Frame) (price : Nat) : Prop :=
  f'.gasMeter.phi + price = f.gasMeter.phi ∧ (1 ≤ price → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi)

private theorem address_cases {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) :
    RunLaws address ctx f w ctx.config.costs.opcodeAddress (ctx.currentTarget.toU256) :=
  ⟨address_run_oog ctx f w, address_run_overflow ctx f w, address_run_success ctx f w⟩

private theorem address_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((address ctx f).run w).run = .ok (.continue f', w')) :
    Accounting f f' ctx.config.costs.opcodeAddress :=
  ⟨address_continue_phi ctx f f' w w' run, address_continue_progress ctx f f' w w' run⟩

private theorem origin_cases {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) :
    RunLaws origin ctx f w ctx.config.costs.opcodeOrigin (ctx.txEnv.origin.toU256) :=
  ⟨origin_run_oog ctx f w, origin_run_overflow ctx f w, origin_run_success ctx f w⟩

private theorem origin_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((origin ctx f).run w).run = .ok (.continue f', w')) :
    Accounting f f' ctx.config.costs.opcodeOrigin :=
  ⟨origin_continue_phi ctx f f' w w' run, origin_continue_progress ctx f f' w w' run⟩

private theorem caller_cases {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) :
    RunLaws caller ctx f w ctx.config.costs.opcodeCaller (ctx.caller.toU256) :=
  ⟨caller_run_oog ctx f w, caller_run_overflow ctx f w, caller_run_success ctx f w⟩

private theorem caller_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((caller ctx f).run w).run = .ok (.continue f', w')) :
    Accounting f f' ctx.config.costs.opcodeCaller :=
  ⟨caller_continue_phi ctx f f' w w' run, caller_continue_progress ctx f f' w w' run⟩

private theorem callvalue_cases {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) :
    RunLaws callvalue ctx f w ctx.config.costs.opcodeCallValue (ctx.value) :=
  ⟨callvalue_run_oog ctx f w, callvalue_run_overflow ctx f w, callvalue_run_success ctx f w⟩

private theorem callvalue_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((callvalue ctx f).run w).run = .ok (.continue f', w')) :
    Accounting f f' ctx.config.costs.opcodeCallValue :=
  ⟨callvalue_continue_phi ctx f f' w w' run, callvalue_continue_progress ctx f f' w w' run⟩

private theorem coinbase_cases {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) :
    RunLaws coinbase ctx f w ctx.config.costs.opcodeCoinbase (ctx.blockEnv.coinbase.toU256) :=
  ⟨coinbase_run_oog ctx f w, coinbase_run_overflow ctx f w, coinbase_run_success ctx f w⟩

private theorem coinbase_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((coinbase ctx f).run w).run = .ok (.continue f', w')) :
    Accounting f f' ctx.config.costs.opcodeCoinbase :=
  ⟨coinbase_continue_phi ctx f f' w w' run, coinbase_continue_progress ctx f f' w w' run⟩

private theorem timestamp_cases {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) :
    RunLaws timestamp ctx f w ctx.config.costs.opcodeTimestamp (ctx.blockEnv.time) :=
  ⟨timestamp_run_oog ctx f w, timestamp_run_overflow ctx f w, timestamp_run_success ctx f w⟩

private theorem timestamp_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((timestamp ctx f).run w).run = .ok (.continue f', w')) :
    Accounting f f' ctx.config.costs.opcodeTimestamp :=
  ⟨timestamp_continue_phi ctx f f' w w' run, timestamp_continue_progress ctx f f' w w' run⟩

private theorem prevRandao_cases {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) :
    RunLaws prevRandao ctx f w ctx.config.costs.opcodePrevRandao (U256.ofBeBytes32 ctx.blockEnv.prevRandao) :=
  ⟨prevRandao_run_oog ctx f w, prevRandao_run_overflow ctx f w, prevRandao_run_success ctx f w⟩

private theorem prevRandao_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((prevRandao ctx f).run w).run = .ok (.continue f', w')) :
    Accounting f f' ctx.config.costs.opcodePrevRandao :=
  ⟨prevRandao_continue_phi ctx f f' w w' run, prevRandao_continue_progress ctx f f' w w' run⟩

private theorem chainId_cases {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) :
    RunLaws chainId ctx f w ctx.config.costs.opcodeChainId (U256.ofNat ctx.blockEnv.chainId.toNat) :=
  ⟨chainId_run_oog ctx f w, chainId_run_overflow ctx f w, chainId_run_success ctx f w⟩

private theorem chainId_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((chainId ctx f).run w).run = .ok (.continue f', w')) :
    Accounting f f' ctx.config.costs.opcodeChainId :=
  ⟨chainId_continue_phi ctx f f' w w' run, chainId_continue_progress ctx f f' w w' run⟩

private theorem slotNumber_cases {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) :
    RunLaws slotNumber ctx f w ctx.config.costs.opcodeSlotNum (U256.ofNat ctx.blockEnv.slotNumber.toNat) :=
  ⟨slotNumber_run_oog ctx f w, slotNumber_run_overflow ctx f w, slotNumber_run_success ctx f w⟩

private theorem slotNumber_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((slotNumber ctx f).run w).run = .ok (.continue f', w')) :
    Accounting f f' ctx.config.costs.opcodeSlotNum :=
  ⟨slotNumber_continue_phi ctx f f' w w' run, slotNumber_continue_progress ctx f f' w w' run⟩

end STFSpec.Conformance.Vm.Instructions.ContextWordControls
