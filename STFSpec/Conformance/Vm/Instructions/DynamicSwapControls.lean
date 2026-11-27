/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions
import STFSpec.Fork.Amsterdam

/-!
# SWAPN and EXCHANGE controls

Library `EthConformance`. The guards observe the complete frame, result tag and sampled world values.
The ordinary clients check the public local laws. See
`STFSpec/informal/modules/EthVmInstructions.md` §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.DynamicSwapControls
open STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private def addr (n : Nat) := Address.ofNat n
private def hash (n : Nat) := Hash32.ofBytes32 (FixedBytes.ofNat n)

private def blockEnv : BlockEnvironment :=
  ⟨U64.ofNat 11, 13, #[hash 17, hash 19], addr 23, 29, 31,
    U256.ofNat 37, FixedBytes.ofNat 41, U64.ofNat 43, hash 47, U64.ofNat 53⟩

private def txEnv : TransactionEnvironment :=
  ⟨addr 59, addr 61, true, Bytes.ofList [0, 128, 0], U256.ofNat 67, 71, 73,
    79, 83, 89, ∅, ∅, #[], #[], some 0, some (hash 97)⟩

private def context (swapnPrice exchangePrice : Nat) (code : Bytes) : FrameCtx :=
  let costs := { STFSpec.Fork.Amsterdam.gasCosts with
    base := 29
    veryLow := 19
    low := 23
    opcodeSwapn := swapnPrice
    opcodeExchange := exchangePrice }
  ⟨⟨costs, ⟨0, 7, 2 ^ 300 + 11, 13⟩, ⟨7, 0, 2 ^ 301 + 17⟩⟩,
    blockEnv, txEnv, addr 101, addr 103, U256.max, Bytes.ofList [255, 0, 128],
    some (addr 0), code,
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

private def runCase (run : Handler Id) (swapnPrice exchangePrice gas pc : Nat)
    (code : List UInt8) (words : List Nat) (expected : Expected) : Bool := Id.run do
  let some stack := stackOf words | return false
  let some desired := stackOf expected.stack | return false
  let expectedFrame := frameModel (frame expected.pc expected.gas desired)
  let result := ((run (context swapnPrice exchangePrice (Bytes.ofList code))
    (frame pc gas stack)).run world).run
  match result, expected.fault with
  | .ok (.halt after .outOfGas, retained), some .outOfGas
  | .ok (.halt after .invalidParameter, retained), some .invalidParameter
  | .ok (.halt after .stackUnderflow, retained), some .stackUnderflow
  | .ok (.continue after, retained), none =>
    return frameModel after == expectedFrame && worldModel retained == worldModel world
  | _, _ => return false

#guard runCase swapn 7 19 6 0 [0xe7, 91] [] ⟨0, 6, [], some .outOfGas⟩
#guard runCase swapn 7 19 7 0 [0xe7, 91] [] ⟨0, 0, [], some .invalidParameter⟩
#guard runCase swapn 7 19 7 0 [0xe7, 127] (List.range 1024)
  ⟨0, 0, List.range 1024, some .invalidParameter⟩
#guard runCase swapn 7 19 7 0 [0xe7, 128] (List.range 17)
  ⟨0, 0, List.range 17, some .stackUnderflow⟩
#guard runCase swapn 7 19 7 1 [91, 0xe7, 128] (List.range 18)
  ⟨3, 0, (17 :: (List.range 16).map (· + 1)) ++ [0], none⟩
#guard runCase swapn 7 99 8 0 [0xe7, 90] (List.range 1024)
  ⟨2, 1, ((List.range 1024).set 0 235).set 235 0, none⟩
#guard runCase swapn 0 19 0 0 [0xe7, 128] (List.range 18)
  ⟨2, 0, ((List.range 18).set 0 17).set 17 0, none⟩
#guard runCase swapn 7 19 7 0 [0xe7] (List.range 146)
  ⟨2, 0, ((List.range 146).set 0 145).set 145 0, none⟩
#guard runCase swapn (2 ^ 300 + 3) 19 (2 ^ 300 + 2) (2 ^ 256) [91] []
  ⟨2 ^ 256, 2 ^ 300 + 2, [], some .outOfGas⟩
#guard runCase swapn (2 ^ 300 + 3) 19 (2 ^ 300 + 3) (2 ^ 256 - 1) [91] (List.range 146)
  ⟨2 ^ 256 + 1, 0, ((List.range 146).set 0 145).set 145 0, none⟩

#guard runCase exchange 7 19 18 0 [0xe8, 82] [] ⟨0, 18, [], some .outOfGas⟩
#guard runCase exchange 7 19 19 0 [0xe8, 82] [] ⟨0, 0, [], some .invalidParameter⟩
#guard runCase exchange 7 19 19 0 [0xe8, 127] (List.range 1024)
  ⟨0, 0, List.range 1024, some .invalidParameter⟩
#guard runCase exchange 7 19 19 0 [0xe8, 128] (List.range 16)
  ⟨0, 0, List.range 16, some .stackUnderflow⟩
#guard runCase exchange 7 19 19 1 [82, 0xe8, 128] (List.range 17)
  ⟨3, 0, ((List.range 17).set 1 16).set 16 1, none⟩
#guard runCase exchange 99 19 20 0 [0xe8, 81] (List.range 1024)
  ⟨2, 1, ((List.range 1024).set 14 15).set 15 14, none⟩
#guard runCase exchange 7 0 0 0 [0xe8, 128] (List.range 17)
  ⟨2, 0, ((List.range 17).set 1 16).set 16 1, none⟩
#guard runCase exchange 7 19 19 0 [0xe8] (List.range 17)
  ⟨2, 0, ((List.range 17).set 9 16).set 16 9, none⟩
#guard runCase exchange 7 (2 ^ 300 + 3) (2 ^ 300 + 2) (2 ^ 256) [82] []
  ⟨2 ^ 256, 2 ^ 300 + 2, [], some .outOfGas⟩
#guard runCase exchange 7 (2 ^ 300 + 3) (2 ^ 300 + 3) (2 ^ 256 - 1) [82] (List.range 17)
  ⟨2 ^ 256 + 1, 0, ((List.range 17).set 9 16).set 16 9, none⟩

private def handlerTypes {m : Type → Type} [Monad m] : Handler m × Handler m :=
  (swapn, exchange)

private def debit (f : Frame) (price : Nat) : Frame :=
  { f with gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - price } }

private theorem swapn_failures {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (depth : Nat) :
    let price := ctx.config.costs.opcodeSwapn
    let run := ((swapn ctx f).run w).run
    let decoded := decodeSingle ((ctx.code[f.pc + 1]?).getD 0)
    (f.gasMeter.gasLeft < price → run = pure (Except.ok (.halt f .outOfGas, w))) ∧
    (price ≤ f.gasMeter.gasLeft → decoded = .error .invalidParameter →
      run = pure (Except.ok (.halt (debit f price) .invalidParameter, w))) ∧
    (price ≤ f.gasMeter.gasLeft → decoded = .ok depth → f.stack.size ≤ depth →
      run = pure (Except.ok (.halt (debit f price) .stackUnderflow, w))) :=
  ⟨swapn_run_oog ctx f w, swapn_run_invalid ctx f w, swapn_run_underflow ctx f w depth⟩

private theorem swapn_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (depth : Nat)
    (enough : ctx.config.costs.opcodeSwapn ≤ f.gasMeter.gasLeft)
    (decoded : decodeSingle ((ctx.code[f.pc + 1]?).getD 0) = .ok depth)
    (fits : depth < f.stack.size) :
    ∃ (stack : Stack) (a b : U256),
      f.stack.swap? 0 depth = some stack ∧
      f.stack.toList[0]? = some a ∧ f.stack.toList[depth]? = some b ∧
      stack.toList = (f.stack.toList.set 0 b).set depth a ∧
      ((swapn ctx f).run w).run = pure (Except.ok
        (.continue { debit f ctx.config.costs.opcodeSwapn with pc := f.pc + 2, stack }, w)) :=
  swapn_run_success ctx f w depth enough decoded fits

private theorem swapn_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((swapn ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeSwapn = f.gasMeter.phi ∧
      (1 ≤ ctx.config.costs.opcodeSwapn → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨swapn_continue_phi ctx f f' w w' run, swapn_continue_progress ctx f f' w w' run⟩

private theorem exchange_failures {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (i j : Nat) :
    let price := ctx.config.costs.opcodeExchange
    let run := ((exchange ctx f).run w).run
    let decoded := decodePair ((ctx.code[f.pc + 1]?).getD 0)
    (f.gasMeter.gasLeft < price → run = pure (Except.ok (.halt f .outOfGas, w))) ∧
    (price ≤ f.gasMeter.gasLeft → decoded = .error .invalidParameter →
      run = pure (Except.ok (.halt (debit f price) .invalidParameter, w))) ∧
    (price ≤ f.gasMeter.gasLeft → decoded = .ok (i, j) → f.stack.size ≤ j →
      run = pure (Except.ok (.halt (debit f price) .stackUnderflow, w))) :=
  ⟨exchange_run_oog ctx f w, exchange_run_invalid ctx f w, exchange_run_underflow ctx f w i j⟩

private theorem exchange_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (i j : Nat)
    (enough : ctx.config.costs.opcodeExchange ≤ f.gasMeter.gasLeft)
    (decoded : decodePair ((ctx.code[f.pc + 1]?).getD 0) = .ok (i, j))
    (fits : j < f.stack.size) :
    ∃ (stack : Stack) (a b : U256),
      f.stack.swap? i j = some stack ∧
      f.stack.toList[i]? = some a ∧ f.stack.toList[j]? = some b ∧
      stack.toList = (f.stack.toList.set i b).set j a ∧
      ((exchange ctx f).run w).run = pure (Except.ok
        (.continue { debit f ctx.config.costs.opcodeExchange with pc := f.pc + 2, stack }, w)) :=
  exchange_run_success ctx f w i j enough decoded fits

private theorem exchange_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((exchange ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeExchange = f.gasMeter.phi ∧
      (1 ≤ ctx.config.costs.opcodeExchange → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨exchange_continue_phi ctx f f' w w' run, exchange_continue_progress ctx f f' w w' run⟩

end STFSpec.Conformance.Vm.Instructions.DynamicSwapControls
