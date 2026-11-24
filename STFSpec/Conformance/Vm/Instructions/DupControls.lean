/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions
import STFSpec.Fork.Amsterdam

/-!
# DUP and DUPN controls

Library `EthConformance`. The guards observe the complete frame, the result tag and sampled world values.
The ordinary clients check the public local laws. See
`STFSpec/informal/modules/EthVmInstructions.md` §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.DupControls
open STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private def addr (n : Nat) := Address.ofNat n
private def hash (n : Nat) := Hash32.ofBytes32 (FixedBytes.ofNat n)

private def blockEnv : BlockEnvironment :=
  ⟨U64.ofNat 11, 13, #[hash 17, hash 19], addr 23, 29, 31,
    U256.ofNat 37, FixedBytes.ofNat 41, U64.ofNat 43, hash 47, U64.ofNat 53⟩

private def txEnv : TransactionEnvironment :=
  ⟨addr 59, addr 61, true, Bytes.ofList [0, 128, 0], U256.ofNat 67, 71, 73,
    79, 83, 89, ∅, ∅, #[], #[], some 0, some (hash 97)⟩

private def context (fixedPrice dynamicPrice : Nat) (code : Bytes) : FrameCtx :=
  let costs := { STFSpec.Fork.Amsterdam.gasCosts with
    base := 29
    veryLow := 19
    low := 23
    opcodeDup := fixedPrice
    opcodeDupn := dynamicPrice }
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

private def runCase (run : Handler Id) (fixedPrice dynamicPrice gas pc : Nat)
    (code : List UInt8) (words : List Nat) (expected : Expected) : Bool := Id.run do
  let some stack := stackOf words | return false
  let some desired := stackOf expected.stack | return false
  let expectedFrame := frameModel (frame expected.pc expected.gas desired)
  let result := ((run (context fixedPrice dynamicPrice (Bytes.ofList code))
    (frame pc gas stack)).run world).run
  match result, expected.fault with
  | .ok (.halt after .outOfGas, retained), some .outOfGas
  | .ok (.halt after .invalidParameter, retained), some .invalidParameter
  | .ok (.halt after .stackUnderflow, retained), some .stackUnderflow
  | .ok (.halt after .stackOverflow, retained), some .stackOverflow
  | .ok (.continue after, retained), none =>
    return frameModel after == expectedFrame && worldModel retained == worldModel world
  | _, _ => return false

#guard runCase (dupN 15) 7 19 6 17 [] [] ⟨17, 6, [], some .outOfGas⟩
#guard runCase (dupN 15) 7 19 7 17 [] (List.range 15)
  ⟨17, 0, List.range 15, some .stackUnderflow⟩
#guard runCase (dupN 15) 7 19 8 (2 ^ 256) [] (List.range 16)
  ⟨2 ^ 256 + 1, 1, 15 :: List.range 16, none⟩
#guard runCase (dupN 0) (2 ^ 300 + 3) 19 (2 ^ 300 + 3) 17 [] (List.replicate 1024 31)
  ⟨17, 0, List.replicate 1024 31, some .stackOverflow⟩
#guard runCase (dupN 0) 0 19 0 17 [] [31] ⟨18, 0, [31, 31], none⟩

#guard runCase dupn 7 19 18 0 [0xe6, 91] [] ⟨0, 18, [], some .outOfGas⟩
#guard runCase dupn 7 19 19 0 [0xe6, 91] [] ⟨0, 0, [], some .invalidParameter⟩
#guard runCase dupn 7 19 19 0 [0xe6, 127] (List.replicate 1024 31)
  ⟨0, 0, List.replicate 1024 31, some .invalidParameter⟩
#guard runCase dupn 7 19 19 0 [0xe6, 128] (List.range 16)
  ⟨0, 0, List.range 16, some .stackUnderflow⟩
#guard runCase dupn 77 19 20 0 [0xe6, 128] (List.range 17)
  ⟨2, 1, 16 :: List.range 17, none⟩
#guard runCase dupn 7 19 19 0 [0xe6, 128] (List.replicate 1024 31)
  ⟨0, 0, List.replicate 1024 31, some .stackOverflow⟩
#guard runCase dupn 7 (2 ^ 300 + 3) (2 ^ 300 + 2) (2 ^ 256) [0xe6] []
  ⟨2 ^ 256, 2 ^ 300 + 2, [], some .outOfGas⟩
#guard runCase dupn 7 19 19 0 [0xe6] (List.range 145)
  ⟨2, 0, 144 :: List.range 145, none⟩
#guard runCase dupn 7 19 19 (2 ^ 256) [0xe6, 91] (List.range 145)
  ⟨2 ^ 256 + 2, 0, 144 :: List.range 145, none⟩

private def handlerTypes {m : Type → Type} [Monad m] :
    (Fin 16 → Handler m) × Handler m := (fun n ↦ dupN n, dupn)

private def debit (f : Frame) (price : Nat) : Frame :=
  { f with gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - price } }

private theorem fixed_failures (n : Fin 16) {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) :
    let price := ctx.config.costs.opcodeDup
    let run := ((dupN n ctx f).run w).run
    (f.gasMeter.gasLeft < price → run = pure (Except.ok (.halt f .outOfGas, w))) ∧
    (price ≤ f.gasMeter.gasLeft → f.stack.size ≤ n.val →
      run = pure (Except.ok (.halt (debit f price) .stackUnderflow, w))) ∧
    (price ≤ f.gasMeter.gasLeft → f.stack.size = 1024 →
      run = pure (Except.ok (.halt (debit f price) .stackOverflow, w))) :=
  ⟨dupN_run_oog n ctx f w, dupN_run_underflow n ctx f w, dupN_run_overflow n ctx f w⟩

private theorem dynamic_failures {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (depth : Nat) :
    let price := ctx.config.costs.opcodeDupn
    let run := ((dupn ctx f).run w).run
    let decoded := decodeSingle ((ctx.code[f.pc + 1]?).getD 0)
    (f.gasMeter.gasLeft < price → run = pure (Except.ok (.halt f .outOfGas, w))) ∧
    (price ≤ f.gasMeter.gasLeft → decoded = .error .invalidParameter →
      run = pure (Except.ok (.halt (debit f price) .invalidParameter, w))) ∧
    (price ≤ f.gasMeter.gasLeft → decoded = .ok depth → f.stack.size < depth →
      run = pure (Except.ok (.halt (debit f price) .stackUnderflow, w))) ∧
    (price ≤ f.gasMeter.gasLeft → decoded = .ok depth → f.stack.size = 1024 →
      run = pure (Except.ok (.halt (debit f price) .stackOverflow, w))) :=
  ⟨dupn_run_oog ctx f w, dupn_run_invalid ctx f w,
    dupn_run_underflow ctx f w depth, dupn_run_overflow ctx f w depth⟩

private theorem fixed_success (n : Fin 16) {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeDup ≤ f.gasMeter.gasLeft)
    (fits : n.val < f.stack.size) (space : f.stack.size < 1024) :
    ∃ (word : U256) (stack : Stack),
      f.stack.peek? n.val = some word ∧ f.stack.push word = .ok stack ∧
      stack.toList = word :: f.stack.toList ∧
      ((dupN n ctx f).run w).run = pure (Except.ok
        (.continue { debit f ctx.config.costs.opcodeDup with pc := f.pc + 1, stack }, w)) :=
  dupN_run_success n ctx f w enough fits space

private theorem dynamic_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (depth : Nat)
    (enough : ctx.config.costs.opcodeDupn ≤ f.gasMeter.gasLeft)
    (decoded : decodeSingle ((ctx.code[f.pc + 1]?).getD 0) = .ok depth)
    (fits : depth ≤ f.stack.size) (space : f.stack.size < 1024) :
    ∃ (word : U256) (stack : Stack),
      f.stack.peek? (depth - 1) = some word ∧ f.stack.push word = .ok stack ∧
      stack.toList = word :: f.stack.toList ∧
      ((dupn ctx f).run w).run = pure (Except.ok
        (.continue { debit f ctx.config.costs.opcodeDupn with pc := f.pc + 2, stack }, w)) :=
  dupn_run_success ctx f w depth enough decoded fits space

private theorem fixed_accounting (n : Fin 16) (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((dupN n ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeDup = f.gasMeter.phi ∧
      (1 ≤ ctx.config.costs.opcodeDup → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨dupN_continue_phi n ctx f f' w w' run, dupN_continue_progress n ctx f f' w w' run⟩

private theorem dynamic_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((dupn ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeDupn = f.gasMeter.phi ∧
      (1 ≤ ctx.config.costs.opcodeDupn → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨dupn_continue_phi ctx f f' w w' run, dupn_continue_progress ctx f f' w w' run⟩

end STFSpec.Conformance.Vm.Instructions.DupControls
