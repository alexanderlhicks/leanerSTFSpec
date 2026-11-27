/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions
import STFSpec.Fork.Amsterdam

/-!
# Fixed SWAP controls

Library `EthConformance`. Check the complete frame and the public run laws
through the Instructions facade. See `STFSpec/informal/modules/EthVmInstructions.md` §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.SwapControls
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
  let costs := { STFSpec.Fork.Amsterdam.gasCosts with opcodeSwap := price, opcodeSwapn := 29 }
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

private def check (n : Fin 16) (price budget pc : Nat) (words expected : List Nat)
    (failure : Option ExceptionalHalt) : Bool := Id.run do
  let some stack := stackOf words | return false
  let some resultStack := stackOf expected | return false
  let start := frame pc budget stack
  let endPc := if failure.isNone then pc + 1 else pc
  let paid := if budget < price then budget else budget - price
  let expectedFrame := frameModel (frame endPc paid resultStack)
  match ((swapN n (context price) start).run world).run, failure with
  | .ok (.halt after .outOfGas, retained), some .outOfGas
  | .ok (.halt after .stackUnderflow, retained), some .stackUnderflow
  | .ok (.continue after, retained), none =>
    return frameModel after == expectedFrame && worldModel retained == worldModel world
  | _, _ => return false

private def allIndices (n : Fin 16) : Bool :=
  let depth := n.val + 1
  let raw := List.range (depth + 1)
  check n 3 2 13 [] [] (some .outOfGas) &&
    check n 3 3 13 (List.range depth) (List.range depth) (some .stackUnderflow) &&
    check n 3 3 13 raw (depth :: (List.range depth).drop 1 ++ [0]) none

#guard (List.finRange 16).all allIndices
#guard check 15 13 17 (2^274 + 53) (List.range 1024) ((List.range 1024).set 0 16 |>.set 16 0) none
#guard check 0 0 0 (2^256) [2^256 - 1, 0] [0, 2^256 - 1] none
#guard check 15 (2^277 + 59) (2^277 + 58) 11 [] [] (some .outOfGas)
#guard check 0 (2^277 + 59) (2^277 + 59) 17 [7, 9, 11] [9, 7, 11] none

private theorem checkUnderflowLaw {m : Type → Type} [Monad m] (n : Fin 16)
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeSwap ≤ f.gasMeter.gasLeft) (short : f.stack.size ≤ n.val + 1) :
    ((swapN n ctx f).run w).run =
      pure (Except.ok (.halt { f with gasMeter :=
        { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSwap } }
        .stackUnderflow, w)) :=
  swapN_run_underflow n ctx f w enough short

private theorem checkSuccessLaw {m : Type → Type} [Monad m] (n : Fin 16)
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeSwap ≤ f.gasMeter.gasLeft) (fits : n.val + 1 < f.stack.size) :
    ∃ stack : Stack, stack.size = f.stack.size ∧
      ((swapN n ctx f).run w).run =
        pure (Except.ok (.continue { f with
          gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSwap }
          pc := f.pc + 1, stack }, w)) := by
  obtain ⟨stack, _, _, _, _, _, _, size, ran⟩ := swapN_run_success n ctx f w enough fits
  exact ⟨stack, size, ran⟩

private theorem checkDeniedLaw {m : Type → Type} [Monad m] (n : Fin 16)
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeSwap) :
    ((swapN n ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w)) :=
  swapN_run_oog n ctx f w short

private theorem checkAccountingLaw (n : Fin 16) (ctx : FrameCtx) (f next : Frame) (w w' : VmWorld Id)
    (ran : ((swapN n ctx f).run w).run = .ok (.continue next, w')) :
    next.gasMeter.phi + ctx.config.costs.opcodeSwap = f.gasMeter.phi :=
  swapN_continue_phi n ctx f next w w' ran

private theorem checkProgressLaw (n : Fin 16) (ctx : FrameCtx) (f next : Frame) (w w' : VmWorld Id)
    (ran : ((swapN n ctx f).run w).run = .ok (.continue next, w'))
    (positive : 1 ≤ ctx.config.costs.opcodeSwap) :
    next.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  swapN_continue_progress n ctx f next w w' ran positive

end STFSpec.Conformance.Vm.Instructions.SwapControls
