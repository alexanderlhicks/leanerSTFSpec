/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions
import STFSpec.Fork.Amsterdam

/-!
# JUMP and JUMPI controls

Library `EthConformance`. The guards observe the complete frame, the result tag and sampled world values.
The ordinary clients check the public local laws. See
`STFSpec/informal/modules/EthVmInstructions.md` §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.JumpControls
open STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private def addr (n : Nat) := Address.ofNat n
private def hash (n : Nat) := Hash32.ofBytes32 (FixedBytes.ofNat n)

private def blockEnv : BlockEnvironment :=
  ⟨U64.ofNat 11, 13, #[hash 17, hash 19], addr 23, 29, 31,
    U256.ofNat 37, FixedBytes.ofNat 41, U64.ofNat 43, hash 47, U64.ofNat 53⟩

private def txEnv : TransactionEnvironment :=
  ⟨addr 59, addr 61, true, Bytes.ofList [0, 128, 0], U256.ofNat 67, 71, 73,
    79, 83, 89, ∅, ∅, #[], #[], some 0, some (hash 97)⟩

private def context (jumpPrice jumpiPrice : Nat) : FrameCtx :=
  let costs := { STFSpec.Fork.Amsterdam.gasCosts with
    base := 29
    veryLow := 19
    low := 23
    opcodeJump := jumpPrice
    opcodeJumpi := jumpiPrice }
  ⟨⟨costs, ⟨0, 7, 2 ^ 300 + 11, 13⟩, ⟨7, 0, 2 ^ 301 + 17⟩⟩,
    blockEnv, txEnv, addr 101, addr 103, U256.max, Bytes.ofList [255, 0, 128],
    some (addr 0), Bytes.ofList [96, 91, 255],
    validJumpDestinations (Bytes.ofList [0x57, 0x60, 0x5b, 0, 0x5b, 0, 0x5b]),
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

private def runCase (run : Handler Id) (jumpPrice jumpiPrice gas pc : Nat)
    (words : List Nat) (expected : Expected) : Bool := Id.run do
  let some stack := stackOf words | return false
  let some residual := stackOf expected.stack | return false
  let want := frameModel (frame expected.pc expected.gas residual)
  let result := ((run (context jumpPrice jumpiPrice) (frame pc gas stack)).run world).run
  match result, expected.fault with
  | .ok (.halt after .stackUnderflow, retained), some .stackUnderflow
  | .ok (.halt after .outOfGas, retained), some .outOfGas
  | .ok (.halt after .invalidJumpDest, retained), some .invalidJumpDest
  | .ok (.continue after, retained), none =>
    return frameModel after == want && worldModel retained == worldModel world
  | _, _ => return false

#guard runCase jump 7 11 0 17 [] ⟨17, 0, [], some .stackUnderflow⟩
#guard runCase jump 7 11 6 17 [2, 31] ⟨17, 6, [31], some .outOfGas⟩
#guard runCase jump 7 11 7 17 [2, 31] ⟨17, 0, [31], some .invalidJumpDest⟩
#guard runCase jump 7 11 9 17 [4, 31] ⟨4, 2, [31], none⟩
#guard runCase jump 0 11 0 (2 ^ 256) [2 ^ 256 - 1] ⟨2 ^ 256, 0, [], some .invalidJumpDest⟩
#guard runCase jump (2 ^ 300 + 3) 11 (2 ^ 300 + 3) 17 [6] ⟨6, 0, [], none⟩
#guard runCase jumpi 7 11 0 17 [] ⟨17, 0, [], some .stackUnderflow⟩
#guard runCase jumpi 7 11 0 17 [4] ⟨17, 0, [], some .stackUnderflow⟩
#guard runCase jumpi 7 11 10 17 [2, 0, 31] ⟨17, 10, [31], some .outOfGas⟩
#guard runCase jumpi 7 11 11 (2 ^ 256) [2, 0, 31] ⟨2 ^ 256 + 1, 0, [31], none⟩
#guard runCase jumpi 7 11 12 17 [2, 1, 31] ⟨17, 1, [31], some .invalidJumpDest⟩
#guard runCase jumpi 7 11 13 17 [4, 2 ^ 256 - 1, 31] ⟨4, 2, [31], none⟩
#guard runCase jumpi 7 (2 ^ 300 + 3) (2 ^ 300 + 4) 17
  (6 :: 1 :: List.replicate 1022 31) ⟨6, 1, List.replicate 1022 31, none⟩

private def signatures {m : Type → Type} [Monad m] : Handler m × Handler m := (jump, jumpi)

private theorem empty_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (empty : f.stack.toList = []) :
    ((jump ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) ∧
      ((jumpi ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) :=
  ⟨jump_run_empty ctx f w empty, jumpi_run_empty ctx f w empty⟩

private theorem missing_condition {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (d : U256) (first : Stack)
    (popped : f.stack.pop = .ok (d, first)) (empty : first.toList = []) :
    ((jumpi ctx f).run w).run =
      pure (Except.ok (.halt { f with stack := first } .stackUnderflow, w)) :=
  jumpi_run_missing_condition ctx f w d first popped empty

private theorem denial {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (d c : U256) (first residual : Stack)
    (popped : f.stack.pop = .ok (d, first)) (tested : first.pop = .ok (c, residual))
    (jumpShort : f.gasMeter.gasLeft < ctx.config.costs.opcodeJump)
    (jumpiShort : f.gasMeter.gasLeft < ctx.config.costs.opcodeJumpi) :
    ((jump ctx f).run w).run = pure (Except.ok (.halt { f with stack := first } .outOfGas, w)) ∧
      ((jumpi ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := residual } .outOfGas, w)) :=
  ⟨jump_run_oog ctx f w d first popped jumpShort,
    jumpi_run_oog ctx f w d c first residual popped tested jumpiShort⟩

private theorem unconditional_taken {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (d : U256) (residual : Stack)
    (popped : f.stack.pop = .ok (d, residual))
    (enough : ctx.config.costs.opcodeJump ≤ f.gasMeter.gasLeft)
    (valid : ctx.jumpdests.contains d.toNat = true) :
    ((jump ctx f).run w).run = pure (Except.ok (.continue { f with
      stack := residual
      pc := d.toNat
      gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeJump } }, w)) := by
  rw [jump_run_paid ctx f w d residual popped enough]
  simp [valid]

private theorem conditional_fallthrough {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (d c : U256) (first residual : Stack)
    (popped : f.stack.pop = .ok (d, first)) (tested : first.pop = .ok (c, residual))
    (enough : ctx.config.costs.opcodeJumpi ≤ f.gasMeter.gasLeft) (zero : c.toNat = 0) :
    ((jumpi ctx f).run w).run = pure (Except.ok (.continue { f with
      stack := residual
      pc := f.pc + 1
      gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeJumpi } }, w)) :=
  jumpi_run_paid_zero ctx f w d c first residual popped tested enough zero

private theorem conditional_invalid {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (d c : U256) (first residual : Stack)
    (popped : f.stack.pop = .ok (d, first)) (tested : first.pop = .ok (c, residual))
    (enough : ctx.config.costs.opcodeJumpi ≤ f.gasMeter.gasLeft) (nonzero : c.toNat ≠ 0)
    (invalid : ctx.jumpdests.contains d.toNat = false) :
    ((jumpi ctx f).run w).run = pure (Except.ok (.halt { f with
      stack := residual
      gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeJumpi } }
      .invalidJumpDest, w)) := by
  rw [jumpi_run_paid_nonzero ctx f w d c first residual popped tested enough nonzero]
  simp [invalid]

private theorem jump_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((jump ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeJump = f.gasMeter.phi ∧
      (1 ≤ ctx.config.costs.opcodeJump → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨jump_continue_phi ctx f f' w w' run, jump_continue_progress ctx f f' w w' run⟩

private theorem jumpi_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((jumpi ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeJumpi = f.gasMeter.phi ∧
      (1 ≤ ctx.config.costs.opcodeJumpi → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨jumpi_continue_phi ctx f f' w w' run, jumpi_continue_progress ctx f f' w w' run⟩

end STFSpec.Conformance.Vm.Instructions.JumpControls
