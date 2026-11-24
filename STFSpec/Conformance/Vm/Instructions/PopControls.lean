/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions
import STFSpec.Fork.Amsterdam

/-!
# POP controls

Library `EthConformance`. The guards observe the complete frame, the result tag and sampled world values.
The ordinary clients check the public local laws. See
`STFSpec/informal/modules/EthVmInstructions.md` §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.PopControls
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
  let costs := { STFSpec.Fork.Amsterdam.gasCosts with
    base := 29
    veryLow := 19
    low := 23
    opcodePop := price }
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

private def runCase (price gas pc : Nat) (input expected : List Nat)
    (expectedHalt : Option ExceptionalHalt) : Bool := Id.run do
  let some inputStack := stackOf input | return false
  let some expectedStack := stackOf expected | return false
  let incoming := frame pc gas inputStack
  let desired := match expectedHalt with
    | some _ => frame pc gas expectedStack
    | none => frame (pc + 1) (gas - price) expectedStack
  let result := ((pop (context price) incoming).run world).run
  match result, expectedHalt with
  | .ok (.halt after .stackUnderflow, retained), some .stackUnderflow
  | .ok (.halt after .outOfGas, retained), some .outOfGas
  | .ok (.continue after, retained), none =>
    return frameModel after == frameModel desired && worldModel retained == worldModel world
  | _, _ => return false

#guard runCase 7 0 11 [] [] (some .stackUnderflow)
#guard runCase 7 7 11 [] [] (some .stackUnderflow)
#guard runCase 7 6 11 [31, 17] [17] (some .outOfGas)
#guard runCase 7 7 (2 ^ 64 - 1) [31] [] none
#guard runCase 7 10 (2 ^ 256 - 1) [31, 17] [17] none
#guard runCase 0 0 (2 ^ 290 + 11) [2 ^ 256 - 1] [] none
#guard runCase (2 ^ 300 + 3) (2 ^ 300 + 3) (2 ^ 290 + 11)
  (31 :: List.replicate 1023 17) (List.replicate 1023 17) none
#guard runCase (2 ^ 300 + 3) (2 ^ 300 + 2) (2 ^ 290 + 11)
  (31 :: List.replicate 1023 17) (List.replicate 1023 17) (some .outOfGas)

private def signature {m : Type → Type} [Monad m] : Handler m := pop

private theorem empty_precedence {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (empty : f.stack.toList = []) :
    ((pop ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) :=
  pop_run_empty ctx f w empty

private theorem denied_stack {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256) (xs : List U256)
    (entry : f.stack.toList = x :: xs) (short : f.gasMeter.gasLeft < ctx.config.costs.opcodePop) :
    ∃ stack : Stack, f.stack.pop = .ok (x, stack) ∧ stack.size = xs.length ∧
      ((pop ctx f).run w).run = pure (Except.ok (.halt { f with stack } .outOfGas, w)) := by
  obtain ⟨stack, popped, model, run⟩ := pop_run_oog ctx f w x xs entry short
  exact ⟨stack, popped, by rw [Stack.size_eq_length_toList, model], run⟩

private theorem paid_stack {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256) (xs : List U256)
    (entry : f.stack.toList = x :: xs) (enough : ctx.config.costs.opcodePop ≤ f.gasMeter.gasLeft) :
    ∃ stack : Stack, f.stack.pop = .ok (x, stack) ∧ stack.size = xs.length ∧
      ((pop ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack
          gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodePop } }, w)) := by
  obtain ⟨stack, popped, model, run⟩ := pop_run_success ctx f w x xs entry enough
  exact ⟨stack, popped, by rw [Stack.size_eq_length_toList, model], run⟩

private theorem price_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (continued : ((pop ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodePop = f.gasMeter.phi ∧
      (1 ≤ ctx.config.costs.opcodePop → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨pop_continue_phi ctx f f' w w' continued, pop_continue_progress ctx f f' w w' continued⟩

end STFSpec.Conformance.Vm.Instructions.PopControls
