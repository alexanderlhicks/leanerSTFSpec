/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions
import STFSpec.Fork.Amsterdam

/-!
# PUSH controls

Library `EthConformance`. The guards observe the complete frame, the result tag and sampled world values.
The ordinary clients check the public local laws. See
`STFSpec/informal/modules/EthVmInstructions.md` §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.PushControls
open STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private def addr (n : Nat) := Address.ofNat n
private def hash (n : Nat) := Hash32.ofBytes32 (FixedBytes.ofNat n)

private def blockEnv : BlockEnvironment :=
  ⟨U64.ofNat 11, 13, #[hash 17, hash 19], addr 23, 29, 31,
    U256.ofNat 37, FixedBytes.ofNat 41, U64.ofNat 43, hash 47, U64.ofNat 53⟩

private def txEnv : TransactionEnvironment :=
  ⟨addr 59, addr 61, true, Bytes.ofList [0, 128, 0], U256.ofNat 67, 71, 73,
    79, 83, 89, ∅, ∅, #[], #[], some 0, some (hash 97)⟩

private def context (zeroPrice pushPrice : Nat) (code : Bytes) : FrameCtx :=
  let costs := { STFSpec.Fork.Amsterdam.gasCosts with
    base := 29
    veryLow := 19
    low := 23
    opcodePush0 := zeroPrice
    opcodePush := pushPrice }
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

private def runCase (n : Fin 33) (zeroPrice pushPrice gas pc : Nat) (code : List UInt8)
    (input expected : List Nat) (expectedHalt : Option ExceptionalHalt) : Bool := Id.run do
  let some inputStack := stackOf input | return false
  let some expectedStack := stackOf expected | return false
  let incoming := frame pc gas inputStack
  let price := if n.val = 0 then zeroPrice else pushPrice
  let desired := match expectedHalt with
    | some .outOfGas => incoming
    | some _ => frame pc (gas - price) inputStack
    | none => frame (pc + 1 + n.val) (gas - price) expectedStack
  let result := ((pushN n (context zeroPrice pushPrice (Bytes.ofList code)) incoming).run world).run
  match result, expectedHalt with
  | .ok (.halt after .stackOverflow, retained), some .stackOverflow
  | .ok (.halt after .outOfGas, retained), some .outOfGas
  | .ok (.continue after, retained), none =>
    return frameModel after == frameModel desired && worldModel retained == worldModel world
  | _, _ => return false

#guard runCase 0 7 19 7 (2 ^ 256) [0x5f, 0xab] [31] [0, 31] none
#guard runCase 0 7 19 6 0 [0x5f, 0xab] [31] [31] (some .outOfGas)
#guard runCase 1 19 7 7 0 [0x60, 0xab] [31] [0xab, 31] none
#guard runCase 1 19 7 7 (2 ^ 256) [0x60, 0xab] [31] [0, 31] none
#guard runCase 2 19 7 10 0 [0x61, 0xab] [] [0xab00] none
#guard runCase 32 19 7 7 0 (0x7f :: List.replicate 32 0xff) [] [2 ^ 256 - 1] none
#guard runCase 32 19 7 7 (2 ^ 256 - 2) [0x7f, 0xab] [] [0] none
#guard runCase 1 19 (2 ^ 300 + 3) (2 ^ 300 + 2) (2 ^ 256) [0x60, 0xab]
  (List.replicate 1024 31) (List.replicate 1024 31) (some .outOfGas)
#guard runCase 1 19 (2 ^ 300 + 3) (2 ^ 300 + 3) (2 ^ 256) [0x60, 0xab]
  (List.replicate 1024 31) (List.replicate 1024 31) (some .stackOverflow)
#guard runCase 1 19 0 0 0 [0x60, 0xab] [31] [0xab, 31] none

private def signature (n : Fin 33) {m : Type → Type} [Monad m] : Handler m := pushN n

private theorem denial {m : Type → Type} [Monad m]
    (n : Fin 33) (ctx : FrameCtx) (f : Frame) (w : VmWorld m) :
    let price := if n.val = 0 then ctx.config.costs.opcodePush0 else ctx.config.costs.opcodePush
    f.gasMeter.gasLeft < price →
      ((pushN n ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w)) :=
  pushN_run_oog n ctx f w

private theorem overflow {m : Type → Type} [Monad m]
    (n : Fin 33) (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (full : f.stack.size = 1024) :
    let price := if n.val = 0 then ctx.config.costs.opcodePush0 else ctx.config.costs.opcodePush
    price ≤ f.gasMeter.gasLeft →
      ((pushN n ctx f).run w).run = pure (Except.ok
        (.halt { f with gasMeter := { f.gasMeter with
          gasLeft := f.gasMeter.gasLeft - price } } .stackOverflow, w)) :=
  pushN_run_overflow n ctx f w full

private theorem pushed_stack_size {m : Type → Type} [Monad m]
    (n : Fin 33) (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (space : f.stack.size < 1024) :
    let price := if n.val = 0 then ctx.config.costs.opcodePush0 else ctx.config.costs.opcodePush
    let word := U256.ofNat (Uint.ofBeBytes (ctx.code.extractPadded (f.pc + 1) n.val))
    price ≤ f.gasMeter.gasLeft →
      ∃ stack : Stack, f.stack.push word = .ok stack ∧ stack.size = f.stack.size + 1 ∧
        ((pushN n ctx f).run w).run = pure (Except.ok
          (.continue { f with
            pc := f.pc + 1 + n.val
            stack
            gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - price } }, w)) := by
  dsimp only
  intro enough
  obtain ⟨stack, pushed, model, run⟩ := pushN_run_success n ctx f w space enough
  exact ⟨stack, pushed, by rw [Stack.size_eq_length_toList, model, List.length_cons,
    ← Stack.size_eq_length_toList], run⟩

private theorem price_accounting (n : Fin 33) (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((pushN n ctx f).run w).run = .ok (.continue f', w')) :
    let price := if n.val = 0 then ctx.config.costs.opcodePush0 else ctx.config.costs.opcodePush
    f'.gasMeter.phi + price = f.gasMeter.phi ∧
      (1 ≤ price → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨pushN_continue_phi n ctx f f' w w' run, pushN_continue_progress n ctx f f' w w' run⟩

end STFSpec.Conformance.Vm.Instructions.PushControls
