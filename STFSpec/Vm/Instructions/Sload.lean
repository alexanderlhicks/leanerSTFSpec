/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.IntegerBytes
import STFSpec.State.CurrentStorage
import STFSpec.Vm.Core.StateLift
import STFSpec.Vm.Instructions.Handler

/-!
# SLOAD

Library `EthVmInstructions`. Observe entry slot warmth, charge, then read
the current target's storage. See `STFSpec/informal/modules/EthVmInstructions.md` §§2/5/7.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base STFSpec.State STFSpec.Vm.Core

private theorem room_after_pop (stack tail : Stack) (word : U256)
    (popped : stack.pop = .ok (word, tail)) : tail.size < 1024 := by
  have bound := stack.size_le
  rw [Stack.size_eq_length_toList, (Stack.pop_eq_ok_iff stack tail word).mp popped,
    List.length_cons] at bound
  rw [Stack.size_eq_length_toList]
  omega

private def popFrameReference (f : Frame) : Except (Frame × ExceptionalHalt) (U256 × Frame) :=
  match f.stack.pop with
  | .error error => .error (f, error)
  | .ok (word, tail) => .ok (word, { f with stack := tail })

private theorem pop_error_on_nonempty (f : Frame) (error : ExceptionalHalt)
    (nonempty : 0 < f.stack.size) (failed : f.stack.pop = .error error) : False := by
  have empty := ((Stack.pop_eq_error_iff f.stack error).mp failed).1
  simp [Stack.size_eq_length_toList, empty] at nonempty

private def popFrame (f : Frame) : Except (Frame × ExceptionalHalt) (U256 × Frame) :=
  if nonempty : 0 < f.stack.size then
    match popped : f.stack.pop with
    | .error error => False.elim (pop_error_on_nonempty f error nonempty popped)
    | .ok (word, tail) => .ok (word, { f with stack := tail })
  else
    popFrameReference f

private theorem popFrame_eq (f : Frame) : popFrame f = popFrameReference f := by
  unfold popFrame
  split
  · rename_i nonempty
    unfold popFrameReference
    split
    · rename_i error failed
      exact False.elim (pop_error_on_nonempty f error nonempty failed)
    · rename_i word tail popped
      rw [popped]
  · rfl

private theorem poppedFrame_room (f residual : Frame) (word : U256)
    (popped : popFrame f = .ok (word, residual)) : residual.stack.size < 1024 := by
  rw [popFrame_eq] at popped
  cases observed : f.stack.pop with
  | error error => simp [popFrameReference, observed] at popped
  | ok result =>
    rcases result with ⟨value, tail⟩
    have same : (value, { f with stack := tail }) = (word, residual) := by
      apply Except.ok.inj
      simpa only [popFrameReference, observed] using popped
    rw [← (Prod.mk.inj same).2]
    exact room_after_pop f.stack tail value observed

private theorem push_error_with_room (tail : Stack) (word : U256) (room : tail.size < 1024)
    (error : ExceptionalHalt) (failed : tail.push word = .error error) : False :=
  (Nat.ne_of_lt room) ((Stack.push_eq_error_iff tail word error).mp failed).1

private def pushLoaded (tail : Stack) (word : U256) (room : tail.size < 1024) : Stack :=
  match pushed : tail.push word with
  | .ok stack => stack
  | .error error => False.elim (push_error_with_room tail word room error pushed)

private theorem pushLoaded_actual (tail : Stack) (word : U256) (room : tail.size < 1024) :
    tail.push word = .ok (pushLoaded tail word room) := by
  unfold pushLoaded
  split
  · rename_i stack pushed
    exact pushed
  · rename_i error failed
    exact False.elim (push_error_with_room tail word room error failed)

private def paidResult (ctx : FrameCtx) (f : Frame) (room : f.stack.size < 1024)
    (slots : SlotSet) (meter : GasMeter) (value : U256) : StepResult ctx :=
  match f with
  | ⟨pc, stack, memory, _, logs, deleted, returnData, addresses, _⟩ =>
    .continue ⟨pc + 1, pushLoaded stack value room, memory, meter, logs, deleted,
      returnData, addresses, slots⟩

private theorem paidResult_eq (ctx : FrameCtx) (f : Frame) (room : f.stack.size < 1024)
    (slots : SlotSet) (meter : GasMeter) (value : U256) :
    paidResult ctx f room slots meter value =
      .continue { f with
        pc := f.pc + 1
        stack := pushLoaded f.stack value room
        gasMeter := meter
        accessedStorageKeys := slots } := by
  cases f
  rfl

private def warmAndPrice (cfg : VmConfig) (warm : SlotSet) (slot : Address × Bytes32) :
    SlotSet × Nat :=
  if slot ∈ warm then (warm, cfg.costs.warmAccess)
  else (warm.insert slot, cfg.costs.coldStorageAccess)

private def loadAfterPop {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame)
    (word : U256) (room : f.stack.size < 1024) : VmM m (StepResult ctx) :=
  let key := word.toBeBytes32
  let (slots, price) := warmAndPrice ctx.config f.accessedStorageKeys (ctx.currentTarget, key)
  match chargeGas f.gasMeter price with
  | .error error => pure (.halt { f with accessedStorageKeys := slots } error)
  | .ok meter => do
    let value ← liftState (getStorage ctx.currentTarget key)
    pure (paidResult ctx f room slots meter value)

/-- Pop the slot word, charge for its original warmth, then read current storage.
EELS `src/ethereum/forks/amsterdam/vm/instructions/storage.py:37–65` at the pin. -/
def sload {m : Type → Type} [Monad m] : Handler m := fun ctx f ↦
  match popped : popFrame f with
  | .error (residual, error) => pure (.halt residual error)
  | .ok (word, residual) => loadAfterPop ctx residual word (poppedFrame_room f residual word popped)

private theorem load_of_error {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame)
    (error : ExceptionalHalt) (missing : f.stack.pop = .error error) :
    (sload ctx f : VmM m (StepResult ctx)) = pure (.halt f error) := by
  have popped : popFrame f = .error (f, error) := by simp [popFrame_eq, popFrameReference, missing]
  unfold sload
  split
  · rename_i residual actual observed
    have same := Except.error.inj (popped.symm.trans observed)
    cases same
    rfl
  · rename_i word residual observed
    rw [popped] at observed
    contradiction

private theorem load_of_pop {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame)
    (word : U256) (tail : Stack) (popped : f.stack.pop = .ok (word, tail)) :
    (sload ctx f : VmM m (StepResult ctx)) =
      loadAfterPop ctx { f with stack := tail } word (room_after_pop f.stack tail word popped) := by
  have framePop : popFrame f = .ok (word, { f with stack := tail }) := by
    simp [popFrame_eq, popFrameReference, popped]
  unfold sload
  split
  · rename_i residual error observed
    rw [framePop] at observed
    contradiction
  · rename_i actual residual observed
    have same := Except.ok.inj (framePop.symm.trans observed)
    cases same
    rfl

private abbrev selectedSlots (ctx : FrameCtx) (f : Frame) (word : U256) : SlotSet × Nat :=
  warmAndPrice ctx.config f.accessedStorageKeys (ctx.currentTarget, word.toBeBytes32)

private theorem underflow {m : Type → Type} [Monad m] (ctx : FrameCtx) (f : Frame)
    (w : VmWorld m) (missing : f.stack.pop = .error .stackUnderflow) :
    ((sload ctx f).run w).run = pure (.ok (.halt f .stackUnderflow, w)) := by
  rw [load_of_error _ _ _ missing]
  rfl

private theorem warmDenial {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (word : U256) (tail : Stack)
    (popped : f.stack.pop = .ok (word, tail))
    (warm : (ctx.currentTarget, word.toBeBytes32) ∈ f.accessedStorageKeys)
    (short : f.gasMeter.gasLeft < ctx.config.costs.warmAccess) :
    ((sload ctx f).run w).run = pure (.ok (.halt { f with stack := tail } .outOfGas, w)) := by
  have denied := (chargeGas_eq_error_iff f.gasMeter ctx.config.costs.warmAccess .outOfGas).mpr
    ⟨short, rfl⟩
  rw [load_of_pop _ _ _ _ popped]
  simp only [loadAfterPop, warmAndPrice, warm, ite_true, denied]
  rfl

private theorem coldDenial {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (word : U256) (tail : Stack)
    (popped : f.stack.pop = .ok (word, tail))
    (cold : (ctx.currentTarget, word.toBeBytes32) ∉ f.accessedStorageKeys)
    (short : f.gasMeter.gasLeft < ctx.config.costs.coldStorageAccess) :
    ((sload ctx f).run w).run = pure (.ok (.halt { f with
      stack := tail
      accessedStorageKeys := f.accessedStorageKeys.insert (ctx.currentTarget, word.toBeBytes32)
    } .outOfGas, w)) := by
  have denied := (chargeGas_eq_error_iff f.gasMeter ctx.config.costs.coldStorageAccess .outOfGas).mpr
    ⟨short, rfl⟩
  rw [load_of_pop _ _ _ _ popped]
  simp only [loadAfterPop, warmAndPrice, cold, ite_false, denied]
  rfl

private theorem paidAction {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (word : U256) (tail : Stack) (meter : GasMeter)
    (popped : f.stack.pop = .ok (word, tail))
    (paid : chargeGas f.gasMeter (selectedSlots ctx f word).2 = .ok meter) :
    ((sload ctx f).run w).run =
      (((do
        let value ← liftState (getStorage ctx.currentTarget word.toBeBytes32)
        pure (paidResult ctx { f with stack := tail } (room_after_pop f.stack tail word popped)
          (selectedSlots ctx f word).1 meter value)) : VmM m (StepResult ctx)).run w).run := by
  rw [load_of_pop _ _ _ _ popped]
  simp only [loadAfterPop, paid]

private theorem idPaidResult (ctx : FrameCtx) (f : Frame) (w : VmWorld Id) (word : U256)
    (tail : Stack) (meter : GasMeter) (popped : f.stack.pop = .ok (word, tail))
    (paid : chargeGas f.gasMeter (selectedSlots ctx f word).2 = .ok meter) :
    ((sload ctx f).run w).run =
      match ((getStorage ctx.currentTarget word.toBeBytes32).run w.tx).run with
      | .error error => .error (.state error)
      | .ok (value, next) =>
        .ok (paidResult ctx { f with stack := tail } (room_after_pop f.stack tail word popped)
          (selectedSlots ctx f word).1 meter value, { w with tx := next }) := by
  rw [paidAction ctx f w word tail meter popped paid]
  simp only [StateT.run_bind, ExceptT.run_bind, liftState_run]
  cases ((getStorage ctx.currentTarget word.toBeBytes32).run w.tx).run <;> rfl

private theorem paidFault (ctx : FrameCtx) (f : Frame) (w : VmWorld Id) (word : U256) (tail : Stack)
    (meter : GasMeter) (popped : f.stack.pop = .ok (word, tail))
    (paid : chargeGas f.gasMeter (selectedSlots ctx f word).2 = .ok meter)
    (error : StateError)
    (read : ((getStorage ctx.currentTarget word.toBeBytes32).run w.tx).run = .error error) :
    ((sload ctx f).run w).run = .error (.state error) := by
  rw [idPaidResult ctx f w word tail meter popped paid, read]

private theorem paidSuccess (ctx : FrameCtx) (f : Frame) (w : VmWorld Id) (word : U256) (tail : Stack)
    (meter : GasMeter) (popped : f.stack.pop = .ok (word, tail))
    (paid : chargeGas f.gasMeter (selectedSlots ctx f word).2 = .ok meter)
    (value : U256) (next : TxState Id)
    (read : ((getStorage ctx.currentTarget word.toBeBytes32).run w.tx).run = .ok (value, next)) :
    ∃ stack, tail.push value = .ok stack ∧ stack.toList = value :: tail.toList ∧
      ((sload ctx f).run w).run = .ok (.continue { f with
        pc := f.pc + 1
        stack := stack
        gasMeter := meter
        accessedStorageKeys := (selectedSlots ctx f word).1 }, { w with tx := next }) := by
  let room := room_after_pop f.stack tail word popped
  have actual := pushLoaded_actual tail value room
  refine ⟨pushLoaded tail value room, actual, ((Stack.push_eq_ok_iff tail _ value).mp actual).2, ?_⟩
  rw [idPaidResult ctx f w word tail meter popped paid, read]
  change Except.ok (paidResult ctx { f with stack := tail } room
    (selectedSlots ctx f word).1 meter value, { w with tx := next }) = _
  rw [paidResult_eq]

private theorem continuationPhi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (word : U256) (tail : Stack) (popped : f.stack.pop = .ok (word, tail))
    (ran : ((sload ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + (selectedSlots ctx f word).2 = f.gasMeter.phi := by
  cases charge : chargeGas f.gasMeter (selectedSlots ctx f word).2 with
  | error error =>
    rw [load_of_pop _ _ _ _ popped] at ran
    simp only [loadAfterPop, charge] at ran
    change Except.ok (StepResult.halt _ error, w) = _ at ran
    have impossible := (Prod.mk.inj (Except.ok.inj ran)).1
    cases impossible
  | ok meter =>
    cases read : ((getStorage ctx.currentTarget word.toBeBytes32).run w.tx).run with
    | error error =>
      rw [paidFault ctx f w word tail meter popped charge error read] at ran
      contradiction
    | ok pair =>
      rcases pair with ⟨value, next⟩
      obtain ⟨stack, _, _, result⟩ := paidSuccess ctx f w word tail meter popped charge value next read
      rw [result] at ran
      have frame := StepResult.continue.inj (Prod.mk.inj (Except.ok.inj ran)).1
      rw [← frame]
      exact chargeGas_phi f.gasMeter (selectedSlots ctx f word).2 meter charge

private theorem continuationProgress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (word : U256) (tail : Stack) (popped : f.stack.pop = .ok (word, tail))
    (ran : ((sload ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ (selectedSlots ctx f word).2) :
    f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have spent := continuationPhi ctx f f' w w' word tail popped ran
  omega

end STFSpec.Vm.Instructions
