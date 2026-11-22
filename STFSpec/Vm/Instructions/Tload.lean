/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.IntegerBytes
import STFSpec.State.TransientStorage
import STFSpec.Vm.Core.StateLift
import STFSpec.Vm.Instructions.Handler

/-!
# TLOAD

Library `EthVmInstructions`. See EELS
`src/ethereum/forks/amsterdam/vm/instructions/storage.py:164–186` at the pin
and `STFSpec/informal/modules/EthVmInstructions.md` §§3/5/7.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base STFSpec.State STFSpec.Vm.Core

private theorem tload_pop_not_error (stack : Stack) (error : ExceptionalHalt)
    (nonempty : stack.size ≠ 0) (pop : stack.pop = .error error) : False := by
  have empty := ((Stack.pop_eq_error_iff stack error).mp pop).1
  apply nonempty
  simp [Stack.size_eq_length_toList, empty]

private theorem tload_room_after_pop (before popped : Stack) (key : U256)
    (pop : before.pop = .ok (key, popped)) : popped.size < 1024 := by
  have isTop := (Stack.pop_eq_ok_iff before popped key).mp pop
  have fits := before.size_le
  rw [Stack.size_eq_length_toList, isTop, List.length_cons] at fits
  rw [Stack.size_eq_length_toList]
  omega

private theorem tload_push_not_error (before popped : Stack) (key value : U256)
    (pop : before.pop = .ok (key, popped)) (error : ExceptionalHalt)
    (push : popped.push value = .error error) : False :=
  (Nat.ne_of_lt (tload_room_after_pop before popped key pop))
    (((Stack.push_eq_error_iff popped value error).mp push).1)

private def tloadReference {m : Type → Type} [Monad m] : Handler m := fun ctx frame ↦
  match frame.stack.pop with
  | .error error => pure (.halt frame error)
  | .ok (key, popped) =>
    let slot := key.toBeBytes32
    let entered := { frame with stack := popped }
    match chargeGas frame.gasMeter ctx.config.costs.opcodeTload with
    | .error error => pure (.halt entered error)
    | .ok meter => do
      let value ← liftState (getTransientStorage ctx.currentTarget slot)
      match popped.push value with
      | .error error => pure (.halt { entered with gasMeter := meter } error)
      | .ok stack =>
        pure (.continue { entered with pc := frame.pc + 1, stack := stack, gasMeter := meter })

/-- Pop the slot key, charge execution gas, and push the current target's transient word. -/
def tload {m : Type → Type} [Monad m] : Handler m := fun ctx frame ↦
  if empty : frame.stack.size = 0 then
    pure (.halt frame .stackUnderflow)
  else
    match pop : frame.stack.pop with
    | .error error => False.elim (tload_pop_not_error frame.stack error empty pop)
    | .ok (key, popped) =>
      let slot := key.toBeBytes32
      let entered := { frame with stack := popped }
      match chargeGas frame.gasMeter ctx.config.costs.opcodeTload with
      | .error error => pure (.halt entered error)
      | .ok meter => do
        let value ← liftState (getTransientStorage ctx.currentTarget slot)
        match push : popped.push value with
        | .error error =>
          False.elim (tload_push_not_error frame.stack popped key value pop error push)
        | .ok stack =>
          pure (.continue { entered with pc := frame.pc + 1, stack := stack, gasMeter := meter })

private theorem tload_eq_reference {m : Type → Type} [Monad m] :
    (tload : Handler m) = tloadReference := by
  funext ctx frame
  unfold tload tloadReference
  split
  · rename_i empty
    have emptyList : frame.stack.toList = [] := by
      rw [Stack.size_eq_length_toList] at empty
      exact List.length_eq_zero_iff.mp empty
    rw [(Stack.pop_eq_error_iff frame.stack .stackUnderflow).mpr ⟨emptyList, rfl⟩]
  · rename_i nonempty
    split
    · rename_i error pop
      exact False.elim (tload_pop_not_error frame.stack error nonempty pop)
    · rename_i key popped pop
      conv =>
        rhs
        rw [pop]
      split
      · rfl
      · refine congrArg
          (fun continueWith : U256 → VmM m (StepResult ctx) =>
            liftState (getTransientStorage ctx.currentTarget key.toBeBytes32) >>= continueWith) ?_
        funext value
        split
        · rename_i error push
          exact False.elim (tload_push_not_error frame.stack popped key value pop error push)
        · rename_i stack push
          conv =>
            rhs
            rw [push]

private theorem tload_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (frame : Frame) (world : VmWorld m) (empty : frame.stack.toList = []) :
    ((tload ctx frame).run world).run =
      pure (.ok (.halt frame .stackUnderflow, world)) := by
  rw [tload_eq_reference, tloadReference,
    (Stack.pop_eq_error_iff frame.stack .stackUnderflow).mpr ⟨empty, rfl⟩]
  rfl

private theorem tload_outOfGas {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (frame : Frame) (world : VmWorld m)
    (key : U256) (popped : Stack) (pop : frame.stack.pop = .ok (key, popped))
    (insufficient : frame.gasMeter.gasLeft < ctx.config.costs.opcodeTload) :
    ((tload ctx frame).run world).run =
      pure (.ok (.halt { frame with stack := popped } .outOfGas, world)) := by
  rw [tload_eq_reference, tloadReference, pop,
    (chargeGas_eq_error_iff frame.gasMeter ctx.config.costs.opcodeTload .outOfGas).mpr
      ⟨insufficient, rfl⟩]
  rfl

private theorem tload_push_after_pop (before popped : Stack) (key value : U256)
    (pop : before.pop = .ok (key, popped)) :
    ∃ after, popped.push value = .ok after ∧ after.toList = value :: popped.toList := by
  cases pushed : popped.push value with
  | error error => exact False.elim (tload_push_not_error before popped key value pop error pushed)
  | ok after => exact ⟨after, rfl, ((Stack.push_eq_ok_iff popped after value).mp pushed).2⟩

private theorem tload_read_id (world : VmWorld Id) (owner : Address) (slot : Bytes32) :
    ((liftState (getTransientStorage owner slot)).run world).run =
      .ok ((world.tx.rev.transient[(owner, slot)]?).getD U256.zero, world) := by
  rw [liftState_run, getTransientStorage_action]
  cases world
  rfl

private theorem tload_success (ctx : FrameCtx) (frame : Frame) (world : VmWorld Id)
    (key : U256) (popped : Stack) (pop : frame.stack.pop = .ok (key, popped))
    (affordable : ctx.config.costs.opcodeTload ≤ frame.gasMeter.gasLeft) :
    let value := (world.tx.rev.transient[(ctx.currentTarget, key.toBeBytes32)]?).getD U256.zero
    let meter := { frame.gasMeter with gasLeft := frame.gasMeter.gasLeft - ctx.config.costs.opcodeTload }
    ∃ stack, stack.toList = value :: popped.toList ∧
      ((tload ctx frame).run world).run =
        .ok (.continue { frame with pc := frame.pc + 1, stack := stack, gasMeter := meter }, world) ∧
      meter.phi + ctx.config.costs.opcodeTload = frame.gasMeter.phi := by
  intro value meter
  obtain ⟨stack, push, stackList⟩ := tload_push_after_pop frame.stack popped key value pop
  have charge : chargeGas frame.gasMeter ctx.config.costs.opcodeTload = .ok meter :=
    chargeGas_of_le frame.gasMeter ctx.config.costs.opcodeTload affordable
  refine ⟨stack, stackList, ?_, chargeGas_phi frame.gasMeter ctx.config.costs.opcodeTload meter charge⟩
  simp only [tload_eq_reference, tloadReference, pop, charge, StateT.run_bind, ExceptT.run_bind,
    tload_read_id]
  have idBind {α β : Type} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl
  rw [idBind]
  change ((match popped.push value with
    | .error error => pure (StepResult.halt { frame with stack := popped, gasMeter := meter } error)
    | .ok pushed => pure (StepResult.continue { frame with
        pc := frame.pc + 1, stack := pushed, gasMeter := meter }) : VmM Id (StepResult ctx)).run world).run = _
  rw [push]
  rfl

end STFSpec.Vm.Instructions
