/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.IntegerBytes
import STFSpec.State.TransientStorageWrite
import STFSpec.Vm.Core.StateLift
import STFSpec.Vm.Instructions.Handler

/-!
# TSTORE

Library `EthVmInstructions`. See EELS
`src/ethereum/forks/amsterdam/vm/instructions/storage.py:189–216` at the pin
and `STFSpec/informal/modules/EthVmInstructions.md` §§3/5/7.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base STFSpec.State STFSpec.Vm.Core

private theorem pop_error_of_empty (s : Stack) (empty : s.size = 0) :
    s.pop = .error .stackUnderflow := by
  rw [Stack.size_eq_length_toList] at empty
  exact (Stack.pop_eq_error_iff s .stackUnderflow).mpr ⟨List.length_eq_zero_iff.mp empty, rfl⟩

private theorem pop_failure_impossible (s : Stack) (e : ExceptionalHalt)
    (nonempty : s.size ≠ 0) (pop : s.pop = .error e) : False := by
  have empty := ((Stack.pop_eq_error_iff s e).mp pop).1
  apply nonempty
  simp [Stack.size_eq_length_toList, empty]

private def tstoreReference {m : Type → Type} [Monad m] : Handler m := fun ctx frame ↦
  if ctx.isStatic then
    pure (.halt frame .writeInStaticContext)
  else
    match frame.stack.pop with
    | .error error => pure (.halt frame error)
    | .ok (key, rest) =>
      let slot := key.toBeBytes32
      match rest.pop with
      | .error error => pure (.halt { frame with stack := rest } error)
      | .ok (value, stack) =>
        let entered := { frame with stack := stack }
        match chargeGas entered.gasMeter ctx.config.costs.opcodeTstore with
        | .error error => pure (.halt entered error)
        | .ok meter => do
          liftState (setTransientStorage ctx.currentTarget slot value)
          pure (.continue { entered with pc := frame.pc + 1, gasMeter := meter })

/-- Reject static execution, pop the slot and value, charge gas and write the current target. -/
def tstore {m : Type → Type} [Monad m] : Handler m := fun ctx frame ↦
  if ctx.isStatic then
    pure (.halt frame .writeInStaticContext)
  else if empty : frame.stack.size = 0 then
    pure (.halt frame .stackUnderflow)
  else
    match keyPop : frame.stack.pop with
    | .error error => False.elim (pop_failure_impossible frame.stack error empty keyPop)
    | .ok (key, rest) =>
      let slot := key.toBeBytes32
      if empty : rest.size = 0 then
        pure (.halt { frame with stack := rest } .stackUnderflow)
      else
        match valuePop : rest.pop with
        | .error error => False.elim (pop_failure_impossible rest error empty valuePop)
        | .ok (value, stack) =>
          let entered := { frame with stack := stack }
          match chargeGas entered.gasMeter ctx.config.costs.opcodeTstore with
          | .error error => pure (.halt entered error)
          | .ok meter => do
            liftState (setTransientStorage ctx.currentTarget slot value)
            pure (.continue { entered with pc := frame.pc + 1, gasMeter := meter })

private theorem tstore_eq_reference {m : Type → Type} [Monad m] :
    (tstore : Handler m) = tstoreReference := by
  funext ctx frame
  unfold tstore tstoreReference
  split
  · rfl
  · split
    · rename_i empty
      rw [pop_error_of_empty frame.stack empty]
    · rename_i nonempty
      split
      · rename_i error pop
        exact False.elim (pop_failure_impossible frame.stack error nonempty pop)
      · rename_i key rest pop
        conv => rhs; rw [pop]; dsimp only
        split
        · rename_i empty
          rw [pop_error_of_empty rest empty]
        · rename_i nonemptyRest
          split
          · rename_i error valuePop
            exact False.elim (pop_failure_impossible rest error nonemptyRest valuePop)
          · rename_i value stack valuePop
            conv => rhs; rw [valuePop]

private theorem tstore_static {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (frame : Frame) (world : VmWorld m) (isStatic : ctx.isStatic = true) :
    ((tstore ctx frame).run world).run = pure (.ok (.halt frame .writeInStaticContext, world)) := by
  simp only [tstore_eq_reference, tstoreReference, isStatic, ite_true]
  rfl

private theorem tstore_first_pop_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (frame : Frame) (world : VmWorld m)
    (nonStatic : ctx.isStatic = false) (empty : frame.stack.toList = []) :
    ((tstore ctx frame).run world).run = pure (.ok (.halt frame .stackUnderflow, world)) := by
  simp only [tstore_eq_reference, tstoreReference, nonStatic, Bool.false_eq_true, ite_false,
    (Stack.pop_eq_error_iff frame.stack .stackUnderflow).mpr ⟨empty, rfl⟩]
  rfl

private theorem tstore_second_pop_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (frame : Frame) (world : VmWorld m) (key : U256) (rest : Stack)
    (nonStatic : ctx.isStatic = false) (keyPop : frame.stack.pop = .ok (key, rest))
    (empty : rest.toList = []) :
    ((tstore ctx frame).run world).run =
      pure (.ok (.halt { frame with stack := rest } .stackUnderflow, world)) := by
  simp only [tstore_eq_reference, tstoreReference, nonStatic, Bool.false_eq_true, ite_false, keyPop,
    (Stack.pop_eq_error_iff rest .stackUnderflow).mpr ⟨empty, rfl⟩]
  rfl

private theorem tstore_outOfGas {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (frame : Frame) (world : VmWorld m) (key value : U256) (rest stack : Stack)
    (nonStatic : ctx.isStatic = false)
    (keyPop : frame.stack.pop = .ok (key, rest)) (valuePop : rest.pop = .ok (value, stack))
    (insufficient : frame.gasMeter.gasLeft < ctx.config.costs.opcodeTstore) :
    ((tstore ctx frame).run world).run =
      pure (.ok (.halt { frame with stack := stack } .outOfGas, world)) := by
  have chargeFailure := (chargeGas_eq_error_iff frame.gasMeter ctx.config.costs.opcodeTstore
    .outOfGas).mpr ⟨insufficient, rfl⟩
  simp only [tstore_eq_reference, tstoreReference, nonStatic, Bool.false_eq_true, ite_false,
    keyPop, valuePop, chargeFailure]
  rfl

private theorem tstore_paid_action {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (frame : Frame) (world : VmWorld m) (key value : U256) (rest stack : Stack)
    (nonStatic : ctx.isStatic = false)
    (keyPop : frame.stack.pop = .ok (key, rest)) (valuePop : rest.pop = .ok (value, stack))
    (affordable : ctx.config.costs.opcodeTstore ≤ frame.gasMeter.gasLeft) :
    let meter := { frame.gasMeter with gasLeft := frame.gasMeter.gasLeft - ctx.config.costs.opcodeTstore }
    let advanced := { frame with stack := stack, gasMeter := meter, pc := frame.pc + 1 }
    ((tstore ctx frame).run world).run =
      ((do
        liftState (setTransientStorage ctx.currentTarget key.toBeBytes32 value)
        pure (StepResult.continue advanced) : VmM m (StepResult ctx)).run world).run := by
  intro meter advanced
  have charged : chargeGas frame.gasMeter ctx.config.costs.opcodeTstore = .ok meter :=
    chargeGas_of_le frame.gasMeter ctx.config.costs.opcodeTstore affordable
  simp only [tstore_eq_reference, tstoreReference, nonStatic, Bool.false_eq_true, ite_false,
    keyPop, valuePop, charged]
  rfl

end STFSpec.Vm.Instructions
