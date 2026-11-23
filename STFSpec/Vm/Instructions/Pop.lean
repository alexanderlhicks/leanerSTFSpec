/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions.Handler

/-!
# POP

Library `EthVmInstructions`. The handler consumes one operand through the
EthVmCore Stack and charges the raw POP execution price.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§3/5/7.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base STFSpec.Vm.Core

private def popReference (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  match f.stack.pop with
  | .error e => .halt f e
  | .ok (_, stack) =>
    match chargeGas f.gasMeter ctx.config.costs.opcodePop with
    | .error e => .halt { f with stack } e
    | .ok paid => .continue { f with pc := f.pc + 1, stack, gasMeter := paid }

private theorem pop_empty (s : Stack) (zero : s.size = 0) :
    s.pop = .error .stackUnderflow := by
  rw [Stack.size_eq_length_toList] at zero
  exact (Stack.pop_eq_error_iff s .stackUnderflow).mpr
    ⟨List.length_eq_zero_iff.mp zero, rfl⟩

private theorem pop_error_contradicts_nonempty (s : Stack) (e : ExceptionalHalt)
    (nonempty : s.size ≠ 0) (failed : s.pop = .error e) : False := by
  have empty := ((Stack.pop_eq_error_iff s e).mp failed).1
  apply nonempty
  simp [Stack.size_eq_length_toList, empty]

/-- Check emptiness before taking ownership of the entry stack. -/
private def popLinear (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  if empty : f.stack.size = 0 then
    .halt f .stackUnderflow
  else
    match entry : f.stack.pop with
    | .error e => False.elim (pop_error_contradicts_nonempty f.stack e empty entry)
    | .ok (_, stack) =>
      match chargeGas f.gasMeter ctx.config.costs.opcodePop with
      | .error e => .halt { f with stack } e
      | .ok paid => .continue { f with pc := f.pc + 1, stack, gasMeter := paid }

private theorem popLinear_eq_reference (ctx : FrameCtx) (f : Frame) :
    popLinear ctx f = popReference ctx f := by
  unfold popLinear popReference
  split
  · rename_i empty
    rw [pop_empty f.stack empty]
  · rename_i nonempty
    split
    · rename_i e failed
      exact False.elim (pop_error_contradicts_nonempty f.stack e nonempty failed)
    · rename_i word stack popped
      simp only [popped]

/-- Pop and discard the top word, then charge and advance PC.
EELS `src/ethereum/forks/amsterdam/vm/instructions/stack.py:26–46`. -/
def pop {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (popLinear ctx f)

private theorem pop_of_model (s : Stack) (x : U256) (xs : List U256)
    (entry : s.toList = x :: xs) :
    ∃ t, s.pop = .ok (x, t) ∧ t.toList = xs := by
  cases popped : s.pop with
  | error e =>
    have impossible := (Stack.pop_eq_error_iff s e).mp popped
    rw [entry] at impossible
    simp at impossible
  | ok pair =>
    rcases pair with ⟨v, t⟩
    have model := (Stack.pop_eq_ok_iff s t v).mp popped
    rw [entry] at model
    rcases List.cons.inj model with ⟨rfl, observed⟩
    exact ⟨t, rfl, observed.symm⟩

/-- Underflow precedes charging and retains the complete frame and world. -/
theorem pop_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (empty : f.stack.toList = []) :
    ((pop ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) := by
  have popped := (Stack.pop_eq_error_iff f.stack .stackUnderflow).mpr ⟨empty, rfl⟩
  change pure (Except.ok (popLinear ctx f, w)) = _
  rw [popLinear_eq_reference]
  simp only [popReference, popped]

/-- Gas denial retains the completed pop, original PC, meter and world. -/
theorem pop_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256) (xs : List U256)
    (entry : f.stack.toList = x :: xs)
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodePop) :
    ∃ stack : Stack, f.stack.pop = .ok (x, stack) ∧ stack.toList = xs ∧
      ((pop ctx f).run w).run =
        pure (Except.ok (.halt { f with stack } .outOfGas, w)) := by
  obtain ⟨stack, popped, model⟩ := pop_of_model f.stack x xs entry
  have denied := (chargeGas_eq_error_iff f.gasMeter ctx.config.costs.opcodePop .outOfGas).mpr
    ⟨short, rfl⟩
  refine ⟨stack, popped, model, ?_⟩
  change pure (Except.ok (popLinear ctx f, w)) = _
  rw [popLinear_eq_reference]
  simp only [popReference, popped, denied]

/-- An affordable charge retains the popped stack and updates only execution gas and PC. -/
theorem pop_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256) (xs : List U256)
    (entry : f.stack.toList = x :: xs)
    (enough : ctx.config.costs.opcodePop ≤ f.gasMeter.gasLeft) :
    ∃ stack : Stack, f.stack.pop = .ok (x, stack) ∧ stack.toList = xs ∧
      ((pop ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodePop } }, w)) := by
  obtain ⟨stack, popped, model⟩ := pop_of_model f.stack x xs entry
  have paid := chargeGas_of_le f.gasMeter ctx.config.costs.opcodePop enough
  refine ⟨stack, popped, model, ?_⟩
  change pure (Except.ok (popLinear ctx f, w)) = _
  rw [popLinear_eq_reference]
  simp only [popReference, popped, paid]

/-- A continuing Id run spends exactly the selected execution price in meter potential. -/
theorem pop_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((pop ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodePop = f.gasMeter.phi := by
  change Except.ok (popLinear ctx f, w) = .ok (.continue f', w') at run
  have outcome := (Prod.mk.inj (Except.ok.inj run)).1
  rw [popLinear_eq_reference] at outcome
  cases popped : f.stack.pop with
  | error e =>
    simp only [popReference, popped] at outcome
    contradiction
  | ok pair =>
    rcases pair with ⟨_, stack⟩
    cases paid : chargeGas f.gasMeter ctx.config.costs.opcodePop with
    | error e =>
      simp only [popReference, popped, paid] at outcome
      contradiction
    | ok meter =>
      simp only [popReference, popped, paid, StepResult.continue.injEq] at outcome
      subst f'
      exact chargeGas_phi f.gasMeter ctx.config.costs.opcodePop meter paid

/-- A positive selected price gives strict potential decrease on a continuing Id run. -/
theorem pop_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((pop ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodePop) :
    f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have accounting := pop_continue_phi ctx f f' w w' run
  omega

end STFSpec.Vm.Instructions
