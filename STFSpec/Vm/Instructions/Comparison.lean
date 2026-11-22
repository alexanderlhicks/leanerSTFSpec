/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions.Handler
import STFSpec.Base.U256Bitwise

/-!
# ISZERO

Library `EthVmInstructions`. The handler uses the word model from EthBase and
the stack and meter operations from EthVmCore.
Spec guidance is in `STFSpec/informal/modules/EthVmInstructions.md` §§3/5/7.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base STFSpec.Vm.Core

private def evalIsZero (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  match f.stack.pop with
  | .error e => .halt f e
  | .ok (x, stack) =>
    match chargeGas f.gasMeter ctx.config.costs.opcodeIsZero with
    | .error e => .halt { f with stack } e
    | .ok paid =>
      match stack.push (U256.iszero x) with
      | .error e => .halt { f with stack, gasMeter := paid } e
      | .ok out => .continue { f with pc := f.pc + 1, stack := out, gasMeter := paid }

/-- Pop one word, charge the selected execution price, push the zero test and advance the PC.
EELS `src/ethereum/forks/amsterdam/vm/instructions/comparison.py:154–177`. -/
def isZero {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (evalIsZero ctx f)

private theorem pop_of_model (s : Stack) (x : U256) (xs : List U256)
    (h : s.toList = x :: xs) : ∃ t, s.pop = .ok (x, t) ∧ t.toList = xs := by
  cases hp : s.pop with
  | error e =>
    have he := (Stack.pop_eq_error_iff s e).mp hp
    rw [h] at he
    simp at he
  | ok pair =>
    rcases pair with ⟨v, t⟩
    have hm := (Stack.pop_eq_ok_iff s t v).mp hp
    rw [h] at hm
    rcases List.cons.inj hm with ⟨rfl, ht⟩
    exact ⟨t, rfl, ht.symm⟩

/-- An empty stack halts before charging and retains the complete frame and world. -/
theorem isZero_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((isZero ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) := by
  have hp := (Stack.pop_eq_error_iff f.stack .stackUnderflow).mpr ⟨h, rfl⟩
  change pure (Except.ok (evalIsZero ctx f, w)) = _
  simp only [evalIsZero, hp]

/-- An unaffordable charge halts after one pop and retains every other frame field and the world. -/
theorem isZero_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256) (xs : List U256)
    (h : f.stack.toList = x :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeIsZero) :
    ∃ stack : Stack, f.stack.pop = .ok (x, stack) ∧ stack.toList = xs ∧
      ((isZero ctx f).run w).run =
        pure (Except.ok (.halt { f with stack } .outOfGas, w)) := by
  obtain ⟨stack, hp, model⟩ := pop_of_model f.stack x xs h
  have hg := (chargeGas_eq_error_iff f.gasMeter ctx.config.costs.opcodeIsZero .outOfGas).mpr
    ⟨hc, rfl⟩
  refine ⟨stack, hp, model, ?_⟩
  change pure (Except.ok (evalIsZero ctx f, w)) = _
  simp only [evalIsZero, hp, hg]

/-- An affordable charge replaces the top word and changes only the PC and execution gas.
The bounded stack guarantees space for the push after the pop. -/
theorem isZero_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256) (xs : List U256)
    (h : f.stack.toList = x :: xs)
    (hc : ctx.config.costs.opcodeIsZero ≤ f.gasMeter.gasLeft) :
    ∃ stack out : Stack, f.stack.pop = .ok (x, stack) ∧ stack.toList = xs ∧
      stack.push (U256.iszero x) = .ok out ∧ out.toList = U256.iszero x :: xs ∧
      ((isZero ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeIsZero } }, w)) := by
  obtain ⟨stack, hp, model⟩ := pop_of_model f.stack x xs h
  have oldBound := f.stack.size_le
  rw [Stack.size_eq_length_toList, h] at oldBound
  have available : stack.size < 1024 := by
    rw [Stack.size_eq_length_toList, model]
    simp only [List.length_cons] at oldBound
    omega
  cases next : stack.push (U256.iszero x) with
  | error e =>
    have he := (Stack.push_eq_error_iff stack (U256.iszero x) e).mp next
    omega
  | ok out =>
    have hm := (Stack.push_eq_ok_iff stack out (U256.iszero x)).mp next
    have hg := chargeGas_of_le f.gasMeter ctx.config.costs.opcodeIsZero hc
    refine ⟨stack, out, hp, model, next, ?_, ?_⟩
    · simpa only [model] using hm.2
    · change pure (Except.ok (evalIsZero ctx f, w)) = _
      simp only [evalIsZero, hp, hg, next]

/-- A continuing Id run spends exactly the selected execution price in meter potential. -/
theorem isZero_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((isZero ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeIsZero = f.gasMeter.phi := by
  change Except.ok (evalIsZero ctx f, w) = .ok (.continue f', w') at h
  have step := (Prod.mk.inj (Except.ok.inj h)).1
  cases hp : f.stack.pop with
  | error e =>
    simp only [evalIsZero, hp] at step
    contradiction
  | ok pair =>
    rcases pair with ⟨x, stack⟩
    cases hg : chargeGas f.gasMeter ctx.config.costs.opcodeIsZero with
    | error e =>
      simp only [evalIsZero, hp, hg] at step
      contradiction
    | ok paid =>
      cases next : stack.push (U256.iszero x) with
      | error e =>
        simp only [evalIsZero, hp, hg, next] at step
        contradiction
      | ok out =>
        simp only [evalIsZero, hp, hg, next, StepResult.continue.injEq] at step
        subst f'
        exact chargeGas_phi f.gasMeter ctx.config.costs.opcodeIsZero paid hg

/-- A positive selected execution price implies strict potential decrease on a continuing Id run. -/
theorem isZero_continue_progress (ctx : FrameCtx) (f f' : Frame)
    (w w' : VmWorld Id) (h : ((isZero ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeIsZero) :
    f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have accounting := isZero_continue_phi ctx f f' w w' h
  omega

end STFSpec.Vm.Instructions
