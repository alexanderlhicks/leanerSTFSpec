/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions.Handler

/-!
# Standalone control-flow handlers

Library `EthVmInstructions`. JUMP and JUMPI pop operands before charging.
JUMPDEST charges before advancing the PC.
Spec guidance `STFSpec/informal/modules/EthVmInstructions.md` §§2/3/5/7.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base STFSpec.Vm.Core

private def jumpdestResult (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  match chargeGas f.gasMeter ctx.config.costs.opcodeJumpDest with
  | .error e => .halt f e
  | .ok paid => .continue { f with pc := f.pc + 1, gasMeter := paid }

/-- Charge the JUMPDEST execution price and advance the PC.
EELS `src/ethereum/forks/amsterdam/vm/instructions/control_flow.py:149–171`. -/
def jumpdest {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (jumpdestResult ctx f)

/-- Execution shortage retains the complete entry frame and world. -/
theorem jumpdest_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeJumpDest) :
    ((jumpdest ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w)) := by
  change pure (Except.ok (jumpdestResult ctx f, w)) = _
  have denied := (chargeGas_eq_error_iff f.gasMeter ctx.config.costs.opcodeJumpDest .outOfGas).mpr
    ⟨short, rfl⟩
  simp only [jumpdestResult, denied]

/-- Payment changes execution gas and advances the PC by one. -/
theorem jumpdest_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeJumpDest ≤ f.gasMeter.gasLeft) :
    ((jumpdest ctx f).run w).run = pure (Except.ok
      (.continue { f with
        pc := f.pc + 1
        gasMeter := { f.gasMeter with
          gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeJumpDest } }, w)) := by
  change pure (Except.ok (jumpdestResult ctx f, w)) = _
  simp only [jumpdestResult, chargeGas_of_le f.gasMeter ctx.config.costs.opcodeJumpDest enough]

/-- A continuing Id run spends the exact selected execution price. -/
theorem jumpdest_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((jumpdest ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeJumpDest = f.gasMeter.phi := by
  change Except.ok (jumpdestResult ctx f, w) = .ok (.continue f', w') at run
  have next := (Prod.mk.inj (Except.ok.inj run)).1
  cases paid : chargeGas f.gasMeter ctx.config.costs.opcodeJumpDest with
  | error e =>
    simp only [jumpdestResult, paid] at next
    contradiction
  | ok meter =>
    simp only [jumpdestResult, paid, StepResult.continue.injEq] at next
    subst f'
    exact chargeGas_phi f.gasMeter ctx.config.costs.opcodeJumpDest meter paid

/-- A positive price strictly decreases potential on a continuing Id run. -/
theorem jumpdest_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((jumpdest ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeJumpDest) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have accounting := jumpdest_continue_phi ctx f f' w w' run
  omega

private def jumpReference (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  match f.stack.pop with
  | .error e => .halt f e
  | .ok (destination, stack) =>
    let popped := { f with stack }
    match chargeGas f.gasMeter ctx.config.costs.opcodeJump with
    | .error e => .halt popped e
    | .ok paid =>
      let next := { popped with gasMeter := paid }
      if ctx.jumpdests.contains destination.toNat then
        .continue { next with pc := destination.toNat }
      else
        .halt next .invalidJumpDest

private def jumpiReference (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  match f.stack.pop with
  | .error e => .halt f e
  | .ok (destination, first) =>
    let once := { f with stack := first }
    match first.pop with
    | .error e => .halt once e
    | .ok (condition, second) =>
      let popped := { once with stack := second }
      match chargeGas f.gasMeter ctx.config.costs.opcodeJumpi with
      | .error e => .halt popped e
      | .ok paid =>
        let next := { popped with gasMeter := paid }
        if condition.toNat = 0 then
          .continue { next with pc := f.pc + 1 }
        else if ctx.jumpdests.contains destination.toNat then
          .continue { next with pc := destination.toNat }
        else
          .halt next .invalidJumpDest

private theorem empty_pop (s : Stack) (empty : s.size = 0) :
    s.pop = .error .stackUnderflow := by
  rw [Stack.size_eq_length_toList] at empty
  exact (Stack.pop_eq_error_iff s .stackUnderflow).mpr ⟨List.length_eq_zero_iff.mp empty, rfl⟩

private theorem nonempty_pop (s : Stack) (e : ExceptionalHalt)
    (nonempty : s.size ≠ 0) (failed : s.pop = .error e) : False := by
  have empty := ((Stack.pop_eq_error_iff s e).mp failed).1
  apply nonempty
  simp [Stack.size_eq_length_toList, empty]

private def jumpLinear (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  if empty : f.stack.size = 0 then
    .halt f .stackUnderflow
  else
    match popped : f.stack.pop with
    | .error e => False.elim (nonempty_pop f.stack e empty popped)
    | .ok (destination, stack) =>
      match chargeGas f.gasMeter ctx.config.costs.opcodeJump with
      | .error e => .halt { f with stack } e
      | .ok paid =>
        if ctx.jumpdests.contains destination.toNat then
          .continue { f with stack, gasMeter := paid, pc := destination.toNat }
        else
          .halt { f with stack, gasMeter := paid } .invalidJumpDest

private theorem jumpLinear_eq (ctx : FrameCtx) (f : Frame) :
    jumpLinear ctx f = jumpReference ctx f := by
  unfold jumpLinear jumpReference
  split
  · rename_i empty
    rw [empty_pop f.stack empty]
  · rename_i nonempty
    split
    · rename_i e failed
      exact False.elim (nonempty_pop f.stack e nonempty failed)
    · rename_i destination stack popped
      simp only [popped]

private def jumpiLinear (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  if empty : f.stack.size = 0 then
    .halt f .stackUnderflow
  else
    match popped : f.stack.pop with
    | .error e => False.elim (nonempty_pop f.stack e empty popped)
    | .ok (destination, first) =>
      if empty : first.size = 0 then
        .halt { f with stack := first } .stackUnderflow
      else
        match popped : first.pop with
        | .error e => False.elim (nonempty_pop first e empty popped)
        | .ok (condition, stack) =>
          match chargeGas f.gasMeter ctx.config.costs.opcodeJumpi with
          | .error e => .halt { f with stack } e
          | .ok paid =>
            if condition.toNat = 0 then
              .continue { f with stack, gasMeter := paid, pc := f.pc + 1 }
            else if ctx.jumpdests.contains destination.toNat then
              .continue { f with stack, gasMeter := paid, pc := destination.toNat }
            else
              .halt { f with stack, gasMeter := paid } .invalidJumpDest

private theorem jumpiLinear_eq (ctx : FrameCtx) (f : Frame) :
    jumpiLinear ctx f = jumpiReference ctx f := by
  unfold jumpiLinear jumpiReference
  split
  · rename_i empty
    rw [empty_pop f.stack empty]
  · rename_i nonempty
    split
    · rename_i e failed
      exact False.elim (nonempty_pop f.stack e nonempty failed)
    · rename_i destination first popped
      simp only [popped]
      split
      · rename_i empty
        rw [empty_pop first empty]
      · rename_i nonemptyFirst
        split
        · rename_i e failed
          exact False.elim (nonempty_pop first e nonemptyFirst failed)
        · rename_i condition stack poppedFirst
          simp only [poppedFirst]

/-- Pop, charge and jump to a valid destination.
EELS `src/ethereum/forks/amsterdam/vm/instructions/control_flow.py:45–68`. -/
def jump {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (jumpLinear ctx f)

/-- Pop the destination and condition, charge and take the selected branch.
EELS `src/ethereum/forks/amsterdam/vm/instructions/control_flow.py:70–98`. -/
def jumpi {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (jumpiLinear ctx f)

/-- An empty stack halts before charging and retains the entry frame and world. -/
theorem jump_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (empty : f.stack.toList = []) :
    ((jump ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) := by
  have popped := (Stack.pop_eq_error_iff f.stack .stackUnderflow).mpr ⟨empty, rfl⟩
  change pure (Except.ok (jumpLinear ctx f, w)) = _
  rw [jumpLinear_eq]
  simp only [jumpReference, popped]

/-- An empty stack halts before the first pop or charge. -/
theorem jumpi_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (empty : f.stack.toList = []) :
    ((jumpi ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) := by
  have popped := (Stack.pop_eq_error_iff f.stack .stackUnderflow).mpr ⟨empty, rfl⟩
  change pure (Except.ok (jumpiLinear ctx f, w)) = _
  rw [jumpiLinear_eq]
  simp only [jumpiReference, popped]

/-- Missing the condition retains the first pop and precedes charging. -/
theorem jumpi_run_missing_condition {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (destination : U256) (residual : Stack)
    (popped : f.stack.pop = .ok (destination, residual)) (empty : residual.toList = []) :
    ((jumpi ctx f).run w).run =
      pure (Except.ok (.halt { f with stack := residual } .stackUnderflow, w)) := by
  have absent := (Stack.pop_eq_error_iff residual .stackUnderflow).mpr ⟨empty, rfl⟩
  change pure (Except.ok (jumpiLinear ctx f, w)) = _
  rw [jumpiLinear_eq]
  simp only [jumpiReference, popped, absent]

/-- Execution shortage retains the completed destination pop. -/
theorem jump_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (destination : U256) (residual : Stack)
    (popped : f.stack.pop = .ok (destination, residual))
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeJump) :
    ((jump ctx f).run w).run =
      pure (Except.ok (.halt { f with stack := residual } .outOfGas, w)) := by
  have denied := (chargeGas_eq_error_iff _ _ .outOfGas).mpr ⟨short, rfl⟩
  change pure (Except.ok (jumpLinear ctx f, w)) = _
  rw [jumpLinear_eq]
  simp only [jumpReference, popped, denied]

/-- Execution shortage retains both completed pops. -/
theorem jumpi_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (destination condition : U256)
    (first residual : Stack)
    (popped : f.stack.pop = .ok (destination, first)) (tested : first.pop = .ok (condition, residual))
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeJumpi) :
    ((jumpi ctx f).run w).run =
      pure (Except.ok (.halt { f with stack := residual } .outOfGas, w)) := by
  have denied := (chargeGas_eq_error_iff _ _ .outOfGas).mpr ⟨short, rfl⟩
  change pure (Except.ok (jumpiLinear ctx f, w)) = _
  rw [jumpiLinear_eq]
  simp only [jumpiReference, popped, tested, denied]

/-- Payment preserves the residual stack and uses the supplied destination map. -/
theorem jump_run_paid {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (destination : U256) (residual : Stack)
    (popped : f.stack.pop = .ok (destination, residual))
    (enough : ctx.config.costs.opcodeJump ≤ f.gasMeter.gasLeft) :
    let after : Frame := { f with
      stack := residual
      gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeJump } }
    ((jump ctx f).run w).run = pure (Except.ok
      ((if ctx.jumpdests.contains destination.toNat then .continue { after with pc := destination.toNat }
        else .halt after .invalidJumpDest), w)) := by
  change pure (Except.ok (jumpLinear ctx f, w)) = _
  rw [jumpLinear_eq]
  simp only [jumpReference, popped, chargeGas_of_le _ _ enough]

/-- A paid zero condition advances the PC without checking the destination. -/
theorem jumpi_run_paid_zero {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (destination condition : U256)
    (first residual : Stack)
    (popped : f.stack.pop = .ok (destination, first)) (tested : first.pop = .ok (condition, residual))
    (enough : ctx.config.costs.opcodeJumpi ≤ f.gasMeter.gasLeft)
    (zero : condition.toNat = 0) :
    let after : Frame := { f with
      stack := residual
      gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeJumpi } }
    ((jumpi ctx f).run w).run =
      pure (Except.ok (.continue { after with pc := f.pc + 1 }, w)) := by
  change pure (Except.ok (jumpiLinear ctx f, w)) = _
  rw [jumpiLinear_eq]
  simp only [jumpiReference, popped, tested, chargeGas_of_le _ _ enough, zero, ↓reduceIte]

/-- A paid nonzero condition selects the checked destination. -/
theorem jumpi_run_paid_nonzero {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (destination condition : U256)
    (first residual : Stack)
    (popped : f.stack.pop = .ok (destination, first)) (tested : first.pop = .ok (condition, residual))
    (enough : ctx.config.costs.opcodeJumpi ≤ f.gasMeter.gasLeft)
    (nonzero : condition.toNat ≠ 0) :
    let after : Frame := { f with
      stack := residual
      gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeJumpi } }
    ((jumpi ctx f).run w).run = pure (Except.ok
      ((if ctx.jumpdests.contains destination.toNat then .continue { after with pc := destination.toNat }
        else .halt after .invalidJumpDest), w)) := by
  change pure (Except.ok (jumpiLinear ctx f, w)) = _
  rw [jumpiLinear_eq]
  simp only [jumpiReference, popped, tested, chargeGas_of_le _ _ enough,
    ite_eq_right nonzero]

/-- A continuing Id jump spends exactly the selected execution price. -/
theorem jump_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((jump ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeJump = f.gasMeter.phi := by
  change Except.ok (jumpLinear ctx f, w) = .ok (.continue f', w') at run
  rw [jumpLinear_eq] at run
  have step := (Prod.mk.inj (Except.ok.inj run)).1
  cases popped : f.stack.pop with
  | error e =>
    simp only [jumpReference, popped] at step
    contradiction
  | ok pair =>
    rcases pair with ⟨destination, residual⟩
    cases paid : chargeGas f.gasMeter ctx.config.costs.opcodeJump with
    | error e =>
      simp only [jumpReference, popped, paid] at step
      contradiction
    | ok meter =>
      simp only [jumpReference, popped, paid] at step
      split at step
      · simp only [StepResult.continue.injEq] at step
        subst f'
        exact chargeGas_phi f.gasMeter ctx.config.costs.opcodeJump meter paid
      · contradiction

/-- Either continuing Id branch spends exactly the selected execution price. -/
theorem jumpi_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((jumpi ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeJumpi = f.gasMeter.phi := by
  change Except.ok (jumpiLinear ctx f, w) = .ok (.continue f', w') at run
  rw [jumpiLinear_eq] at run
  have step := (Prod.mk.inj (Except.ok.inj run)).1
  cases popped : f.stack.pop with
  | error e =>
    simp only [jumpiReference, popped] at step
    contradiction
  | ok pair =>
    rcases pair with ⟨destination, first⟩
    cases tested : first.pop with
    | error e =>
      simp only [jumpiReference, popped, tested] at step
      contradiction
    | ok pair =>
      rcases pair with ⟨condition, residual⟩
      cases paid : chargeGas f.gasMeter ctx.config.costs.opcodeJumpi with
      | error e =>
        simp only [jumpiReference, popped, tested, paid] at step
        contradiction
      | ok meter =>
        simp only [jumpiReference, popped, tested, paid] at step
        split at step
        · simp only [StepResult.continue.injEq] at step
          subst f'
          exact chargeGas_phi f.gasMeter ctx.config.costs.opcodeJumpi meter paid
        · split at step
          · simp only [StepResult.continue.injEq] at step
            subst f'
            exact chargeGas_phi f.gasMeter ctx.config.costs.opcodeJumpi meter paid
          · contradiction

/-- A positive price gives strict execution-potential progress after a jump. -/
theorem jump_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((jump ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeJump) :
    f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have accounting := jump_continue_phi ctx f f' w w' run
  omega

/-- A positive price gives strict progress on either continuing conditional branch. -/
theorem jumpi_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (run : ((jumpi ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeJumpi) :
    f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have accounting := jumpi_continue_phi ctx f f' w w' run
  omega

end STFSpec.Vm.Instructions
