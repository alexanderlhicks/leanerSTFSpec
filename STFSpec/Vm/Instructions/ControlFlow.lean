/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions.Handler

/-!
# Standalone control-flow handlers

Library `EthVmInstructions`. JUMPDEST advances the PC after charging.
Spec guidance `STFSpec/informal/modules/EthVmInstructions.md` §§2/3/5/7.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Vm.Core

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

end STFSpec.Vm.Instructions
