/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions.Handler

/-!
# Fixed stack swaps

Library `EthVmInstructions`. SWAP1–SWAP16 charge before exchanging two existing
stack entries. See `STFSpec/informal/modules/EthVmInstructions.md`.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base STFSpec.Vm.Core

private def swapPaid (depth : Nat) (ctx : FrameCtx) (paid : Frame) : StepResult ctx :=
  match paid.stack.swap? 0 depth with
  | none => .halt paid .stackUnderflow
  | some stack => .continue { paid with pc := paid.pc + 1, stack }

private theorem swap_available (stack : Stack) (depth : Nat) (fits : depth < stack.size)
    (missing : stack.swap? 0 depth = none) : False := by
  have invalid := (Stack.swap?_eq_none_iff stack 0 depth).mp missing
  omega

private def swapPaidLinear (depth : Nat) (ctx : FrameCtx) (paid : Frame) : StepResult ctx :=
  if fits : depth < paid.stack.size then
    match swapped : paid.stack.swap? 0 depth with
    | none => False.elim (swap_available paid.stack depth fits swapped)
    | some stack => .continue { paid with pc := paid.pc + 1, stack }
  else
    .halt paid .stackUnderflow

private theorem swapPaidLinear_eq (depth : Nat) (ctx : FrameCtx) (paid : Frame) :
    swapPaidLinear depth ctx paid = swapPaid depth ctx paid := by
  unfold swapPaidLinear swapPaid
  by_cases fits : depth < paid.stack.size
  · simp only [dite_eq_left fits]
    split
    · rename_i missing
      exact False.elim (swap_available paid.stack depth fits missing)
    · rename_i stack observed
      simp only [observed]
  · have missing := (Stack.swap?_eq_none_iff paid.stack 0 depth).mpr (Or.inr (Nat.not_lt.mp fits))
    simp only [dite_eq_right fits, missing]

private def swapRun (depth : Nat) (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  match chargeGas f.gasMeter ctx.config.costs.opcodeSwap with
  | .error error => .halt f error
  | .ok paid => swapPaidLinear depth ctx { f with gasMeter := paid }

/-- Charge and exchange the top with depth `n.val + 1`.
Pinned EELS `src/ethereum/forks/amsterdam/vm/instructions/stack.py:110–141,195–210`. -/
def swapN (n : Fin 16) {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (swapRun (n.val + 1) ctx f)

/-- Gas shortage retains the complete entry frame and world. -/
theorem swapN_run_oog (n : Fin 16) {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (short : f.gasMeter.gasLeft < ctx.config.costs.opcodeSwap) :
    ((swapN n ctx f).run w).run = pure (Except.ok (.halt f .outOfGas, w)) := by
  change pure (Except.ok (swapRun (n.val + 1) ctx f, w)) = _
  simp only [swapRun, (chargeGas_eq_error_iff _ _ _).mpr ⟨short, rfl⟩]

/-- Missing depth after payment retains the complete paid frame and world. -/
theorem swapN_run_underflow (n : Fin 16) {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeSwap ≤ f.gasMeter.gasLeft) (short : f.stack.size ≤ n.val + 1) :
    ((swapN n ctx f).run w).run =
      pure (Except.ok (.halt { f with gasMeter :=
        { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSwap } }
        .stackUnderflow, w)) := by
  have missing := (Stack.swap?_eq_none_iff f.stack 0 (n.val + 1)).mpr (Or.inr short)
  change pure (Except.ok (swapRun (n.val + 1) ctx f, w)) = _
  simp only [swapRun, chargeGas_of_le _ _ enough, swapPaidLinear_eq, swapPaid, missing]

/-- Successful payment and exchange keep the stack size and advance the PC by one. -/
theorem swapN_run_success (n : Fin 16) {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (enough : ctx.config.costs.opcodeSwap ≤ f.gasMeter.gasLeft) (fits : n.val + 1 < f.stack.size) :
    ∃ (stack : Stack) (top word : U256),
      f.stack.swap? 0 (n.val + 1) = some stack ∧
      f.stack.toList[0]? = some top ∧ f.stack.toList[n.val + 1]? = some word ∧
      stack.toList = (f.stack.toList.set 0 word).set (n.val + 1) top ∧ stack.size = f.stack.size ∧
      ((swapN n ctx f).run w).run =
        pure (Except.ok (.continue { f with
          gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSwap }
          pc := f.pc + 1, stack }, w)) := by
  cases swapped : f.stack.swap? 0 (n.val + 1) with
  | none => exact False.elim (swap_available f.stack _ fits swapped)
  | some stack =>
    obtain ⟨top, word, first, other, model⟩ :=
      (Stack.swap?_eq_some_iff f.stack stack 0 (n.val + 1)).mp swapped
    have size : stack.size = f.stack.size := by
      rw [Stack.size_eq_length_toList, Stack.size_eq_length_toList, model, List.length_set, List.length_set]
    refine ⟨stack, top, word, rfl, first, other, model, size, ?_⟩
    change pure (Except.ok (swapRun (n.val + 1) ctx f, w)) = _
    simp only [swapRun, chargeGas_of_le _ _ enough, swapPaidLinear_eq, swapPaid, swapped]

/-- A continuing Id run loses exactly the configured fixed SWAP price. -/
theorem swapN_continue_phi (n : Fin 16) (ctx : FrameCtx) (f next : Frame) (w w' : VmWorld Id)
    (ran : ((swapN n ctx f).run w).run = .ok (.continue next, w')) :
    next.gasMeter.phi + ctx.config.costs.opcodeSwap = f.gasMeter.phi := by
  change Except.ok (swapRun (n.val + 1) ctx f, w) = .ok (.continue next, w') at ran
  have result := (Prod.mk.inj (Except.ok.inj ran)).1
  cases charged : chargeGas f.gasMeter ctx.config.costs.opcodeSwap with
  | error e =>
    simp only [swapRun, charged] at result
    contradiction
  | ok meter =>
    cases swapped : f.stack.swap? 0 (n.val + 1) with
    | none =>
      simp only [swapRun, charged, swapPaidLinear_eq, swapPaid, swapped] at result
      contradiction
    | some stack =>
      simp only [swapRun, charged, swapPaidLinear_eq, swapPaid, swapped, StepResult.continue.injEq] at result
      subst next
      exact chargeGas_phi f.gasMeter ctx.config.costs.opcodeSwap meter charged

/-- A positive fixed SWAP price gives strict progress on continuation. -/
theorem swapN_continue_progress (n : Fin 16) (ctx : FrameCtx) (f next : Frame) (w w' : VmWorld Id)
    (ran : ((swapN n ctx f).run w).run = .ok (.continue next, w'))
    (positive : 1 ≤ ctx.config.costs.opcodeSwap) :
    next.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have accounting := swapN_continue_phi n ctx f next w w' ran
  omega

end STFSpec.Vm.Instructions
