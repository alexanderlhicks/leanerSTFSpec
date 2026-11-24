/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions.Handler

/-!
# Byte-size words

Library `EthVmInstructions`. Charge for the instruction and push the modular
word for the selected byte count. See `STFSpec/informal/modules/EthVmInstructions.md`.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base STFSpec.Vm.Core

private def pushSizeReference (ctx : FrameCtx) (paid : Frame) (word : U256) : StepResult ctx :=
  match paid.stack.push word with
  | .error error => .halt paid error
  | .ok stack => .continue { paid with stack, pc := paid.pc + 1 }

private theorem size_push_fits (stack : Stack) (word : U256) (error : ExceptionalHalt)
    (space : stack.size ≠ 1024) (failed : stack.push word = .error error) : False :=
  space ((Stack.push_eq_error_iff stack word error).mp failed).1

private def pushSize (ctx : FrameCtx) (paid : Frame) (word : U256) : StepResult ctx :=
  if full : paid.stack.size = 1024 then
    .halt paid .stackOverflow
  else
    match pushed : paid.stack.push word with
    | .error error => False.elim (size_push_fits paid.stack word error full pushed)
    | .ok stack => .continue { paid with stack, pc := paid.pc + 1 }

private theorem pushSize_eq_reference (ctx : FrameCtx) (paid : Frame) (word : U256) :
    pushSize ctx paid word = pushSizeReference ctx paid word := by
  unfold pushSize pushSizeReference
  by_cases full : paid.stack.size = 1024
  · have rejected := (Stack.push_eq_error_iff paid.stack word .stackOverflow).mpr ⟨full, rfl⟩
    simp only [dite_eq_left full, rejected]
  · simp only [dite_eq_right full]
    split
    · rename_i error failed
      exact False.elim (size_push_fits paid.stack word error full failed)
    · rename_i stack pushed
      simp only [pushed]

private def sizeStep (price : Nat) (readSize : FrameCtx → Frame → Nat)
    (ctx : FrameCtx) (entry : Frame) : StepResult ctx :=
  match chargeGas entry.gasMeter price with
  | .error error => .halt entry error
  | .ok paid =>
    let word := U256.ofNat (readSize ctx entry)
    pushSize ctx { entry with gasMeter := paid } word

private def runSize {m : Type → Type} [Monad m] (price : FrameCtx → Nat)
    (readSize : FrameCtx → Frame → Nat) : Handler m :=
  fun ctx entry ↦ pure (sizeStep (price ctx) readSize ctx entry)

/-- Charge and push the size of this frame's call data.
Pinned EELS `src/ethereum/forks/amsterdam/vm/instructions/environment.py:185–205`. -/
def calldatasize {m : Type → Type} [Monad m] : Handler m :=
  runSize (·.config.costs.opcodeCallDataSize) (fun ctx _ ↦ ctx.callData.size)

/-- Charge and push the size of the executing code.
Pinned EELS `src/ethereum/forks/amsterdam/vm/instructions/environment.py:246–266`. -/
def codesize {m : Type → Type} [Monad m] : Handler m :=
  runSize (·.config.costs.opcodeCodeSize) (fun ctx _ ↦ ctx.code.size)

/-- Charge and push the size of the frame's current return data.
Pinned EELS `src/ethereum/forks/amsterdam/vm/instructions/environment.py:411–431`. -/
def returndatasize {m : Type → Type} [Monad m] : Handler m :=
  runSize (·.config.costs.opcodeReturnDataSize) (fun _ entry ↦ entry.returnData.size)

private theorem runSize_denied {m : Type → Type} [Monad m] (price : FrameCtx → Nat)
    (readSize : FrameCtx → Frame → Nat) (ctx : FrameCtx) (entry : Frame) (world : VmWorld m)
    (short : entry.gasMeter.gasLeft < price ctx) :
    ((runSize price readSize ctx entry).run world).run =
      pure (.ok (.halt entry .outOfGas, world)) := by
  have order := (chargeGas_eq_error_iff _ _ _).2 ⟨short, rfl⟩
  change pure (Except.ok (sizeStep (price ctx) readSize ctx entry, world)) = _
  simp only [sizeStep, order]

private theorem runSize_full {m : Type → Type} [Monad m] (price : FrameCtx → Nat)
    (readSize : FrameCtx → Frame → Nat) (ctx : FrameCtx) (entry : Frame) (world : VmWorld m)
    (payable : price ctx ≤ entry.gasMeter.gasLeft) (full : entry.stack.size = 1024) :
    ((runSize price readSize ctx entry).run world).run =
      pure (.ok (.halt { entry with gasMeter.gasLeft := entry.gasMeter.gasLeft - price ctx }
        .stackOverflow, world)) := by
  have rejected := (Stack.push_eq_error_iff entry.stack (U256.ofNat (readSize ctx entry))
    .stackOverflow).2 ⟨full, rfl⟩
  change pure (Except.ok (sizeStep (price ctx) readSize ctx entry, world)) = _
  simp only [sizeStep, chargeGas_of_le _ _ payable, pushSize_eq_reference, pushSizeReference, rejected]

private theorem runSize_success {m : Type → Type} [Monad m] (price : FrameCtx → Nat)
    (readSize : FrameCtx → Frame → Nat) (ctx : FrameCtx) (entry : Frame) (world : VmWorld m)
    (payable : price ctx ≤ entry.gasMeter.gasLeft) (space : entry.stack.size < 1024) :
    ∃ nextStack : Stack,
      nextStack.toList = U256.ofNat (readSize ctx entry) :: entry.stack.toList ∧
      ((runSize price readSize ctx entry).run world).run =
        pure (.ok (.continue { entry with
          stack := nextStack, gasMeter.gasLeft := entry.gasMeter.gasLeft - price ctx,
          pc := entry.pc + 1 }, world)) := by
  cases pushed : entry.stack.push (U256.ofNat (readSize ctx entry)) with
  | error fault => exact False.elim (size_push_fits _ _ fault (Nat.ne_of_lt space) pushed)
  | ok nextStack =>
    refine ⟨nextStack, ((Stack.push_eq_ok_iff _ _ _).1 pushed).2, ?_⟩
    change pure (Except.ok (sizeStep (price ctx) readSize ctx entry, world)) = _
    simp only [sizeStep, chargeGas_of_le _ _ payable, pushSize_eq_reference, pushSizeReference, pushed]

private theorem sizeWord_whole (size : Nat) (fits : size < 2^256) :
    (U256.ofNat size).toNat = size :=
  U256.toNat_ofNat_of_lt fits

private theorem sizeWord_firstExcluded : (U256.ofNat (2^256)).toNat = 0 := by
  rw [U256.toNat_ofNat, Nat.mod_self]

private theorem runSize_continue_phi (price : FrameCtx → Nat)
    (readSize : FrameCtx → Frame → Nat) (ctx : FrameCtx) (entry next : Frame)
    (world nextWorld : VmWorld Id)
    (ran : ((runSize price readSize ctx entry).run world).run = .ok (.continue next, nextWorld)) :
    next.gasMeter.phi + price ctx = entry.gasMeter.phi := by
  change Except.ok (sizeStep (price ctx) readSize ctx entry, world) = .ok (.continue next, nextWorld) at ran
  have stepResult := (Prod.mk.inj (Except.ok.inj ran)).1
  cases charged : chargeGas entry.gasMeter (price ctx) with
  | error error =>
    simp only [sizeStep, charged] at stepResult
    contradiction
  | ok paid =>
    cases pushed : entry.stack.push (U256.ofNat (readSize ctx entry)) with
    | error error =>
      simp only [sizeStep, charged, pushSize_eq_reference, pushSizeReference, pushed] at stepResult
      contradiction
    | ok stack =>
      simp only [sizeStep, charged, pushSize_eq_reference, pushSizeReference, pushed,
        StepResult.continue.injEq] at stepResult
      subst next
      exact chargeGas_phi _ _ paid charged

private theorem runSize_continue_progress (price : FrameCtx → Nat)
    (readSize : FrameCtx → Frame → Nat) (ctx : FrameCtx) (entry next : Frame)
    (world nextWorld : VmWorld Id)
    (ran : ((runSize price readSize ctx entry).run world).run = .ok (.continue next, nextWorld))
    (positive : 1 ≤ price ctx) :
    next.gasMeter.phi + 1 ≤ entry.gasMeter.phi := by
  have accounting := runSize_continue_phi price readSize ctx entry next world nextWorld ran
  omega

end STFSpec.Vm.Instructions
