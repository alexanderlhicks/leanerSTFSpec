/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions.Handler
import STFSpec.Vm.Core.MemoryGas

/-!
# RETURN and REVERT

Library `EthVmInstructions`. Both handlers pop the memory offset and length,
pay the selected charge, and return the exact expanded-memory window.
Spec guidance `STFSpec/informal/modules/EthVmInstructions.md` Q92.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base STFSpec.Vm.Core

private theorem window_fits (cfg : VmConfig) (memory : Memory) (off len : U256) :
    let expansion := calculateGasExtendMemory cfg memory [(off, len)]
    let expanded := memory.expand expansion.expandBy
      (calculateGasExtendMemory_aligned cfg memory [(off, len)])
    len.toNat = 0 ∨ off.toNat + len.toNat ≤ expanded.size := by
  dsimp only
  rw [← Memory.length_toBytes, Memory.toBytes_expand, List.length_append,
    Memory.length_toBytes, List.length_replicate]
  exact calculateGasExtendMemory_covers cfg memory [(off, len)] off len (by simp)

private def popFrameReference (f : Frame) : Except (Frame × ExceptionalHalt) (U256 × Frame) :=
  match f.stack.pop with
  | .error error => .error (f, error)
  | .ok (value, stack) => .ok (value, { f with stack })

private theorem pop_error_of_nonempty (f : Frame) (error : ExceptionalHalt)
    (nonempty : 0 < f.stack.size) (failed : f.stack.pop = .error error) : False := by
  have observed := (Stack.pop_eq_error_iff f.stack error).mp failed
  simp [Stack.size_eq_length_toList, observed.1] at nonempty

private def popFrame (f : Frame) : Except (Frame × ExceptionalHalt) (U256 × Frame) :=
  if nonempty : 0 < f.stack.size then
    match popped : f.stack.pop with
    | .error error => False.elim (pop_error_of_nonempty f error nonempty popped)
    | .ok (value, stack) => .ok (value, { f with stack })
  else
    popFrameReference f

private theorem popFrame_eq (f : Frame) : popFrame f = popFrameReference f := by
  unfold popFrame
  split
  · rename_i nonempty
    unfold popFrameReference
    split
    · rename_i error failed
      exact False.elim (pop_error_of_nonempty f error nonempty failed)
    · rename_i value stack popped
      rw [popped]
  · rfl

private def terminateFromMemory (reverting : Bool) (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  match popFrame f with
  | .error (frame, error) => .halt frame error
  | .ok (off, first) =>
    match popFrame first with
    | .error (frame, error) => .halt frame error
    | .ok (len, residual) =>
      let expansion := calculateGasExtendMemory ctx.config residual.memory [(off, len)]
      let cost := if reverting then expansion.cost else ctx.config.costs.zero + expansion.cost
      match chargeGas residual.gasMeter cost with
      | .error error => .halt residual error
      | .ok gasMeter =>
        let memory := residual.memory.expand expansion.expandBy
          (calculateGasExtendMemory_aligned ctx.config residual.memory [(off, len)])
        let output := memory.readBytes off.toNat len.toNat (window_fits ctx.config residual.memory off len)
        let terminal := { residual with gasMeter, memory }
        if reverting then .revert terminal output else .stop terminal output

/-- Pop offset and length, pay the explicit ZERO and the extension cost, and stop.
EELS `src/ethereum/forks/amsterdam/vm/instructions/system.py:307–337` at the pin. -/
def return_ {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (terminateFromMemory false ctx f)

/-- Pop offset and length, pay the extension cost, and return the revert output.
EELS `src/ethereum/forks/amsterdam/vm/instructions/system.py:987–1016` at the pin. -/
def revert {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (terminateFromMemory true ctx f)

/-- RETURN's first underflow retains the entry frame and world. -/
theorem return_run_first_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (first : f.stack.pop = .error .stackUnderflow) :
    ((return_ ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) := by
  change pure (Except.ok (terminateFromMemory false ctx f, w)) = _
  simp [terminateFromMemory, popFrame_eq, popFrameReference, first]

/-- RETURN's second underflow retains the first actual residual stack. -/
theorem return_run_second_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off : U256) (s₁ : Stack)
    (first : f.stack.pop = .ok (off, s₁)) (second : s₁.pop = .error .stackUnderflow) :
    ((return_ ctx f).run w).run =
      pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w)) := by
  change pure (Except.ok (terminateFromMemory false ctx f, w)) = _
  simp [terminateFromMemory, popFrame_eq, popFrameReference, first, second]

/-- RETURN's gas denial retains both actual pops and the entry meter and memory. -/
theorem return_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off len : U256) (s₁ s₂ : Stack)
    (first : f.stack.pop = .ok (off, s₁)) (second : s₁.pop = .ok (len, s₂))
    (short : f.gasMeter.gasLeft <
      ctx.config.costs.zero + (calculateGasExtendMemory ctx.config f.memory [(off, len)]).cost) :
    ((return_ ctx f).run w).run =
      pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  change pure (Except.ok (terminateFromMemory false ctx f, w)) = _
  have denied := (chargeGas_eq_error_iff f.gasMeter
    (ctx.config.costs.zero + (calculateGasExtendMemory ctx.config f.memory [(off, len)]).cost)
    .outOfGas).2 ⟨short, rfl⟩
  simp [terminateFromMemory, popFrame_eq, popFrameReference, first, second, denied]

/-- Paid RETURN supplies the exact expanded window with the complete terminal frame. -/
theorem return_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off len : U256) (s₁ s₂ : Stack)
    (first : f.stack.pop = .ok (off, s₁)) (second : s₁.pop = .ok (len, s₂))
    (enough : ctx.config.costs.zero + (calculateGasExtendMemory ctx.config f.memory [(off, len)]).cost
      ≤ f.gasMeter.gasLeft) :
    let expansion := calculateGasExtendMemory ctx.config f.memory [(off, len)]
    let memory := f.memory.expand expansion.expandBy
      (calculateGasExtendMemory_aligned ctx.config f.memory [(off, len)])
    let output := memory.readBytes off.toNat len.toNat (window_fits ctx.config f.memory off len)
    ((return_ ctx f).run w).run = pure (Except.ok (.stop { f with
      stack := s₂
      memory
      gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - (ctx.config.costs.zero + expansion.cost) }
    } output, w)) := by
  change pure (Except.ok (terminateFromMemory false ctx f, w)) = _
  have paid := chargeGas_of_le f.gasMeter
    (ctx.config.costs.zero + (calculateGasExtendMemory ctx.config f.memory [(off, len)]).cost) enough
  simp [terminateFromMemory, popFrame_eq, popFrameReference, first, second, paid]

/-- REVERT's first underflow retains the entry frame and world. -/
theorem revert_run_first_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (first : f.stack.pop = .error .stackUnderflow) :
    ((revert ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) := by
  change pure (Except.ok (terminateFromMemory true ctx f, w)) = _
  simp [terminateFromMemory, popFrame_eq, popFrameReference, first]

/-- REVERT's second underflow retains the first actual residual stack. -/
theorem revert_run_second_underflow {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off : U256) (s₁ : Stack)
    (first : f.stack.pop = .ok (off, s₁)) (second : s₁.pop = .error .stackUnderflow) :
    ((revert ctx f).run w).run =
      pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w)) := by
  change pure (Except.ok (terminateFromMemory true ctx f, w)) = _
  simp [terminateFromMemory, popFrame_eq, popFrameReference, first, second]

/-- REVERT's gas denial retains both actual pops and the entry meter and memory. -/
theorem revert_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off len : U256) (s₁ s₂ : Stack)
    (first : f.stack.pop = .ok (off, s₁)) (second : s₁.pop = .ok (len, s₂))
    (short : f.gasMeter.gasLeft < (calculateGasExtendMemory ctx.config f.memory [(off, len)]).cost) :
    ((revert ctx f).run w).run =
      pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  change pure (Except.ok (terminateFromMemory true ctx f, w)) = _
  have denied := (chargeGas_eq_error_iff f.gasMeter
    (calculateGasExtendMemory ctx.config f.memory [(off, len)]).cost .outOfGas).2 ⟨short, rfl⟩
  simp [terminateFromMemory, popFrame_eq, popFrameReference, first, second, denied]

/-- Paid REVERT supplies the exact expanded window with the complete terminal frame. -/
theorem revert_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (off len : U256) (s₁ s₂ : Stack)
    (first : f.stack.pop = .ok (off, s₁)) (second : s₁.pop = .ok (len, s₂))
    (enough : (calculateGasExtendMemory ctx.config f.memory [(off, len)]).cost ≤ f.gasMeter.gasLeft) :
    let expansion := calculateGasExtendMemory ctx.config f.memory [(off, len)]
    let memory := f.memory.expand expansion.expandBy
      (calculateGasExtendMemory_aligned ctx.config f.memory [(off, len)])
    let output := memory.readBytes off.toNat len.toNat (window_fits ctx.config f.memory off len)
    ((revert ctx f).run w).run = pure (Except.ok (.revert { f with
      stack := s₂
      memory
      gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - expansion.cost }
    } output, w)) := by
  change pure (Except.ok (terminateFromMemory true ctx f, w)) = _
  have paid := chargeGas_of_le f.gasMeter
    (calculateGasExtendMemory ctx.config f.memory [(off, len)]).cost enough
  simp [terminateFromMemory, popFrame_eq, popFrameReference, first, second, paid]

end STFSpec.Vm.Instructions
