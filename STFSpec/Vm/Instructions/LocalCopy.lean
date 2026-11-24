/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.Numeric
import STFSpec.Vm.Core.MemoryGas
import STFSpec.Vm.Instructions.Handler

/-!
# Copy from call data or executing code

Library `EthVmInstructions`. CALLDATACOPY and CODECOPY pop three words, charge
for the destination window and copy the padded input after payment.
See `STFSpec/informal/modules/EthVmInstructions.md`.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base STFSpec.Vm.Core

private def copyPopReference (f : Frame) : Except (Frame × ExceptionalHalt) (U256 × Frame) :=
  match f.stack.pop with
  | .error error => .error (f, error)
  | .ok (word, stack) => .ok (word, { f with stack })

private theorem copy_pop_nonempty (f : Frame) (error : ExceptionalHalt)
    (nonempty : 0 < f.stack.size) (failed : f.stack.pop = .error error) : False := by
  have empty := ((Stack.pop_eq_error_iff f.stack error).mp failed).1
  simp [Stack.size_eq_length_toList, empty] at nonempty

private def copyPop (f : Frame) : Except (Frame × ExceptionalHalt) (U256 × Frame) :=
  if nonempty : 0 < f.stack.size then
    match popped : f.stack.pop with
    | .error error => False.elim (copy_pop_nonempty f error nonempty popped)
    | .ok (word, stack) => .ok (word, { f with stack })
  else
    copyPopReference f

private theorem copyPop_eq_reference (f : Frame) : copyPop f = copyPopReference f := by
  unfold copyPop
  split
  · rename_i nonempty
    unfold copyPopReference
    split
    · rename_i error failed
      exact False.elim (copy_pop_nonempty f error nonempty failed)
    · rename_i word stack popped
      rw [popped]
  · rfl

private abbrev copyQuote (cfg : VmConfig) (memory : Memory) (destination length : U256) : ExtendMemory :=
  calculateGasExtendMemory cfg memory [(destination, length)]

private def copyCharge (cfg : VmConfig) (base : Nat) (length : U256) (quote : ExtendMemory) : Nat :=
  base + cfg.costs.opcodeCopyPerWord * (ceil32 length.toNat / 32) + quote.cost

private theorem copy_expanded_size (memory : Memory) (extent : Nat) (aligned : extent % 32 = 0) :
    (memory.expand extent aligned).size = memory.size + extent := by
  rw [← Memory.length_toBytes, Memory.toBytes_expand, List.length_append,
    Memory.length_toBytes, List.length_replicate]

private def copyWindow (source : Bytes) (destination offset length : U256)
    (memory : Memory) (extent : Nat) (aligned : extent % 32 = 0)
    (covered : length.toNat = 0 ∨ destination.toNat + length.toNat ≤ memory.size + extent) : Memory :=
  let expanded := memory.expand extent aligned
  let value := bufferRead source offset length
  expanded.write destination.toNat value (by
    rw [bufferRead_size, copy_expanded_size]
    exact covered)

private theorem copyWindow_toBytes (source : Bytes) (destination offset length : U256)
    (memory : Memory) (extent : Nat) (aligned : extent % 32 = 0)
    (covered : length.toNat = 0 ∨ destination.toNat + length.toNat ≤ memory.size + extent) :
    let bytes := memory.toBytes ++ List.replicate extent 0
    (copyWindow source destination offset length memory extent aligned covered).toBytes =
      bytes.take destination.toNat ++ (bufferRead source offset length).toList ++
        bytes.drop (destination.toNat + length.toNat) := by
  dsimp only [copyWindow]
  rw [Memory.toBytes_write, Memory.toBytes_expand, bufferRead_size]

private def copyAdvance (ctx : FrameCtx) (f : Frame) (meter : GasMeter)
    (update : (memory : Memory) → memory = f.memory → Memory) : StepResult ctx :=
  match f with
  | ⟨pc, stack, memory, _, logs, deleted, ret, addresses, slots⟩ =>
    .continue ⟨pc + 1, stack, update memory rfl, meter, logs, deleted, ret, addresses, slots⟩

private theorem copyAdvance_eq (ctx : FrameCtx) (f : Frame) (meter : GasMeter)
    (update : (memory : Memory) → memory = f.memory → Memory) :
    copyAdvance ctx f meter update =
      .continue { f with pc := f.pc + 1, memory := update f.memory rfl, gasMeter := meter } := by
  cases f
  rfl

private def localCopyAfterPops (source : Bytes) (base : Nat) (ctx : FrameCtx) (f : Frame)
    (destination offset length : U256) : StepResult ctx :=
  let quote := copyQuote ctx.config f.memory destination length
  match chargeGas f.gasMeter (copyCharge ctx.config base length quote) with
  | .error error => .halt f error
  | .ok meter =>
    have covered := calculateGasExtendMemory_covers ctx.config f.memory
      [(destination, length)] destination length (by simp)
    copyAdvance ctx f meter fun memory same ↦
      copyWindow source destination offset length memory quote.expandBy
        (calculateGasExtendMemory_aligned ctx.config f.memory [(destination, length)])
        (same.symm ▸ covered)

private def localCopyResult (source : Bytes) (base : Nat) (ctx : FrameCtx) (f : Frame) :
    StepResult ctx :=
  match copyPop f with
  | .error (residual, error) => .halt residual error
  | .ok (destination, rest) =>
    match copyPop rest with
    | .error (residual, error) => .halt residual error
    | .ok (offset, rest) =>
      match copyPop rest with
      | .error (residual, error) => .halt residual error
      | .ok (length, residual) => localCopyAfterPops source base ctx residual destination offset length

private def runLocalCopy {m : Type → Type} [Monad m]
    (source : FrameCtx → Bytes) (base : VmConfig → Nat) : Handler m :=
  fun ctx f ↦ pure (localCopyResult (source ctx) (base ctx.config) ctx f)

/-- Copy the padded frame call data into the charged destination memory window.
Pinned EELS `src/ethereum/forks/amsterdam/vm/instructions/environment.py:208–243`. -/
def calldatacopy {m : Type → Type} [Monad m] : Handler m :=
  runLocalCopy (·.callData) (·.costs.opcodeCallDataCopyBase)

/-- Copy the padded executing code into the charged destination memory window.
Pinned EELS `src/ethereum/forks/amsterdam/vm/instructions/environment.py:269–304`. -/
def codecopy {m : Type → Type} [Monad m] : Handler m :=
  runLocalCopy (·.code) (·.costs.opcodeCodeCopyBase)

private theorem localCopy_of_pops (source : Bytes) (base : Nat) (ctx : FrameCtx) (f : Frame)
    (destination offset length : U256) (s₁ s₂ s₃ : Stack)
    (first : f.stack.pop = .ok (destination, s₁)) (second : s₁.pop = .ok (offset, s₂))
    (third : s₂.pop = .ok (length, s₃)) :
    localCopyResult source base ctx f =
      localCopyAfterPops source base ctx { f with stack := s₃ } destination offset length := by
  simp only [localCopyResult, copyPop_eq_reference, copyPopReference, first, second, third]

private theorem localCopy_run_first_underflow {m : Type → Type} [Monad m]
    (source : FrameCtx → Bytes) (base : VmConfig → Nat)
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (missing : f.stack.pop = .error .stackUnderflow) :
    ((runLocalCopy source base ctx f).run w).run = pure (.ok (.halt f .stackUnderflow, w)) := by
  change pure (Except.ok (localCopyResult (source ctx) (base ctx.config) ctx f, w)) = _
  simp only [localCopyResult, copyPop_eq_reference, copyPopReference, missing]

private theorem localCopy_run_second_underflow {m : Type → Type} [Monad m]
    (source : FrameCtx → Bytes) (base : VmConfig → Nat)
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (destination : U256) (s₁ : Stack)
    (first : f.stack.pop = .ok (destination, s₁)) (missing : s₁.pop = .error .stackUnderflow) :
    ((runLocalCopy source base ctx f).run w).run =
      pure (.ok (.halt { f with stack := s₁ } .stackUnderflow, w)) := by
  change pure (Except.ok (localCopyResult (source ctx) (base ctx.config) ctx f, w)) = _
  simp only [localCopyResult, copyPop_eq_reference, copyPopReference, first, missing]

private theorem localCopy_run_third_underflow {m : Type → Type} [Monad m]
    (source : FrameCtx → Bytes) (base : VmConfig → Nat)
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (destination offset : U256) (s₁ s₂ : Stack)
    (first : f.stack.pop = .ok (destination, s₁)) (second : s₁.pop = .ok (offset, s₂))
    (missing : s₂.pop = .error .stackUnderflow) :
    ((runLocalCopy source base ctx f).run w).run =
      pure (.ok (.halt { f with stack := s₂ } .stackUnderflow, w)) := by
  change pure (Except.ok (localCopyResult (source ctx) (base ctx.config) ctx f, w)) = _
  simp only [localCopyResult, copyPop_eq_reference, copyPopReference, first, second, missing]

private theorem localCopy_run_denied {m : Type → Type} [Monad m]
    (source : FrameCtx → Bytes) (base : VmConfig → Nat) (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (destination offset length : U256) (s₁ s₂ s₃ : Stack)
    (first : f.stack.pop = .ok (destination, s₁)) (second : s₁.pop = .ok (offset, s₂))
    (third : s₂.pop = .ok (length, s₃))
    (short : f.gasMeter.gasLeft < copyCharge ctx.config (base ctx.config) length
      (copyQuote ctx.config f.memory destination length)) :
    ((runLocalCopy source base ctx f).run w).run =
      pure (.ok (.halt { f with stack := s₃ } .outOfGas, w)) := by
  have denied := (chargeGas_eq_error_iff _ _ _).2 ⟨short, rfl⟩
  change pure (Except.ok (localCopyResult (source ctx) (base ctx.config) ctx f, w)) = _
  rw [localCopy_of_pops _ _ _ _ _ _ _ _ _ _ first second third]
  simp only [localCopyAfterPops, denied]

private theorem localCopy_run_success {m : Type → Type} [Monad m]
    (source : FrameCtx → Bytes) (base : VmConfig → Nat) (ctx : FrameCtx) (f : Frame) (w : VmWorld m)
    (destination offset length : U256) (s₁ s₂ s₃ : Stack)
    (first : f.stack.pop = .ok (destination, s₁)) (second : s₁.pop = .ok (offset, s₂))
    (third : s₂.pop = .ok (length, s₃))
    (enough : copyCharge ctx.config (base ctx.config) length
      (copyQuote ctx.config f.memory destination length) ≤ f.gasMeter.gasLeft) :
    let quote := copyQuote ctx.config f.memory destination length
    let price := copyCharge ctx.config (base ctx.config) length quote
    let bytes := f.memory.toBytes ++ List.replicate quote.expandBy 0
    ∃ memory : Memory,
      memory.toBytes = bytes.take destination.toNat ++ (bufferRead (source ctx) offset length).toList ++
        bytes.drop (destination.toNat + length.toNat) ∧
      ((runLocalCopy source base ctx f).run w).run =
        pure (.ok (.continue { f with
          stack := s₃, memory, pc := f.pc + 1,
          gasMeter.gasLeft := f.gasMeter.gasLeft - price }, w)) := by
  let quote := copyQuote ctx.config f.memory destination length
  let aligned := calculateGasExtendMemory_aligned ctx.config f.memory [(destination, length)]
  have covered := calculateGasExtendMemory_covers ctx.config f.memory
    [(destination, length)] destination length (by simp)
  refine ⟨copyWindow (source ctx) destination offset length f.memory quote.expandBy aligned covered,
    copyWindow_toBytes _ _ _ _ _ _ _ _, ?_⟩
  change pure (Except.ok (localCopyResult (source ctx) (base ctx.config) ctx f, w)) = _
  rw [localCopy_of_pops _ _ _ _ _ _ _ _ _ _ first second third]
  simp only [localCopyAfterPops, chargeGas_of_le _ _ enough, copyAdvance_eq]
  rfl

private theorem localCopy_empty_quote (cfg : VmConfig) (memory : Memory) (destination : U256) :
    copyQuote cfg memory destination U256.zero = ⟨cfg.costs.zero, 0⟩ := by
  have erased := calculateGasExtendMemory_zero cfg memory [] [] destination
  exact erased.trans (calculateGasExtendMemory_nil cfg memory)

private theorem copyWindow_empty (source : Bytes) (destination offset : U256) (memory : Memory)
    (covered : U256.zero.toNat = 0 ∨ destination.toNat + U256.zero.toNat ≤ memory.size + 0) :
    copyWindow source destination offset U256.zero memory 0 (by decide) covered = memory := by
  have empty : bufferRead source offset U256.zero = Bytes.empty := Bytes.size_eq_zero_iff.mp (by
    rw [bufferRead_size]
    rfl)
  simp only [copyWindow, empty, Memory.write_empty]
  cases memory
  rfl

private theorem localCopy_continue_phi (source : FrameCtx → Bytes) (base : VmConfig → Nat)
    (ctx : FrameCtx) (f next : Frame) (w w' : VmWorld Id)
    (destination offset length : U256) (s₁ s₂ s₃ : Stack)
    (first : f.stack.pop = .ok (destination, s₁)) (second : s₁.pop = .ok (offset, s₂))
    (third : s₂.pop = .ok (length, s₃))
    (ran : ((runLocalCopy source base ctx f).run w).run = .ok (.continue next, w')) :
    next.gasMeter.phi + copyCharge ctx.config (base ctx.config) length
      (copyQuote ctx.config f.memory destination length) = f.gasMeter.phi := by
  change Except.ok (localCopyResult (source ctx) (base ctx.config) ctx f, w) = .ok (.continue next, w') at ran
  have step := (Prod.mk.inj (Except.ok.inj ran)).1
  rw [localCopy_of_pops _ _ _ _ _ _ _ _ _ _ first second third] at step
  cases paid : chargeGas f.gasMeter
      (copyCharge ctx.config (base ctx.config) length (copyQuote ctx.config f.memory destination length)) with
  | error error =>
    simp only [localCopyAfterPops, paid] at step
    contradiction
  | ok meter =>
    simp only [localCopyAfterPops, paid, copyAdvance_eq, StepResult.continue.injEq] at step
    subst next
    exact chargeGas_phi _ _ meter paid

private theorem localCopy_continue_progress (source : FrameCtx → Bytes) (base : VmConfig → Nat)
    (ctx : FrameCtx) (f next : Frame) (w w' : VmWorld Id)
    (destination offset length : U256) (s₁ s₂ s₃ : Stack)
    (first : f.stack.pop = .ok (destination, s₁)) (second : s₁.pop = .ok (offset, s₂))
    (third : s₂.pop = .ok (length, s₃))
    (ran : ((runLocalCopy source base ctx f).run w).run = .ok (.continue next, w'))
    (positive : 1 ≤ copyCharge ctx.config (base ctx.config) length
      (copyQuote ctx.config f.memory destination length)) :
    next.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have accounting := localCopy_continue_phi source base ctx f next w w' destination offset length
    s₁ s₂ s₃ first second third ran
  omega

end STFSpec.Vm.Instructions
