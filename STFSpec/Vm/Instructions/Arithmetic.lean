/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions.Handler
import STFSpec.Base.U256Arithmetic

/-!
# ADD and SUB

Library `EthVmInstructions`. Ordered pops, execution charge, wrapping operation,
push and PC advance follow pinned EELS
`src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:25–76`.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§3/5/7.
-/

namespace STFSpec.Vm.Instructions
open STFSpec.Base STFSpec.Vm.Core

private def binary (ctx : FrameCtx) (f : Frame) (cost : Nat)
    (word : U256 → U256 → U256) : StepResult ctx :=
  match f.stack.pop with
  | .error e => .halt f e
  | .ok (x, s₁) =>
    match s₁.pop with
    | .error e => .halt { f with stack := s₁ } e
    | .ok (y, s₂) =>
      match chargeGas f.gasMeter cost with
      | .error e => .halt { f with stack := s₂ } e
      | .ok paid =>
        match s₂.push (word x y) with
        | .error e => .halt { f with stack := s₂, gasMeter := paid } e
        | .ok out => .continue { f with pc := f.pc + 1, stack := out, gasMeter := paid }

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

private theorem binary_empty (ctx : FrameCtx) (f : Frame) (c : Nat)
    (word : U256 → U256 → U256) (h : f.stack.toList = []) :
    binary ctx f c word = .halt f .stackUnderflow := by
  have hp := (Stack.pop_eq_error_iff f.stack .stackUnderflow).mpr ⟨h, rfl⟩
  simp only [binary, hp]

private theorem binary_singleton (ctx : FrameCtx) (f : Frame) (c : Nat)
    (word : U256 → U256 → U256) (x : U256) (h : f.stack.toList = [x]) :
    ∃ s₁, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      binary ctx f c word = .halt { f with stack := s₁ } .stackUnderflow := by
  obtain ⟨s₁, hp, hm⟩ := pop_of_model f.stack x [] h
  have he := (Stack.pop_eq_error_iff s₁ .stackUnderflow).mpr ⟨hm, rfl⟩
  exact ⟨s₁, hp, hm, by simp only [binary, hp, he]⟩

private theorem binary_oog (ctx : FrameCtx) (f : Frame) (c : Nat)
    (word : U256 → U256 → U256) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : f.gasMeter.gasLeft < c) :
    ∃ s₁ s₂, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ binary ctx f c word = .halt { f with stack := s₂ } .outOfGas := by
  obtain ⟨s₁, h₁, hm₁⟩ := pop_of_model f.stack x (y :: xs) h
  obtain ⟨s₂, h₂, hm₂⟩ := pop_of_model s₁ y xs hm₁
  have hg := (chargeGas_eq_error_iff f.gasMeter c .outOfGas).mpr ⟨hc, rfl⟩
  exact ⟨s₁, s₂, h₁, h₂, hm₂, by simp only [binary, h₁, h₂, hg]⟩

private theorem binary_success (ctx : FrameCtx) (f : Frame) (c : Nat)
    (word : U256 → U256 → U256) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : c ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (word x y) = .ok out ∧
      out.toList = word x y :: xs ∧
      binary ctx f c word = .continue { f with
        pc := f.pc + 1
        stack := out
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - c } } := by
  obtain ⟨s₁, h₁, hm₁⟩ := pop_of_model f.stack x (y :: xs) h
  obtain ⟨s₂, h₂, hm₂⟩ := pop_of_model s₁ y xs hm₁
  have hb := f.stack.size_le
  rw [Stack.size_eq_length_toList, h] at hb
  have hs : s₂.size < 1024 := by rw [Stack.size_eq_length_toList, hm₂]; simp at hb; omega
  cases hp : s₂.push (word x y) with
  | error e =>
    have he := (Stack.push_eq_error_iff s₂ (word x y) e).mp hp
    omega
  | ok out =>
    have hm := (Stack.push_eq_ok_iff s₂ out (word x y)).mp hp
    have hg := chargeGas_of_le f.gasMeter c hc
    refine ⟨s₁, s₂, out, h₁, h₂, hm₂, hp, ?_, ?_⟩
    · simpa only [hm₂] using hm.2
    · simp only [binary, h₁, h₂, hg, hp]

private theorem binary_continue_phi (ctx : FrameCtx) (f f' : Frame) (c : Nat)
    (word : U256 → U256 → U256) (h : binary ctx f c word = .continue f') :
    f'.gasMeter.phi + c = f.gasMeter.phi := by
  cases h₁ : f.stack.pop with
  | error e => simp only [binary, h₁] at h; contradiction
  | ok pair =>
    rcases pair with ⟨x, s₁⟩
    cases h₂ : s₁.pop with
    | error e => simp only [binary, h₁, h₂] at h; contradiction
    | ok pair =>
      rcases pair with ⟨y, s₂⟩
      cases hg : chargeGas f.gasMeter c with
      | error e => simp only [binary, h₁, h₂, hg] at h; contradiction
      | ok paid =>
        cases hp : s₂.push (word x y) with
        | error e => simp only [binary, h₁, h₂, hg, hp] at h; contradiction
        | ok out =>
          simp only [binary, h₁, h₂, hg, hp, StepResult.continue.injEq] at h
          subst f'
          exact chargeGas_phi f.gasMeter c paid hg

/-- Add the top two words after ordered pops and the selected execution charge.
EELS `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:25–49`. -/
def add {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (binary ctx f ctx.config.costs.opcodeAdd U256.add)

/-- Empty-stack underflow keeps the complete frame and supplied world. -/
theorem add_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((add ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) := by
  change pure (Except.ok (binary ctx f ctx.config.costs.opcodeAdd U256.add, w)) = _
  rw [binary_empty ctx f ctx.config.costs.opcodeAdd U256.add h]

/-- The first pop survives second-pop underflow, before any charge. -/
theorem add_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((add ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w)) := by
  obtain ⟨s₁, hp, hm, hr⟩ := binary_singleton ctx f ctx.config.costs.opcodeAdd U256.add x h
  refine ⟨s₁, hp, hm, ?_⟩
  change pure (Except.ok (binary ctx f ctx.config.costs.opcodeAdd U256.add, w)) = _
  rw [hr]

/-- Both pops survive an execution shortage; the complete meter remains unchanged. -/
theorem add_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeAdd) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((add ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  obtain ⟨s₁, s₂, h₁, h₂, hm, hr⟩ :=
    binary_oog ctx f ctx.config.costs.opcodeAdd U256.add x y xs h hc
  refine ⟨s₁, s₂, h₁, h₂, hm, ?_⟩
  change pure (Except.ok (binary ctx f ctx.config.costs.opcodeAdd U256.add, w)) = _
  rw [hr]

/-- Complete successful result, including proved push availability and whole-world retention. -/
theorem add_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : ctx.config.costs.opcodeAdd ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.add x y) = .ok out ∧
      out.toList = U256.add x y :: xs ∧
      ((add ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeAdd } }, w)) := by
  obtain ⟨s₁, s₂, out, h₁, h₂, hm, hp, ho, hr⟩ :=
    binary_success ctx f ctx.config.costs.opcodeAdd U256.add x y xs h hc
  refine ⟨s₁, s₂, out, h₁, h₂, hm, hp, ho, ?_⟩
  change pure (Except.ok (binary ctx f ctx.config.costs.opcodeAdd U256.add, w)) = _
  rw [hr]

/-- Every actual Id continuation loses exactly the selected raw opcode price. -/
theorem add_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((add ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeAdd = f.gasMeter.phi := by
  change Except.ok (binary ctx f ctx.config.costs.opcodeAdd U256.add, w) =
    .ok (.continue f', w') at h
  exact binary_continue_phi ctx f f' ctx.config.costs.opcodeAdd U256.add
    (Prod.mk.inj (Except.ok.inj h)).1

/-- Strict continuing progress requires only positivity of the selected price. -/
theorem add_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((add ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeAdd) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have hp := add_continue_phi ctx f f' w w' h
  omega

/-- Subtract the top two words after ordered pops and the selected execution charge.
EELS `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py:52–76`. -/
def sub {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (binary ctx f ctx.config.costs.opcodeSub U256.sub)

/-- Empty-stack underflow keeps the complete frame and supplied world. -/
theorem sub_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((sub ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) := by
  change pure (Except.ok (binary ctx f ctx.config.costs.opcodeSub U256.sub, w)) = _
  rw [binary_empty ctx f ctx.config.costs.opcodeSub U256.sub h]

/-- The first pop survives second-pop underflow, before any charge. -/
theorem sub_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((sub ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w)) := by
  obtain ⟨s₁, hp, hm, hr⟩ := binary_singleton ctx f ctx.config.costs.opcodeSub U256.sub x h
  refine ⟨s₁, hp, hm, ?_⟩
  change pure (Except.ok (binary ctx f ctx.config.costs.opcodeSub U256.sub, w)) = _
  rw [hr]

/-- Both pops survive an execution shortage; the complete meter remains unchanged. -/
theorem sub_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeSub) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((sub ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  obtain ⟨s₁, s₂, h₁, h₂, hm, hr⟩ :=
    binary_oog ctx f ctx.config.costs.opcodeSub U256.sub x y xs h hc
  refine ⟨s₁, s₂, h₁, h₂, hm, ?_⟩
  change pure (Except.ok (binary ctx f ctx.config.costs.opcodeSub U256.sub, w)) = _
  rw [hr]

/-- Complete successful result, including proved push availability and whole-world retention. -/
theorem sub_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : ctx.config.costs.opcodeSub ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.sub x y) = .ok out ∧
      out.toList = U256.sub x y :: xs ∧
      ((sub ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSub } }, w)) := by
  obtain ⟨s₁, s₂, out, h₁, h₂, hm, hp, ho, hr⟩ :=
    binary_success ctx f ctx.config.costs.opcodeSub U256.sub x y xs h hc
  refine ⟨s₁, s₂, out, h₁, h₂, hm, hp, ho, ?_⟩
  change pure (Except.ok (binary ctx f ctx.config.costs.opcodeSub U256.sub, w)) = _
  rw [hr]

/-- Every actual Id continuation loses exactly the selected raw opcode price. -/
theorem sub_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((sub ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeSub = f.gasMeter.phi := by
  change Except.ok (binary ctx f ctx.config.costs.opcodeSub U256.sub, w) =
    .ok (.continue f', w') at h
  exact binary_continue_phi ctx f f' ctx.config.costs.opcodeSub U256.sub
    (Prod.mk.inj (Except.ok.inj h)).1

/-- Strict continuing progress requires only positivity of the selected price. -/
theorem sub_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((sub ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeSub) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have hp := sub_continue_phi ctx f f' w w' h
  omega

end STFSpec.Vm.Instructions
