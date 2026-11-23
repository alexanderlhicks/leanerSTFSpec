/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions.Handler
import STFSpec.Base.U256Bitwise

/-!
# AND, OR, XOR and NOT

Library `EthVmInstructions`. The handlers use the word model from EthBase and
the stack and meter operations from EthVmCore.
Spec guidance is in `STFSpec/informal/modules/EthVmInstructions.md` §§3/5/7.
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

private def unary (ctx : FrameCtx) (f : Frame) (cost : Nat)
    (word : U256 → U256) : StepResult ctx :=
  match f.stack.pop with
  | .error e => .halt f e
  | .ok (x, stack) =>
    match chargeGas f.gasMeter cost with
    | .error e => .halt { f with stack } e
    | .ok paid =>
      match stack.push (word x) with
      | .error e => .halt { f with stack, gasMeter := paid } e
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

private theorem pop_empty (s : Stack) (empty : s.size = 0) :
    s.pop = .error .stackUnderflow := by
  rw [Stack.size_eq_length_toList] at empty
  exact (Stack.pop_eq_error_iff s .stackUnderflow).mpr
    ⟨List.length_eq_zero_iff.mp empty, rfl⟩

private theorem pop_not_error (s : Stack) (e : ExceptionalHalt)
    (nonempty : s.size ≠ 0) (hp : s.pop = .error e) : False := by
  have empty := ((Stack.pop_eq_error_iff s e).mp hp).1
  apply nonempty
  simp [Stack.size_eq_length_toList, empty]

private theorem push_not_error (s t : Stack) (x v : U256) (e : ExceptionalHalt)
    (hp : s.pop = .ok (x, t)) (he : t.push v = .error e) : False := by
  have bound := s.size_le
  have popped := (Stack.pop_eq_ok_iff s t x).mp hp
  have full := ((Stack.push_eq_error_iff t v e).mp he).1
  rw [Stack.size_eq_length_toList, popped, List.length_cons] at bound
  rw [Stack.size_eq_length_toList] at full
  omega

/-- Keep the entry stack only on the underflow branch. -/
private def unaryLinear (ctx : FrameCtx) (f : Frame) (cost : Nat)
    (word : U256 → U256) : StepResult ctx :=
  if empty : f.stack.size = 0 then
    .halt f .stackUnderflow
  else
    match pop : f.stack.pop with
    | .error e => False.elim (pop_not_error f.stack e empty pop)
    | .ok (x, stack) =>
      match chargeGas f.gasMeter cost with
      | .error e => .halt { f with stack } e
      | .ok paid =>
        match push : stack.push (word x) with
        | .error e => False.elim (push_not_error f.stack stack x (word x) e pop push)
        | .ok out => .continue { f with pc := f.pc + 1, stack := out, gasMeter := paid }

private theorem unaryLinear_eq_unary (ctx : FrameCtx) (f : Frame) (cost : Nat)
    (word : U256 → U256) :
    unaryLinear ctx f cost word = unary ctx f cost word := by
  unfold unaryLinear unary
  split
  · rename_i empty
    rw [pop_empty f.stack empty]
  · rename_i nonempty
    split
    · rename_i e pop
      exact False.elim (pop_not_error f.stack e nonempty pop)
    · rename_i x stack pop
      simp only [pop]
      split
      · rfl
      · split
        · rename_i e push
          exact False.elim (push_not_error f.stack stack x (word x) e pop push)
        · rename_i out push
          simp only [push]

/-- Keep each residual stack only through the last branch that can return it. -/
private def binaryLinear (ctx : FrameCtx) (f : Frame) (cost : Nat)
    (word : U256 → U256 → U256) : StepResult ctx :=
  if empty₁ : f.stack.size = 0 then
    .halt f .stackUnderflow
  else
    match pop₁ : f.stack.pop with
    | .error e => False.elim (pop_not_error f.stack e empty₁ pop₁)
    | .ok (x, s₁) =>
      if empty₂ : s₁.size = 0 then
        .halt { f with stack := s₁ } .stackUnderflow
      else
        match pop₂ : s₁.pop with
        | .error e => False.elim (pop_not_error s₁ e empty₂ pop₂)
        | .ok (y, s₂) =>
          match chargeGas f.gasMeter cost with
          | .error e => .halt { f with stack := s₂ } e
          | .ok paid =>
            match push : s₂.push (word x y) with
            | .error e => False.elim (push_not_error s₁ s₂ y (word x y) e pop₂ push)
            | .ok out => .continue { f with pc := f.pc + 1, stack := out, gasMeter := paid }

private theorem binaryLinear_eq_binary (ctx : FrameCtx) (f : Frame) (cost : Nat)
    (word : U256 → U256 → U256) :
    binaryLinear ctx f cost word = binary ctx f cost word := by
  unfold binaryLinear binary
  split
  · rename_i empty
    rw [pop_empty f.stack empty]
  · rename_i nonempty₁
    split
    · rename_i e hp₁
      exact False.elim (pop_not_error f.stack e nonempty₁ hp₁)
    · rename_i x s₁ hp₁
      simp only [hp₁]
      split
      · rename_i empty₂
        simp only [pop_empty s₁ empty₂]
      · rename_i nonempty₂
        split
        · rename_i e hp₂
          exact False.elim (pop_not_error s₁ e nonempty₂ hp₂)
        · rename_i y s₂ hp₂
          simp only [hp₂]
          split
          · rfl
          · split
            · rename_i e he
              exact False.elim (push_not_error s₁ s₂ y _ e hp₂ he)
            · rename_i out push
              simp only [push]

private theorem binary_empty (ctx : FrameCtx) (f : Frame) (c : Nat)
    (word : U256 → U256 → U256) (h : f.stack.toList = []) :
    binaryLinear ctx f c word = .halt f .stackUnderflow := by
  have hp := (Stack.pop_eq_error_iff f.stack .stackUnderflow).mpr ⟨h, rfl⟩
  simp only [binaryLinear_eq_binary, binary, hp]

private theorem binary_singleton (ctx : FrameCtx) (f : Frame) (c : Nat)
    (word : U256 → U256 → U256) (x : U256) (h : f.stack.toList = [x]) :
    ∃ s₁, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      binaryLinear ctx f c word = .halt { f with stack := s₁ } .stackUnderflow := by
  obtain ⟨s₁, hp, hm⟩ := pop_of_model f.stack x [] h
  have he := (Stack.pop_eq_error_iff s₁ .stackUnderflow).mpr ⟨hm, rfl⟩
  exact ⟨s₁, hp, hm, by simp only [binaryLinear_eq_binary, binary, hp, he]⟩

private theorem binary_oog (ctx : FrameCtx) (f : Frame) (c : Nat)
    (word : U256 → U256 → U256) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : f.gasMeter.gasLeft < c) :
    ∃ s₁ s₂, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧
      binaryLinear ctx f c word = .halt { f with stack := s₂ } .outOfGas := by
  obtain ⟨s₁, h₁, hm₁⟩ := pop_of_model f.stack x (y :: xs) h
  obtain ⟨s₂, h₂, hm₂⟩ := pop_of_model s₁ y xs hm₁
  have hg := (chargeGas_eq_error_iff f.gasMeter c .outOfGas).mpr ⟨hc, rfl⟩
  refine ⟨s₁, s₂, h₁, h₂, hm₂, ?_⟩
  simp only [binaryLinear_eq_binary, binary, h₁, h₂, hg]

private theorem binary_success (ctx : FrameCtx) (f : Frame) (c : Nat)
    (word : U256 → U256 → U256) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : c ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (word x y) = .ok out ∧
      out.toList = word x y :: xs ∧
      binaryLinear ctx f c word = .continue { f with
        pc := f.pc + 1
        stack := out
        gasMeter := { f.gasMeter with gasLeft := f.gasMeter.gasLeft - c } } := by
  obtain ⟨s₁, h₁, hm₁⟩ := pop_of_model f.stack x (y :: xs) h
  obtain ⟨s₂, h₂, hm₂⟩ := pop_of_model s₁ y xs hm₁
  have hb := f.stack.size_le
  rw [Stack.size_eq_length_toList, h] at hb
  have hs : s₂.size < 1024 := by
    rw [Stack.size_eq_length_toList, hm₂]
    simp only [List.length_cons] at hb
    omega
  cases hp : s₂.push (word x y) with
  | error e =>
    have he := (Stack.push_eq_error_iff s₂ (word x y) e).mp hp
    omega
  | ok out =>
    have hm := (Stack.push_eq_ok_iff s₂ out (word x y)).mp hp
    have hg := chargeGas_of_le f.gasMeter c hc
    refine ⟨s₁, s₂, out, h₁, h₂, hm₂, hp, ?_, ?_⟩
    · simpa only [hm₂] using hm.2
    · simp only [binaryLinear_eq_binary, binary, h₁, h₂, hg, hp]

private theorem binary_continue_phi (ctx : FrameCtx) (f f' : Frame) (c : Nat)
    (word : U256 → U256 → U256) (h : binaryLinear ctx f c word = .continue f') :
    f'.gasMeter.phi + c = f.gasMeter.phi := by
  rw [binaryLinear_eq_binary] at h
  cases h₁ : f.stack.pop with
  | error e =>
    simp only [binary, h₁] at h
    contradiction
  | ok pair =>
    rcases pair with ⟨x, s₁⟩
    cases h₂ : s₁.pop with
    | error e =>
      simp only [binary, h₁, h₂] at h
      contradiction
    | ok pair =>
      rcases pair with ⟨y, s₂⟩
      cases hg : chargeGas f.gasMeter c with
      | error e =>
        simp only [binary, h₁, h₂, hg] at h
        contradiction
      | ok paid =>
        cases hp : s₂.push (word x y) with
        | error e =>
          simp only [binary, h₁, h₂, hg, hp] at h
          contradiction
        | ok out =>
          simp only [binary, h₁, h₂, hg, hp, StepResult.continue.injEq] at h
          subst f'
          exact chargeGas_phi f.gasMeter c paid hg

/-- Push the bitwise AND of the two popped words after charging and advance the PC.
EELS `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:21–43`. -/
def bitwiseAnd {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (binaryLinear ctx f ctx.config.costs.opcodeAnd U256.and)

/-- First-pop underflow retains the complete frame and world. -/
theorem bitwiseAnd_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((bitwiseAnd ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) := by
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeAnd U256.and, w)) = _
  rw [binary_empty ctx f ctx.config.costs.opcodeAnd U256.and h]

/-- Second-pop underflow retains the first pop and precedes the charge. -/
theorem bitwiseAnd_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((bitwiseAnd ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w)) := by
  obtain ⟨s₁, hp, hm, hr⟩ := binary_singleton ctx f ctx.config.costs.opcodeAnd U256.and x h
  refine ⟨s₁, hp, hm, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeAnd U256.and, w)) = _
  rw [hr]

/-- A denied charge retains both pops and the complete entry meter. -/
theorem bitwiseAnd_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeAnd) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((bitwiseAnd ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  obtain ⟨s₁, s₂, h₁, h₂, hm, hr⟩ :=
    binary_oog ctx f ctx.config.costs.opcodeAnd U256.and x y xs h hc
  refine ⟨s₁, s₂, h₁, h₂, hm, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeAnd U256.and, w)) = _
  rw [hr]

/-- An affordable charge permits the push and retains every other frame field and the world. -/
theorem bitwiseAnd_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeAnd ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.and x y) = .ok out ∧
      out.toList = U256.and x y :: xs ∧
      ((bitwiseAnd ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeAnd } }, w)) := by
  obtain ⟨s₁, s₂, out, h₁, h₂, hm, hp, ho, hr⟩ :=
    binary_success ctx f ctx.config.costs.opcodeAnd U256.and x y xs h hc
  refine ⟨s₁, s₂, out, h₁, h₂, hm, hp, ho, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeAnd U256.and, w)) = _
  rw [hr]

/-- A continuing Id run spends exactly the selected price in meter potential. -/
theorem bitwiseAnd_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((bitwiseAnd ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeAnd = f.gasMeter.phi := by
  change Except.ok (binaryLinear ctx f ctx.config.costs.opcodeAnd U256.and, w) =
    .ok (.continue f', w') at h
  exact binary_continue_phi ctx f f' ctx.config.costs.opcodeAnd U256.and
    (Prod.mk.inj (Except.ok.inj h)).1

/-- A positive selected price gives strict potential decrease on a continuing Id run. -/
theorem bitwiseAnd_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((bitwiseAnd ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeAnd) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have hp := bitwiseAnd_continue_phi ctx f f' w w' h
  omega

/-- Push the bitwise OR of the two popped words after charging and advance the PC.
EELS `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:46–68`. -/
def bitwiseOr {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (binaryLinear ctx f ctx.config.costs.opcodeOr U256.or)

/-- First-pop underflow retains the complete frame and world. -/
theorem bitwiseOr_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((bitwiseOr ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) := by
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeOr U256.or, w)) = _
  rw [binary_empty ctx f ctx.config.costs.opcodeOr U256.or h]

/-- Second-pop underflow retains the first pop and precedes the charge. -/
theorem bitwiseOr_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((bitwiseOr ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w)) := by
  obtain ⟨s₁, hp, hm, hr⟩ := binary_singleton ctx f ctx.config.costs.opcodeOr U256.or x h
  refine ⟨s₁, hp, hm, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeOr U256.or, w)) = _
  rw [hr]

/-- A denied charge retains both pops and the complete entry meter. -/
theorem bitwiseOr_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeOr) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((bitwiseOr ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  obtain ⟨s₁, s₂, h₁, h₂, hm, hr⟩ :=
    binary_oog ctx f ctx.config.costs.opcodeOr U256.or x y xs h hc
  refine ⟨s₁, s₂, h₁, h₂, hm, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeOr U256.or, w)) = _
  rw [hr]

/-- An affordable charge permits the push and retains every other frame field and the world. -/
theorem bitwiseOr_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeOr ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.or x y) = .ok out ∧
      out.toList = U256.or x y :: xs ∧
      ((bitwiseOr ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeOr } }, w)) := by
  obtain ⟨s₁, s₂, out, h₁, h₂, hm, hp, ho, hr⟩ :=
    binary_success ctx f ctx.config.costs.opcodeOr U256.or x y xs h hc
  refine ⟨s₁, s₂, out, h₁, h₂, hm, hp, ho, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeOr U256.or, w)) = _
  rw [hr]

/-- A continuing Id run spends exactly the selected price in meter potential. -/
theorem bitwiseOr_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((bitwiseOr ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeOr = f.gasMeter.phi := by
  change Except.ok (binaryLinear ctx f ctx.config.costs.opcodeOr U256.or, w) =
    .ok (.continue f', w') at h
  exact binary_continue_phi ctx f f' ctx.config.costs.opcodeOr U256.or
    (Prod.mk.inj (Except.ok.inj h)).1

/-- A positive selected price gives strict potential decrease on a continuing Id run. -/
theorem bitwiseOr_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((bitwiseOr ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeOr) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have hp := bitwiseOr_continue_phi ctx f f' w w' h
  omega

/-- Push the bitwise XOR of the two popped words after charging and advance the PC.
EELS `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:71–93`. -/
def bitwiseXor {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (binaryLinear ctx f ctx.config.costs.opcodeXor U256.xor)

/-- First-pop underflow retains the complete frame and world. -/
theorem bitwiseXor_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((bitwiseXor ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) := by
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeXor U256.xor, w)) = _
  rw [binary_empty ctx f ctx.config.costs.opcodeXor U256.xor h]

/-- Second-pop underflow retains the first pop and precedes the charge. -/
theorem bitwiseXor_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((bitwiseXor ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w)) := by
  obtain ⟨s₁, hp, hm, hr⟩ := binary_singleton ctx f ctx.config.costs.opcodeXor U256.xor x h
  refine ⟨s₁, hp, hm, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeXor U256.xor, w)) = _
  rw [hr]

/-- A denied charge retains both pops and the complete entry meter. -/
theorem bitwiseXor_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeXor) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((bitwiseXor ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  obtain ⟨s₁, s₂, h₁, h₂, hm, hr⟩ :=
    binary_oog ctx f ctx.config.costs.opcodeXor U256.xor x y xs h hc
  refine ⟨s₁, s₂, h₁, h₂, hm, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeXor U256.xor, w)) = _
  rw [hr]

/-- An affordable charge permits the push and retains every other frame field and the world. -/
theorem bitwiseXor_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeXor ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.xor x y) = .ok out ∧
      out.toList = U256.xor x y :: xs ∧
      ((bitwiseXor ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeXor } }, w)) := by
  obtain ⟨s₁, s₂, out, h₁, h₂, hm, hp, ho, hr⟩ :=
    binary_success ctx f ctx.config.costs.opcodeXor U256.xor x y xs h hc
  refine ⟨s₁, s₂, out, h₁, h₂, hm, hp, ho, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeXor U256.xor, w)) = _
  rw [hr]

/-- A continuing Id run spends exactly the selected price in meter potential. -/
theorem bitwiseXor_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((bitwiseXor ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeXor = f.gasMeter.phi := by
  change Except.ok (binaryLinear ctx f ctx.config.costs.opcodeXor U256.xor, w) =
    .ok (.continue f', w') at h
  exact binary_continue_phi ctx f f' ctx.config.costs.opcodeXor U256.xor
    (Prod.mk.inj (Except.ok.inj h)).1

/-- A positive selected price gives strict potential decrease on a continuing Id run. -/
theorem bitwiseXor_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((bitwiseXor ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeXor) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have hp := bitwiseXor_continue_phi ctx f f' w w' h
  omega

/-- Push the 256-bit complement of the popped word after charging and advance the PC.
EELS `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py:96–117`. -/
def bitwiseNot {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (unaryLinear ctx f ctx.config.costs.opcodeNot U256.not)

/-- An empty stack halts before charging and retains the complete frame and world. -/
theorem bitwiseNot_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((bitwiseNot ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) := by
  have hp := (Stack.pop_eq_error_iff f.stack .stackUnderflow).mpr ⟨h, rfl⟩
  change pure (Except.ok (unaryLinear ctx f ctx.config.costs.opcodeNot U256.not, w)) = _
  simp only [unaryLinear_eq_unary, unary, hp]

/-- An unaffordable charge halts after one pop and retains every other frame field and the world. -/
theorem bitwiseNot_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256) (xs : List U256)
    (h : f.stack.toList = x :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeNot) :
    ∃ stack : Stack, f.stack.pop = .ok (x, stack) ∧ stack.toList = xs ∧
      ((bitwiseNot ctx f).run w).run =
        pure (Except.ok (.halt { f with stack } .outOfGas, w)) := by
  obtain ⟨stack, hp, model⟩ := pop_of_model f.stack x xs h
  have hg := (chargeGas_eq_error_iff f.gasMeter ctx.config.costs.opcodeNot .outOfGas).mpr
    ⟨hc, rfl⟩
  refine ⟨stack, hp, model, ?_⟩
  change pure (Except.ok (unaryLinear ctx f ctx.config.costs.opcodeNot U256.not, w)) = _
  simp only [unaryLinear_eq_unary, unary, hp, hg]

/-- An affordable charge replaces the top word and changes only the PC and execution gas.
The bounded stack guarantees space for the push after the pop. -/
theorem bitwiseNot_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256) (xs : List U256)
    (h : f.stack.toList = x :: xs)
    (hc : ctx.config.costs.opcodeNot ≤ f.gasMeter.gasLeft) :
    ∃ stack out : Stack, f.stack.pop = .ok (x, stack) ∧ stack.toList = xs ∧
      stack.push (U256.not x) = .ok out ∧ out.toList = U256.not x :: xs ∧
      ((bitwiseNot ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeNot } }, w)) := by
  obtain ⟨stack, hp, model⟩ := pop_of_model f.stack x xs h
  have oldBound := f.stack.size_le
  rw [Stack.size_eq_length_toList, h] at oldBound
  have available : stack.size < 1024 := by
    rw [Stack.size_eq_length_toList, model]
    simp only [List.length_cons] at oldBound
    omega
  cases next : stack.push (U256.not x) with
  | error e =>
    have he := (Stack.push_eq_error_iff stack (U256.not x) e).mp next
    omega
  | ok out =>
    have hm := (Stack.push_eq_ok_iff stack out (U256.not x)).mp next
    have hg := chargeGas_of_le f.gasMeter ctx.config.costs.opcodeNot hc
    refine ⟨stack, out, hp, model, next, ?_, ?_⟩
    · simpa only [model] using hm.2
    · change pure (Except.ok (unaryLinear ctx f ctx.config.costs.opcodeNot U256.not, w)) = _
      simp only [unaryLinear_eq_unary, unary, hp, hg, next]

/-- A continuing Id run spends exactly the selected execution price in meter potential. -/
theorem bitwiseNot_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((bitwiseNot ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeNot = f.gasMeter.phi := by
  change Except.ok (unaryLinear ctx f ctx.config.costs.opcodeNot U256.not, w) =
    .ok (.continue f', w') at h
  have step := (Prod.mk.inj (Except.ok.inj h)).1
  cases hp : f.stack.pop with
  | error e =>
    simp only [unaryLinear_eq_unary, unary, hp] at step
    contradiction
  | ok pair =>
    rcases pair with ⟨x, stack⟩
    cases hg : chargeGas f.gasMeter ctx.config.costs.opcodeNot with
    | error e =>
      simp only [unaryLinear_eq_unary, unary, hp, hg] at step
      contradiction
    | ok paid =>
      cases next : stack.push (U256.not x) with
      | error e =>
        simp only [unaryLinear_eq_unary, unary, hp, hg, next] at step
        contradiction
      | ok out =>
        simp only [unaryLinear_eq_unary, unary, hp, hg, next, StepResult.continue.injEq] at step
        subst f'
        exact chargeGas_phi f.gasMeter ctx.config.costs.opcodeNot paid hg

/-- A positive selected execution price implies strict potential decrease on a continuing Id run. -/
theorem bitwiseNot_continue_progress (ctx : FrameCtx) (f f' : Frame)
    (w w' : VmWorld Id) (h : ((bitwiseNot ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeNot) :
    f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have accounting := bitwiseNot_continue_phi ctx f f' w w' h
  omega

end STFSpec.Vm.Instructions
