/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions.Handler
import STFSpec.Base.U256Bitwise

/-!
# LT, GT, SLT, SGT, EQ and ISZERO

Library `EthVmInstructions`. The handlers use the word model from EthBase and
the stack and meter operations from EthVmCore.
Spec guidance is in `STFSpec/informal/modules/EthVmInstructions.md` §§3/5/7.
-/

namespace STFSpec.Vm.Instructions

open STFSpec.Base STFSpec.Vm.Core

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

private def evalIsZeroLinear (ctx : FrameCtx) (f : Frame) : StepResult ctx :=
  if empty : f.stack.size = 0 then
    .halt f .stackUnderflow
  else
    match pop : f.stack.pop with
    | .error e => False.elim (pop_not_error f.stack e empty pop)
    | .ok (x, stack) =>
      match chargeGas f.gasMeter ctx.config.costs.opcodeIsZero with
      | .error e => .halt { f with stack } e
      | .ok paid =>
        let result := U256.iszero x
        match push : stack.push result with
        | .error e => False.elim (push_not_error f.stack stack x result e pop push)
        | .ok out => .continue { f with pc := f.pc + 1, stack := out, gasMeter := paid }

private theorem evalIsZeroLinear_eq_evalIsZero (ctx : FrameCtx) (f : Frame) :
    evalIsZeroLinear ctx f = evalIsZero ctx f := by
  unfold evalIsZeroLinear evalIsZero
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
          exact False.elim (push_not_error f.stack stack x (U256.iszero x) e pop push)
        · rename_i out push
          simp only [push]

/-- Pop one word, charge the selected execution price, push the zero test and advance the PC.
EELS `src/ethereum/forks/amsterdam/vm/instructions/comparison.py:154–177`. -/
def isZero {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (evalIsZeroLinear ctx f)

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
  change pure (Except.ok (evalIsZeroLinear ctx f, w)) = _
  simp only [evalIsZeroLinear_eq_evalIsZero, evalIsZero, hp]

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
  change pure (Except.ok (evalIsZeroLinear ctx f, w)) = _
  simp only [evalIsZeroLinear_eq_evalIsZero, evalIsZero, hp, hg]

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
    · change pure (Except.ok (evalIsZeroLinear ctx f, w)) = _
      simp only [evalIsZeroLinear_eq_evalIsZero, evalIsZero, hp, hg, next]

/-- A continuing Id run spends exactly the selected execution price in meter potential. -/
theorem isZero_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((isZero ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeIsZero = f.gasMeter.phi := by
  change Except.ok (evalIsZeroLinear ctx f, w) = .ok (.continue f', w') at h
  rw [evalIsZeroLinear_eq_evalIsZero] at h
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

/-- Release each stack once its remaining operations can no longer return it. -/
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
      s₂.toList = xs ∧ binaryLinear ctx f c word = .halt { f with stack := s₂ } .outOfGas := by
  obtain ⟨s₁, h₁, hm₁⟩ := pop_of_model f.stack x (y :: xs) h
  obtain ⟨s₂, h₂, hm₂⟩ := pop_of_model s₁ y xs hm₁
  have hg := (chargeGas_eq_error_iff f.gasMeter c .outOfGas).mpr ⟨hc, rfl⟩
  exact ⟨s₁, s₂, h₁, h₂, hm₂, by simp only [binaryLinear_eq_binary, binary, h₁, h₂, hg]⟩

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

/-- Test whether the first popped word is less than the second, unsigned.
EELS `src/ethereum/forks/amsterdam/vm/instructions/comparison.py:21–45`. -/
def lessThan {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (binaryLinear ctx f ctx.config.costs.opcodeLt U256.lt)

/-- Empty-stack underflow keeps the complete frame and supplied world. -/
theorem lessThan_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((lessThan ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) := by
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeLt U256.lt, w)) = _
  rw [binary_empty ctx f ctx.config.costs.opcodeLt U256.lt h]

/-- The first pop survives second-pop underflow, before any charge. -/
theorem lessThan_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((lessThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w)) := by
  obtain ⟨s₁, hp, hm, hr⟩ := binary_singleton ctx f ctx.config.costs.opcodeLt U256.lt x h
  refine ⟨s₁, hp, hm, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeLt U256.lt, w)) = _
  rw [hr]

/-- Both pops survive an execution shortage; the complete meter remains unchanged. -/
theorem lessThan_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeLt) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((lessThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  obtain ⟨s₁, s₂, h₁, h₂, hm, hr⟩ :=
    binary_oog ctx f ctx.config.costs.opcodeLt U256.lt x y xs h hc
  refine ⟨s₁, s₂, h₁, h₂, hm, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeLt U256.lt, w)) = _
  rw [hr]

/-- Complete successful result, including proved push availability and whole-world retention. -/
theorem lessThan_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeLt ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.lt x y) = .ok out ∧
      out.toList = U256.lt x y :: xs ∧
      ((lessThan ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeLt } }, w)) := by
  obtain ⟨s₁, s₂, out, h₁, h₂, hm, hp, ho, hr⟩ :=
    binary_success ctx f ctx.config.costs.opcodeLt U256.lt x y xs h hc
  refine ⟨s₁, s₂, out, h₁, h₂, hm, hp, ho, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeLt U256.lt, w)) = _
  rw [hr]

/-- Every actual Id continuation loses exactly the selected raw opcode price. -/
theorem lessThan_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((lessThan ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeLt = f.gasMeter.phi := by
  change Except.ok (binaryLinear ctx f ctx.config.costs.opcodeLt U256.lt, w) =
    .ok (.continue f', w') at h
  exact binary_continue_phi ctx f f' ctx.config.costs.opcodeLt U256.lt
    (Prod.mk.inj (Except.ok.inj h)).1

/-- Strict continuing progress requires only positivity of the selected price. -/
theorem lessThan_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((lessThan ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeLt) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have hp := lessThan_continue_phi ctx f f' w w' h
  omega

/-- Test whether the first popped word is greater than the second, unsigned.
EELS `src/ethereum/forks/amsterdam/vm/instructions/comparison.py:74–98`. -/
def greaterThan {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (binaryLinear ctx f ctx.config.costs.opcodeGt U256.gt)

/-- Empty-stack underflow keeps the complete frame and supplied world. -/
theorem greaterThan_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((greaterThan ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) := by
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeGt U256.gt, w)) = _
  rw [binary_empty ctx f ctx.config.costs.opcodeGt U256.gt h]

/-- The first pop survives second-pop underflow, before any charge. -/
theorem greaterThan_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((greaterThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w)) := by
  obtain ⟨s₁, hp, hm, hr⟩ := binary_singleton ctx f ctx.config.costs.opcodeGt U256.gt x h
  refine ⟨s₁, hp, hm, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeGt U256.gt, w)) = _
  rw [hr]

/-- Both pops survive an execution shortage; the complete meter remains unchanged. -/
theorem greaterThan_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeGt) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((greaterThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  obtain ⟨s₁, s₂, h₁, h₂, hm, hr⟩ :=
    binary_oog ctx f ctx.config.costs.opcodeGt U256.gt x y xs h hc
  refine ⟨s₁, s₂, h₁, h₂, hm, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeGt U256.gt, w)) = _
  rw [hr]

/-- Complete successful result, including proved push availability and whole-world retention. -/
theorem greaterThan_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeGt ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.gt x y) = .ok out ∧
      out.toList = U256.gt x y :: xs ∧
      ((greaterThan ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeGt } }, w)) := by
  obtain ⟨s₁, s₂, out, h₁, h₂, hm, hp, ho, hr⟩ :=
    binary_success ctx f ctx.config.costs.opcodeGt U256.gt x y xs h hc
  refine ⟨s₁, s₂, out, h₁, h₂, hm, hp, ho, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeGt U256.gt, w)) = _
  rw [hr]

/-- Every actual Id continuation loses exactly the selected raw opcode price. -/
theorem greaterThan_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((greaterThan ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeGt = f.gasMeter.phi := by
  change Except.ok (binaryLinear ctx f ctx.config.costs.opcodeGt U256.gt, w) =
    .ok (.continue f', w') at h
  exact binary_continue_phi ctx f f' ctx.config.costs.opcodeGt U256.gt
    (Prod.mk.inj (Except.ok.inj h)).1

/-- Strict continuing progress requires only positivity of the selected price. -/
theorem greaterThan_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((greaterThan ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeGt) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have hp := greaterThan_continue_phi ctx f f' w w' h
  omega

/-- Test whether the first popped word is less than the second, signed.
EELS `src/ethereum/forks/amsterdam/vm/instructions/comparison.py:48–71`. -/
def signedLessThan {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (binaryLinear ctx f ctx.config.costs.opcodeSlt U256.slt)

/-- Empty-stack underflow keeps the complete frame and supplied world. -/
theorem signedLessThan_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((signedLessThan ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) := by
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeSlt U256.slt, w)) = _
  rw [binary_empty ctx f ctx.config.costs.opcodeSlt U256.slt h]

/-- The first pop survives second-pop underflow, before any charge. -/
theorem signedLessThan_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((signedLessThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w)) := by
  obtain ⟨s₁, hp, hm, hr⟩ := binary_singleton ctx f ctx.config.costs.opcodeSlt U256.slt x h
  refine ⟨s₁, hp, hm, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeSlt U256.slt, w)) = _
  rw [hr]

/-- Both pops survive an execution shortage; the complete meter remains unchanged. -/
theorem signedLessThan_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeSlt) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((signedLessThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  obtain ⟨s₁, s₂, h₁, h₂, hm, hr⟩ :=
    binary_oog ctx f ctx.config.costs.opcodeSlt U256.slt x y xs h hc
  refine ⟨s₁, s₂, h₁, h₂, hm, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeSlt U256.slt, w)) = _
  rw [hr]

/-- Complete successful result, including proved push availability and whole-world retention. -/
theorem signedLessThan_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeSlt ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.slt x y) = .ok out ∧
      out.toList = U256.slt x y :: xs ∧
      ((signedLessThan ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSlt } }, w)) := by
  obtain ⟨s₁, s₂, out, h₁, h₂, hm, hp, ho, hr⟩ :=
    binary_success ctx f ctx.config.costs.opcodeSlt U256.slt x y xs h hc
  refine ⟨s₁, s₂, out, h₁, h₂, hm, hp, ho, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeSlt U256.slt, w)) = _
  rw [hr]

/-- Every actual Id continuation loses exactly the selected raw opcode price. -/
theorem signedLessThan_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((signedLessThan ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeSlt = f.gasMeter.phi := by
  change Except.ok (binaryLinear ctx f ctx.config.costs.opcodeSlt U256.slt, w) =
    .ok (.continue f', w') at h
  exact binary_continue_phi ctx f f' ctx.config.costs.opcodeSlt U256.slt
    (Prod.mk.inj (Except.ok.inj h)).1

/-- Strict continuing progress requires only positivity of the selected price. -/
theorem signedLessThan_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((signedLessThan ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeSlt) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have hp := signedLessThan_continue_phi ctx f f' w w' h
  omega

/-- Test whether the first popped word is greater than the second, signed.
EELS `src/ethereum/forks/amsterdam/vm/instructions/comparison.py:101–124`. -/
def signedGreaterThan {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (binaryLinear ctx f ctx.config.costs.opcodeSgt U256.sgt)

/-- Empty-stack underflow keeps the complete frame and supplied world. -/
theorem signedGreaterThan_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((signedGreaterThan ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) := by
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeSgt U256.sgt, w)) = _
  rw [binary_empty ctx f ctx.config.costs.opcodeSgt U256.sgt h]

/-- The first pop survives second-pop underflow, before any charge. -/
theorem signedGreaterThan_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((signedGreaterThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w)) := by
  obtain ⟨s₁, hp, hm, hr⟩ := binary_singleton ctx f ctx.config.costs.opcodeSgt U256.sgt x h
  refine ⟨s₁, hp, hm, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeSgt U256.sgt, w)) = _
  rw [hr]

/-- Both pops survive an execution shortage; the complete meter remains unchanged. -/
theorem signedGreaterThan_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeSgt) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((signedGreaterThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  obtain ⟨s₁, s₂, h₁, h₂, hm, hr⟩ :=
    binary_oog ctx f ctx.config.costs.opcodeSgt U256.sgt x y xs h hc
  refine ⟨s₁, s₂, h₁, h₂, hm, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeSgt U256.sgt, w)) = _
  rw [hr]

/-- Complete successful result, including proved push availability and whole-world retention. -/
theorem signedGreaterThan_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeSgt ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.sgt x y) = .ok out ∧
      out.toList = U256.sgt x y :: xs ∧
      ((signedGreaterThan ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSgt } }, w)) := by
  obtain ⟨s₁, s₂, out, h₁, h₂, hm, hp, ho, hr⟩ :=
    binary_success ctx f ctx.config.costs.opcodeSgt U256.sgt x y xs h hc
  refine ⟨s₁, s₂, out, h₁, h₂, hm, hp, ho, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeSgt U256.sgt, w)) = _
  rw [hr]

/-- Every actual Id continuation loses exactly the selected raw opcode price. -/
theorem signedGreaterThan_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((signedGreaterThan ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeSgt = f.gasMeter.phi := by
  change Except.ok (binaryLinear ctx f ctx.config.costs.opcodeSgt U256.sgt, w) =
    .ok (.continue f', w') at h
  exact binary_continue_phi ctx f f' ctx.config.costs.opcodeSgt U256.sgt
    (Prod.mk.inj (Except.ok.inj h)).1

/-- Strict continuing progress requires only positivity of the selected price. -/
theorem signedGreaterThan_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((signedGreaterThan ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeSgt) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have hp := signedGreaterThan_continue_phi ctx f f' w w' h
  omega

/-- Test whether the two popped words are equal.
EELS `src/ethereum/forks/amsterdam/vm/instructions/comparison.py:127–151`. -/
def equal {m : Type → Type} [Monad m] : Handler m :=
  fun ctx f ↦ pure (binaryLinear ctx f ctx.config.costs.opcodeEq U256.eq)

/-- Empty-stack underflow keeps the complete frame and supplied world. -/
theorem equal_run_empty {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((equal ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) := by
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeEq U256.eq, w)) = _
  rw [binary_empty ctx f ctx.config.costs.opcodeEq U256.eq h]

/-- The first pop survives second-pop underflow, before any charge. -/
theorem equal_run_singleton {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ s₁ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.toList = [] ∧
      ((equal ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₁ } .stackUnderflow, w)) := by
  obtain ⟨s₁, hp, hm, hr⟩ := binary_singleton ctx f ctx.config.costs.opcodeEq U256.eq x h
  refine ⟨s₁, hp, hm, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeEq U256.eq, w)) = _
  rw [hr]

/-- Both pops survive an execution shortage; the complete meter remains unchanged. -/
theorem equal_run_oog {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeEq) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ ((equal ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  obtain ⟨s₁, s₂, h₁, h₂, hm, hr⟩ :=
    binary_oog ctx f ctx.config.costs.opcodeEq U256.eq x y xs h hc
  refine ⟨s₁, s₂, h₁, h₂, hm, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeEq U256.eq, w)) = _
  rw [hr]

/-- Complete successful result, including proved push availability and whole-world retention. -/
theorem equal_run_success {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeEq ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.toList = xs ∧ s₂.push (U256.eq x y) = .ok out ∧
      out.toList = U256.eq x y :: xs ∧
      ((equal ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeEq } }, w)) := by
  obtain ⟨s₁, s₂, out, h₁, h₂, hm, hp, ho, hr⟩ :=
    binary_success ctx f ctx.config.costs.opcodeEq U256.eq x y xs h hc
  refine ⟨s₁, s₂, out, h₁, h₂, hm, hp, ho, ?_⟩
  change pure (Except.ok (binaryLinear ctx f ctx.config.costs.opcodeEq U256.eq, w)) = _
  rw [hr]

/-- Every actual Id continuation loses exactly the selected raw opcode price. -/
theorem equal_continue_phi (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((equal ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeEq = f.gasMeter.phi := by
  change Except.ok (binaryLinear ctx f ctx.config.costs.opcodeEq U256.eq, w) =
    .ok (.continue f', w') at h
  exact binary_continue_phi ctx f f' ctx.config.costs.opcodeEq U256.eq
    (Prod.mk.inj (Except.ok.inj h)).1

/-- Strict continuing progress requires only positivity of the selected price. -/
theorem equal_continue_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((equal ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeEq) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi := by
  have hp := equal_continue_phi ctx f f' w w' h
  omega

end STFSpec.Vm.Instructions
