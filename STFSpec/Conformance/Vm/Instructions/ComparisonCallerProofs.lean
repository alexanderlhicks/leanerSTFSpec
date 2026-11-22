/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions

/-!
# Comparison public-law clients

Library `EthConformance`. These clients use the instruction facade and public
stack and word models. See `STFSpec/informal/modules/EthVmInstructions.md` §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.ComparisonCallerProofs
open STFSpec.Base STFSpec.Vm.Core STFSpec.Vm.Instructions

private def signature {m : Type → Type} [Monad m] : Handler m := isZero

private theorem empty_precedence {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((isZero ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) :=
  isZero_run_empty ctx f w h

private theorem shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256) (xs : List U256)
    (h : f.stack.toList = x :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeIsZero) :
    ∃ rest : Stack, f.stack.pop = .ok (x, rest) ∧ rest.toList = xs ∧
      ((isZero ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .outOfGas, w)) :=
  isZero_run_oog ctx f w x xs h hc

private theorem success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256) (xs : List U256)
    (h : f.stack.toList = x :: xs) (hc : ctx.config.costs.opcodeIsZero ≤ f.gasMeter.gasLeft) :
    ∃ stack out : Stack, f.stack.pop = .ok (x, stack) ∧
      stack.push (U256.iszero x) = .ok out ∧
      out.toList.map U256.toNat = (if x.toNat = 0 then 1 else 0) :: xs.map U256.toNat ∧
      ((isZero ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeIsZero } }, w)) := by
  obtain ⟨stack, out, hp, _, push, model, run⟩ := isZero_run_success ctx f w x xs h hc
  exact ⟨stack, out, hp, push, by rw [model, List.map_cons, U256.toNat_iszero], run⟩

private theorem success_world (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (x : U256) (xs : List U256) (h : f.stack.toList = x :: xs)
    (hc : ctx.config.costs.opcodeIsZero ≤ f.gasMeter.gasLeft)
    (run : ((isZero ctx f).run w).run = .ok (.continue f', w')) :
    w' = w := by
  obtain ⟨_, _, _, _, _, _, expected⟩ := isZero_run_success ctx f w x xs h hc
  exact (Prod.mk.inj (Except.ok.inj (run.symm.trans expected))).2

private theorem zero_price_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((isZero ctx f).run w).run = .ok (.continue f', w'))
    (zero : ctx.config.costs.opcodeIsZero = 0) : f'.gasMeter.phi = f.gasMeter.phi := by
  simpa only [zero, Nat.add_zero] using isZero_continue_phi ctx f f' w w' h

private theorem progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((isZero ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeIsZero) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  isZero_continue_progress ctx f f' w w' h positive

private def binarySignatures {m : Type → Type} [Monad m] :
    Handler m × Handler m × Handler m × Handler m × Handler m :=
  (lessThan, greaterThan, signedLessThan, signedGreaterThan, equal)

private theorem binary_empty_precedence {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((lessThan ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) ∧
    ((greaterThan ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) ∧
    ((signedLessThan ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) ∧
    ((signedGreaterThan ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) ∧
    ((equal ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) :=
  ⟨lessThan_run_empty ctx f w h, greaterThan_run_empty ctx f w h,
    signedLessThan_run_empty ctx f w h, signedGreaterThan_run_empty ctx f w h,
    equal_run_empty ctx f w h⟩

private theorem lessThan_singleton_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ rest : Stack, f.stack.pop = .ok (x, rest) ∧ rest.size = 0 ∧
      ((lessThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .stackUnderflow, w)) := by
  obtain ⟨rest, pop, model, run⟩ := lessThan_run_singleton ctx f w x h
  exact ⟨rest, pop, by simp only [Stack.size_eq_length_toList, model, List.length_nil], run⟩

private theorem lessThan_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeLt) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.size = xs.length ∧ ((lessThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  obtain ⟨s₁, s₂, first, second, model, run⟩ := lessThan_run_oog ctx f w x y xs h hc
  exact ⟨s₁, s₂, first, second, by rw [Stack.size_eq_length_toList, model], run⟩

private theorem lessThan_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeLt ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.push (U256.lt x y) = .ok out ∧
      out.toList.map U256.toNat = (if x.toNat < y.toNat then 1 else 0) :: xs.map U256.toNat ∧
      ((lessThan ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeLt } }, w)) := by
  obtain ⟨s₁, s₂, out, first, second, _, push, model, run⟩ :=
    lessThan_run_success ctx f w x y xs h hc
  exact ⟨s₁, s₂, out, first, second, push,
    by rw [model, List.map_cons, U256.toNat_lt_result], run⟩

private theorem lessThan_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((lessThan ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeLt = f.gasMeter.phi ∧
      (1 ≤ ctx.config.costs.opcodeLt → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨lessThan_continue_phi ctx f f' w w' h,
    lessThan_continue_progress ctx f f' w w' h⟩

private theorem greaterThan_singleton_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ rest : Stack, f.stack.pop = .ok (x, rest) ∧ rest.size = 0 ∧
      ((greaterThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .stackUnderflow, w)) := by
  obtain ⟨rest, pop, model, run⟩ := greaterThan_run_singleton ctx f w x h
  exact ⟨rest, pop, by simp only [Stack.size_eq_length_toList, model, List.length_nil], run⟩

private theorem greaterThan_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeGt) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.size = xs.length ∧ ((greaterThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  obtain ⟨s₁, s₂, first, second, model, run⟩ := greaterThan_run_oog ctx f w x y xs h hc
  exact ⟨s₁, s₂, first, second, by rw [Stack.size_eq_length_toList, model], run⟩

private theorem greaterThan_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeGt ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.push (U256.gt x y) = .ok out ∧
      out.toList.map U256.toNat = (if y.toNat < x.toNat then 1 else 0) :: xs.map U256.toNat ∧
      ((greaterThan ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeGt } }, w)) := by
  obtain ⟨s₁, s₂, out, first, second, _, push, model, run⟩ :=
    greaterThan_run_success ctx f w x y xs h hc
  exact ⟨s₁, s₂, out, first, second, push,
    by rw [model, List.map_cons, U256.toNat_gt], run⟩

private theorem greaterThan_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((greaterThan ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeGt = f.gasMeter.phi ∧
      (1 ≤ ctx.config.costs.opcodeGt → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨greaterThan_continue_phi ctx f f' w w' h,
    greaterThan_continue_progress ctx f f' w w' h⟩

private theorem signedLessThan_singleton_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ rest : Stack, f.stack.pop = .ok (x, rest) ∧ rest.size = 0 ∧
      ((signedLessThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .stackUnderflow, w)) := by
  obtain ⟨rest, pop, model, run⟩ := signedLessThan_run_singleton ctx f w x h
  exact ⟨rest, pop, by simp only [Stack.size_eq_length_toList, model, List.length_nil], run⟩

private theorem signedLessThan_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeSlt) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.size = xs.length ∧ ((signedLessThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  obtain ⟨s₁, s₂, first, second, model, run⟩ := signedLessThan_run_oog ctx f w x y xs h hc
  exact ⟨s₁, s₂, first, second, by rw [Stack.size_eq_length_toList, model], run⟩

private theorem signedLessThan_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeSlt ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.push (U256.slt x y) = .ok out ∧
      out.toList.map U256.toNat = (if x.toInt < y.toInt then 1 else 0) :: xs.map U256.toNat ∧
      ((signedLessThan ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSlt } }, w)) := by
  obtain ⟨s₁, s₂, out, first, second, _, push, model, run⟩ :=
    signedLessThan_run_success ctx f w x y xs h hc
  exact ⟨s₁, s₂, out, first, second, push,
    by rw [model, List.map_cons, U256.toNat_slt], run⟩

private theorem signedLessThan_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((signedLessThan ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeSlt = f.gasMeter.phi ∧
      (1 ≤ ctx.config.costs.opcodeSlt → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨signedLessThan_continue_phi ctx f f' w w' h,
    signedLessThan_continue_progress ctx f f' w w' h⟩

private theorem signedGreaterThan_singleton_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ rest : Stack, f.stack.pop = .ok (x, rest) ∧ rest.size = 0 ∧
      ((signedGreaterThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .stackUnderflow, w)) := by
  obtain ⟨rest, pop, model, run⟩ := signedGreaterThan_run_singleton ctx f w x h
  exact ⟨rest, pop, by simp only [Stack.size_eq_length_toList, model, List.length_nil], run⟩

private theorem signedGreaterThan_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeSgt) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.size = xs.length ∧ ((signedGreaterThan ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  obtain ⟨s₁, s₂, first, second, model, run⟩ :=
    signedGreaterThan_run_oog ctx f w x y xs h hc
  exact ⟨s₁, s₂, first, second, by rw [Stack.size_eq_length_toList, model], run⟩

private theorem signedGreaterThan_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeSgt ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.push (U256.sgt x y) = .ok out ∧
      out.toList.map U256.toNat = (if y.toInt < x.toInt then 1 else 0) :: xs.map U256.toNat ∧
      ((signedGreaterThan ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSgt } }, w)) := by
  obtain ⟨s₁, s₂, out, first, second, _, push, model, run⟩ :=
    signedGreaterThan_run_success ctx f w x y xs h hc
  exact ⟨s₁, s₂, out, first, second, push,
    by rw [model, List.map_cons, U256.toNat_sgt], run⟩

private theorem signedGreaterThan_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((signedGreaterThan ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeSgt = f.gasMeter.phi ∧
      (1 ≤ ctx.config.costs.opcodeSgt → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨signedGreaterThan_continue_phi ctx f f' w w' h,
    signedGreaterThan_continue_progress ctx f f' w w' h⟩

private theorem equal_singleton_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ rest : Stack, f.stack.pop = .ok (x, rest) ∧ rest.size = 0 ∧
      ((equal ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .stackUnderflow, w)) := by
  obtain ⟨rest, pop, model, run⟩ := equal_run_singleton ctx f w x h
  exact ⟨rest, pop, by simp only [Stack.size_eq_length_toList, model, List.length_nil], run⟩

private theorem equal_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeEq) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.size = xs.length ∧ ((equal ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  obtain ⟨s₁, s₂, first, second, model, run⟩ := equal_run_oog ctx f w x y xs h hc
  exact ⟨s₁, s₂, first, second, by rw [Stack.size_eq_length_toList, model], run⟩

private theorem equal_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeEq ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.push (U256.eq x y) = .ok out ∧
      out.toList.map U256.toNat = (if x.toNat = y.toNat then 1 else 0) :: xs.map U256.toNat ∧
      ((equal ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeEq } }, w)) := by
  obtain ⟨s₁, s₂, out, first, second, _, push, model, run⟩ :=
    equal_run_success ctx f w x y xs h hc
  exact ⟨s₁, s₂, out, first, second, push,
    by rw [model, List.map_cons, U256.toNat_eq_result], run⟩

private theorem equal_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((equal ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeEq = f.gasMeter.phi ∧
      (1 ≤ ctx.config.costs.opcodeEq → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨equal_continue_phi ctx f f' w w' h,
    equal_continue_progress ctx f f' w w' h⟩

end STFSpec.Conformance.Vm.Instructions.ComparisonCallerProofs
