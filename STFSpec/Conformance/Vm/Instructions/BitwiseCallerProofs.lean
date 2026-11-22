/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions

/-!
# Bitwise public-law clients

Library `EthConformance`. These clients use the instruction facade and public
stack and word models. See `STFSpec/informal/modules/EthVmInstructions.md` §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.BitwiseCallerProofs
open STFSpec.Base STFSpec.Vm.Core STFSpec.Vm.Instructions

private def signatures {m : Type → Type} [Monad m] :
    Handler m × Handler m × Handler m × Handler m :=
  (bitwiseAnd, bitwiseOr, bitwiseXor, bitwiseNot)

private theorem binary_empty_precedence {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((bitwiseAnd ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) ∧
    ((bitwiseOr ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) ∧
    ((bitwiseXor ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) :=
  ⟨bitwiseAnd_run_empty ctx f w h, bitwiseOr_run_empty ctx f w h,
    bitwiseXor_run_empty ctx f w h⟩

private theorem bitwiseAnd_singleton_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ rest : Stack, f.stack.pop = .ok (x, rest) ∧ rest.size = 0 ∧
      ((bitwiseAnd ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .stackUnderflow, w)) := by
  obtain ⟨rest, pop, model, run⟩ := bitwiseAnd_run_singleton ctx f w x h
  exact ⟨rest, pop, by simp only [Stack.size_eq_length_toList, model, List.length_nil], run⟩

private theorem bitwiseAnd_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeAnd) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.size = xs.length ∧ ((bitwiseAnd ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  obtain ⟨s₁, s₂, first, second, model, run⟩ := bitwiseAnd_run_oog ctx f w x y xs h hc
  exact ⟨s₁, s₂, first, second, by rw [Stack.size_eq_length_toList, model], run⟩

private theorem bitwiseAnd_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeAnd ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.push (U256.and x y) = .ok out ∧
      out.toList.map U256.toBitVec = (x.toBitVec &&& y.toBitVec) :: xs.map U256.toBitVec ∧
      ((bitwiseAnd ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeAnd } }, w)) := by
  obtain ⟨s₁, s₂, out, hp₁, hp₂, _, push, model, run⟩ :=
    bitwiseAnd_run_success ctx f w x y xs h hc
  refine ⟨s₁, s₂, out, hp₁, hp₂, push, ?_, run⟩
  rw [model, List.map_cons, U256.toBitVec_and]

private theorem bitwiseAnd_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((bitwiseAnd ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeAnd = f.gasMeter.phi ∧
      (1 ≤ ctx.config.costs.opcodeAnd → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨bitwiseAnd_continue_phi ctx f f' w w' h,
    bitwiseAnd_continue_progress ctx f f' w w' h⟩

private theorem bitwiseOr_singleton_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ rest : Stack, f.stack.pop = .ok (x, rest) ∧ rest.size = 0 ∧
      ((bitwiseOr ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .stackUnderflow, w)) := by
  obtain ⟨rest, pop, model, run⟩ := bitwiseOr_run_singleton ctx f w x h
  exact ⟨rest, pop, by simp only [Stack.size_eq_length_toList, model, List.length_nil], run⟩

private theorem bitwiseOr_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeOr) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.size = xs.length ∧ ((bitwiseOr ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  obtain ⟨s₁, s₂, first, second, model, run⟩ := bitwiseOr_run_oog ctx f w x y xs h hc
  exact ⟨s₁, s₂, first, second, by rw [Stack.size_eq_length_toList, model], run⟩

private theorem bitwiseOr_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeOr ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.push (U256.or x y) = .ok out ∧
      out.toList.map U256.toBitVec = (x.toBitVec ||| y.toBitVec) :: xs.map U256.toBitVec ∧
      ((bitwiseOr ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeOr } }, w)) := by
  obtain ⟨s₁, s₂, out, hp₁, hp₂, _, push, model, run⟩ :=
    bitwiseOr_run_success ctx f w x y xs h hc
  refine ⟨s₁, s₂, out, hp₁, hp₂, push, ?_, run⟩
  rw [model, List.map_cons, U256.toBitVec_or]

private theorem bitwiseOr_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((bitwiseOr ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeOr = f.gasMeter.phi ∧
      (1 ≤ ctx.config.costs.opcodeOr → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨bitwiseOr_continue_phi ctx f f' w w' h,
    bitwiseOr_continue_progress ctx f f' w w' h⟩

private theorem bitwiseXor_singleton_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ rest : Stack, f.stack.pop = .ok (x, rest) ∧ rest.size = 0 ∧
      ((bitwiseXor ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .stackUnderflow, w)) := by
  obtain ⟨rest, pop, model, run⟩ := bitwiseXor_run_singleton ctx f w x h
  exact ⟨rest, pop, by simp only [Stack.size_eq_length_toList, model, List.length_nil], run⟩

private theorem bitwiseXor_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeXor) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.size = xs.length ∧ ((bitwiseXor ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  obtain ⟨s₁, s₂, first, second, model, run⟩ := bitwiseXor_run_oog ctx f w x y xs h hc
  exact ⟨s₁, s₂, first, second, by rw [Stack.size_eq_length_toList, model], run⟩

private theorem bitwiseXor_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeXor ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.push (U256.xor x y) = .ok out ∧
      out.toList.map U256.toBitVec = (x.toBitVec ^^^ y.toBitVec) :: xs.map U256.toBitVec ∧
      ((bitwiseXor ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeXor } }, w)) := by
  obtain ⟨s₁, s₂, out, hp₁, hp₂, _, push, model, run⟩ :=
    bitwiseXor_run_success ctx f w x y xs h hc
  refine ⟨s₁, s₂, out, hp₁, hp₂, push, ?_, run⟩
  rw [model, List.map_cons, U256.toBitVec_xor]

private theorem bitwiseXor_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((bitwiseXor ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeXor = f.gasMeter.phi ∧
      (1 ≤ ctx.config.costs.opcodeXor → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨bitwiseXor_continue_phi ctx f f' w w' h,
    bitwiseXor_continue_progress ctx f f' w w' h⟩

private theorem empty_precedence {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((bitwiseNot ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) :=
  bitwiseNot_run_empty ctx f w h

private theorem shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256) (xs : List U256)
    (h : f.stack.toList = x :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeNot) :
    ∃ rest : Stack, f.stack.pop = .ok (x, rest) ∧ rest.toList = xs ∧
      ((bitwiseNot ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .outOfGas, w)) :=
  bitwiseNot_run_oog ctx f w x xs h hc

private theorem success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256) (xs : List U256)
    (h : f.stack.toList = x :: xs) (hc : ctx.config.costs.opcodeNot ≤ f.gasMeter.gasLeft) :
    ∃ stack out : Stack, f.stack.pop = .ok (x, stack) ∧
      stack.push (U256.not x) = .ok out ∧
      out.toList.map U256.toBitVec = (~~~x.toBitVec) :: xs.map U256.toBitVec ∧
      ((bitwiseNot ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeNot } }, w)) := by
  obtain ⟨stack, out, hp, _, push, model, run⟩ := bitwiseNot_run_success ctx f w x xs h hc
  exact ⟨stack, out, hp, push, by rw [model, List.map_cons, U256.toBitVec_not], run⟩

private theorem success_world (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (x : U256) (xs : List U256) (h : f.stack.toList = x :: xs)
    (hc : ctx.config.costs.opcodeNot ≤ f.gasMeter.gasLeft)
    (run : ((bitwiseNot ctx f).run w).run = .ok (.continue f', w')) :
    w' = w := by
  obtain ⟨_, _, _, _, _, _, expected⟩ := bitwiseNot_run_success ctx f w x xs h hc
  exact (Prod.mk.inj (Except.ok.inj (run.symm.trans expected))).2

private theorem zero_price_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((bitwiseNot ctx f).run w).run = .ok (.continue f', w'))
    (zero : ctx.config.costs.opcodeNot = 0) : f'.gasMeter.phi = f.gasMeter.phi := by
  simpa only [zero, Nat.add_zero] using bitwiseNot_continue_phi ctx f f' w w' h

private theorem progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((bitwiseNot ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeNot) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  bitwiseNot_continue_progress ctx f f' w w' h positive

private def byteShiftClzSignatures {m : Type → Type} [Monad m] :
    Handler m × Handler m × Handler m × Handler m × Handler m :=
  (getByte, bitwiseShl, bitwiseShr, bitwiseSar, countLeadingZeros)

private theorem byte_shift_empty_precedence {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((getByte ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) ∧
    ((bitwiseShl ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) ∧
    ((bitwiseShr ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) ∧
    ((bitwiseSar ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) :=
  ⟨getByte_run_empty ctx f w h, bitwiseShl_run_empty ctx f w h,
    bitwiseShr_run_empty ctx f w h, bitwiseSar_run_empty ctx f w h⟩

private theorem getByte_singleton_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ rest : Stack, f.stack.pop = .ok (x, rest) ∧ rest.size = 0 ∧
      ((getByte ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .stackUnderflow, w)) := by
  obtain ⟨rest, pop, model, run⟩ := getByte_run_singleton ctx f w x h
  exact ⟨rest, pop, by simp only [Stack.size_eq_length_toList, model, List.length_nil], run⟩

private theorem getByte_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeByte) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.size = xs.length ∧ ((getByte ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  obtain ⟨s₁, s₂, first, second, model, run⟩ := getByte_run_oog ctx f w x y xs h hc
  exact ⟨s₁, s₂, first, second, by rw [Stack.size_eq_length_toList, model], run⟩

private theorem getByte_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeByte ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.push (U256.byte x y) = .ok out ∧
      out.toList.map U256.toNat = (if 32 ≤ x.toNat then 0 else y.toNat / 2 ^ (8 * (31 - x.toNat)) % 256) :: xs.map U256.toNat ∧
      ((getByte ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeByte } }, w)) := by
  obtain ⟨s₁, s₂, out, hp₁, hp₂, _, push, model, run⟩ :=
    getByte_run_success ctx f w x y xs h hc
  refine ⟨s₁, s₂, out, hp₁, hp₂, push, ?_, run⟩
  rw [model, List.map_cons, U256.toNat_byte]

private theorem getByte_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((getByte ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeByte = f.gasMeter.phi ∧
      (1 ≤ ctx.config.costs.opcodeByte → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨getByte_continue_phi ctx f f' w w' h,
    getByte_continue_progress ctx f f' w w' h⟩

private theorem bitwiseShl_singleton_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ rest : Stack, f.stack.pop = .ok (x, rest) ∧ rest.size = 0 ∧
      ((bitwiseShl ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .stackUnderflow, w)) := by
  obtain ⟨rest, pop, model, run⟩ := bitwiseShl_run_singleton ctx f w x h
  exact ⟨rest, pop, by simp only [Stack.size_eq_length_toList, model, List.length_nil], run⟩

private theorem bitwiseShl_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeShl) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.size = xs.length ∧ ((bitwiseShl ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  obtain ⟨s₁, s₂, first, second, model, run⟩ := bitwiseShl_run_oog ctx f w x y xs h hc
  exact ⟨s₁, s₂, first, second, by rw [Stack.size_eq_length_toList, model], run⟩

private theorem bitwiseShl_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeShl ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.push (U256.shl x y) = .ok out ∧
      out.toList.map U256.toBitVec = (if 256 ≤ x.toNat then 0 else y.toBitVec <<< x.toNat) :: xs.map U256.toBitVec ∧
      ((bitwiseShl ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeShl } }, w)) := by
  obtain ⟨s₁, s₂, out, hp₁, hp₂, _, push, model, run⟩ :=
    bitwiseShl_run_success ctx f w x y xs h hc
  refine ⟨s₁, s₂, out, hp₁, hp₂, push, ?_, run⟩
  rw [model, List.map_cons, U256.toBitVec_shl]

private theorem bitwiseShl_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((bitwiseShl ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeShl = f.gasMeter.phi ∧
      (1 ≤ ctx.config.costs.opcodeShl → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨bitwiseShl_continue_phi ctx f f' w w' h,
    bitwiseShl_continue_progress ctx f f' w w' h⟩

private theorem bitwiseShr_singleton_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ rest : Stack, f.stack.pop = .ok (x, rest) ∧ rest.size = 0 ∧
      ((bitwiseShr ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .stackUnderflow, w)) := by
  obtain ⟨rest, pop, model, run⟩ := bitwiseShr_run_singleton ctx f w x h
  exact ⟨rest, pop, by simp only [Stack.size_eq_length_toList, model, List.length_nil], run⟩

private theorem bitwiseShr_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeShr) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.size = xs.length ∧ ((bitwiseShr ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  obtain ⟨s₁, s₂, first, second, model, run⟩ := bitwiseShr_run_oog ctx f w x y xs h hc
  exact ⟨s₁, s₂, first, second, by rw [Stack.size_eq_length_toList, model], run⟩

private theorem bitwiseShr_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeShr ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.push (U256.shr x y) = .ok out ∧
      out.toList.map U256.toBitVec = (if 256 ≤ x.toNat then 0 else y.toBitVec >>> x.toNat) :: xs.map U256.toBitVec ∧
      ((bitwiseShr ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeShr } }, w)) := by
  obtain ⟨s₁, s₂, out, hp₁, hp₂, _, push, model, run⟩ :=
    bitwiseShr_run_success ctx f w x y xs h hc
  refine ⟨s₁, s₂, out, hp₁, hp₂, push, ?_, run⟩
  rw [model, List.map_cons, U256.toBitVec_shr]

private theorem bitwiseShr_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((bitwiseShr ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeShr = f.gasMeter.phi ∧
      (1 ≤ ctx.config.costs.opcodeShr → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨bitwiseShr_continue_phi ctx f f' w w' h,
    bitwiseShr_continue_progress ctx f f' w w' h⟩

private theorem bitwiseSar_singleton_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ rest : Stack, f.stack.pop = .ok (x, rest) ∧ rest.size = 0 ∧
      ((bitwiseSar ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .stackUnderflow, w)) := by
  obtain ⟨rest, pop, model, run⟩ := bitwiseSar_run_singleton ctx f w x h
  exact ⟨rest, pop, by simp only [Stack.size_eq_length_toList, model, List.length_nil], run⟩

private theorem bitwiseSar_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeSar) :
    ∃ s₁ s₂ : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.size = xs.length ∧ ((bitwiseSar ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := s₂ } .outOfGas, w)) := by
  obtain ⟨s₁, s₂, first, second, model, run⟩ := bitwiseSar_run_oog ctx f w x y xs h hc
  exact ⟨s₁, s₂, first, second, by rw [Stack.size_eq_length_toList, model], run⟩

private theorem bitwiseSar_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs)
    (hc : ctx.config.costs.opcodeSar ≤ f.gasMeter.gasLeft) :
    ∃ s₁ s₂ out : Stack, f.stack.pop = .ok (x, s₁) ∧ s₁.pop = .ok (y, s₂) ∧
      s₂.push (U256.sar x y) = .ok out ∧
      out.toList.map U256.toBitVec = y.toBitVec.sshiftRight x.toNat :: xs.map U256.toBitVec ∧
      ((bitwiseSar ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSar } }, w)) := by
  obtain ⟨s₁, s₂, out, hp₁, hp₂, _, push, model, run⟩ :=
    bitwiseSar_run_success ctx f w x y xs h hc
  refine ⟨s₁, s₂, out, hp₁, hp₂, push, ?_, run⟩
  rw [model, List.map_cons, U256.toBitVec_sar]

private theorem bitwiseSar_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((bitwiseSar ctx f).run w).run = .ok (.continue f', w')) :
    f'.gasMeter.phi + ctx.config.costs.opcodeSar = f.gasMeter.phi ∧
      (1 ≤ ctx.config.costs.opcodeSar → f'.gasMeter.phi + 1 ≤ f.gasMeter.phi) :=
  ⟨bitwiseSar_continue_phi ctx f f' w w' h,
    bitwiseSar_continue_progress ctx f f' w w' h⟩

private theorem clz_empty_precedence {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((countLeadingZeros ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) :=
  countLeadingZeros_run_empty ctx f w h

private theorem clz_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256) (xs : List U256)
    (h : f.stack.toList = x :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeClz) :
    ∃ rest : Stack, f.stack.pop = .ok (x, rest) ∧ rest.toList = xs ∧
      ((countLeadingZeros ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .outOfGas, w)) :=
  countLeadingZeros_run_oog ctx f w x xs h hc

private theorem clz_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256) (xs : List U256)
    (h : f.stack.toList = x :: xs) (hc : ctx.config.costs.opcodeClz ≤ f.gasMeter.gasLeft) :
    ∃ stack out : Stack, f.stack.pop = .ok (x, stack) ∧
      stack.push (U256.clz x) = .ok out ∧
      out.toList.map U256.toNat = (256 - U256.bitLength x) :: xs.map U256.toNat ∧
      ((countLeadingZeros ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeClz } }, w)) := by
  obtain ⟨stack, out, hp, _, push, model, run⟩ := countLeadingZeros_run_success ctx f w x xs h hc
  exact ⟨stack, out, hp, push, by rw [model, List.map_cons, U256.toNat_clz], run⟩

private theorem clz_success_world (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (x : U256) (xs : List U256) (h : f.stack.toList = x :: xs)
    (hc : ctx.config.costs.opcodeClz ≤ f.gasMeter.gasLeft)
    (run : ((countLeadingZeros ctx f).run w).run = .ok (.continue f', w')) :
    w' = w := by
  obtain ⟨_, _, _, _, _, _, expected⟩ := countLeadingZeros_run_success ctx f w x xs h hc
  exact (Prod.mk.inj (Except.ok.inj (run.symm.trans expected))).2

private theorem clz_zero_price_accounting (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((countLeadingZeros ctx f).run w).run = .ok (.continue f', w'))
    (zero : ctx.config.costs.opcodeClz = 0) : f'.gasMeter.phi = f.gasMeter.phi := by
  simpa only [zero, Nat.add_zero] using countLeadingZeros_continue_phi ctx f f' w w' h

private theorem clz_progress (ctx : FrameCtx) (f f' : Frame) (w w' : VmWorld Id)
    (h : ((countLeadingZeros ctx f).run w).run = .ok (.continue f', w'))
    (positive : 1 ≤ ctx.config.costs.opcodeClz) : f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  countLeadingZeros_continue_progress ctx f f' w w' h positive

end STFSpec.Conformance.Vm.Instructions.BitwiseCallerProofs
