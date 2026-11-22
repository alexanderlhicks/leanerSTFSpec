/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions

/-!
# ISZERO public-law clients

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

end STFSpec.Conformance.Vm.Instructions.ComparisonCallerProofs
