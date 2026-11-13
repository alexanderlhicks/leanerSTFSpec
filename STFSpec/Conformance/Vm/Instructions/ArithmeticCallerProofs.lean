/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions

/-!
# Arithmetic public-law clients

Library `EthConformance`. Generic consumers retain complete action equations;
actual Id consumers use exact accounting and locally conditional progress.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Instructions.ArithmeticCallerProofs
open STFSpec.Base STFSpec.Vm.Core STFSpec.Vm.Instructions

private def signatures {m : Type → Type} [Monad m] : Handler m × Handler m :=
  (add, sub)

private theorem empty_precedence {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (h : f.stack.toList = []) :
    ((add ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) ∧
    ((sub ctx f).run w).run = pure (Except.ok (.halt f .stackUnderflow, w)) :=
  ⟨add_run_empty ctx f w h, sub_run_empty ctx f w h⟩

private theorem add_singleton_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ rest : Stack, rest.toList = [] ∧
      ((add ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .stackUnderflow, w)) := by
  obtain ⟨rest, _, hm, hr⟩ := add_run_singleton ctx f w x h
  exact ⟨rest, hm, hr⟩

private theorem add_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeAdd) :
    ∃ rest : Stack, rest.size = xs.length ∧
      ((add ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .outOfGas, w)) := by
  obtain ⟨_, rest, _, _, hm, hr⟩ := add_run_oog ctx f w x y xs h hc
  exact ⟨rest, by rw [Stack.size_eq_length_toList, hm], hr⟩

private theorem add_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : ctx.config.costs.opcodeAdd ≤ f.gasMeter.gasLeft) :
    ∃ out : Stack, out.toList = U256.add x y :: xs ∧
      ((add ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeAdd } }, w)) := by
  obtain ⟨_, _, out, _, _, _, _, hm, hr⟩ := add_run_success ctx f w x y xs h hc
  exact ⟨out, hm, hr⟩

private theorem add_accounting (ctx : FrameCtx) (f f' : Frame)
    (w w' : VmWorld Id)
    (h : ((add ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeAdd) :
    f'.gasMeter.phi + ctx.config.costs.opcodeAdd = f.gasMeter.phi ∧
      f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  ⟨add_continue_phi ctx f f' w w' h, add_continue_progress ctx f f' w w' h hc⟩

private theorem sub_singleton_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x : U256)
    (h : f.stack.toList = [x]) :
    ∃ rest : Stack, rest.toList = [] ∧
      ((sub ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .stackUnderflow, w)) := by
  obtain ⟨rest, _, hm, hr⟩ := sub_run_singleton ctx f w x h
  exact ⟨rest, hm, hr⟩

private theorem sub_shortage_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : f.gasMeter.gasLeft < ctx.config.costs.opcodeSub) :
    ∃ rest : Stack, rest.size = xs.length ∧
      ((sub ctx f).run w).run =
        pure (Except.ok (.halt { f with stack := rest } .outOfGas, w)) := by
  obtain ⟨_, rest, _, _, hm, hr⟩ := sub_run_oog ctx f w x y xs h hc
  exact ⟨rest, by rw [Stack.size_eq_length_toList, hm], hr⟩

private theorem sub_success_model {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) (x y : U256) (xs : List U256)
    (h : f.stack.toList = x :: y :: xs) (hc : ctx.config.costs.opcodeSub ≤ f.gasMeter.gasLeft) :
    ∃ out : Stack, out.toList = U256.sub x y :: xs ∧
      ((sub ctx f).run w).run = pure (Except.ok
        (.continue { f with
          pc := f.pc + 1
          stack := out
          gasMeter := { f.gasMeter with
            gasLeft := f.gasMeter.gasLeft - ctx.config.costs.opcodeSub } }, w)) := by
  obtain ⟨_, _, out, _, _, _, _, hm, hr⟩ := sub_run_success ctx f w x y xs h hc
  exact ⟨out, hm, hr⟩

private theorem sub_accounting (ctx : FrameCtx) (f f' : Frame)
    (w w' : VmWorld Id)
    (h : ((sub ctx f).run w).run = .ok (.continue f', w'))
    (hc : 1 ≤ ctx.config.costs.opcodeSub) :
    f'.gasMeter.phi + ctx.config.costs.opcodeSub = f.gasMeter.phi ∧
      f'.gasMeter.phi + 1 ≤ f.gasMeter.phi :=
  ⟨sub_continue_phi ctx f f' w w' h, sub_continue_progress ctx f f' w w' h hc⟩

end STFSpec.Conformance.Vm.Instructions.ArithmeticCallerProofs
