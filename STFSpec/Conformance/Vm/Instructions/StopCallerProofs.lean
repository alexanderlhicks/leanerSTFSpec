/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions

/-!
# STOP law clients

Library `EthConformance`. Private clients use the public complete transformer law
without representation unfolding or extra monad, hash or admission premises.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Instructions.StopCallerProofs
open STFSpec.Base STFSpec.Vm.Core STFSpec.Vm.Instructions

private def signature {m : Type → Type} [Monad m] : Handler m := stop

private theorem generic_run {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) :
    ((stop ctx f).run w).run =
      pure (Except.ok (.stop { f with pc := f.pc + 1 } Bytes.empty, w)) :=
  stop_run ctx f w

private theorem id_run (ctx : FrameCtx) (f : Frame) (w : VmWorld Id) :
    ((stop ctx f).run w).run =
      Except.ok (.stop { f with pc := f.pc + 1 } Bytes.empty, w) :=
  stop_run ctx f w

private theorem complete_retention (ctx : FrameCtx) (f : Frame) (w : VmWorld Id)
    (r : StepResult ctx) (after : VmWorld Id)
    (h : ((stop ctx f).run w).run = .ok (r, after)) :
    r = .stop { f with pc := f.pc + 1 } Bytes.empty ∧ after = w := by
  rw [stop_run] at h
  have hp := Prod.mk.inj (Except.ok.inj h)
  exact ⟨hp.1.symm, hp.2.symm⟩

end STFSpec.Conformance.Vm.Instructions.StopCallerProofs
