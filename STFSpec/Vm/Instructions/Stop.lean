/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions.Handler

/-!
# STOP

Library `EthVmInstructions`. The terminal handler follows pinned EELS
`src/ethereum/forks/amsterdam/vm/instructions/control_flow.py:22–42`.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§3/5/7.
-/

namespace STFSpec.Vm.Instructions
open STFSpec.Base STFSpec.Vm.Core

/-- Stop with empty output, advancing PC and retaining the complete frame and world.
EELS `src/ethereum/forks/amsterdam/vm/instructions/control_flow.py:22–42`.
Source correspondence requires empty source output and no existing source error;
these control fields are distinct from Frame.returnData. -/
def stop {m : Type → Type} [Monad m] : Handler m :=
  fun _ f ↦ pure (.stop { f with pc := f.pc + 1 } Bytes.empty)

/-- Complete STOP transformer equation, under the supplied underlying `pure`.
No law or effect interpretation of that arbitrary `pure` is assumed. -/
theorem stop_run {m : Type → Type} [Monad m]
    (ctx : FrameCtx) (f : Frame) (w : VmWorld m) :
    ((stop ctx f).run w).run =
      pure (Except.ok
        (StepResult.stop { f with pc := f.pc + 1 } Bytes.empty, w)) := rfl

end STFSpec.Vm.Instructions
