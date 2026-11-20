/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.World
import STFSpec.Vm.Instructions.StepResult

/-!
# Instruction handler signature

Library `EthVmInstructions`. The alias retains the original immutable context as
the result index and needs no monad instance to form.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§3/5/7.
-/

namespace STFSpec.Vm.Instructions
open STFSpec.Vm.Core

/-- A handler returns mutable frame/control data under its supplied fixed context.
Actual operations impose their own monad and hashing requirements. -/
abbrev Handler (m : Type → Type) := (ctx : FrameCtx) → Frame → VmM m (StepResult ctx)

end STFSpec.Vm.Instructions
