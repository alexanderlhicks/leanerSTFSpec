/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.Exceptions
import STFSpec.Vm.Core.GasMeter
import STFSpec.Vm.Core.Memory
import STFSpec.Vm.Core.Stack

/-!
# STFSpec.Vm.Core

The `Evm` frame, `Message`, environments, operand stack, memory, gas meter and
gas parameters, and jumpdest analysis.

Library `EthVmCore`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). The local gas algebra, bounded Stack,
aligned Memory, padded buffer read and nominal exceptional halts are supplied;
other components remain scaffolding.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md`.
-/
