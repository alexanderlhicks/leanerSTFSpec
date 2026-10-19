/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.Exceptions
import STFSpec.Vm.Core.GasMeter

/-!
# STFSpec.Vm.Core

The `Evm` frame, `Message`, environments, operand stack, memory, gas meter and
gas parameters, and jumpdest analysis.

Library `EthVmCore`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). The charge kernel and nominal exceptional
halts are supplied; other components remain scaffolding.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md`.
-/
