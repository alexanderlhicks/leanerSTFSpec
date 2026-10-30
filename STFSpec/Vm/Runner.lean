/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Runner.Budget
import STFSpec.Vm.Runner.ExecKind

/-!
# STFSpec.Vm.Runner

The recursive call executor: the frame loop, child execution, named resume operations, and termination.

Library `EthVmRunner`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). Budget and entry-kind vocabulary are supplied;
recursive execution and fuel guarantees remain open.
Spec guidance: `STFSpec/informal/modules/EthVmRunner.md`.
-/
