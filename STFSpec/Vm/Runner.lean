/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Runner.Budget
import STFSpec.Vm.Runner.Checked
import STFSpec.Vm.Runner.RunChecked
import STFSpec.Vm.Runner.Environment
import STFSpec.Vm.Runner.ExecKind
import STFSpec.Vm.Runner.Output

/-!
# STFSpec.Vm.Runner

The recursive call executor: the frame loop, child execution, named resume operations, and termination.

Library `EthVmRunner`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). The facade exports budget and entry-kind
vocabulary, raw `RunnerEnv`, output records, child outcome conversion, checked control
carriers and the F14 VM adapter. Recursive execution and fuel guarantees remain open.
Spec guidance: `STFSpec/informal/modules/EthVmRunner.md`.
-/
