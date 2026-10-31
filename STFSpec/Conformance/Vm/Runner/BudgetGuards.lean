/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Runner

/-!
# Bounded complete-meter budget controls

Library `EthConformance`. Every field is explicitly supplied; independent larger controls
are consumed by the interpreted/native producer. These are mathematical policy tests.
Spec guidance: `STFSpec/informal/modules/EthVmRunner.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Runner.BudgetGuards
open STFSpec.Vm.Core STFSpec.Vm.Runner

#guard phiBudget (GasMeter.mk 0 0 0 0 0 0) == 1
#guard phiBudget (GasMeter.mk 1 0 0 0 0 0) == 2
#guard phiBudget (GasMeter.mk 0 0 0 0 1 0) == 2
#guard phiBudget (GasMeter.mk 0 0 0 0 0 1) == 2
#guard phiBudget (GasMeter.mk 2 999 0 (-1000) 3 5) == 11
#guard phiBudget (GasMeter.mk 2 0 999 1000 3 5) == 11
#guard constBudget 0 (GasMeter.mk 2 999 0 (-1000) 3 5) == 0
#guard constBudget 17 (GasMeter.mk 0 0 0 0 0 0) == 17
#guard constBudget 17 (GasMeter.mk 2 999 0 (-1000) 3 5) == 17

end STFSpec.Conformance.Vm.Runner.BudgetGuards
