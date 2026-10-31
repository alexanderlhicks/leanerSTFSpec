/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.GasMeter

/-!
# Selectable per-frame budget vocabulary

Library `EthVmRunner`. Pure mathematical policies over the existing complete `GasMeter`.
These definitions install no runner default and prove no fuel adequacy: `phiBudget` remains
the unproved candidate of B11. There is no corresponding EELS budget function.
Spec guidance: `STFSpec/informal/modules/EthVmRunner.md` §§3/5/7.
-/

namespace STFSpec.Vm.Runner

open STFSpec.Vm.Core

/-- A pure policy on every finite raw meter, with no well-formedness premise. -/
abbrev BudgetPolicy := GasMeter → Nat

/-- The B11 candidate, using the existing meter potential; sufficiency remains unproved. -/
def phiBudget : BudgetPolicy := fun m ↦ m.phi + 1

/-- A selectable constant policy, including zero, independent of the complete meter. -/
def constBudget (n : Nat) : BudgetPolicy := fun _ ↦ n

end STFSpec.Vm.Runner
