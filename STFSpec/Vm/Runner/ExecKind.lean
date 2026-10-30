/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

/-!
# Execution entry-kind vocabulary

Library `EthVmRunner`. Project vocabulary for the three specified execution entries.
The execution relation and its meaning remain open; this carrier supplies no runner.
Spec guidance: `STFSpec/informal/modules/EthVmRunner.md` §§3/5/7.
-/

namespace STFSpec.Vm.Runner

/-- The three entry kinds specified for the prospective execution relation. -/
inductive ExecKind
  | frameLoop
  | call
  | create

end STFSpec.Vm.Runner
