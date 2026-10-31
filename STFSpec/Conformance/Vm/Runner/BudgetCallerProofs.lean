/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Runner

/-!
# Ordinary budget-policy clients

Library `EthConformance`. Private generic clients reduce only the owned simple policy
definitions and use public meter laws. No runner or adequacy claim follows.
Spec guidance: `STFSpec/informal/modules/EthVmRunner.md` §§3/5/7.
-/

namespace STFSpec.Conformance.Vm.Runner.BudgetCallerProofs
open STFSpec.Vm.Core STFSpec.Vm.Runner

private def callback (policy : GasMeter → Nat) (meter : GasMeter) : Nat := policy meter

private theorem policy_signature : BudgetPolicy = (GasMeter → Nat) := rfl

private theorem phi_equation (meter : GasMeter) : phiBudget meter = meter.phi + 1 := rfl

private theorem constant_equation (n : Nat) (meter : GasMeter) : constBudget n meter = n := rfl

private theorem phi_callback (meter : GasMeter) :
    callback phiBudget meter = meter.phi + 1 := rfl

private theorem constant_callback (n : Nat) (meter : GasMeter) :
    callback (constBudget n) meter = n := rfl

private theorem positive (meter : GasMeter) : 0 < phiBudget meter := by
  rw [phi_equation]
  exact Nat.zero_lt_succ _

private theorem constant_independent (n : Nat) (left right : GasMeter) :
    constBudget n left = constBudget n right := rfl

private theorem potential_transport (left right : GasMeter) (h : left.phi = right.phi) :
    phiBudget left = phiBudget right := by
  rw [phi_equation, phi_equation, h]

private theorem signed_refund_independent (meter : GasMeter) (refund : Int) :
    phiBudget (addRefund meter refund) = phiBudget meter :=
  potential_transport _ _ (addRefund_phi meter refund)

private theorem reservoir_drain_independent (meter : GasMeter) :
    phiBudget (drainStateGasReservoir meter).2 = phiBudget meter :=
  potential_transport _ _ (drainStateGasReservoir_phi meter)

end STFSpec.Conformance.Vm.Runner.BudgetCallerProofs
