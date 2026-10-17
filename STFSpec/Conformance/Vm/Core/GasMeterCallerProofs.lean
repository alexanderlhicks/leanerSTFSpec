/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Ordinary public charge-kernel callers

Library `EthConformance`. Generic all-raw-meter clients use only the ten public laws.
Positive execution-charge progress is conditional on the supplied positive amount.
No frame, schedule, settlement or runner progress is asserted.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/7.
-/

namespace STFSpec.Conformance.Vm.Core.GasMeterCallerProofs
open STFSpec.Vm.Core

private theorem check_success (g : GasMeter) (a : Nat) :
    checkGas g a = .ok () ↔ a ≤ g.gasLeft := checkGas_eq_ok_iff g a

private theorem check_failure (g : GasMeter) (a : Nat) (e : ExceptionalHalt) :
    checkGas g a = .error e ↔ g.gasLeft < a ∧ e = .outOfGas :=
  checkGas_eq_error_iff g a e

private theorem charged_fields (g : GasMeter) (a : Nat) (h : a ≤ g.gasLeft) :
    chargeGas g a = .ok { g with gasLeft := g.gasLeft - a } := chargeGas_of_le g a h

private theorem charge_failure (g : GasMeter) (a : Nat) (e : ExceptionalHalt) :
    chargeGas g a = .error e ↔ g.gasLeft < a ∧ e = .outOfGas :=
  chargeGas_eq_error_iff g a e

private theorem positive_charge_progress (g g' : GasMeter) (a : Nat)
    (h : chargeGas g a = .ok g') (ha : 1 ≤ a) : g'.phi + 1 ≤ g.phi := by
  have hp := chargeGas_phi g a g' h
  omega

private theorem zero_charge_neutral (g g' : GasMeter)
    (h : chargeGas g 0 = .ok g') : g'.phi = g.phi := by
  have hp := chargeGas_phi g 0 g' h
  omega

private theorem reservoir_fields (g : GasMeter) (a : Nat) (h : a ≤ g.stateGasLeft) :
    chargeStateGas g a = .ok { g with stateGasLeft := g.stateGasLeft - a } :=
  chargeStateGas_of_le g a h

private theorem spill_fields (g : GasMeter) (a : Nat) (hR : g.stateGasLeft < a)
    (hA : a ≤ g.stateGasLeft + g.gasLeft) :
    chargeStateGas g a = .ok { g with
      gasLeft := g.gasLeft - (a - g.stateGasLeft)
      stateGasLeft := 0
      stateGasSpilled := g.stateGasSpilled + (a - g.stateGasLeft) } :=
  chargeStateGas_of_lt g a hR hA

private theorem state_failure (g : GasMeter) (a : Nat) (e : ExceptionalHalt) :
    chargeStateGas g a = .error e ↔ g.stateGasLeft + g.gasLeft < a ∧ e = .outOfGas :=
  chargeStateGas_eq_error_iff g a e

private theorem execution_then_state (g g' g'' : GasMeter) (a b : Nat)
    (h : chargeGas g a = .ok g') (hs : chargeStateGas g' b = .ok g'') :
    g''.phi + a = g.phi ∧ g''.gasLeft ≤ g'.gasLeft := by
  have hp := chargeGas_phi g a g' h
  have hsphi := chargeStateGas_phi g' b g'' hs
  exact ⟨by omega, chargeStateGas_gasLeft_le g' b g'' hs⟩

private theorem source_error_distinct (g : GasMeter) (a : Nat) (code : UInt8) :
    chargeGas g a ≠ .error (.invalidOpcode code) := by
  intro h
  have he := (chargeGas_eq_error_iff g a (.invalidOpcode code)).mp h
  cases he.2

private theorem bare_reason_retained (reason : String) :
    (match ExceptionalHalt.precompileHalt reason with
     | .precompileHalt payload => payload
     | _ => "") = reason := rfl

private theorem opcode_retained (code : UInt8) :
    (match ExceptionalHalt.invalidOpcode code with
     | .invalidOpcode payload => payload
     | _ => 0) = code := rfl

end STFSpec.Conformance.Vm.Core.GasMeterCallerProofs
