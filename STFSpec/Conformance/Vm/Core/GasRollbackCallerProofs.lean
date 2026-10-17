/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Public gas rollback clients

Library `EthConformance`. Ordinary generic clients consume all eight rollback laws.
No caller reachability, child settlement, transaction conservation or fuel claim follows.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/7.
-/

namespace STFSpec.Conformance.Vm.Core.GasRollbackCallerProofs
open STFSpec.Vm.Core

private theorem commit_fields (m : GasMeter)
    (h : m.stateGasLeft ≤ m.stateGasBaseline) :
    commitStateGas m h = { m with
      stateGasCommittedSpill := m.stateGasCommittedSpill + m.stateGasSpilled
      stateGasBaseline := m.stateGasLeft
      stateGasSpilled := 0 } := commitStateGas_eq m h

private theorem commit_lowers_baseline (m : GasMeter)
    (h : m.stateGasLeft ≤ m.stateGasBaseline) :
    (commitStateGas m h).stateGasBaseline ≤ m.stateGasBaseline := by
  rw [commitStateGas_eq]
  exact h

private theorem restore_fields (m : GasMeter) :
    restoreStateGas m = { m with
      gasLeft := m.gasLeft + m.stateGasSpilled
      stateGasSpilled := 0
      stateGasLeft := m.stateGasBaseline
      refundCounter := 0 } :=
  restoreStateGas_eq m

private theorem restore_retains_committed (m : GasMeter) :
    (restoreStateGas m).stateGasCommittedSpill = m.stateGasCommittedSpill := by
  rw [restoreStateGas_eq]

private theorem restore_idempotent (m : GasMeter) :
    restoreStateGas (restoreStateGas m) = restoreStateGas m := by
  rw [restoreStateGas_eq, restoreStateGas_eq]
  simp only [Nat.add_zero]

private theorem entry_fields (m : GasMeter) (R : Nat)
    (h₁ : m.stateGasBaseline ≤ R) (h₂ : m.refundCounter = 0) :
    restoreStateGasToEntry m R h₁ h₂ = { m with
      gasLeft := m.gasLeft + m.stateGasSpilled + m.stateGasCommittedSpill,
      stateGasSpilled := 0, stateGasCommittedSpill := 0,
      stateGasLeft := R, stateGasBaseline := R } :=
  restoreStateGasToEntry_eq m R h₁ h₂

private theorem entry_post (m : GasMeter) (R : Nat)
    (h₁ : m.stateGasBaseline ≤ R) (h₂ : m.refundCounter = 0) :
    (restoreStateGasToEntry m R h₁ h₂).stateGasSpilled = 0 ∧
    (restoreStateGasToEntry m R h₁ h₂).stateGasCommittedSpill = 0 ∧
    (restoreStateGasToEntry m R h₁ h₂).refundCounter = 0 ∧
    (restoreStateGasToEntry m R h₁ h₂).stateGasLeft = R ∧
    (restoreStateGasToEntry m R h₁ h₂).stateGasBaseline = R :=
  restoreStateGasToEntry_post m R h₁ h₂

private theorem equal_inputs (m n : GasMeter) (heq : m = n)
    (hm : m.stateGasLeft ≤ m.stateGasBaseline)
    (hn : n.stateGasLeft ≤ n.stateGasBaseline) :
    commitStateGas m hm = commitStateGas n hn := by
  rw [commitStateGas_eq, commitStateGas_eq, heq]

private theorem charge_commit_rollback_phi (m charged : GasMeter) (a R : Nat)
    (hc : chargeStateGas m a = .ok charged)
    (hk : charged.stateGasLeft ≤ charged.stateGasBaseline)
    (hr : (restoreStateGas (commitStateGas charged hk)).stateGasBaseline ≤ R) :
    (restoreStateGasToEntry (restoreStateGas (commitStateGas charged hk)) R hr
      (restoreStateGas_post _).2.1).phi = m.phi := by
  rw [restoreStateGasToEntry_phi, restoreStateGas_phi, commitStateGas_phi]
  exact chargeStateGas_phi m a charged hc

end STFSpec.Conformance.Vm.Core.GasRollbackCallerProofs
