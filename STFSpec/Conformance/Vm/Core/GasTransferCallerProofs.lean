/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Public gas-transfer clients

Library `EthConformance`. Consume all eight public laws without unfolding providers.
Complete local round trips do not establish actual caller reachability or settlement.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/7.
-/

namespace STFSpec.Conformance.Vm.Core.GasTransferCallerProofs
open STFSpec.Vm.Core

private theorem forfeit_retains_fields (m : GasMeter) (h : m.stateGasSpilled = 0) :
    (forfeitRemainingGas m h).stateGasLeft = m.stateGasLeft ∧
    (forfeitRemainingGas m h).stateGasBaseline = m.stateGasBaseline ∧
    (forfeitRemainingGas m h).refundCounter = m.refundCounter ∧
    (forfeitRemainingGas m h).stateGasSpilled = m.stateGasSpilled ∧
    (forfeitRemainingGas m h).stateGasCommittedSpill = m.stateGasCommittedSpill := by
  rw [forfeitRemainingGas_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem withhold_retains_fields (m : GasMeter) :
    (withholdCreateGas m).2.stateGasLeft = m.stateGasLeft ∧
    (withholdCreateGas m).2.stateGasBaseline = m.stateGasBaseline ∧
    (withholdCreateGas m).2.refundCounter = m.refundCounter ∧
    (withholdCreateGas m).2.stateGasSpilled = m.stateGasSpilled ∧
    (withholdCreateGas m).2.stateGasCommittedSpill = m.stateGasCommittedSpill := by
  rw [withholdCreateGas_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem drain_retains_fields (m : GasMeter) :
    (drainStateGasReservoir m).2.gasLeft = m.gasLeft ∧
    (drainStateGasReservoir m).2.stateGasBaseline = m.stateGasBaseline ∧
    (drainStateGasReservoir m).2.refundCounter = m.refundCounter ∧
    (drainStateGasReservoir m).2.stateGasSpilled = m.stateGasSpilled ∧
    (drainStateGasReservoir m).2.stateGasCommittedSpill = m.stateGasCommittedSpill := by
  rw [drainStateGasReservoir_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem restore_retains_fields (m : GasMeter) (g T : Nat) :
    (restoreChildGas m g T).stateGasBaseline = m.stateGasBaseline ∧
    (restoreChildGas m g T).refundCounter = m.refundCounter ∧
    (restoreChildGas m g T).stateGasSpilled = m.stateGasSpilled ∧
    (restoreChildGas m g T).stateGasCommittedSpill = m.stateGasCommittedSpill := by
  rw [restoreChildGas_eq]
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem retained_execution (m : GasMeter) :
    (withholdCreateGas m).2.gasLeft = m.gasLeft / 64 := by
  rw [withholdCreateGas_eq]
  have hDiv : m.gasLeft / 64 ≤ m.gasLeft := Nat.div_le_self _ _
  simp only
  omega

private theorem forfeit_again (m : GasMeter) (h : m.stateGasSpilled = 0) :
    ∃ h' : (forfeitRemainingGas m h).stateGasSpilled = 0,
      forfeitRemainingGas (forfeitRemainingGas m h) h' = forfeitRemainingGas m h := by
  have h' : (forfeitRemainingGas m h).stateGasSpilled = 0 :=
    (forfeit_retains_fields m h).2.2.2.1.trans h
  refine ⟨h', ?_⟩
  rw [forfeitRemainingGas_eq, forfeitRemainingGas_eq]

private theorem drain_again (m : GasMeter) :
    drainStateGasReservoir (drainStateGasReservoir m).2 =
      (0, (drainStateGasReservoir m).2) := by
  rw [drainStateGasReservoir_eq, drainStateGasReservoir_eq]

private theorem restore_zero (m : GasMeter) : restoreChildGas m 0 0 = m := by
  rw [restoreChildGas_eq]
  simp only [Nat.add_zero]

private theorem restore_withhold_drain (m : GasMeter) :
    let w := withholdCreateGas m
    let d := drainStateGasReservoir w.2
    restoreChildGas d.2 w.1 d.1 = m := by
  simp only
  rw [drainStateGasReservoir_eq, withholdCreateGas_eq, restoreChildGas_eq]
  have hGrant : m.gasLeft - m.gasLeft / 64 ≤ m.gasLeft := Nat.sub_le _ _
  have he : m.gasLeft - (m.gasLeft - m.gasLeft / 64) +
      (m.gasLeft - m.gasLeft / 64) = m.gasLeft := Nat.sub_add_cancel hGrant
  simp only [he, Nat.zero_add]

private theorem roundtrip_potential (m : GasMeter) :
    let w := withholdCreateGas m
    let d := drainStateGasReservoir w.2
    (restoreChildGas d.2 w.1 d.1).phi = m.phi := by
  simp only
  rw [restoreChildGas_phi, drainStateGasReservoir_phi]
  exact withholdCreateGas_phi m

private theorem ordinary_rollback_forfeit (m : GasMeter) :
    let r := restoreStateGas m
    forfeitRemainingGas r (restoreStateGas_post m).1 =
      { m with
        gasLeft := 0, stateGasLeft := m.stateGasBaseline,
        refundCounter := 0, stateGasSpilled := 0 } := by
  simp only
  rw [forfeitRemainingGas_eq, restoreStateGas_eq]

private theorem ordinary_rollback_forfeit_potential (m : GasMeter) :
    (forfeitRemainingGas (restoreStateGas m) (restoreStateGas_post m).1).phi =
      m.stateGasCommittedSpill := by
  have h := (forfeitRemainingGas_phi (restoreStateGas m) (restoreStateGas_post m).1).1
  have retained : (restoreStateGas m).stateGasCommittedSpill = m.stateGasCommittedSpill := by
    rw [restoreStateGas_eq]
  exact h.trans retained

private theorem entry_rollback_forfeit (m : GasMeter) (T : Nat)
    (hB : m.stateGasBaseline ≤ T) (hq : m.refundCounter = 0) :
    let r := restoreStateGasToEntry m T hB hq
    forfeitRemainingGas r (restoreStateGasToEntry_post m T hB hq).1 =
      { m with
        gasLeft := 0, stateGasLeft := T, stateGasBaseline := T,
        stateGasSpilled := 0, stateGasCommittedSpill := 0 } := by
  simp only
  rw [forfeitRemainingGas_eq, restoreStateGasToEntry_eq]

end STFSpec.Conformance.Vm.Core.GasTransferCallerProofs
