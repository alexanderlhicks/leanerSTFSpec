/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.ChildSettled

/-!
# Incorporate a settled child frame

Library `EthVmCore`. Both outcomes return the child's meter fields to the
parent. Success also repays pending spill and combines the accumulated effects.
Spec guidance `STFSpec/informal/modules/EthVmCore.md` §§2.2/3/5/7.
-/

namespace STFSpec.Vm.Core

private def absorbChildGas (parent child : GasMeter) : GasMeter :=
  { parent with
    gasLeft := parent.gasLeft + child.gasLeft
    stateGasLeft := parent.stateGasLeft + child.stateGasLeft
    stateGasSpilled := parent.stateGasSpilled + child.stateGasSpilled
    refundCounter := parent.refundCounter + child.refundCounter }

/-- Incorporate a settled child into the parent.
EELS `src/ethereum/forks/amsterdam/vm/__init__.py:188–244`. -/
def incorporateChild (parent child : Frame) (childFailed : Bool)
    (_settled : ChildSettled child childFailed) : Frame :=
  let meter := absorbChildGas parent.gasMeter child.gasMeter
  if childFailed then
    { parent with gasMeter := meter }
  else
    { parent with
      gasMeter := repayStateGasSpill meter
      logs := parent.logs.append child.logs
      accountsToDelete := parent.accountsToDelete.union child.accountsToDelete
      accessedAddresses := parent.accessedAddresses.union child.accessedAddresses
      accessedStorageKeys := parent.accessedStorageKeys.union child.accessedStorageKeys }

/-- Incorporation adds exactly the child's gas potential to the parent's. -/
theorem incorporateChild_phi (parent child : Frame) (childFailed : Bool)
    (settled : ChildSettled child childFailed) :
    (incorporateChild parent child childFailed settled).gasMeter.phi =
      parent.gasMeter.phi + child.gasMeter.phi := by
  have noCommittedSpill := settled.1
  cases childFailed
  · change (repayStateGasSpill (absorbChildGas parent.gasMeter child.gasMeter)).phi = _
    rw [repayStateGasSpill_phi]
    simp only [absorbChildGas, GasMeter.phi, noCommittedSpill]
    omega
  · change (absorbChildGas parent.gasMeter child.gasMeter).phi = _
    simp only [absorbChildGas, GasMeter.phi, noCommittedSpill]
    omega

/-- On success the child's warm addresses suffice when they include the parent's. -/
theorem incorporateChild_accessedAddresses_of_subset (parent child : Frame)
    (settled : ChildSettled child false)
    (included : ∀ a, a ∈ parent.accessedAddresses → a ∈ child.accessedAddresses) :
    (incorporateChild parent child false settled).accessedAddresses = child.accessedAddresses := by
  change parent.accessedAddresses.union child.accessedAddresses = _
  apply Std.ExtTreeSet.ext_mem
  intro a
  rw [Std.ExtTreeSet.union_eq, Std.ExtTreeSet.mem_union_iff]
  exact ⟨fun which ↦ which.elim (included a) id, Or.inr⟩

/-- On success the child's warm slots suffice when they include the parent's. -/
theorem incorporateChild_accessedStorageKeys_of_subset (parent child : Frame)
    (settled : ChildSettled child false)
    (included : ∀ k, k ∈ parent.accessedStorageKeys → k ∈ child.accessedStorageKeys) :
    (incorporateChild parent child false settled).accessedStorageKeys =
      child.accessedStorageKeys := by
  change parent.accessedStorageKeys.union child.accessedStorageKeys = _
  apply Std.ExtTreeSet.ext_mem
  intro k
  rw [Std.ExtTreeSet.union_eq, Std.ExtTreeSet.mem_union_iff]
  exact ⟨fun which ↦ which.elim (included k) id, Or.inr⟩

end STFSpec.Vm.Core
