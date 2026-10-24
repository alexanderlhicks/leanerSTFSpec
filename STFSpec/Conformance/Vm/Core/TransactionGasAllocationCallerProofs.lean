/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Public-law allocation clients

Library `EthConformance`. Nine private client groups on arbitrary raw data and
local proofs. Constructed meters establish no Runner reachability or G1–G7 gate.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Conformance.Vm.Core.TransactionGasAllocationCallerProofs
open STFSpec.Vm.Core

-- 1. Raw construction, extensionality, eta, independently varied fields.
private theorem raw (a b : EvmGasAllocation) (hE : a.executionGas = b.executionGas)
    (hR : a.stateGasReservoir = b.stateGasReservoir) : a = b :=
  EvmGasAllocation.ext a b hE hR

private theorem reconstruct (e r : Nat) :
    EvmGasAllocation.mk (EvmGasAllocation.mk e r).executionGas
      (EvmGasAllocation.mk e r).stateGasReservoir = EvmGasAllocation.mk e r :=
  EvmGasAllocation.eta _

private theorem raw_distinct (e r : Nat) (h : e ≠ r) :
    EvmGasAllocation.mk e r ≠ EvmGasAllocation.mk r e := by
  intro he
  exact h (congrArg EvmGasAllocation.executionGas he)

-- 2. Both projections from the public complete equation.
private theorem projections (cfg : VmConfig) (t i : Nat) (ht : i ≤ t)
    (hc : i ≤ cfg.costs.txMaxGasLimit) :
    let a := allocateEvmGas cfg t i ht hc
    a.executionGas = min (cfg.costs.txMaxGasLimit - i) (t - i) ∧
    a.stateGasReservoir = (t - i) - min (cfg.costs.txMaxGasLimit - i) (t - i) := by
  rw [allocateEvmGas_eq]
  exact ⟨rfl, rfl⟩

-- 3. Local arithmetic identities, with no transaction conservation claim.
private theorem arithmetic (cfg : VmConfig) (t i : Nat) (ht : i ≤ t)
    (hc : i ≤ cfg.costs.txMaxGasLimit) :
    let a := allocateEvmGas cfg t i ht hc
    i + a.executionGas + a.stateGasReservoir = t ∧
    i + a.executionGas = min cfg.costs.txMaxGasLimit t ∧
    a.stateGasReservoir = t - cfg.costs.txMaxGasLimit := by
  have hp := projections cfg t i ht hc
  dsimp only at hp ⊢
  omega

-- 4. Complete branches, overlap, zero and exact boundaries, all local bounds.
private theorem below (cfg : VmConfig) (t i : Nat) (ht : i ≤ t)
    (hc : i ≤ cfg.costs.txMaxGasLimit) (h : t ≤ cfg.costs.txMaxGasLimit) :
    allocateEvmGas cfg t i ht hc = EvmGasAllocation.mk (t - i) 0 := by
  apply EvmGasAllocation.ext
  · have hp := projections cfg t i ht hc; dsimp only at hp ⊢; omega
  · have hp := projections cfg t i ht hc; dsimp only at hp ⊢; omega

private theorem above (cfg : VmConfig) (t i : Nat) (ht : i ≤ t)
    (hc : i ≤ cfg.costs.txMaxGasLimit) (h : cfg.costs.txMaxGasLimit ≤ t) :
    allocateEvmGas cfg t i ht hc =
      EvmGasAllocation.mk (cfg.costs.txMaxGasLimit - i) (t - cfg.costs.txMaxGasLimit) := by
  apply EvmGasAllocation.ext
  · have hp := projections cfg t i ht hc; dsimp only at hp ⊢; omega
  · have hp := arithmetic cfg t i ht hc; dsimp only at hp; exact hp.2.2

private theorem boundaries (cfg : VmConfig) (i : Nat) (hc : i ≤ cfg.costs.txMaxGasLimit) :
    allocateEvmGas cfg i i (Nat.le_refl _) hc = EvmGasAllocation.mk 0 0 ∧
    allocateEvmGas cfg cfg.costs.txMaxGasLimit i hc hc =
      EvmGasAllocation.mk (cfg.costs.txMaxGasLimit - i) 0 := by
  constructor
  · calc
      _ = EvmGasAllocation.mk (i - i) 0 := below cfg i i (Nat.le_refl _) hc hc
      _ = EvmGasAllocation.mk 0 0 := by rw [Nat.sub_self]
  · exact below _ _ _ _ _ (Nat.le_refl _)

private theorem zero_cap (cfg : VmConfig) (h : cfg.costs.txMaxGasLimit = 0) (t : Nat) :
    allocateEvmGas cfg t 0 (Nat.zero_le _) (by omega) = EvmGasAllocation.mk 0 t := by
  calc
    _ = EvmGasAllocation.mk (cfg.costs.txMaxGasLimit - 0) (t - cfg.costs.txMaxGasLimit) :=
      above cfg t 0 (Nat.zero_le _) (by omega) (by omega)
    _ = EvmGasAllocation.mk 0 t := by rw [h, Nat.sub_zero, Nat.sub_zero]

private theorem bounds (cfg : VmConfig) (t i : Nat) (ht : i ≤ t)
    (hc : i ≤ cfg.costs.txMaxGasLimit) :
    let a := allocateEvmGas cfg t i ht hc
    a.executionGas ≤ t - i ∧ a.executionGas ≤ cfg.costs.txMaxGasLimit - i ∧
      a.stateGasReservoir ≤ t - i := by
  have hp := projections cfg t i ht hc
  dsimp only at hp ⊢
  omega

private def entry (a : EvmGasAllocation) : GasMeter :=
  GasMeter.mk a.executionGas a.stateGasReservoir a.stateGasReservoir 0 0 0

-- 5. Cap transport, independent proofs, unrelated costs/state/limits and meters.
private theorem transport (a b : VmConfig) (t i : Nat) (ha : i ≤ t)
    (hca : i ≤ a.costs.txMaxGasLimit) (hb : i ≤ t)
    (hcb : i ≤ b.costs.txMaxGasLimit) (h : a.costs.txMaxGasLimit = b.costs.txMaxGasLimit) :
    allocateEvmGas a t i ha hca = allocateEvmGas b t i hb hcb ∧
      entry (allocateEvmGas a t i ha hca) = entry (allocateEvmGas b t i hb hcb) := by
  have he := allocateEvmGas_congr a b t i ha hca hb hcb h
  exact ⟨he, congrArg entry he⟩

private theorem derived_cap (a b : VmConfig) (t i : Nat) (ht : i ≤ t)
    (hc : i ≤ a.costs.txMaxGasLimit) (h : a.costs.txMaxGasLimit = b.costs.txMaxGasLimit) :
    allocateEvmGas a t i ht hc = allocateEvmGas b t i ht (by omega) :=
  allocateEvmGas_congr _ _ _ _ _ _ _ _ h

-- 6. Changed-cap complete counterexample and intrinsic-independent reservoir.
private theorem changed_cap (a b : VmConfig)
    (ha : a.costs.txMaxGasLimit = 7) (hb : b.costs.txMaxGasLimit = 9) :
    allocateEvmGas a 9 2 (by decide) (by omega) = EvmGasAllocation.mk 5 2 ∧
    allocateEvmGas b 9 2 (by decide) (by omega) = EvmGasAllocation.mk 7 0 ∧
    allocateEvmGas a 9 2 (by decide) (by omega) ≠ allocateEvmGas b 9 2 (by decide) (by omega) := by
  have ea := above a 9 2 (by decide) (by omega) (by omega)
  have eb := below b 9 2 (by decide) (by omega) (by omega)
  have ea' : allocateEvmGas a 9 2 (by decide) (by omega) = EvmGasAllocation.mk 5 2 := by
    calc
      _ = EvmGasAllocation.mk (a.costs.txMaxGasLimit - 2) (9 - a.costs.txMaxGasLimit) := ea
      _ = EvmGasAllocation.mk 5 2 := by rw [ha]
  refine ⟨ea', eb, ?_⟩
  rw [ea', eb]
  intro h
  have := congrArg EvmGasAllocation.executionGas h
  contradiction

private theorem intrinsic_independent (cfg : VmConfig) (t i j : Nat)
    (hi : i ≤ t) (hic : i ≤ cfg.costs.txMaxGasLimit)
    (hj : j ≤ t) (hjc : j ≤ cfg.costs.txMaxGasLimit) :
    (allocateEvmGas cfg t i hi hic).stateGasReservoir =
      (allocateEvmGas cfg t j hj hjc).stateGasReservoir := by
  have ha := arithmetic cfg t i hi hic
  have hb := arithmetic cfg t j hj hjc
  exact ha.2.2.trans hb.2.2.symm

-- 7. Complete constructed entry, potential, signed state usage at its grant.
private theorem entry_observations (a : EvmGasAllocation) :
    entry a = GasMeter.mk a.executionGas a.stateGasReservoir a.stateGasReservoir 0 0 0 ∧
    (entry a).phi = a.executionGas ∧
    txStateGasUsed (entry a) a.stateGasReservoir (Nat.le_refl a.stateGasReservoir) = 0 := by
  refine ⟨rfl, ?_, ?_⟩
  · simp only [entry, GasMeter.phi, Nat.add_zero]
  · calc
      _ = (a.stateGasReservoir : Int) - (a.stateGasReservoir : Int) + (0 : Int) + 0 :=
        txStateGasUsed_eq (entry a) a.stateGasReservoir (Nat.le_refl a.stateGasReservoir)
      _ = 0 := by omega

-- 8. Complete execution-charge branches and potential; no intrinsic double charge.
private theorem execution_charge (a : EvmGasAllocation) (n : Nat) (h : n ≤ a.executionGas) :
    chargeGas (entry a) n = .ok (GasMeter.mk (a.executionGas - n)
      a.stateGasReservoir a.stateGasReservoir 0 0 0) :=
  chargeGas_of_le _ _ h

private theorem execution_exact (a : EvmGasAllocation) :
    chargeGas (entry a) a.executionGas = .ok (GasMeter.mk 0
      a.stateGasReservoir a.stateGasReservoir 0 0 0) := by
  simpa only [Nat.sub_self] using execution_charge a a.executionGas (Nat.le_refl _)

private theorem execution_short (a : EvmGasAllocation) :
    chargeGas (entry a) (a.executionGas + 1) = .error .outOfGas :=
  (chargeGas_eq_error_iff _ _ _).mpr ⟨by dsimp only [entry]; omega, rfl⟩

private theorem execution_potential (a : EvmGasAllocation) (n : Nat) (post : GasMeter)
    (h : chargeGas (entry a) n = .ok post) : post.phi + n = a.executionGas := by
  have hp := chargeGas_phi _ _ _ h
  rw [(entry_observations a).2.1] at hp
  exact hp

-- 9. State reservoir/spill/error branches, potential and signed usage via public law.
private theorem state_reservoir (a : EvmGasAllocation) (n : Nat)
    (h : n ≤ a.stateGasReservoir) :
    chargeStateGas (entry a) n = .ok (GasMeter.mk a.executionGas
      (a.stateGasReservoir - n) a.stateGasReservoir 0 0 0) :=
  chargeStateGas_of_le _ _ h

private theorem state_spill (a : EvmGasAllocation) (n : Nat)
    (hr : a.stateGasReservoir < n) (ha : n ≤ a.stateGasReservoir + a.executionGas) :
    chargeStateGas (entry a) n = .ok (GasMeter.mk (a.executionGas - (n - a.stateGasReservoir))
      0 a.stateGasReservoir 0 (n - a.stateGasReservoir) 0) := by
  simpa only [entry, Nat.zero_add] using chargeStateGas_of_lt (entry a) n hr ha

private theorem state_error (a : EvmGasAllocation) (n : Nat)
    (h : a.stateGasReservoir + a.executionGas < n) :
    chargeStateGas (entry a) n = .error .outOfGas :=
  (chargeStateGas_eq_error_iff _ _ _).mpr ⟨h, rfl⟩

private theorem state_observations (a : EvmGasAllocation) (n : Nat) (post : GasMeter)
    (h : chargeStateGas (entry a) n = .ok post)
    (hb : post.stateGasBaseline ≤ a.stateGasReservoir) :
    post.phi = a.executionGas ∧
    txStateGasUsed post a.stateGasReservoir hb =
      (a.stateGasReservoir : Int) - (post.stateGasLeft : Int) +
        (post.stateGasSpilled : Int) + (post.stateGasCommittedSpill : Int) := by
  have hp := chargeStateGas_phi _ _ _ h
  rw [(entry_observations a).2.1] at hp
  exact ⟨hp, txStateGasUsed_eq _ _ _⟩

end STFSpec.Conformance.Vm.Core.TransactionGasAllocationCallerProofs
