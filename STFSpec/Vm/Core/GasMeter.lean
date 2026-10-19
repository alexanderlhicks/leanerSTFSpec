/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.Exceptions

/-!
# Two-dimensional gas charges and rollback

Library `EthVmCore`. Pure numeric meter helpers, without diagnostic tracing or frame settlement.
Pinned EELS `src/ethereum/forks/amsterdam/vm/gas.py:270–336,374–448,471–567`.
Charges admit every raw Nat/Int record; rollback assertions become local proof arguments.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§2.5/5/7.
-/

namespace STFSpec.Vm.Core

/-- Complete meter; pinned EELS `src/ethereum/forks/amsterdam/vm/gas.py:270–336`. -/
structure GasMeter where
  /-- Remaining execution grant. -/
  gasLeft : Nat
  /-- Remaining state reservoir. -/
  stateGasLeft : Nat
  /-- Reservoir level to which later rollback restores. -/
  stateGasBaseline : Nat
  /-- Signed per-frame refund, which may be negative. -/
  refundCounter : Int := 0
  /-- Pending execution gas spent on state charges. -/
  stateGasSpilled : Nat := 0
  /-- Committed execution gas spent on state charges. -/
  stateGasCommittedSpill : Nat := 0

/-- Local execution potential; the reservoir and signed refund are excluded. -/
def GasMeter.phi (g : GasMeter) : Nat :=
  g.gasLeft + g.stateGasSpilled + g.stateGasCommittedSpill

/-- Read-only affordability; EELS `src/ethereum/forks/amsterdam/vm/gas.py:374–388`. -/
def checkGas (g : GasMeter) (a : Nat) : Except ExceptionalHalt Unit :=
  if g.gasLeft < a then .error .outOfGas else .ok ()

/-- Checked execution charge; EELS `src/ethereum/forks/amsterdam/vm/gas.py:391–405`.
The frame wrapper's diagnostic trace is outside this numeric operation. -/
def chargeGas (g : GasMeter) (a : Nat) : Except ExceptionalHalt GasMeter :=
  if g.gasLeft < a then .error .outOfGas
  else .ok { g with gasLeft := g.gasLeft - a }

/-- Reservoir-first state charge; EELS `src/ethereum/forks/amsterdam/vm/gas.py:425–448`.
An unaffordable amount returns out-of-gas before any meter update. -/
def chargeStateGas (g : GasMeter) (a : Nat) : Except ExceptionalHalt GasMeter :=
  if a ≤ g.stateGasLeft then .ok { g with stateGasLeft := g.stateGasLeft - a }
  else if a ≤ g.stateGasLeft + g.gasLeft then
    let remainder := a - g.stateGasLeft
    .ok { g with
      gasLeft := g.gasLeft - remainder
      stateGasLeft := 0
      stateGasSpilled := g.stateGasSpilled + remainder }
  else .error .outOfGas

/-- Affordability is exactly successful read-only checking. -/
theorem checkGas_eq_ok_iff (g : GasMeter) (a : Nat) :
    checkGas g a = .ok () ↔ a ≤ g.gasLeft := by
  simp only [checkGas]
  split <;> simp_all <;> omega

/-- Only out-of-gas can be returned, exactly on execution shortage. -/
theorem checkGas_eq_error_iff (g : GasMeter) (a : Nat) (e : ExceptionalHalt) :
    checkGas g a = .error e ↔ g.gasLeft < a ∧ e = .outOfGas := by
  simp only [checkGas]
  split <;> simp_all [eq_comm] <;> omega

/-- Successful execution charging changes only execution gas. -/
theorem chargeGas_of_le (g : GasMeter) (a : Nat) (h : a ≤ g.gasLeft) :
    chargeGas g a = .ok { g with gasLeft := g.gasLeft - a } := by
  simp only [chargeGas, Nat.not_lt.mpr h, ↓reduceIte]

/-- Execution charging fails exactly on shortage and emits only out-of-gas. -/
theorem chargeGas_eq_error_iff (g : GasMeter) (a : Nat) (e : ExceptionalHalt) :
    chargeGas g a = .error e ↔ g.gasLeft < a ∧ e = .outOfGas := by
  simp only [chargeGas]
  split <;> simp_all [eq_comm] <;> omega

/-- Successful execution charging consumes precisely the requested potential. -/
theorem chargeGas_phi (g : GasMeter) (a : Nat) (g' : GasMeter)
    (h : chargeGas g a = .ok g') : g'.phi + a = g.phi := by
  unfold chargeGas at h
  split at h
  · contradiction
  · cases h
    simp only [GasMeter.phi]
    omega

/-- The first state-charge branch changes only the reservoir. -/
theorem chargeStateGas_of_le (g : GasMeter) (a : Nat) (h : a ≤ g.stateGasLeft) :
    chargeStateGas g a = .ok { g with stateGasLeft := g.stateGasLeft - a } := by
  simp only [chargeStateGas, h, ↓reduceIte]

/-- An affordable spill exhausts the reservoir and adds exactly its shortfall to pending spill. -/
theorem chargeStateGas_of_lt (g : GasMeter) (a : Nat) (hR : g.stateGasLeft < a)
    (hA : a ≤ g.stateGasLeft + g.gasLeft) :
    chargeStateGas g a = .ok { g with
      gasLeft := g.gasLeft - (a - g.stateGasLeft)
      stateGasLeft := 0
      stateGasSpilled := g.stateGasSpilled + (a - g.stateGasLeft) } := by
  simp only [chargeStateGas, Nat.not_le.mpr hR, hA, ↓reduceIte]

/-- State charging fails exactly on total shortage and emits only out-of-gas. -/
theorem chargeStateGas_eq_error_iff (g : GasMeter) (a : Nat) (e : ExceptionalHalt) :
    chargeStateGas g a = .error e ↔ g.stateGasLeft + g.gasLeft < a ∧ e = .outOfGas := by
  simp only [chargeStateGas]
  split
  · constructor
    · intro h
      contradiction
    · intro h
      omega
  · split <;> simp_all [eq_comm] <;> omega <;> omega

/-- State charging redistributes counted potential without consuming it. -/
theorem chargeStateGas_phi (g : GasMeter) (a : Nat) (g' : GasMeter)
    (h : chargeStateGas g a = .ok g') : g'.phi = g.phi := by
  unfold chargeStateGas at h
  split at h
  · cases h
    rfl
  · split at h
    · cases h
      simp only [GasMeter.phi]
      omega
    · contradiction

/-- Successful state charging never increases execution gas. -/
theorem chargeStateGas_gasLeft_le (g : GasMeter) (a : Nat) (g' : GasMeter)
    (h : chargeStateGas g a = .ok g') : g'.gasLeft ≤ g.gasLeft := by
  unfold chargeStateGas at h
  split at h
  · cases h
    exact Nat.le_refl _
  · split at h
    · cases h
      exact Nat.sub_le _ _
    · contradiction

/-- Commit pending spill and lower the baseline; EELS
`src/ethereum/forks/amsterdam/vm/gas.py:471–502`. The assertion is a proof argument. -/
def commitStateGas (m : GasMeter)
    (_h : m.stateGasLeft ≤ m.stateGasBaseline) : GasMeter :=
  { m with
    stateGasCommittedSpill := m.stateGasCommittedSpill + m.stateGasSpilled
    stateGasBaseline := m.stateGasLeft
    stateGasSpilled := 0 }

/-- Restore pending spill and the current baseline; EELS
`src/ethereum/forks/amsterdam/vm/gas.py:505–529`. Committed spill is retained. -/
def restoreStateGas (m : GasMeter) : GasMeter :=
  { m with
    gasLeft := m.gasLeft + m.stateGasSpilled
    stateGasSpilled := 0
    stateGasLeft := m.stateGasBaseline
    refundCounter := 0 }

/-- Restore both spill pools and the entry grant; EELS
`src/ethereum/forks/amsterdam/vm/gas.py:532–567`. Both assertions precede mutation;
refund is preserved, and its proof argument establishes that it is zero. -/
def restoreStateGasToEntry (m : GasMeter) (R : Nat)
    (_h₁ : m.stateGasBaseline ≤ R) (_h₂ : m.refundCounter = 0) : GasMeter :=
  { m with
    gasLeft := m.gasLeft + m.stateGasSpilled + m.stateGasCommittedSpill
    stateGasSpilled := 0
    stateGasCommittedSpill := 0
    stateGasLeft := R
    stateGasBaseline := R }

/-- Committing changes exactly the baseline and two spill pools. -/
theorem commitStateGas_eq (m : GasMeter)
    (h : m.stateGasLeft ≤ m.stateGasBaseline) :
    commitStateGas m h = { m with
      stateGasCommittedSpill := m.stateGasCommittedSpill + m.stateGasSpilled
      stateGasBaseline := m.stateGasLeft
      stateGasSpilled := 0 } := rfl

/-- Committing redistributes pending into committed potential. -/
theorem commitStateGas_phi (m : GasMeter)
    (h : m.stateGasLeft ≤ m.stateGasBaseline) :
    (commitStateGas m h).phi = m.phi := by
  simp only [commitStateGas_eq, GasMeter.phi]
  omega

/-- Ordinary rollback resets the signed refund and retains committed spill. -/
theorem restoreStateGas_eq (m : GasMeter) :
    restoreStateGas m = { m with
      gasLeft := m.gasLeft + m.stateGasSpilled
      stateGasSpilled := 0
      stateGasLeft := m.stateGasBaseline
      refundCounter := 0 } := rfl

/-- Ordinary rollback redistributes pending spill into execution gas. -/
theorem restoreStateGas_phi (m : GasMeter) :
    (restoreStateGas m).phi = m.phi := by
  simp only [restoreStateGas_eq, GasMeter.phi]
  omega

/-- Local ordinary-rollback fields; no committed-spill-zero claim is made. -/
theorem restoreStateGas_post (m : GasMeter) :
    (restoreStateGas m).stateGasSpilled = 0 ∧
    (restoreStateGas m).refundCounter = 0 ∧
    (restoreStateGas m).stateGasLeft = (restoreStateGas m).stateGasBaseline := by
  rw [restoreStateGas_eq]
  exact ⟨rfl, rfl, rfl⟩

/-- Entry rollback changes exactly execution gas, both spill pools and reservoir/baseline. -/
theorem restoreStateGasToEntry_eq (m : GasMeter) (R : Nat)
    (h₁ : m.stateGasBaseline ≤ R) (h₂ : m.refundCounter = 0) :
    restoreStateGasToEntry m R h₁ h₂ = { m with
      gasLeft := m.gasLeft + m.stateGasSpilled + m.stateGasCommittedSpill
      stateGasSpilled := 0
      stateGasCommittedSpill := 0
      stateGasLeft := R
      stateGasBaseline := R } := rfl

/-- Entry rollback redistributes both spill pools into execution gas. -/
theorem restoreStateGasToEntry_phi (m : GasMeter) (R : Nat)
    (h₁ : m.stateGasBaseline ≤ R) (h₂ : m.refundCounter = 0) :
    (restoreStateGasToEntry m R h₁ h₂).phi = m.phi := by
  simp only [restoreStateGasToEntry_eq, GasMeter.phi]
  omega

/-- Entry rollback's zero-refund fact uses its equality premise. -/
theorem restoreStateGasToEntry_post (m : GasMeter) (R : Nat)
    (h₁ : m.stateGasBaseline ≤ R) (h₂ : m.refundCounter = 0) :
    (restoreStateGasToEntry m R h₁ h₂).stateGasSpilled = 0 ∧
    (restoreStateGasToEntry m R h₁ h₂).stateGasCommittedSpill = 0 ∧
    (restoreStateGasToEntry m R h₁ h₂).refundCounter = 0 ∧
    (restoreStateGasToEntry m R h₁ h₂).stateGasLeft = R ∧
    (restoreStateGasToEntry m R h₁ h₂).stateGasBaseline = R := by
  rw [restoreStateGasToEntry_eq]
  exact ⟨rfl, rfl, h₂, rfl, rfl⟩

end STFSpec.Vm.Core
