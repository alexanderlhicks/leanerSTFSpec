/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.Exceptions

/-!
# Two-dimensional gas charges, rollback, refunds and grant transfers

Library `EthVmCore`. Pure numeric meter helpers, without diagnostic tracing or frame settlement.
Pinned EELS `src/ethereum/forks/amsterdam/vm/gas.py:270–336,374–448,471–567,606–746,861–876`.
Charges and refunds admit every raw Nat/Int record; rollback assertions are local proof arguments.
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

/-- Credit pending spill first, then the reservoir; EELS
`src/ethereum/forks/amsterdam/vm/gas.py:606–628`. Baseline, signed refund and
committed spill are retained, without a baseline cap. -/
def creditStateGasRefund (m : GasMeter) (a : Nat) : GasMeter :=
  let fromGasLeft := min a m.stateGasSpilled
  { m with
    gasLeft := m.gasLeft + fromGasLeft
    stateGasSpilled := m.stateGasSpilled - fromGasLeft
    stateGasLeft := m.stateGasLeft + (a - fromGasLeft) }

/-- Repay pending spill from the reservoir; EELS
`src/ethereum/forks/amsterdam/vm/gas.py:631–659`. The final source assertion
is a universal postcondition, proved below, with no input premise. -/
def repayStateGasSpill (m : GasMeter) : GasMeter :=
  let repayment := min m.stateGasLeft m.stateGasSpilled
  { m with
    gasLeft := m.gasLeft + repayment
    stateGasLeft := m.stateGasLeft - repayment
    stateGasSpilled := m.stateGasSpilled - repayment }

/-- Refund credit changes exactly execution gas, pending spill and reservoir. -/
theorem creditStateGasRefund_eq (m : GasMeter) (a : Nat) :
    creditStateGasRefund m a =
      { m with
        gasLeft := m.gasLeft + min a m.stateGasSpilled
        stateGasSpilled := m.stateGasSpilled - min a m.stateGasSpilled
        stateGasLeft := m.stateGasLeft + (a - min a m.stateGasSpilled) } := rfl

/-- Credit transfers pending spill into execution gas without changing potential. -/
theorem creditStateGasRefund_phi (m : GasMeter) (a : Nat) :
    (creditStateGasRefund m a).phi = m.phi := by
  rw [creditStateGasRefund_eq]
  simp only [GasMeter.phi]
  have hSpill := Nat.min_le_right a m.stateGasSpilled
  have hAmount := Nat.min_le_left a m.stateGasSpilled
  omega

/-- Zero credit leaves the complete meter unchanged. -/
theorem creditStateGasRefund_zero (m : GasMeter) :
    creditStateGasRefund m 0 = m := by
  rw [creditStateGasRefund_eq]
  simp only [Nat.zero_min, Nat.add_zero, Nat.sub_zero]

/-- Repayment changes exactly execution gas, reservoir and pending spill. -/
theorem repayStateGasSpill_eq (m : GasMeter) :
    repayStateGasSpill m =
      { m with
        gasLeft := m.gasLeft + min m.stateGasLeft m.stateGasSpilled
        stateGasLeft := m.stateGasLeft - min m.stateGasLeft m.stateGasSpilled
        stateGasSpilled := m.stateGasSpilled - min m.stateGasLeft m.stateGasSpilled } := rfl

/-- Repayment transfers pending spill into execution gas without changing potential. -/
theorem repayStateGasSpill_phi (m : GasMeter) :
    (repayStateGasSpill m).phi = m.phi := by
  rw [repayStateGasSpill_eq]
  simp only [GasMeter.phi]
  have hReservoir := Nat.min_le_left m.stateGasLeft m.stateGasSpilled
  have hSpill := Nat.min_le_right m.stateGasLeft m.stateGasSpilled
  omega

/-- At least one pool is exhausted on every raw meter, including equality. -/
theorem repayStateGasSpill_post (m : GasMeter) :
    (repayStateGasSpill m).stateGasLeft = 0 ∨
    (repayStateGasSpill m).stateGasSpilled = 0 := by
  rw [repayStateGasSpill_eq]
  by_cases h : m.stateGasLeft ≤ m.stateGasSpilled
  · simp only [Nat.min_eq_left h, Nat.sub_self, true_or]
  · have h' : m.stateGasSpilled ≤ m.stateGasLeft := by omega
    simp only [Nat.min_eq_right h', Nat.sub_self, or_true]

/-- Repayment leaves no further transfer available. -/
theorem repayStateGasSpill_idempotent (m : GasMeter) :
    repayStateGasSpill (repayStateGasSpill m) = repayStateGasSpill m := by
  have h := repayStateGasSpill_post m
  rw [repayStateGasSpill_eq (repayStateGasSpill m)]
  have hz : min (repayStateGasSpill m).stateGasLeft
      (repayStateGasSpill m).stateGasSpilled = 0 := by
    rcases h with h | h
    · simp only [h, Nat.zero_min]
    · simp only [h, Nat.min_zero]
  rw [hz]
  simp only [Nat.add_zero, Nat.sub_zero]

/-- Forfeit execution gas after spill rollback; EELS
`src/ethereum/forks/amsterdam/vm/gas.py:662–675`. Only pending spill must be zero. -/
def forfeitRemainingGas (m : GasMeter) (_h : m.stateGasSpilled = 0) : GasMeter :=
  { m with gasLeft := 0 }

/-- Save the CREATE execution grant, then subtract it; EELS
`src/ethereum/forks/amsterdam/vm/gas.py:678–698`, inlining `:876`. -/
def withholdCreateGas (m : GasMeter) : Nat × GasMeter :=
  let childGas := m.gasLeft - m.gasLeft / 64
  (childGas, { m with gasLeft := m.gasLeft - childGas })

/-- Save the whole reservoir, then empty it; EELS
`src/ethereum/forks/amsterdam/vm/gas.py:701–722`. The saved amount is first. -/
def drainStateGasReservoir (m : GasMeter) : Nat × GasMeter :=
  (m.stateGasLeft, { m with stateGasLeft := 0 })

/-- Restore execution and reservoir amounts; EELS
`src/ethereum/forks/amsterdam/vm/gas.py:725–746`. Both amounts are unbounded. -/
def restoreChildGas (m : GasMeter) (g T : Nat) : GasMeter :=
  { m with gasLeft := m.gasLeft + g, stateGasLeft := m.stateGasLeft + T }

/-- Forfeiture changes only remaining execution gas. -/
theorem forfeitRemainingGas_eq (m : GasMeter) (h : m.stateGasSpilled = 0) :
    forfeitRemainingGas m h = { m with gasLeft := 0 } := rfl

/-- Forfeiture retains committed spill and cannot increase potential. -/
theorem forfeitRemainingGas_phi (m : GasMeter) (h : m.stateGasSpilled = 0) :
    (forfeitRemainingGas m h).phi = m.stateGasCommittedSpill ∧
    (forfeitRemainingGas m h).phi ≤ m.phi := by
  rw [forfeitRemainingGas_eq]
  simp only [GasMeter.phi, h]
  omega

/-- Withholding returns the saved grant first and preserves every other field. -/
theorem withholdCreateGas_eq (m : GasMeter) :
    withholdCreateGas m =
      (m.gasLeft - m.gasLeft / 64,
        { m with gasLeft := m.gasLeft - (m.gasLeft - m.gasLeft / 64) }) := rfl

/-- The returned execution grant accounts for exactly the withheld potential. -/
theorem withholdCreateGas_phi (m : GasMeter) :
    (withholdCreateGas m).2.phi + (withholdCreateGas m).1 = m.phi := by
  rw [withholdCreateGas_eq]
  simp only [GasMeter.phi]
  have hDiv : m.gasLeft / 64 ≤ m.gasLeft := Nat.div_le_self _ _
  have hGrant : m.gasLeft - m.gasLeft / 64 ≤ m.gasLeft := Nat.sub_le _ _
  omega

/-- Draining returns the old reservoir first and changes only that reservoir. -/
theorem drainStateGasReservoir_eq (m : GasMeter) :
    drainStateGasReservoir m = (m.stateGasLeft, { m with stateGasLeft := 0 }) := rfl

/-- The reservoir is excluded from execution potential. -/
theorem drainStateGasReservoir_phi (m : GasMeter) :
    (drainStateGasReservoir m).2.phi = m.phi := by
  rw [drainStateGasReservoir_eq]
  rfl

/-- Child restoration adds exactly the two supplied amounts. -/
theorem restoreChildGas_eq (m : GasMeter) (g T : Nat) :
    restoreChildGas m g T =
      { m with gasLeft := m.gasLeft + g, stateGasLeft := m.stateGasLeft + T } := rfl

/-- Only the execution amount contributes to the increase in potential. -/
theorem restoreChildGas_phi (m : GasMeter) (g T : Nat) :
    (restoreChildGas m g T).phi = m.phi + g := by
  rw [restoreChildGas_eq]
  simp only [GasMeter.phi]
  omega

/-- Signed refund addition; EELS inline `refund_counter += k`, at
`src/ethereum/forks/amsterdam/vm/instructions/storage.py:130,134,139` and
`src/ethereum/forks/amsterdam/vm/__init__.py:242`. Every raw meter is admitted. -/
def addRefund (m : GasMeter) (k : Int) : GasMeter :=
  { m with refundCounter := m.refundCounter + k }

/-- Refund addition changes exactly the signed counter. -/
theorem addRefund_eq (m : GasMeter) (k : Int) :
    addRefund m k = { m with refundCounter := m.refundCounter + k } := rfl

/-- Signed refunds do not contribute to execution potential. -/
theorem addRefund_phi (m : GasMeter) (k : Int) :
    (addRefund m k).phi = m.phi := rfl

/-- EIP-150 maximum grant; EELS `src/ethereum/forks/amsterdam/vm/gas.py:861–876`. -/
def maxMessageCallGas (g : Nat) : Nat :=
  g - g / 64

/-- The scalar maximum retains the ordinary unbounded subtraction expression. -/
theorem maxMessageCallGas_eq (g : Nat) :
    maxMessageCallGas g = g - g / 64 := rfl

/-- The maximum grant cannot exceed the supplied execution amount. -/
theorem maxMessageCallGas_le (g : Nat) :
    maxMessageCallGas g ≤ g := by
  rw [maxMessageCallGas_eq]
  exact Nat.sub_le _ _

end STFSpec.Vm.Core
