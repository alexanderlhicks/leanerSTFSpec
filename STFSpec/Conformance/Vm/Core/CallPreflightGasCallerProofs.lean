/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Conditional CALL preflight gas composition

Library `EthConformance`. Private clients compose the public numeric laws for
paid overhead, optional state charge, current-meter forwarding, drain and complete
grant return, optionally followed by state credit. EELS
`src/ethereum/forks/amsterdam/vm/instructions/system.py:386–394,536–559` at the pin.
Literal zero calculator prices require separate source ZERO coherence. No actual
handler reachability, child execution bound, settlement or G2–G7 result is supplied.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/7/10.
-/

namespace STFSpec.Conformance.Vm.Core.CallPreflightGasCallerProofs
open STFSpec.Vm.Core STFSpec.Base

private def returnGrant (charged : GasMeter) (grant : Nat) : GasMeter :=
  let drained := drainStateGasReservoir charged
  restoreChildGas drained.2 grant drained.1

private def optionalCredit (returned : GasMeter) (amount : Nat) (credit : Bool) :
    GasMeter :=
  if credit then creditStateGasRefund returned amount else returned

private theorem successful_charge_fields (before after : GasMeter) (amount : Nat)
    (h : chargeGas before amount = .ok after) :
    amount ≤ before.gasLeft ∧ after = { before with gasLeft := before.gasLeft - amount } := by
  have ha : amount ≤ before.gasLeft := by
    by_cases ha : amount ≤ before.gasLeft
    · exact ha
    have he := (chargeGas_eq_error_iff before amount .outOfGas).mpr ⟨by omega, rfl⟩
    rw [h] at he
    contradiction
  have hf := chargeGas_of_le before amount ha
  rw [h] at hf
  exact ⟨ha, Except.ok.inj hf⟩

private theorem current_forward_share (cfg : VmConfig) (value : U256)
    (requested stipend : Nat) (current : GasMeter) :
    let r := calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend
    r.subCall = r.cost + (if value = U256.zero then cfg.costs.zero else stipend) := by
  dsimp only
  rw [calculateMessageCallGas_eq]
  simp only [Nat.add_zero, Nat.not_lt_zero, ↓reduceIte]

private theorem current_forward_return_fields (cfg : VmConfig) (value : U256)
    (requested stipend : Nat) (current charged : GasMeter)
    (h : chargeGas current
      (calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend).cost =
        .ok charged) :
    returnGrant charged
        (calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend).subCall =
      { current with gasLeft := current.gasLeft +
          (if value = U256.zero then cfg.costs.zero else stipend) } := by
  have hf := successful_charge_fields current charged _ h
  have hs := current_forward_share cfg value requested stipend current
  dsimp only at hs
  simp only [returnGrant, drainStateGasReservoir_eq, restoreChildGas_eq]
  rw [hf.2]
  simp only [Nat.zero_add]
  have he : current.gasLeft -
        (calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend).cost +
        (calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend).subCall =
      current.gasLeft + (if value = U256.zero then cfg.costs.zero else stipend) := by omega
  rw [he]

private theorem optional_credit_phi (returned : GasMeter) (amount : Nat) (credit : Bool) :
    (optionalCredit returned amount credit).phi = returned.phi := by
  cases credit
  · rfl
  · exact creditStateGasRefund_phi returned amount

/-- The optional state step has exactly its successful public-operation premise.
The forwarding calculation reads the resulting meter, with explicit stipend. -/
private theorem preflight_return_accounting (cfg : VmConfig) (value : U256)
    (requested stipend overhead stateAmount : Nat) (initial paid current charged : GasMeter)
    (credit : Bool) (hpaid : chargeGas initial overhead = .ok paid)
    (hstate : current = paid ∨ chargeStateGas paid stateAmount = .ok current)
    (hforward : chargeGas current
      (calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend).cost =
        .ok charged) :
    let r := calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend
    let returned := optionalCredit (returnGrant charged r.subCall) stateAmount credit
    returned.phi + overhead = initial.phi +
      (if value = U256.zero then cfg.costs.zero else stipend) := by
  dsimp only
  rw [optional_credit_phi]
  have hp := chargeGas_phi initial overhead paid hpaid
  have hs : current.phi = paid.phi := by
    rcases hstate with he | hc
    · rw [he]
    · exact chargeStateGas_phi paid stateAmount current hc
  have hf := chargeGas_phi current _ charged hforward
  have hg := current_forward_share cfg value requested stipend current
  have hd := drainStateGasReservoir_phi charged
  have hr := restoreChildGas_phi (drainStateGasReservoir charged).2
    (calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend).subCall
    (drainStateGasReservoir charged).1
  dsimp only [returnGrant] at *
  omega

private theorem preflight_return_progress (cfg : VmConfig) (value : U256)
    (requested stipend overhead stateAmount : Nat) (initial paid current charged : GasMeter)
    (credit : Bool) (hpaid : chargeGas initial overhead = .ok paid)
    (hstate : current = paid ∨ chargeStateGas paid stateAmount = .ok current)
    (hforward : chargeGas current
      (calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend).cost =
        .ok charged)
    (hfinance : (if value = U256.zero then cfg.costs.zero else stipend) + 1 ≤ overhead) :
    (optionalCredit (returnGrant charged
      (calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend).subCall)
      stateAmount credit).phi + 1 ≤ initial.phi := by
  have h := preflight_return_accounting cfg value requested stipend overhead stateAmount
    initial paid current charged credit hpaid hstate hforward
  dsimp only at h
  omega

private theorem preflight_return_nonincrease (cfg : VmConfig) (value : U256)
    (requested stipend overhead stateAmount : Nat) (initial paid current charged : GasMeter)
    (credit : Bool) (hpaid : chargeGas initial overhead = .ok paid)
    (hstate : current = paid ∨ chargeStateGas paid stateAmount = .ok current)
    (hforward : chargeGas current
      (calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend).cost =
        .ok charged)
    (hfinance : (if value = U256.zero then cfg.costs.zero else stipend) ≤ overhead) :
    (optionalCredit (returnGrant charged
      (calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend).subCall)
      stateAmount credit).phi ≤ initial.phi := by
  have h := preflight_return_accounting cfg value requested stipend overhead stateAmount
    initial paid current charged credit hpaid hstate hforward
  dsimp only at h
  omega

private theorem no_state_return_fields (cfg : VmConfig) (value : U256)
    (requested stipend overhead : Nat) (initial paid charged : GasMeter)
    (hpaid : chargeGas initial overhead = .ok paid)
    (hforward : chargeGas paid
      (calculateMessageCallGas cfg value requested paid.gasLeft 0 0 stipend).cost =
        .ok charged) :
    returnGrant charged
        (calculateMessageCallGas cfg value requested paid.gasLeft 0 0 stipend).subCall =
      { initial with gasLeft := initial.gasLeft - overhead +
          (if value = U256.zero then cfg.costs.zero else stipend) } := by
  rw [current_forward_return_fields cfg value requested stipend paid charged hforward]
  rw [(successful_charge_fields initial paid overhead hpaid).2]

/-- Complete source-aligned state-charge/full-credit result. Credit may repay spill
that was already pending before this prefix, so this is not raw-meter rollback. -/
private theorem state_return_credit_fields (cfg : VmConfig) (value : U256)
    (requested stipend stateAmount : Nat) (paid current charged : GasMeter)
    (hstate : chargeStateGas paid stateAmount = .ok current)
    (hforward : chargeGas current
      (calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend).cost =
        .ok charged) :
    let d := stateAmount - paid.stateGasLeft
    let x := min stateAmount (paid.stateGasSpilled + d)
    creditStateGasRefund (returnGrant charged
      (calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend).subCall)
      stateAmount =
        { paid with
          gasLeft := paid.gasLeft - d +
            (if value = U256.zero then cfg.costs.zero else stipend) + x
          stateGasLeft := paid.stateGasLeft - stateAmount + (stateAmount - x)
          stateGasSpilled := paid.stateGasSpilled + d - x } := by
  rw [current_forward_return_fields cfg value requested stipend current charged hforward]
  have hf : current = { paid with
      gasLeft := paid.gasLeft - (stateAmount - paid.stateGasLeft)
      stateGasLeft := paid.stateGasLeft - stateAmount
      stateGasSpilled := paid.stateGasSpilled + (stateAmount - paid.stateGasLeft) } := by
    by_cases ha : stateAmount ≤ paid.stateGasLeft
    · have he := chargeStateGas_of_le paid stateAmount ha
      rw [hstate] at he
      rw [Except.ok.inj he]
      simp only [Nat.sub_eq_zero_of_le ha, Nat.sub_zero, Nat.add_zero]
    · have hb : stateAmount ≤ paid.stateGasLeft + paid.gasLeft := by
        by_cases hb : stateAmount ≤ paid.stateGasLeft + paid.gasLeft
        · exact hb
        have he := (chargeStateGas_eq_error_iff paid stateAmount .outOfGas).mpr
          ⟨by omega, rfl⟩
        rw [hstate] at he
        contradiction
      have he := chargeStateGas_of_lt paid stateAmount (by omega) hb
      rw [hstate] at he
      rw [Except.ok.inj he]
      simp only [Nat.sub_eq_zero_of_le (by omega : paid.stateGasLeft ≤ stateAmount)]
  rw [hf, creditStateGasRefund_eq]

private theorem source_zero_selection (cfg : VmConfig) (stipend : Nat)
    (hzero : cfg.costs.zero = 0) :
    (if U256.zero = U256.zero then cfg.costs.zero else stipend) = 0 := by
  simp only [↓reduceIte, hzero]

/-! ### Arbitrary supplied return amounts -/

private def returnActual (charged : GasMeter) (execution reservoir : Nat) : GasMeter :=
  restoreChildGas (drainStateGasReservoir charged).2 execution reservoir

private theorem return_actual_fields (charged : GasMeter) (execution reservoir : Nat) :
    returnActual charged execution reservoir =
      { charged with gasLeft := charged.gasLeft + execution, stateGasLeft := reservoir } := by
  simp only [returnActual, drainStateGasReservoir_eq, restoreChildGas_eq, Nat.zero_add]

private theorem return_actual_credit_fields (charged : GasMeter)
    (execution reservoir amount : Nat) :
    let x := min amount charged.stateGasSpilled
    creditStateGasRefund (returnActual charged execution reservoir) amount =
      { charged with
        gasLeft := charged.gasLeft + execution + x
        stateGasLeft := reservoir + (amount - x)
        stateGasSpilled := charged.stateGasSpilled - x } := by
  rw [return_actual_fields, creditStateGasRefund_eq]

/-- Only the returned execution amount enters potential accounting. The supplied
reservoir is arbitrary, and optional credit is only the existing numeric operation. -/
private theorem preflight_actual_return_accounting (cfg : VmConfig) (value : U256)
    (requested stipend overhead stateAmount execution reservoir : Nat)
    (initial paid current charged : GasMeter) (credit : Bool)
    (hpaid : chargeGas initial overhead = .ok paid)
    (hstate : current = paid ∨ chargeStateGas paid stateAmount = .ok current)
    (hforward : chargeGas current
      (calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend).cost =
        .ok charged) :
    let r := calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend
    let returned := optionalCredit (returnActual charged execution reservoir) stateAmount credit
    returned.phi + overhead + r.cost = initial.phi + execution := by
  dsimp only
  rw [optional_credit_phi]
  have hp := chargeGas_phi initial overhead paid hpaid
  have hs : current.phi = paid.phi := by
    rcases hstate with he | hc
    · rw [he]
    · exact chargeStateGas_phi paid stateAmount current hc
  have hf := chargeGas_phi current _ charged hforward
  have hd := drainStateGasReservoir_phi charged
  have hr := restoreChildGas_phi (drainStateGasReservoir charged).2 execution reservoir
  dsimp only [returnActual]
  omega

private theorem preflight_actual_return_progress_iff (cfg : VmConfig) (value : U256)
    (requested stipend overhead stateAmount execution reservoir : Nat)
    (initial paid current charged : GasMeter) (credit : Bool)
    (hpaid : chargeGas initial overhead = .ok paid)
    (hstate : current = paid ∨ chargeStateGas paid stateAmount = .ok current)
    (hforward : chargeGas current
      (calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend).cost =
        .ok charged) :
    (optionalCredit (returnActual charged execution reservoir) stateAmount credit).phi + 1 ≤
        initial.phi ↔
      execution + 1 ≤ overhead +
        (calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend).cost := by
  have h := preflight_actual_return_accounting cfg value requested stipend overhead stateAmount
    execution reservoir initial paid current charged credit hpaid hstate hforward
  dsimp only at h
  omega

private theorem preflight_actual_return_bound (cfg : VmConfig) (value : U256)
    (requested stipend overhead stateAmount execution reservoir : Nat)
    (initial paid current charged : GasMeter) (credit : Bool)
    (hpaid : chargeGas initial overhead = .ok paid)
    (hstate : current = paid ∨ chargeStateGas paid stateAmount = .ok current)
    (hforward : chargeGas current
      (calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend).cost =
        .ok charged)
    (hreturn : execution ≤
      (calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend).subCall) :
    (optionalCredit (returnActual charged execution reservoir) stateAmount credit).phi +
        overhead ≤ initial.phi +
      (if value = U256.zero then cfg.costs.zero else stipend) := by
  have h := preflight_actual_return_accounting cfg value requested stipend overhead stateAmount
    execution reservoir initial paid current charged credit hpaid hstate hforward
  have hs := current_forward_share cfg value requested stipend current
  dsimp only at h hs
  omega

private theorem preflight_actual_return_progress (cfg : VmConfig) (value : U256)
    (requested stipend overhead stateAmount execution reservoir : Nat)
    (initial paid current charged : GasMeter) (credit : Bool)
    (hpaid : chargeGas initial overhead = .ok paid)
    (hstate : current = paid ∨ chargeStateGas paid stateAmount = .ok current)
    (hforward : chargeGas current
      (calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend).cost =
        .ok charged)
    (hreturn : execution ≤
      (calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend).subCall)
    (hfinance : (if value = U256.zero then cfg.costs.zero else stipend) + 1 ≤ overhead) :
    (optionalCredit (returnActual charged execution reservoir) stateAmount credit).phi + 1 ≤
      initial.phi := by
  have h := preflight_actual_return_bound cfg value requested stipend overhead stateAmount
    execution reservoir initial paid current charged credit hpaid hstate hforward hreturn
  omega

private theorem preflight_actual_return_nonincrease (cfg : VmConfig) (value : U256)
    (requested stipend overhead stateAmount execution reservoir : Nat)
    (initial paid current charged : GasMeter) (credit : Bool)
    (hpaid : chargeGas initial overhead = .ok paid)
    (hstate : current = paid ∨ chargeStateGas paid stateAmount = .ok current)
    (hforward : chargeGas current
      (calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend).cost =
        .ok charged)
    (hreturn : execution ≤
      (calculateMessageCallGas cfg value requested current.gasLeft 0 0 stipend).subCall)
    (hfinance : (if value = U256.zero then cfg.costs.zero else stipend) ≤ overhead) :
    (optionalCredit (returnActual charged execution reservoir) stateAmount credit).phi ≤
      initial.phi := by
  have h := preflight_actual_return_bound cfg value requested stipend overhead stateAmount
    execution reservoir initial paid current charged credit hpaid hstate hforward hreturn
  omega

/-- This supplied child-potential hypothesis is not a theorem about child execution. -/
private theorem child_execution_le_of_phi_le (child : GasMeter) (grant : Nat)
    (hphi : child.phi ≤ grant) : child.gasLeft ≤ grant := by
  simp only [GasMeter.phi] at hphi
  omega

/-- Every arbitrary Frame admits a settled meter update exceeding any supplied grant.
The public predicate's success and failure clauses impose no execution-gas bound. -/
private theorem child_settled_does_not_bound_execution (child : Frame)
    (grant reservoir : Nat) (failed : Bool) :
    let updated := { child with gasMeter := GasMeter.mk (grant + 1) reservoir reservoir 0 0 0 }
    ChildSettled updated failed ∧ ¬ updated.gasMeter.gasLeft ≤ grant := by
  cases failed <;> simp [ChildSettled]

end STFSpec.Conformance.Vm.Core.CallPreflightGasCallerProofs
