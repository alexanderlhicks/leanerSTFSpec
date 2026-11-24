/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.Numeric
import STFSpec.Hash.KeccakQuery
import STFSpec.Vm.Core.Config
import STFSpec.Vm.Core.Precompile

/-!
# IDENTITY precompile

Library `EthPrecompiles`. The direct entry charges execution gas before
returning its input bytes. See `STFSpec/informal/modules/EthPrecompiles.md`.
-/

namespace STFSpec.Precompiles

open STFSpec.Base STFSpec.Hash STFSpec.Vm.Core

private def identityGasCost (cfg : VmConfig) (size : Nat) : Nat :=
  let wordCount := ceil32 size / 32
  cfg.costs.precompileIdentityBase + cfg.costs.precompileIdentityPerWord * wordCount

private theorem identityGasCost_eq (cfg : VmConfig) (size : Nat) :
    identityGasCost cfg size =
      cfg.costs.precompileIdentityBase + cfg.costs.precompileIdentityPerWord * ((size + 31) / 32) := by
  simp only [identityGasCost, ceil32, Nat.mul_div_cancel _ (by decide : 0 < 32)]

/-- Charge the configured IDENTITY price and return the unchanged input on payment.
Pinned EELS `src/ethereum/forks/amsterdam/vm/precompiled_contracts/identity.py:23–46`. -/
def identity {m : Type → Type} [Monad m] [KeccakQuery m] (cfg : VmConfig) : PrecompileFn m :=
  fun data meter ↦
    match chargeGas meter (identityGasCost cfg data.size) with
    | .ok charged => pure (.ok charged data)
    | .error error => pure (.halt error)

private theorem identity_paid {m : Type → Type} [Monad m] [KeccakQuery m]
    (cfg : VmConfig) (data : Bytes) (meter : GasMeter)
    (h : identityGasCost cfg data.size ≤ meter.gasLeft) :
    identity (m := m) cfg data meter =
      pure (.ok { meter with gasLeft := meter.gasLeft - identityGasCost cfg data.size } data) := by
  rw [identity, chargeGas_of_le _ _ h]

private theorem identity_denied {m : Type → Type} [Monad m] [KeccakQuery m]
    (cfg : VmConfig) (data : Bytes) (meter : GasMeter)
    (h : meter.gasLeft < identityGasCost cfg data.size) :
    identity (m := m) cfg data meter = pure (.halt .outOfGas) := by
  rw [identity, (chargeGas_eq_error_iff _ _ _).2 ⟨h, rfl⟩]

private theorem identity_success_at_id (cfg : VmConfig) (data output : Bytes)
    (meter charged : GasMeter)
    (h : identity (m := Id) cfg data meter = .ok charged output) :
    chargeGas meter (identityGasCost cfg data.size) = .ok charged ∧
      charged = { meter with gasLeft := meter.gasLeft - identityGasCost cfg data.size } ∧
      output = data ∧ output.size = data.size := by
  by_cases affordable : identityGasCost cfg data.size ≤ meter.gasLeft
  · rw [identity_paid _ _ _ affordable] at h
    cases h
    exact ⟨chargeGas_of_le _ _ affordable, rfl, rfl, rfl⟩
  · rw [identity_denied _ _ _ (Nat.lt_of_not_ge affordable)] at h
    cases h

end STFSpec.Precompiles
