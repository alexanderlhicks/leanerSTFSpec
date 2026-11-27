/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.Numeric
import STFSpec.Hash.KeccakQuery
import STFSpec.Hash.Sha256Digest
import STFSpec.Vm.Core.Config
import STFSpec.Vm.Core.Precompile

/-!
# SHA256 precompile

Library `EthPrecompiles`. The direct entry charges for the complete input
before invoking the total SHA-256 provider. See `STFSpec/informal/modules/EthPrecompiles.md`.
-/

namespace STFSpec.Precompiles

open STFSpec.Base STFSpec.Hash STFSpec.Vm.Core

private def sha256GasCost (cfg : VmConfig) (size : Nat) : Nat :=
  let wordCount := ceil32 size / 32
  cfg.costs.precompileSha256Base + cfg.costs.precompileSha256PerWord * wordCount

private theorem sha256GasCost_eq (cfg : VmConfig) (size : Nat) :
    sha256GasCost cfg size =
      cfg.costs.precompileSha256Base + cfg.costs.precompileSha256PerWord * ((size + 31) / 32) := by
  simp only [sha256GasCost, ceil32, Nat.mul_div_cancel _ (by decide : 0 < 32)]

/-- Charge the configured SHA256 price and return the complete digest on payment.
Pinned EELS `src/ethereum/forks/amsterdam/vm/precompiled_contracts/sha256.py:25–48`. -/
def sha256 {m : Type → Type} [Monad m] [KeccakQuery m] (cfg : VmConfig) : PrecompileFn m :=
  fun data meter ↦
    match chargeGas meter (sha256GasCost cfg data.size) with
    | .ok charged => pure (.ok charged (STFSpec.Hash.sha256 data.toByteArray).toBytes)
    | .error error => pure (.halt error)

private theorem sha256_paid {m : Type → Type} [Monad m] [KeccakQuery m]
    (cfg : VmConfig) (data : Bytes) (meter : GasMeter)
    (affordable : sha256GasCost cfg data.size ≤ meter.gasLeft) :
    sha256 (m := m) cfg data meter =
      pure (.ok { meter with gasLeft := meter.gasLeft - sha256GasCost cfg data.size }
        (STFSpec.Hash.sha256 data.toByteArray).toBytes) := by
  rw [sha256, chargeGas_of_le _ _ affordable]

private theorem sha256_denied {m : Type → Type} [Monad m] [KeccakQuery m]
    (cfg : VmConfig) (data : Bytes) (meter : GasMeter)
    (short : meter.gasLeft < sha256GasCost cfg data.size) :
    sha256 (m := m) cfg data meter = pure (.halt .outOfGas) := by
  rw [sha256, (chargeGas_eq_error_iff _ _ _).mpr ⟨short, rfl⟩]

private theorem sha256_success_at_id (cfg : VmConfig) (data output : Bytes)
    (meter charged : GasMeter) (result : sha256 (m := Id) cfg data meter = .ok charged output) :
    chargeGas meter (sha256GasCost cfg data.size) = .ok charged ∧
      charged = { meter with gasLeft := meter.gasLeft - sha256GasCost cfg data.size } ∧
      output = (STFSpec.Hash.sha256 data.toByteArray).toBytes ∧ output.size = 32 := by
  by_cases affordable : sha256GasCost cfg data.size ≤ meter.gasLeft
  · rw [sha256_paid _ _ _ affordable] at result
    cases result
    exact ⟨chargeGas_of_le _ _ affordable, rfl, rfl, size_sha256 _⟩
  · rw [sha256_denied _ _ _ (Nat.lt_of_not_ge affordable)] at result
    cases result

private theorem sha256_fips_at_id (cfg : VmConfig) (data output : Bytes) (meter charged : GasMeter)
    (result : sha256 (m := Id) cfg data meter = .ok charged output)
    (domain : 8 * data.size < 2 ^ 64) :
    Sha256.Model.DigestOnPad (Sha256.Model.fipsPad data.toByteArray.data.toList) output.toList := by
  have packedDomain : 8 * data.toByteArray.size < 2 ^ 64 := by
    simpa only [Bytes.size_toByteArray] using domain
  rw [(sha256_success_at_id cfg data output meter charged result).2.2.1]
  exact Sha256.sha256_fipsDigest _ packedDomain

end STFSpec.Precompiles
