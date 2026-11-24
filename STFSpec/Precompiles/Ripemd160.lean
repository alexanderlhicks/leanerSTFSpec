/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.Numeric
import STFSpec.Hash.KeccakQuery
import STFSpec.Hash.Ripemd160Digest
import STFSpec.Vm.Core.Config
import STFSpec.Vm.Core.Precompile

/-!
# RIPEMD160 precompile

Library `EthPrecompiles`. Charge for the input before computing and left-padding
its complete RIPEMD-160 digest. See `STFSpec/informal/modules/EthPrecompiles.md`.
-/

namespace STFSpec.Precompiles

open STFSpec.Base STFSpec.Hash STFSpec.Vm.Core

private def ripemd160GasCost (cfg : VmConfig) (size : Nat) : Nat :=
  let wordCount := ceil32 size / 32
  cfg.costs.precompileRipemd160Base + cfg.costs.precompileRipemd160PerWord * wordCount

private theorem ripemd160GasCost_eq (cfg : VmConfig) (size : Nat) :
    ripemd160GasCost cfg size =
      cfg.costs.precompileRipemd160Base + cfg.costs.precompileRipemd160PerWord * ((size + 31) / 32) := by
  simp only [ripemd160GasCost, ceil32, Nat.mul_div_cancel _ (by decide : 0 < 32)]

/-- Charge for the input, then compute the digest and pad it on the left with zeros.
Pinned EELS `src/ethereum/forks/amsterdam/vm/precompiled_contracts/ripemd160.py:26–51`. -/
def ripemd160 {m : Type → Type} [Monad m] [KeccakQuery m] (cfg : VmConfig) : PrecompileFn m :=
  fun data meter ↦
    match chargeGas meter (ripemd160GasCost cfg data.size) with
    | .ok paid => pure (.ok paid ((STFSpec.Hash.ripemd160 data.toByteArray).toBytes.leftPadZero 32))
    | .error error => pure (.halt error)

private theorem ripemd160_paid {m : Type → Type} [Monad m] [KeccakQuery m]
    (cfg : VmConfig) (data : Bytes) (meter : GasMeter)
    (affordable : ripemd160GasCost cfg data.size ≤ meter.gasLeft) :
    ripemd160 (m := m) cfg data meter =
      pure (.ok { meter with gasLeft := meter.gasLeft - ripemd160GasCost cfg data.size }
        ((STFSpec.Hash.ripemd160 data.toByteArray).toBytes.leftPadZero 32)) := by
  rw [ripemd160, chargeGas_of_le _ _ affordable]

private theorem ripemd160_denied {m : Type → Type} [Monad m] [KeccakQuery m]
    (cfg : VmConfig) (data : Bytes) (meter : GasMeter)
    (short : meter.gasLeft < ripemd160GasCost cfg data.size) :
    ripemd160 (m := m) cfg data meter = pure (.halt .outOfGas) := by
  rw [ripemd160, (chargeGas_eq_error_iff _ _ _).2 ⟨short, rfl⟩]

private theorem ripemd160_output_model (data : Bytes) :
    let digest := (STFSpec.Hash.ripemd160 data.toByteArray).toBytes
    let output := digest.leftPadZero 32
    output.size = 32 ∧ output.toList = List.replicate 12 0 ++ digest.toList ∧
      Ripemd160.Model.Digest data.toByteArray.data.toList digest.toList := by
  dsimp
  refine ⟨?_, ?_, Ripemd160.ripemd160_digest _⟩
  · rw [Bytes.size_leftPadZero, size_ripemd160]
    decide
  · rw [Bytes.toList_leftPadZero, size_ripemd160]
    rfl

private theorem ripemd160_success_at_id (cfg : VmConfig) (data output : Bytes) (entry final : GasMeter)
    (actual : ripemd160 (m := Id) cfg data entry = .ok final output) :
    chargeGas entry (ripemd160GasCost cfg data.size) = .ok final ∧
    final = { entry with gasLeft := entry.gasLeft - ripemd160GasCost cfg data.size } ∧
    output = (STFSpec.Hash.ripemd160 data.toByteArray).toBytes.leftPadZero 32 := by
  by_cases affordable : ripemd160GasCost cfg data.size ≤ entry.gasLeft
  · rw [ripemd160_paid _ _ _ affordable] at actual
    cases actual
    exact ⟨chargeGas_of_le _ _ affordable, rfl, rfl⟩
  · rw [ripemd160_denied _ _ _ (Nat.lt_of_not_ge affordable)] at actual
    cases actual

end STFSpec.Precompiles
