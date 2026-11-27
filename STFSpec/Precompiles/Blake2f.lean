/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.Bytes
import STFSpec.Hash.Blake2Compression
import STFSpec.Hash.Blake2Parameters
import STFSpec.Hash.KeccakQuery
import STFSpec.Vm.Core.Config
import STFSpec.Vm.Core.Precompile

/-!
# BLAKE2F precompile

Library `EthPrecompiles`. Check input length, parse the raw parameters, and
charge before validating the final flag and compressing.
See `STFSpec/informal/modules/EthPrecompiles.md`.
-/

namespace STFSpec.Precompiles

open STFSpec.Base STFSpec.Hash STFSpec.Vm.Core

private def blake2fParameters (data : Bytes) (sized : data.size = 213) : Blake2b.Params :=
  Blake2b.getParameters data.toByteArray (by simpa only [Bytes.size_toByteArray] using sized)

private def blake2fOutput (params : Blake2b.Params) : Bytes :=
  Bytes.ofByteArray
    (Blake2b.compress params.rounds params.h params.m params.t0 params.t1 (params.f == 1))

/-- Parse a 213-byte input and charge for its rounds before checking the final flag.
Pinned EELS `src/ethereum/forks/amsterdam/vm/precompiled_contracts/blake2f.py:21–42`. -/
def blake2f {m : Type → Type} [Monad m] [KeccakQuery m] (cfg : VmConfig) : PrecompileFn m :=
  fun data meter ↦
    if sized : data.size = 213 then
      let params := blake2fParameters data sized
      match chargeGas meter (cfg.costs.precompileBlake2FPerRound * params.rounds.toNat) with
      | .ok paid =>
        if params.f = 0 ∨ params.f = 1 then pure (.ok paid (blake2fOutput params))
        else pure (.halt .invalidParameter)
      | .error error => pure (.halt error)
    else pure (.halt .invalidParameter)

private theorem blake2f_badLength {m : Type → Type} [Monad m] [KeccakQuery m]
    (cfg : VmConfig) (data : Bytes) (meter : GasMeter) (wrong : data.size ≠ 213) :
    blake2f (m := m) cfg data meter = pure (.halt .invalidParameter) := by
  simp only [blake2f, dite_eq_right wrong]

private theorem blake2f_denied {m : Type → Type} [Monad m] [KeccakQuery m]
    (cfg : VmConfig) (data : Bytes) (meter : GasMeter) (sized : data.size = 213)
    (short : meter.gasLeft < cfg.costs.precompileBlake2FPerRound *
      (blake2fParameters data sized).rounds.toNat) :
    blake2f (m := m) cfg data meter = pure (.halt .outOfGas) := by
  simp only [blake2f, dite_eq_left sized, (chargeGas_eq_error_iff _ _ _).2 ⟨short, rfl⟩]

private theorem blake2f_paidBadFlag {m : Type → Type} [Monad m] [KeccakQuery m]
    (cfg : VmConfig) (data : Bytes) (meter : GasMeter) (sized : data.size = 213)
    (affordable : cfg.costs.precompileBlake2FPerRound *
      (blake2fParameters data sized).rounds.toNat ≤ meter.gasLeft)
    (badFlag : ¬ ((blake2fParameters data sized).f = 0 ∨ (blake2fParameters data sized).f = 1)) :
    blake2f (m := m) cfg data meter = pure (.halt .invalidParameter) := by
  simp only [blake2f, dite_eq_left sized, chargeGas_of_le _ _ affordable, ite_eq_right badFlag]

private theorem blake2f_paid {m : Type → Type} [Monad m] [KeccakQuery m]
    (cfg : VmConfig) (data : Bytes) (meter : GasMeter) (sized : data.size = 213)
    (affordable : cfg.costs.precompileBlake2FPerRound *
      (blake2fParameters data sized).rounds.toNat ≤ meter.gasLeft)
    (validFlag : (blake2fParameters data sized).f = 0 ∨ (blake2fParameters data sized).f = 1) :
    let params := blake2fParameters data sized
    blake2f (m := m) cfg data meter =
      pure (.ok
        { meter with gasLeft := meter.gasLeft - cfg.costs.precompileBlake2FPerRound * params.rounds.toNat }
        (blake2fOutput params)) := by
  simp only [blake2f, dite_eq_left sized, chargeGas_of_le _ _ affordable, ite_eq_left validFlag]

private theorem blake2f_output_model (params : Blake2b.Params) :
    (blake2fOutput params).size = 64 ∧
      (blake2fOutput params).toByteArray =
        Blake2b.Model.compress params.rounds (Blake2b.wordsModel params.h) (Blake2b.wordsModel params.m)
          params.t0.toBitVec params.t1.toBitVec (params.f == 1) := by
  exact ⟨Blake2b.compress_size _ _ _ _ _ _, Blake2b.compress_model _ _ _ _ _ _⟩

end STFSpec.Precompiles
