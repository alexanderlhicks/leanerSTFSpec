/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.U256Arithmetic
import STFSpec.Base.U256Bitwise

/-!
# U256 shift composition laws

Library `EthBase`: nested shifts compose when the natural sum of their unsigned
amounts is below `2^256`. Saturation is compatible with composition. The proofs use
public model equations, not stored fields.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §7.
-/

namespace STFSpec.Base.U256

private theorem toBitVec_shl_eq (shift value : U256) :
    (shl shift value).toBitVec = value.toBitVec <<< shift.toNat := by
  rw [toBitVec_shl]
  split
  next h => exact (BitVec.shiftLeft_eq_zero h).symm
  next h => rfl

private theorem toBitVec_shr_eq (shift value : U256) :
    (shr shift value).toBitVec = value.toBitVec >>> shift.toNat := by
  rw [toBitVec_shr]
  split
  next h => exact (BitVec.ushiftRight_eq_zero h).symm
  next h => rfl

/-- Nested SHL amounts compose through word addition when their unsigned natural
sum is below `2^256`. The premise prevents amount wraparound. -/
theorem shl_shl_of_add_lt (s t v : U256) (h : s.toNat + t.toNat < 2 ^ 256) :
    shl t (shl s v) = shl (add s t) v := by
  apply ext
  rw [toBitVec_shl_eq, toBitVec_shl_eq, toBitVec_shl_eq, toNat_add_of_lt s t h]
  exact (BitVec.shiftLeft_add v.toBitVec s.toNat t.toNat).symm

/-- Nested SHR amounts compose through word addition when their unsigned natural
sum is below `2^256`. The premise prevents amount wraparound. -/
theorem shr_shr_of_add_lt (s t v : U256) (h : s.toNat + t.toNat < 2 ^ 256) :
    shr t (shr s v) = shr (add s t) v := by
  apply ext
  rw [toBitVec_shr_eq, toBitVec_shr_eq, toBitVec_shr_eq, toNat_add_of_lt s t h]
  exact (BitVec.shiftRight_add v.toBitVec s.toNat t.toNat).symm

/-- Nested SAR amounts compose through word addition when their unsigned natural
sum is below `2^256`. The premise prevents amount wraparound. -/
theorem sar_sar_of_add_lt (s t v : U256) (h : s.toNat + t.toNat < 2 ^ 256) :
    sar t (sar s v) = sar (add s t) v := by
  apply ext
  rw [toBitVec_sar, toBitVec_sar, toBitVec_sar, toNat_add_of_lt s t h]
  exact BitVec.sshiftRight_add.symm

end STFSpec.Base.U256
