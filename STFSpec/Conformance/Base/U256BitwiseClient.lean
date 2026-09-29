/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# U256 bitwise client proofs

Library `EthConformance`: callers use only public model laws and constructors.
These unchanged proof scripts are a baseline for REVIEW §7 R4; the full replacement
exercise and opcode-loop cost checks remain open.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §7.
-/

open STFSpec.Base

example (a b : U256) (h : a.toNat < b.toNat) : (U256.lt a b).toNat = 1 := by
  rw [U256.toNat_lt_word, ite_eq_left h]

example (a b : U256) (h : a.toInt < b.toInt) : (U256.slt a b).toNat = 1 := by
  rw [U256.toNat_slt, ite_eq_left h]

example (x : U256) : U256.not (U256.not x) = x := by
  apply U256.ext
  rw [U256.toBitVec_not, U256.toBitVec_not, BitVec.not_not]

example (x : U256) : U256.and x x = x := by
  apply U256.ext
  rw [U256.toBitVec_and, BitVec.and_self]

example (x : U256) : U256.or x x = x := by
  apply U256.ext
  rw [U256.toBitVec_or, BitVec.or_self]

example (x : U256) : (U256.xor x x).toNat = 0 := by
  rw [U256.toNat_eq, U256.toBitVec_xor, BitVec.xor_self]
  rfl

example (i x : U256) (h : 32 ≤ i.toNat) : (U256.byte i x).toNat = 0 := by
  rw [U256.toNat_byte, ite_eq_left h]

example (k x : U256) (h : k.toNat = 31) : U256.signextend k x = x :=
  U256.signextend_eq_self_of_eq k x h

example (s v : U256) (hs : 256 ≤ s.toNat) (hv : v.toInt < 0) :
    U256.sar s v = U256.max := U256.sar_eq_max_of_le s v hs hv

example (s v : U256) (hs : 256 ≤ s.toNat) (hv : 0 ≤ v.toInt) :
    U256.sar s v = U256.zero := U256.sar_eq_zero_of_le s v hs hv

example (s v : U256) (hs : 256 ≤ s.toNat) : U256.shl s v = U256.zero :=
  U256.shl_eq_zero_of_le s v hs

example (s v : U256) (hs : 256 ≤ s.toNat) : U256.shr s v = U256.zero :=
  U256.shr_eq_zero_of_le s v hs

example (x : U256) : (U256.clz x).toNat + U256.bitLength x = 256 := by
  rw [U256.toNat_clz]
  exact Nat.sub_add_cancel (U256.bitLength_le x)
