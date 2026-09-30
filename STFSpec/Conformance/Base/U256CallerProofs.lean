/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# U256 client proof tests

Library `EthConformance`: fixed client proofs use only public observers and laws,
without stored fields, representation unfolding or inherited BitVec instances.
These are baseline proof scripts for REVIEW §7 R4; a complete alternative representation
and opcode-loop benchmarks remain later work.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §7.
-/

open STFSpec.Base

-- Reconstructing a word can be used by clients without learning its representation.
example (x : U256) : U256.ofBitVec x.toBitVec = x := U256.ofBitVec_toBitVec x

example (bits : BitVec 256) : (U256.ofBitVec bits).toBitVec = bits :=
  U256.toBitVec_ofBitVec bits
example (x : U256) : U256.ofNat x.toNat = x := U256.ofNat_toNat x

example (x : U256) : U256.ofNat? x.toNat = some x := U256.ofNat?_toNat x

example (x : U256) : U256.ofInt? x.toInt = some x := U256.ofInt?_toInt x

example (x y : U256) (h : x.toNat = y.toNat) : x = y := U256.toNat_inj.mp h

example (x y : U256) (h : x.toInt = y.toInt) : x = y := U256.toInt_inj.mp h

example (x y : U256) (h : x.toBitVec = y.toBitVec) : x = y := U256.ext h

example (x y : U256) (h : compare x y = .eq) : x = y :=
  (U256.compare_eq_eq_iff x y).mp h

example (x : U256) : U256.ofNat? (x.toNat + 2 ^ 256) = none := by
  apply (U256.ofNat?_eq_none_iff _).mpr
  omega

example (x : U256) (h : x.toNat < 2 ^ 255) : 0 ≤ x.toInt := by
  simp only [U256.toInt_eq_toNat_cond, h, ite_true]
  omega

example (x y : U256) (hx : x.toInt < 0) (hy : 0 ≤ y.toInt) : compare x y = .gt := by
  apply (U256.compare_eq_gt_iff x y).mpr
  have hxr := U256.toNat_lt x
  have hyr := U256.toNat_lt y
  rw [U256.toInt_eq_toNat_cond] at hx hy
  split at hx <;> split at hy <;> omega

example (b : Bool) : (U256.ofBool b).toInt = (U256.ofBool b).toNat := by
  rw [U256.toInt_ofBool, U256.toNat_ofBool]
  cases b <;> rfl

example : Std.TransOrd U256 := inferInstance

example : Std.LawfulEqOrd U256 := inferInstance
