/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# Signed U256 caller proofs

Library `EthConformance`: fixed scripts use public model, range and constructor laws.
These are a baseline for REVIEW §7 R4; the complete replacement exercise and costs
remain open. No operation definition, stored field or inherited BitVec instance is used.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §7.
-/

open STFSpec.Base

example (a : U256) : U256.sdiv a U256.zero = U256.zero := U256.sdiv_zero a

example (a : U256) : U256.smod a U256.zero = U256.zero := U256.smod_zero a

example (a b : U256) (ha : a.toInt = -(2 : Int) ^ 255) (hb : b.toInt = -1) :
    U256.sdiv a b = a := U256.sdiv_eq_left_of_min_neg_one a b ha hb

example (a b : U256) (hb : b.toInt ≠ 0)
    (h : ¬ (a.toInt = -(2 : Int) ^ 255 ∧ b.toInt = -1)) :
    (U256.sdiv a b).toInt = a.toInt.tdiv b.toInt := by
  rw [U256.toInt_sdiv, ite_eq_right hb, ite_eq_right h]

example (a b : U256) (hb : b.toInt ≠ 0) :
    (U256.smod a b).toInt = a.toInt.tmod b.toInt := by
  rw [U256.toInt_smod, ite_eq_right hb]

example (a b : U256) :
    U256.ofInt? (if b.toInt = 0 then 0 else a.toInt.tmod b.toInt) =
      some (U256.smod a b) := U256.ofInt?_smod a b

example (a b : U256) (h : ¬ (a.toInt = -(2 : Int) ^ 255 ∧ b.toInt = -1)) :
    -(2 : Int) ^ 255 ≤ a.toInt.tdiv b.toInt := (U256.tdiv_in_signed_range a b h).1

example (a b : U256) : a.toInt.tmod b.toInt < (2 : Int) ^ 255 :=
  (U256.tmod_in_signed_range a b).2

example (a b : U256) :
    U256.ofInt? (if b.toInt = 0 then 0 else
      if a.toInt = -(2 : Int) ^ 255 ∧ b.toInt = -1 then -(2 : Int) ^ 255
      else a.toInt.tdiv b.toInt) = some (U256.sdiv a b) := U256.ofInt?_sdiv a b
