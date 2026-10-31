/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Field

/-!
# Natural residue reference controls

Library `EthConformance`. Synthetic prime and composite moduli, independent literal
residues, all three arbitrary metadata choices, checked boundaries and actual equality.
Spec guidance: `STFSpec/informal/modules/EthField.md` §§3–4.
-/

namespace STFSpec.Conformance.Field
open STFSpec.Field

private def huge : Nat := 2 ^ 4096 + 17

private def controls (p : Nat) (hp : 1 < p) (metadata : Option Nat)
    (n expected : Nat) (checked : Option Nat) : Bool :=
  letI : FieldModulus p := ⟨hp, metadata⟩
  let a := PrimeFieldRef.ofNat (p := p) n
  let canonical := PrimeFieldRef.ofNat (p := p) expected
  a.toNat == expected && decide (a.toNat < p) &&
    (PrimeFieldRef.ofNat? (p := p) n).map PrimeFieldRef.toNat == checked &&
    decide (a = canonical) && decide (a = PrimeFieldRef.ofNat (n + p)) &&
    decide (a ≠ PrimeFieldRef.ofNat (expected + 1)) &&
    (decide (a = PrimeFieldRef.zero) == (expected == 0)) &&
    (decide (a = PrimeFieldRef.one) == (expected == 1)) &&
    (default : PrimeFieldRef p).toNat == 0 &&
    decide ((default : PrimeFieldRef p) = PrimeFieldRef.zero) &&
    (PrimeFieldRef.zero : PrimeFieldRef p).toNat == 0 &&
    (PrimeFieldRef.one : PrimeFieldRef p).toNat == 1 &&
    reprStr a == reprStr expected && reprStr a == reprStr canonical

-- p2_zero
#guard controls 2 (by decide) none
  (0) 0 (some 0)
#guard controls 2 (by decide) (some 0)
  (0) 0 (some 0)
#guard controls 2 (by decide) (some huge)
  (0) 0 (some 0)
-- p2_p_minus_one
#guard controls 2 (by decide) none
  (2 - 1) 1 (some 1)
#guard controls 2 (by decide) (some 0)
  (2 - 1) 1 (some 1)
#guard controls 2 (by decide) (some huge)
  (2 - 1) 1 (some 1)
-- p2_p
#guard controls 2 (by decide) none
  (2) 0 none
#guard controls 2 (by decide) (some 0)
  (2) 0 none
#guard controls 2 (by decide) (some huge)
  (2) 0 none
-- p2_p_plus_one
#guard controls 2 (by decide) none
  (2 + 1) 1 none
#guard controls 2 (by decide) (some 0)
  (2 + 1) 1 none
#guard controls 2 (by decide) (some huge)
  (2 + 1) 1 none
-- p2_two_p_plus_three
#guard controls 2 (by decide) none
  (2 * 2 + 3) 1 none
#guard controls 2 (by decide) (some 0)
  (2 * 2 + 3) 1 none
#guard controls 2 (by decide) (some huge)
  (2 * 2 + 3) 1 none
-- p2_huge_4096
#guard controls 2 (by decide) none
  (huge) 1 none
#guard controls 2 (by decide) (some 0)
  (huge) 1 none
#guard controls 2 (by decide) (some huge)
  (huge) 1 none
-- p3_zero
#guard controls 3 (by decide) none
  (0) 0 (some 0)
#guard controls 3 (by decide) (some 0)
  (0) 0 (some 0)
#guard controls 3 (by decide) (some huge)
  (0) 0 (some 0)
-- p3_p_minus_one
#guard controls 3 (by decide) none
  (3 - 1) 2 (some 2)
#guard controls 3 (by decide) (some 0)
  (3 - 1) 2 (some 2)
#guard controls 3 (by decide) (some huge)
  (3 - 1) 2 (some 2)
-- p3_p
#guard controls 3 (by decide) none
  (3) 0 none
#guard controls 3 (by decide) (some 0)
  (3) 0 none
#guard controls 3 (by decide) (some huge)
  (3) 0 none
-- p3_p_plus_one
#guard controls 3 (by decide) none
  (3 + 1) 1 none
#guard controls 3 (by decide) (some 0)
  (3 + 1) 1 none
#guard controls 3 (by decide) (some huge)
  (3 + 1) 1 none
-- p3_two_p_plus_three
#guard controls 3 (by decide) none
  (2 * 3 + 3) 0 none
#guard controls 3 (by decide) (some 0)
  (2 * 3 + 3) 0 none
#guard controls 3 (by decide) (some huge)
  (2 * 3 + 3) 0 none
-- p3_huge_4096
#guard controls 3 (by decide) none
  (huge) 0 none
#guard controls 3 (by decide) (some 0)
  (huge) 0 none
#guard controls 3 (by decide) (some huge)
  (huge) 0 none
-- p4_zero
#guard controls 4 (by decide) none
  (0) 0 (some 0)
#guard controls 4 (by decide) (some 0)
  (0) 0 (some 0)
#guard controls 4 (by decide) (some huge)
  (0) 0 (some 0)
-- p4_p_minus_one
#guard controls 4 (by decide) none
  (4 - 1) 3 (some 3)
#guard controls 4 (by decide) (some 0)
  (4 - 1) 3 (some 3)
#guard controls 4 (by decide) (some huge)
  (4 - 1) 3 (some 3)
-- p4_p
#guard controls 4 (by decide) none
  (4) 0 none
#guard controls 4 (by decide) (some 0)
  (4) 0 none
#guard controls 4 (by decide) (some huge)
  (4) 0 none
-- p4_p_plus_one
#guard controls 4 (by decide) none
  (4 + 1) 1 none
#guard controls 4 (by decide) (some 0)
  (4 + 1) 1 none
#guard controls 4 (by decide) (some huge)
  (4 + 1) 1 none
-- p4_two_p_plus_three
#guard controls 4 (by decide) none
  (2 * 4 + 3) 3 none
#guard controls 4 (by decide) (some 0)
  (2 * 4 + 3) 3 none
#guard controls 4 (by decide) (some huge)
  (2 * 4 + 3) 3 none
-- p4_huge_4096
#guard controls 4 (by decide) none
  (huge) 1 none
#guard controls 4 (by decide) (some 0)
  (huge) 1 none
#guard controls 4 (by decide) (some huge)
  (huge) 1 none
-- p9_zero
#guard controls 9 (by decide) none
  (0) 0 (some 0)
#guard controls 9 (by decide) (some 0)
  (0) 0 (some 0)
#guard controls 9 (by decide) (some huge)
  (0) 0 (some 0)
-- p9_p_minus_one
#guard controls 9 (by decide) none
  (9 - 1) 8 (some 8)
#guard controls 9 (by decide) (some 0)
  (9 - 1) 8 (some 8)
#guard controls 9 (by decide) (some huge)
  (9 - 1) 8 (some 8)
-- p9_p
#guard controls 9 (by decide) none
  (9) 0 none
#guard controls 9 (by decide) (some 0)
  (9) 0 none
#guard controls 9 (by decide) (some huge)
  (9) 0 none
-- p9_p_plus_one
#guard controls 9 (by decide) none
  (9 + 1) 1 none
#guard controls 9 (by decide) (some 0)
  (9 + 1) 1 none
#guard controls 9 (by decide) (some huge)
  (9 + 1) 1 none
-- p9_two_p_plus_three
#guard controls 9 (by decide) none
  (2 * 9 + 3) 3 none
#guard controls 9 (by decide) (some 0)
  (2 * 9 + 3) 3 none
#guard controls 9 (by decide) (some huge)
  (2 * 9 + 3) 3 none
-- p9_huge_4096
#guard controls 9 (by decide) none
  (huge) 6 none
#guard controls 9 (by decide) (some 0)
  (huge) 6 none
#guard controls 9 (by decide) (some huge)
  (huge) 6 none
-- p15_zero
#guard controls 15 (by decide) none
  (0) 0 (some 0)
#guard controls 15 (by decide) (some 0)
  (0) 0 (some 0)
#guard controls 15 (by decide) (some huge)
  (0) 0 (some 0)
-- p15_p_minus_one
#guard controls 15 (by decide) none
  (15 - 1) 14 (some 14)
#guard controls 15 (by decide) (some 0)
  (15 - 1) 14 (some 14)
#guard controls 15 (by decide) (some huge)
  (15 - 1) 14 (some 14)
-- p15_p
#guard controls 15 (by decide) none
  (15) 0 none
#guard controls 15 (by decide) (some 0)
  (15) 0 none
#guard controls 15 (by decide) (some huge)
  (15) 0 none
-- p15_p_plus_one
#guard controls 15 (by decide) none
  (15 + 1) 1 none
#guard controls 15 (by decide) (some 0)
  (15 + 1) 1 none
#guard controls 15 (by decide) (some huge)
  (15 + 1) 1 none
-- p15_two_p_plus_three
#guard controls 15 (by decide) none
  (2 * 15 + 3) 3 none
#guard controls 15 (by decide) (some 0)
  (2 * 15 + 3) 3 none
#guard controls 15 (by decide) (some huge)
  (2 * 15 + 3) 3 none
-- p15_huge_4096
#guard controls 15 (by decide) none
  (huge) 3 none
#guard controls 15 (by decide) (some 0)
  (huge) 3 none
#guard controls 15 (by decide) (some huge)
  (huge) 3 none
-- p17_zero
#guard controls 17 (by decide) none
  (0) 0 (some 0)
#guard controls 17 (by decide) (some 0)
  (0) 0 (some 0)
#guard controls 17 (by decide) (some huge)
  (0) 0 (some 0)
-- p17_p_minus_one
#guard controls 17 (by decide) none
  (17 - 1) 16 (some 16)
#guard controls 17 (by decide) (some 0)
  (17 - 1) 16 (some 16)
#guard controls 17 (by decide) (some huge)
  (17 - 1) 16 (some 16)
-- p17_p
#guard controls 17 (by decide) none
  (17) 0 none
#guard controls 17 (by decide) (some 0)
  (17) 0 none
#guard controls 17 (by decide) (some huge)
  (17) 0 none
-- p17_p_plus_one
#guard controls 17 (by decide) none
  (17 + 1) 1 none
#guard controls 17 (by decide) (some 0)
  (17 + 1) 1 none
#guard controls 17 (by decide) (some huge)
  (17 + 1) 1 none
-- p17_two_p_plus_three
#guard controls 17 (by decide) none
  (2 * 17 + 3) 3 none
#guard controls 17 (by decide) (some 0)
  (2 * 17 + 3) 3 none
#guard controls 17 (by decide) (some huge)
  (2 * 17 + 3) 3 none
-- p17_huge_4096
#guard controls 17 (by decide) none
  (huge) 1 none
#guard controls 17 (by decide) (some 0)
  (huge) 1 none
#guard controls 17 (by decide) (some huge)
  (huge) 1 none
-- p170141183460469231731687303715884105727_zero
#guard controls 170141183460469231731687303715884105727 (by decide) none
  (0) 0 (some 0)
#guard controls 170141183460469231731687303715884105727 (by decide) (some 0)
  (0) 0 (some 0)
#guard controls 170141183460469231731687303715884105727 (by decide) (some huge)
  (0) 0 (some 0)
-- p170141183460469231731687303715884105727_p_minus_one
#guard controls 170141183460469231731687303715884105727 (by decide) none
  (170141183460469231731687303715884105727 - 1) 170141183460469231731687303715884105726
  (some 170141183460469231731687303715884105726)
#guard controls 170141183460469231731687303715884105727 (by decide) (some 0)
  (170141183460469231731687303715884105727 - 1) 170141183460469231731687303715884105726
  (some 170141183460469231731687303715884105726)
#guard controls 170141183460469231731687303715884105727 (by decide) (some huge)
  (170141183460469231731687303715884105727 - 1) 170141183460469231731687303715884105726
  (some 170141183460469231731687303715884105726)
-- p170141183460469231731687303715884105727_p
#guard controls 170141183460469231731687303715884105727 (by decide) none
  (170141183460469231731687303715884105727) 0 none
#guard controls 170141183460469231731687303715884105727 (by decide) (some 0)
  (170141183460469231731687303715884105727) 0 none
#guard controls 170141183460469231731687303715884105727 (by decide) (some huge)
  (170141183460469231731687303715884105727) 0 none
-- p170141183460469231731687303715884105727_p_plus_one
#guard controls 170141183460469231731687303715884105727 (by decide) none
  (170141183460469231731687303715884105727 + 1) 1 none
#guard controls 170141183460469231731687303715884105727 (by decide) (some 0)
  (170141183460469231731687303715884105727 + 1) 1 none
#guard controls 170141183460469231731687303715884105727 (by decide) (some huge)
  (170141183460469231731687303715884105727 + 1) 1 none
-- p170141183460469231731687303715884105727_two_p_plus_three
#guard controls 170141183460469231731687303715884105727 (by decide) none
  (2 * 170141183460469231731687303715884105727 + 3) 3 none
#guard controls 170141183460469231731687303715884105727 (by decide) (some 0)
  (2 * 170141183460469231731687303715884105727 + 3) 3 none
#guard controls 170141183460469231731687303715884105727 (by decide) (some huge)
  (2 * 170141183460469231731687303715884105727 + 3) 3 none
-- p170141183460469231731687303715884105727_huge_4096
#guard controls 170141183460469231731687303715884105727 (by decide) none
  (huge) 4294967313 none
#guard controls 170141183460469231731687303715884105727 (by decide) (some 0)
  (huge) 4294967313 none
#guard controls 170141183460469231731687303715884105727 (by decide) (some huge)
  (huge) 4294967313 none

private def pairwise (p : Nat) (hp : 1 < p) (metadata : Option Nat) : List (List Bool) :=
  letI : FieldModulus p := ⟨hp, metadata⟩
  let values := [0, p - 1, p, p + 1, 2 * p + 3, huge].map
    (PrimeFieldRef.ofNat (p := p))
  values.map fun a ↦ values.map fun b ↦ decide (a = b)

#guard pairwise 2 (by decide) none ==
  [
    [true, false, true, false, false, false],
    [false, true, false, true, true, true],
    [true, false, true, false, false, false],
    [false, true, false, true, true, true],
    [false, true, false, true, true, true],
    [false, true, false, true, true, true]  ]
#guard pairwise 2 (by decide) (some 0) ==
  [
    [true, false, true, false, false, false],
    [false, true, false, true, true, true],
    [true, false, true, false, false, false],
    [false, true, false, true, true, true],
    [false, true, false, true, true, true],
    [false, true, false, true, true, true]  ]
#guard pairwise 2 (by decide) (some huge) ==
  [
    [true, false, true, false, false, false],
    [false, true, false, true, true, true],
    [true, false, true, false, false, false],
    [false, true, false, true, true, true],
    [false, true, false, true, true, true],
    [false, true, false, true, true, true]  ]
#guard pairwise 3 (by decide) none ==
  [
    [true, false, true, false, true, true],
    [false, true, false, false, false, false],
    [true, false, true, false, true, true],
    [false, false, false, true, false, false],
    [true, false, true, false, true, true],
    [true, false, true, false, true, true]  ]
#guard pairwise 3 (by decide) (some 0) ==
  [
    [true, false, true, false, true, true],
    [false, true, false, false, false, false],
    [true, false, true, false, true, true],
    [false, false, false, true, false, false],
    [true, false, true, false, true, true],
    [true, false, true, false, true, true]  ]
#guard pairwise 3 (by decide) (some huge) ==
  [
    [true, false, true, false, true, true],
    [false, true, false, false, false, false],
    [true, false, true, false, true, true],
    [false, false, false, true, false, false],
    [true, false, true, false, true, true],
    [true, false, true, false, true, true]  ]
#guard pairwise 4 (by decide) none ==
  [
    [true, false, true, false, false, false],
    [false, true, false, false, true, false],
    [true, false, true, false, false, false],
    [false, false, false, true, false, true],
    [false, true, false, false, true, false],
    [false, false, false, true, false, true]  ]
#guard pairwise 4 (by decide) (some 0) ==
  [
    [true, false, true, false, false, false],
    [false, true, false, false, true, false],
    [true, false, true, false, false, false],
    [false, false, false, true, false, true],
    [false, true, false, false, true, false],
    [false, false, false, true, false, true]  ]
#guard pairwise 4 (by decide) (some huge) ==
  [
    [true, false, true, false, false, false],
    [false, true, false, false, true, false],
    [true, false, true, false, false, false],
    [false, false, false, true, false, true],
    [false, true, false, false, true, false],
    [false, false, false, true, false, true]  ]
#guard pairwise 9 (by decide) none ==
  [
    [true, false, true, false, false, false],
    [false, true, false, false, false, false],
    [true, false, true, false, false, false],
    [false, false, false, true, false, false],
    [false, false, false, false, true, false],
    [false, false, false, false, false, true]  ]
#guard pairwise 9 (by decide) (some 0) ==
  [
    [true, false, true, false, false, false],
    [false, true, false, false, false, false],
    [true, false, true, false, false, false],
    [false, false, false, true, false, false],
    [false, false, false, false, true, false],
    [false, false, false, false, false, true]  ]
#guard pairwise 9 (by decide) (some huge) ==
  [
    [true, false, true, false, false, false],
    [false, true, false, false, false, false],
    [true, false, true, false, false, false],
    [false, false, false, true, false, false],
    [false, false, false, false, true, false],
    [false, false, false, false, false, true]  ]
#guard pairwise 15 (by decide) none ==
  [
    [true, false, true, false, false, false],
    [false, true, false, false, false, false],
    [true, false, true, false, false, false],
    [false, false, false, true, false, false],
    [false, false, false, false, true, true],
    [false, false, false, false, true, true]  ]
#guard pairwise 15 (by decide) (some 0) ==
  [
    [true, false, true, false, false, false],
    [false, true, false, false, false, false],
    [true, false, true, false, false, false],
    [false, false, false, true, false, false],
    [false, false, false, false, true, true],
    [false, false, false, false, true, true]  ]
#guard pairwise 15 (by decide) (some huge) ==
  [
    [true, false, true, false, false, false],
    [false, true, false, false, false, false],
    [true, false, true, false, false, false],
    [false, false, false, true, false, false],
    [false, false, false, false, true, true],
    [false, false, false, false, true, true]  ]
#guard pairwise 17 (by decide) none ==
  [
    [true, false, true, false, false, false],
    [false, true, false, false, false, false],
    [true, false, true, false, false, false],
    [false, false, false, true, false, true],
    [false, false, false, false, true, false],
    [false, false, false, true, false, true]  ]
#guard pairwise 17 (by decide) (some 0) ==
  [
    [true, false, true, false, false, false],
    [false, true, false, false, false, false],
    [true, false, true, false, false, false],
    [false, false, false, true, false, true],
    [false, false, false, false, true, false],
    [false, false, false, true, false, true]  ]
#guard pairwise 17 (by decide) (some huge) ==
  [
    [true, false, true, false, false, false],
    [false, true, false, false, false, false],
    [true, false, true, false, false, false],
    [false, false, false, true, false, true],
    [false, false, false, false, true, false],
    [false, false, false, true, false, true]  ]
#guard pairwise 170141183460469231731687303715884105727 (by decide) none ==
  [
    [true, false, true, false, false, false],
    [false, true, false, false, false, false],
    [true, false, true, false, false, false],
    [false, false, false, true, false, false],
    [false, false, false, false, true, false],
    [false, false, false, false, false, true]  ]
#guard pairwise 170141183460469231731687303715884105727 (by decide) (some 0) ==
  [
    [true, false, true, false, false, false],
    [false, true, false, false, false, false],
    [true, false, true, false, false, false],
    [false, false, false, true, false, false],
    [false, false, false, false, true, false],
    [false, false, false, false, false, true]  ]
#guard pairwise 170141183460469231731687303715884105727 (by decide) (some huge) ==
  [
    [true, false, true, false, false, false],
    [false, true, false, false, false, false],
    [true, false, true, false, false, false],
    [false, false, false, true, false, false],
    [false, false, false, false, true, false],
    [false, false, false, false, false, true]  ]

end STFSpec.Conformance.Field
