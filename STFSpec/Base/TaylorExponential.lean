/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import Std

/-!
# Iterated-floor Taylor exponential

Library `EthBase`: the source-order integer loop from pinned EELS
`src/ethereum/utils/numeric.py:177–216`, on arbitrary natural inputs with a
positive denominator. Each intermediate floor is retained. The private logical
measure proves totality; it does not supply a practical runtime bound (DISC-002).

Spec guidance: `STFSpec/informal/modules/EthBase.md` §3/§7.
-/

namespace STFSpec.Base

private theorem next_lt (numerator denominator i numeratorAccumulated : Nat)
    (hd : 0 < denominator) (hi : numerator < i) (ha : 0 < numeratorAccumulated) :
    numeratorAccumulated * numerator / (denominator * i) < numeratorAccumulated := by
  have hdi : i ≤ denominator * i := by
    simpa using Nat.mul_le_mul_right i (show 1 ≤ denominator by omega)
  have hni : numerator < denominator * i := by omega
  apply (Nat.div_lt_iff_lt_mul (show 0 < denominator * i by omega)).2
  exact Nat.mul_lt_mul_of_pos_left hni ha

private def go (numerator denominator : Nat) (hd : 0 < denominator)
    (i numeratorAccumulated output : Nat) (hi : 0 < i) : Nat :=
  if ha : numeratorAccumulated = 0 then output / denominator
  else
    let output' := output + numeratorAccumulated
    let numeratorAccumulated' := numeratorAccumulated * numerator / (denominator * i)
    let i' := i + 1
    go numerator denominator hd i' numeratorAccumulated' output' (by omega)
termination_by (numerator + 1 - i, numeratorAccumulated)
decreasing_by
  by_cases hprefix : i ≤ numerator
  · apply Prod.Lex.left
    omega
  · have hzero : numerator + 1 - i = 0 := by omega
    have hnextzero : numerator + 1 - (i + 1) = 0 := by omega
    rw [hzero, hnextzero]
    apply Prod.Lex.right
    exact next_lt numerator denominator i numeratorAccumulated hd (by omega) (by omega)

/-- EELS `src/ethereum/utils/numeric.py:177–216`: add each positive accumulated term, floor the
next term, advance the one-based index, and divide the completed sum. -/
def taylorExponential (factor numerator denominator : Nat) (h : 0 < denominator) : Nat :=
  go numerator denominator h 1 (factor * denominator) 0 (by omega)

private theorem go_zero (numerator denominator : Nat) (hd : 0 < denominator)
    (i output : Nat) (hi : 0 < i) :
    go numerator denominator hd i 0 output hi = output / denominator := by
  rw [go]
  simp

private theorem go_step (numerator denominator : Nat) (hd : 0 < denominator)
    (i numeratorAccumulated output : Nat) (hi : 0 < i) (ha : 0 < numeratorAccumulated) :
    go numerator denominator hd i numeratorAccumulated output hi =
      go numerator denominator hd (i + 1)
        (numeratorAccumulated * numerator / (denominator * i))
        (output + numeratorAccumulated) (by omega) := by
  rw [go]
  split
  · omega
  · rfl

/-- A zero factor starts at the terminal branch, at every positive denominator. -/
theorem taylorExponential_zero_factor (numerator denominator : Nat)
    (h : 0 < denominator) : taylorExponential 0 numerator denominator h = 0 := by
  simp only [taylorExponential, Nat.zero_mul, go_zero, Nat.zero_div]

/-- With numerator zero, the single initial term returns the complete factor. -/
theorem taylorExponential_zero_numerator (factor denominator : Nat)
    (h : 0 < denominator) : taylorExponential factor 0 denominator h = factor := by
  by_cases hf : factor = 0
  · subst factor
    exact taylorExponential_zero_factor 0 denominator h
  · unfold taylorExponential
    rw [go_step 0 denominator h 1 (factor * denominator) 0 (by omega)
      (Nat.mul_pos (by omega) h)]
    simp only [Nat.mul_zero, Nat.zero_div, Nat.zero_add, go_zero]
    exact Nat.mul_div_cancel factor h

private theorem small_two : taylorExponential 1 2 1 (by decide) = 6 := by
  unfold taylorExponential
  rw [go_step 2 1 (by decide) 1 1 0 (by decide) (by decide)]
  rw [go_step 2 1 (by decide) 2 2 1 (by decide) (by decide)]
  rw [go_step 2 1 (by decide) 3 2 3 (by decide) (by decide)]
  rw [go_step 2 1 (by decide) 4 1 5 (by decide) (by decide)]
  rw [go_zero]

private theorem iterated_floor_is_not_unfloored_prefix :
    taylorExponential 1 2 1 (by decide) ≠ 7 := by
  rw [small_two]
  decide

end STFSpec.Base
