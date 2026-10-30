/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Witness ancestor public-equation clients

Library `EthConformance`: arbitrary-input private clients use only the public equation.
Spec guidance: `STFSpec/informal/modules/EthState.md` R27/§7.
-/

namespace STFSpec.Conformance.State.WitnessAncestorsCallerProofs

open STFSpec.State

private theorem absent (headers : List ByteArray) :
    getWitnessAncestors headers none = [] := by
  rw [getWitnessAncestors_eq]

private theorem zero (headers : List ByteArray) :
    getWitnessAncestors headers (some 0) = headers := by
  rw [getWitnessAncestors_eq]
  simp only [ite_true]

private theorem positive (headers : List ByteArray) (n : Nat) (hn : n ≠ 0) :
    getWitnessAncestors headers (some n) = headers.drop (headers.length - n) := by
  rw [getWitnessAncestors_eq]
  simp only [hn, ite_false]

private theorem clipped (headers : List ByteArray) (n : Nat) (hn : headers.length ≤ n) :
    getWitnessAncestors headers (some n) = headers := by
  rw [getWitnessAncestors_eq]
  simp only [Nat.sub_eq_zero_of_le hn, List.drop_zero]
  split <;> rfl

private theorem size (headers : List ByteArray) (n : Nat) (hn : n ≠ 0) :
    (getWitnessAncestors headers (some n)).length = min headers.length n := by
  rw [positive headers n hn, List.length_drop]
  omega

end STFSpec.Conformance.State.WitnessAncestorsCallerProofs
