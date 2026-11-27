/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

/-!
# MODEXP pricing

Library `EthPrecompiles`. Price the multiplication and iteration counts
using the exact natural-number formulas in EELS.
See `STFSpec/informal/modules/EthPrecompiles.md`.
-/

namespace STFSpec.Precompiles.Modexp

/-- Estimate multiplication cost from the larger operand width.
Pinned EELS `src/ethereum/forks/amsterdam/vm/precompiled_contracts/modexp.py:76–99`. -/
def complexity (baseLength modulusLength : Nat) : Nat :=
  let length := max baseLength modulusLength
  if length ≤ 32 then 16
  else
    let words := (length + 7) / 8
    2 * words^2

/-- Count at least one iteration, adding 16 for each exponent byte past 32.
Pinned EELS `src/ethereum/forks/amsterdam/vm/precompiled_contracts/modexp.py:102–140`. -/
def iterations (exponentLength exponentHead : Nat) : Nat :=
  max 1 (16 * (exponentLength - 32) + exponentHead.log2)

private theorem adjustedBitLength_eq_log2 (head : Nat) :
    (if head = 0 then 0 else head.log2 + 1) - 1 = head.log2 := by
  by_cases zero : head = 0
  · simp [zero]
  · simp [zero]

private theorem iterations_eq_source (exponentLength exponentHead : Nat) :
    let bitLength := if exponentHead = 0 then 0 else exponentHead.log2 + 1
    iterations exponentLength exponentHead =
      max 1 (if exponentLength ≤ 32 then bitLength - 1
             else 16 * (exponentLength - 32) + (bitLength - 1)) := by
  dsimp only
  rw [adjustedBitLength_eq_log2]
  by_cases short : exponentLength ≤ 32
  · simp [iterations, short, Nat.sub_eq_zero_of_le short]
  · simp [iterations, short]

/-- Multiply the complexity by the iteration count and apply the minimum charge.
Pinned EELS `src/ethereum/forks/amsterdam/vm/precompiled_contracts/modexp.py:143–176`. -/
def gasCost (baseLength modulusLength exponentLength exponentHead : Nat) : Nat :=
  max 500 (complexity baseLength modulusLength * iterations exponentLength exponentHead)

/-- The exact quote includes the minimum charge for every input to the pricing helper. -/
theorem gasCost_ge_500 (baseLength modulusLength exponentLength exponentHead : Nat) :
    500 ≤ gasCost baseLength modulusLength exponentLength exponentHead :=
  Nat.le_max_left _ _

end STFSpec.Precompiles.Modexp
