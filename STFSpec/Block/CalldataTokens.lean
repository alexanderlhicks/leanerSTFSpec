/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.Bytes

/-!
# Calldata token count

Library `EthBlock`. Pinned EELS `src/ethereum/forks/amsterdam/transactions.py:804–814`.
Every zero byte contributes one token, every other byte four. This helper does not
compute the all-bytes calldata floor. Spec guidance: `STFSpec/informal/modules/EthBlock.md`.
-/

namespace STFSpec.Block
open STFSpec.Base

private def tokenWeight (byte : UInt8) : Nat := if byte = 0 then 1 else 4

private def tokenReference : List UInt8 → Nat
  | [] => 0
  | byte :: rest => tokenWeight byte + tokenReference rest

private theorem fold_tokens (xs : List UInt8) (acc : Nat) :
    xs.foldl (fun n byte ↦ n + tokenWeight byte) acc = acc + tokenReference xs := by
  induction xs generalizing acc with
  | nil => simp [tokenReference]
  | cons byte rest ih => simp [tokenReference, ih, Nat.add_assoc]

private theorem reference_formula (xs : List UInt8) :
    tokenReference xs =
      (xs.filter (fun byte ↦ byte == 0)).length +
        4 * (xs.length - (xs.filter (fun byte ↦ byte == 0)).length) := by
  induction xs with
  | nil => simp [tokenReference]
  | cons byte rest ih =>
    have bound := List.length_filter_le (fun byte : UInt8 ↦ byte == 0) rest
    by_cases h : byte = 0
    · simp [tokenReference, tokenWeight, h, ih]
      omega
    · simp [tokenReference, tokenWeight, h, ih]
      omega

/-- Total calldata token count on every finite byte array; EELS
`src/ethereum/forks/amsterdam/transactions.py:804–814`.
The executable path folds the packed input without allocating its list model. -/
def countTokensInData (data : ByteArray) : Nat :=
  (Bytes.ofByteArray data).foldl (fun n byte ↦ n + tokenWeight byte) 0

private theorem countTokensInData_eq_reference (data : ByteArray) :
    countTokensInData data = tokenReference data.data.toList := by
  rw [countTokensInData, Bytes.foldl_eq, Bytes.toList_ofByteArray, fold_tokens]
  exact Nat.zero_add _

/-- Complete source result: zeros plus four times the remaining byte count.
The zero count is at most the input size, so the source Uint subtraction is safe.
This ordinary theorem covers every finite input, including empty data. -/
theorem countTokensInData_eq (data : ByteArray) :
    countTokensInData data =
      (data.data.toList.filter (fun byte ↦ byte == 0)).length +
        4 * (data.size - (data.data.toList.filter (fun byte ↦ byte == 0)).length) := by
  rw [countTokensInData_eq_reference, reference_formula]
  rfl

end STFSpec.Block
