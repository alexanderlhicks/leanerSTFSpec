/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import Init.Data.ByteArray.Lemmas
import Init.Data.List.OfFn
import Init.Data.Array.OfFn
import Init.Omega

/-!
# Byte sequences, zero padding and bounded padded reads

Library `EthBase`. Padding follows pinned EELS `src/ethereum/utils/byte.py:18,40`.
The internal padded-read helper models `src/ethereum/forks/amsterdam/vm/memory.py:63`.
Its loop visits only result indices; a large offset is never traversed or narrowed.
Spec guidance: `STFSpec/informal/modules/EthBase.md`.
-/

namespace STFSpec.Base

/-- Variable-length immutable byte values; `ethereum_types/bytes.py:165` (locked 0.4.1).
Updates retain the linear-buffer discipline. -/
abbrev Bytes := ByteArray

namespace Bytes

/-- Stable list observation of a byte sequence. -/
def toList (b : Bytes) : List UInt8 := b.data.toList

/-- The list observation has exactly the byte sequence's size. -/
theorem length_toList (b : Bytes) : (toList b).length = b.size := by
  simp only [toList, Array.length_toList, ByteArray.size]

/-- Byte sequences are equal whenever their stable observations agree. -/
theorem ext {a b : Bytes} (h : toList a = toList b) : a = b := by
  apply ByteArray.ext
  exact Array.toList_inj.mp h

/-- The stable observation is injective. -/
theorem toList_inj {a b : Bytes} : toList a = toList b ↔ a = b :=
  ⟨ext, fun h => congrArg toList h⟩

/-- Observing a byte sequence built from a list returns that list. -/
theorem toList_toByteArray (xs : List UInt8) : toList xs.toByteArray = xs := by
  simp [toList]

/-- Rebuilding from the stable list observation preserves the byte sequence. -/
theorem toByteArray_toList (b : Bytes) : (toList b).toByteArray = b := by
  apply ext
  rw [toList_toByteArray]

private def zeros (n : Nat) : Bytes := ⟨Array.replicate n 0⟩

private theorem toList_zeros (n : Nat) : toList (zeros n) = List.replicate n 0 := by
  simp [toList, zeros]

private theorem size_zeros (n : Nat) : (zeros n).size = n := by
  simp only [zeros, ByteArray.size, Array.size_replicate]

/-- Nontruncating left zero padding; EELS `src/ethereum/utils/byte.py:18,37`.
Only missing zeros are allocated. Oversize inputs are returned unchanged. -/
def leftPadZero (b : Bytes) (n : Nat) : Bytes :=
  if n ≤ b.size then b else zeros (n - b.size) ++ b

/-- Nontruncating right zero padding; EELS `src/ethereum/utils/byte.py:40,59`. -/
def rightPadZero (b : Bytes) (n : Nat) : Bytes :=
  if n ≤ b.size then b else b ++ zeros (n - b.size)

/-- Left padding prepends exactly the missing zero bytes. -/
theorem toList_leftPadZero (b : Bytes) (n : Nat) :
    toList (leftPadZero b n) = List.replicate (n - b.size) 0 ++ toList b := by
  unfold leftPadZero
  split
  · next h => simp [Nat.sub_eq_zero_of_le h]
  · simp [toList, zeros]

/-- Right padding appends exactly the missing zero bytes. -/
theorem toList_rightPadZero (b : Bytes) (n : Nat) :
    toList (rightPadZero b n) = toList b ++ List.replicate (n - b.size) 0 := by
  unfold rightPadZero
  split
  · next h => simp [Nat.sub_eq_zero_of_le h]
  · simp [toList, zeros]

/-- Left padding produces the greater of the original and requested sizes. -/
theorem size_leftPadZero (b : Bytes) (n : Nat) : (leftPadZero b n).size = max b.size n := by
  unfold leftPadZero
  split
  · next h => simp [Nat.max_eq_left h]
  · next h => rw [ByteArray.size_append, size_zeros]; omega

/-- Right padding produces the greater of the original and requested sizes. -/
theorem size_rightPadZero (b : Bytes) (n : Nat) : (rightPadZero b n).size = max b.size n := by
  unfold rightPadZero
  split
  · next h => simp [Nat.max_eq_left h]
  · next h => rw [ByteArray.size_append, size_zeros]; omega

/-- Left padding never truncates an input already large enough. -/
theorem leftPadZero_of_le (b : Bytes) (n : Nat) (h : n ≤ b.size) : leftPadZero b n = b := by
  simp [leftPadZero, h]

/-- Right padding never truncates an input already large enough. -/
theorem rightPadZero_of_le (b : Bytes) (n : Nat) (h : n ≤ b.size) : rightPadZero b n = b := by
  simp [rightPadZero, h]

/-- Repeating left padding at the same size has no further effect. -/
theorem leftPadZero_idempotent (b : Bytes) (n : Nat) :
    leftPadZero (leftPadZero b n) n = leftPadZero b n := by
  apply leftPadZero_of_le
  rw [size_leftPadZero]
  exact Nat.le_max_right _ _

/-- Repeating right padding at the same size has no further effect. -/
theorem rightPadZero_idempotent (b : Bytes) (n : Nat) :
    rightPadZero (rightPadZero b n) n = rightPadZero b n := by
  apply rightPadZero_of_le
  rw [size_rightPadZero]
  exact Nat.le_max_right _ _

/-- Internal zero-extended read, corresponding to EELS `src/ethereum/forks/amsterdam/vm/memory.py:63,82–83`.
The result array has `len` entries. Bounds are checked in `Nat` before each direct
byte access, so even an enormous `start` does not allocate or traverse a prefix. -/
def extractPadded (b : Bytes) (start len : Nat) : Bytes :=
  ⟨Array.ofFn (fun i : Fin len => if h : start + i.val < b.size then b[start + i.val] else 0)⟩

/-- The padded read always has exactly the requested size. -/
theorem size_extractPadded (b : Bytes) (start len : Nat) :
    (extractPadded b start len).size = len := by
  simp only [extractPadded, ByteArray.size, Array.size_ofFn]

/-- Every result byte is the source byte at the offset, or zero outside the source. -/
theorem getElem_extractPadded (b : Bytes) (start len i : Nat) (hi : i < len) :
    (extractPadded b start len)[i]'(by rw [size_extractPadded]; exact hi) =
      if h : start + i < b.size then b[start + i] else 0 := by
  simp [extractPadded, ByteArray.getElem_eq_getElem_data]

/-- The list model enumerates only result indices, using zero for unavailable source bytes. -/
theorem toList_extractPadded (b : Bytes) (start len : Nat) :
    toList (extractPadded b start len) =
      List.ofFn (fun i : Fin len => ((toList b)[start + i.val]?).getD 0) := by
  apply List.ext_getElem
  · simp [length_toList, size_extractPadded]
  · intro i hi hj
    simp only [toList, extractPadded, Array.getElem_toList, Array.getElem_ofFn,
      List.getElem_ofFn]
    split
    · next h =>
      have hd : start + i < b.data.size := h
      simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hd,
        Option.getD_some, ByteArray.getElem_eq_getElem_data]
    · next h =>
      have hd : b.data.size ≤ start + i := Nat.not_lt.mp h
      simp only [Array.getElem?_toList, Array.getElem?_eq_none hd, Option.getD_none]

/-- A zero-length padded read is empty for every offset. -/
theorem extractPadded_zero (b : Bytes) (start : Nat) : extractPadded b start 0 = ByteArray.empty := by
  apply ByteArray.size_eq_zero_iff.mp
  rw [size_extractPadded]

/-- A wholly out-of-bounds read observes exactly a requested-length list of zeros. -/
theorem toList_extractPadded_of_size_le (b : Bytes) (start len : Nat) (h : b.size ≤ start) :
    toList (extractPadded b start len) = List.replicate len 0 := by
  apply List.ext_getElem
  · simp [length_toList, size_extractPadded]
  · intro i hi hj
    simp only [toList, extractPadded, Array.getElem_toList, Array.getElem_ofFn]
    rw [dite_eq_right (by omega), List.getElem_replicate]

/-- Left padding's byte observation: missing prefix zeros, then the original input. -/
theorem getElem?_toList_leftPadZero (b : Bytes) (n i : Nat) :
    (toList (leftPadZero b n))[i]? =
      if i < n - b.size then some 0 else (toList b)[i - (n - b.size)]? := by
  rw [toList_leftPadZero, List.getElem?_append]
  simp only [List.length_replicate]
  split
  · next h => simp [h]
  · rfl

/-- Right padding's byte observation: original input, then missing suffix zeros. -/
theorem getElem?_toList_rightPadZero (b : Bytes) (n i : Nat) :
    (toList (rightPadZero b n))[i]? =
      if i < b.size then (toList b)[i]? else
        if i < max b.size n then some 0 else none := by
  rw [toList_rightPadZero, List.getElem?_append, length_toList]
  split
  · rfl
  · next h =>
    rw [List.getElem?_replicate]
    have he : (i - b.size < n - b.size) = (i < max b.size n) := propext (by omega)
    simp only [he]

/-- In-bounds byte access commutes with the stable list observation. -/
theorem getElem_toList (b : Bytes) (i : Nat) (h : i < b.size) :
    (toList b)[i]'(by rw [length_toList]; exact h) = b[i] := rfl

/-- Right padding preserves every original byte and returns zero in its added suffix. -/
theorem getElem_rightPadZero (b : Bytes) (n i : Nat) (hi : i < max b.size n) :
    (rightPadZero b n)[i]'(by rw [size_rightPadZero]; exact hi) =
      if h : i < b.size then b[i] else 0 := by
  have hm := getElem?_toList_rightPadZero b n i
  have hl : i < (toList (rightPadZero b n)).length := by
    rw [length_toList, size_rightPadZero]; exact hi
  rw [List.getElem?_eq_getElem hl,
    getElem_toList _ i (by rw [size_rightPadZero]; exact hi)] at hm
  split
  · next h =>
    rw [ite_eq_left h, List.getElem?_eq_getElem (by rw [length_toList]; exact h),
      getElem_toList b i h] at hm
    exact Option.some.inj hm
  · next h =>
    rw [ite_eq_right h, ite_eq_left hi] at hm
    exact Option.some.inj hm

/-- Padded reading equals the unpadded window followed by zero padding to `len`.
`memory_read_bytes` alone is an unpadded slice and is not this operation. -/
theorem extractPadded_eq_rightPadZero_extract (b : Bytes) (start len : Nat) :
    extractPadded b start len = rightPadZero (b.extract start (start + len)) len := by
  have hs : (b.extract start (start + len)).size ≤ len := by
    rw [ByteArray.size_extract]; omega
  apply ByteArray.ext_getElem
  · rw [size_extractPadded, size_rightPadZero, Nat.max_eq_right hs]
  · intro i hi hj
    have hil : i < len := by rw [size_extractPadded] at hi; exact hi
    rw [getElem_extractPadded b start len i hil,
      getElem_rightPadZero _ len i (by rw [Nat.max_eq_right hs]; exact hil)]
    by_cases hb : start + i < b.size
    · have he : i < (b.extract start (start + len)).size := by
        rw [ByteArray.size_extract]; omega
      rw [dite_eq_left hb, dite_eq_left he, ByteArray.getElem_extract]
    · have he : ¬ i < (b.extract start (start + len)).size := by
        rw [ByteArray.size_extract]; omega
      rw [dite_eq_right hb, dite_eq_right he]

/-- The source-style list equation: take the available window, then append missing zeros. -/
theorem toList_extractPadded_window (b : Bytes) (start len : Nat) :
    toList (extractPadded b start len) =
      ((toList b).drop start).take len ++
        List.replicate (len - min len (b.size - start)) 0 := by
  rw [extractPadded_eq_rightPadZero_extract, toList_rightPadZero]
  simp only [toList, ByteArray.data_extract, Array.toList_extract,
    List.extract_eq_take_drop, Nat.add_sub_cancel_left, ByteArray.size_extract]
  congr 2
  omega

/-- Extending the source with trailing zeros does not change any read confined to
that extended size: the explicit zeros agree with zero extension. -/
theorem extractPadded_rightPadZero (b : Bytes) (n start len : Nat)
    (h : start + len ≤ max b.size n) :
    extractPadded (rightPadZero b n) start len = extractPadded b start len := by
  apply ByteArray.ext_getElem
  · rw [size_extractPadded, size_extractPadded]
  · intro i hi hj
    have hil : i < len := by rw [size_extractPadded] at hi; exact hi
    have hb : start + i < max b.size n := by omega
    rw [getElem_extractPadded _ start len i hil,
      getElem_extractPadded _ start len i hil]
    have hp : start + i < (rightPadZero b n).size := by rw [size_rightPadZero]; exact hb
    rw [dite_eq_left hp, getElem_rightPadZero b n (start + i) hb]

end Bytes
end STFSpec.Base
