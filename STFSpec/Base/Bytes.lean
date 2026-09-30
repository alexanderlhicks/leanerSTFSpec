/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import Init.Data.ByteArray.Lemmas
import Init.Data.List.OfFn
import Init.Data.List.Range
import Init.Omega

/-!
# Byte sequences, zero padding and bounded padded reads

Library `EthBase`. Padding follows pinned EELS `src/ethereum/utils/byte.py:18,40`.
The public padded-read helper models `src/ethereum/forks/amsterdam/vm/memory.py:63`.
It copies only available bytes and builds packed zeros for the missing suffix;
a large offset is never traversed or narrowed.
Spec guidance: `STFSpec/informal/modules/EthBase.md`.
-/

namespace STFSpec.Base

universe u v

/-- Variable-length immutable byte values; `ethereum_types/bytes.py:165` (locked 0.4.1).
The packed storage is private; callers use the byte-list model and its laws. -/
structure Bytes where
  private ofByteArrayRaw ::
  private raw : ByteArray

namespace Bytes

/-- Explicit construction from a packed byte array, retaining every byte. -/
def ofByteArray (b : ByteArray) : Bytes := ofByteArrayRaw b

/-- Explicit packed export for consumers whose byte API uses `ByteArray`.
This observes the existing packed buffer without allocating a list or copying bytes. -/
def toByteArray (b : Bytes) : ByteArray := b.raw

/-- Construct a byte sequence from its stable list model. -/
def ofList (xs : List UInt8) : Bytes := ofByteArray xs.toByteArray

/-- Empty byte sequence. -/
def empty : Bytes := ofByteArray ByteArray.empty

/-- Number of bytes in the sequence. -/
def size (b : Bytes) : Nat := b.raw.size

/-- Stable list observation of a byte sequence. -/
def toList (b : Bytes) : List UInt8 := b.raw.data.toList

/-- Fold bytes from left to right through the packed buffer, without allocating a list. -/
def foldl {α : Type u} (f : α → UInt8 → α) (init : α) (b : Bytes) : α :=
  b.raw.foldl f init

/-- Append one byte to the packed sequence. -/
def push (b : Bytes) (value : UInt8) : Bytes := ofByteArray (b.raw.push value)

/-- Append two byte sequences, retaining their order. -/
def append (a b : Bytes) : Bytes :=
  if a.size = 0 then b else if b.size = 0 then a else ofByteArray (a.raw ++ b.raw)

/-- Concatenation uses packed byte append. -/
instance : Append Bytes where append := append

/-- Unpadded slice from `start` inclusive to `stop` exclusive.
Checks and clips natural offsets before the packed runtime primitive, so huge
unavailable offsets never reach a machine-index conversion. -/
def extract (b : Bytes) (start stop : Nat) : Bytes :=
  if start < b.size ∧ start < stop then
    ofByteArray (b.raw.extract start (min stop b.size))
  else empty

/-- Bounds-checked byte access through the stable sequence API. -/
instance : GetElem Bytes Nat UInt8 (fun b i ↦ i < b.size) where
  getElem b i h := b.raw[i]'h

/-- Explicit packed construction preserves the input size. -/
theorem size_ofByteArray (b : ByteArray) : (ofByteArray b).size = b.size := rfl

/-- Explicit packed construction preserves the input byte-list observation. -/
theorem toList_ofByteArray (b : ByteArray) : (ofByteArray b).toList = b.data.toList := rfl

/-- Packed export has the same stable byte-list observation. -/
theorem toList_toByteArray (b : Bytes) : b.toByteArray.data.toList = b.toList := rfl

/-- Packed export preserves the exact byte count. -/
theorem size_toByteArray (b : Bytes) : b.toByteArray.size = b.size := rfl

/-- Export followed by explicit packed construction retains the sequence. -/
theorem ofByteArray_toByteArray (b : Bytes) : ofByteArray b.toByteArray = b := by
  cases b
  rfl

/-- Explicit packed construction followed by export retains the packed input. -/
theorem toByteArray_ofByteArray (b : ByteArray) : (ofByteArray b).toByteArray = b := rfl

/-- The list observation has exactly the byte sequence's size. -/
theorem length_toList (b : Bytes) : (toList b).length = b.size := by
  simp only [toList, Array.length_toList, size, ByteArray.size]

/-- Byte sequences are equal whenever their stable observations agree. -/
theorem ext {a b : Bytes} (h : toList a = toList b) : a = b := by
  cases a
  cases b
  congr 1
  apply ByteArray.ext
  exact Array.toList_inj.mp h

/-- The stable observation is injective. -/
theorem toList_inj {a b : Bytes} : toList a = toList b ↔ a = b :=
  ⟨ext, fun h ↦ congrArg toList h⟩

/-- Equality compares packed storage and agrees with the injective byte-list model. -/
instance : DecidableEq Bytes := fun a b ↦
  decidable_of_iff (a.raw = b.raw) (by
    constructor
    · intro h
      cases a
      cases b
      cases h
      rfl
    · exact congrArg raw)

/-- Observing construction from a list returns that list. -/
theorem toList_ofList (xs : List UInt8) : toList (ofList xs) = xs := by
  simp [ofList, ofByteArray, toList]

/-- Rebuilding from the stable list observation preserves the byte sequence. -/
theorem ofList_toList (b : Bytes) : ofList (toList b) = b := by
  apply ext
  rw [toList_ofList]

/-- List construction has the list's exact length. -/
theorem size_ofList (xs : List UInt8) : (ofList xs).size = xs.length := by
  rw [← length_toList, toList_ofList]

/-- Empty construction has no bytes. -/
theorem toList_empty : empty.toList = [] := rfl

/-- Empty construction has size zero. -/
theorem size_empty : empty.size = 0 := rfl

/-- Size zero is exactly the empty byte sequence. -/
theorem size_eq_zero_iff {b : Bytes} : b.size = 0 ↔ b = empty := by
  constructor
  · intro h
    apply ext
    rw [toList_empty, ← List.length_eq_zero_iff, length_toList, h]
  · intro h
    rw [h, size_empty]

/-- Packed push appends one byte in the list model. -/
theorem toList_push (b : Bytes) (value : UInt8) :
    (push b value).toList = b.toList ++ [value] := by
  simp [push, ofByteArray, toList, ByteArray.data_push]

/-- Packed push increases length by one. -/
theorem size_push (b : Bytes) (value : UInt8) : (push b value).size = b.size + 1 := by
  simp [push, ofByteArray, size]

/-- Packed append concatenates list models. -/
theorem toList_append (a b : Bytes) : (a ++ b).toList = a.toList ++ b.toList := by
  change (append a b).toList = _
  unfold append
  split
  · next h =>
    have ha : a.toList = [] := List.length_eq_zero_iff.mp (by rw [length_toList, h])
    rw [ha, List.nil_append]
  · split
    · next h =>
      have hb : b.toList = [] := List.length_eq_zero_iff.mp (by rw [length_toList, h])
      rw [hb, List.append_nil]
    · change (a.raw ++ b.raw).data.toList = _
      rw [ByteArray.toList_data_append]
      rfl

/-- Packed append adds sizes. -/
theorem size_append (a b : Bytes) : (a ++ b).size = a.size + b.size := by
  rw [← length_toList, toList_append, List.length_append, length_toList, length_toList]

/-- Unpadded slicing takes the available list window. -/
theorem toList_extract (b : Bytes) (start stop : Nat) :
    (extract b start stop).toList = (b.toList.drop start).take (stop - start) := by
  unfold extract
  split
  · rw [toList_ofByteArray, ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop]
    change (b.toList.drop start).take (min stop b.size - start) = _
    by_cases h : stop ≤ b.size
    · rw [Nat.min_eq_left h]
    · have hl : (b.toList.drop start).length = b.size - start := by
        rw [List.length_drop, length_toList]
      rw [Nat.min_eq_right (by omega), ← hl, List.take_length,
        List.take_of_length_le (by rw [hl]; omega)]
  · next h =>
    rw [toList_empty]
    by_cases hs : start < b.size
    · rw [Nat.sub_eq_zero_of_le (by omega), List.take_zero]
    · rw [List.drop_of_length_le (by rw [length_toList]; omega), List.take_nil]

/-- Unpadded slicing clips the end to the available bytes. -/
theorem size_extract (b : Bytes) (start stop : Nat) :
    (extract b start stop).size = min stop b.size - start := by
  rw [← length_toList, toList_extract, List.length_take, List.length_drop, length_toList]
  omega

/-- In-bounds byte access commutes with the stable list observation. -/
theorem getElem_toList (b : Bytes) (i : Nat) (h : i < b.size) :
    (toList b)[i]'(by rw [length_toList]; exact h) = b[i] := rfl

private theorem byteFold_model {β : Type u} {m : Type u → Type v} [Monad m]
    (f : β → UInt8 → m β) (xs : ByteArray) (init : β)
    (i j : Nat) (h : i + j = xs.size) :
    ByteArray.foldlM.loop f xs xs.size (Nat.le_refl _) i j init =
      (xs.data.toList.drop j).foldlM f init := by
  induction i generalizing j init with
  | zero =>
    have hj : xs.size = j := by omega
    simp [ByteArray.foldlM.loop, hj, List.drop_of_length_le]
  | succ i ih =>
    have hj : j < xs.size := by omega
    rw [ByteArray.foldlM.loop]
    simp only [dite_eq_left hj]
    simp only [ih _ (j + 1) (by omega)]
    rw (occs := [2]) [← List.getElem_cons_drop (by simpa using hj)]
    simp [ByteArray.getElem_eq_getElem_data]


/-- The packed fold agrees with the stable list-model fold. -/
theorem foldl_eq {α : Type u} (f : α → UInt8 → α) (init : α) (b : Bytes) :
    b.foldl f init = b.toList.foldl f init := by
  simp only [foldl, ByteArray.foldl, ByteArray.foldlM, dite_eq_left (Nat.le_refl _),
    Nat.sub_zero]
  rw [byteFold_model _ _ _ _ _ (Nat.add_zero _)]
  simp [toList]

-- The tail-recursive loop owns a single packed buffer. Its model is a list window.
private def generateAux (f : Nat → UInt8) : Nat → Nat → ByteArray → ByteArray
  | 0, _, acc => acc
  | remaining + 1, index, acc => generateAux f remaining (index + 1) (acc.push (f index))

private theorem generateAux_model (f : Nat → UInt8) (remaining index : Nat) (acc : ByteArray) :
    (generateAux f remaining index acc).data.toList =
      acc.data.toList ++ (List.range' index remaining).map f := by
  induction remaining generalizing index acc with
  | zero => simp [generateAux]
  | succ remaining ih =>
    simp [generateAux, ih, List.range'_succ, ByteArray.data_push, List.append_assoc]

/-- Build exactly `n` bytes by visiting indices `0` through `n-1` in a packed buffer.
The function is evaluated only at result indices; no boxed array is allocated. -/
def generate (n : Nat) (f : Nat → UInt8) : Bytes :=
  ofByteArray (generateAux f n 0 (ByteArray.emptyWithCapacity n))

/-- The packed generator equals the legible list-range model. -/
theorem toList_generate (n : Nat) (f : Nat → UInt8) :
    (generate n f).toList = (List.range n).map f := by
  rw [generate, toList_ofByteArray, generateAux_model]
  change [] ++ (List.range' 0 n).map f = _
  rw [List.nil_append, ← List.range_eq_range']

/-- Packed generation always produces its requested byte count. -/
theorem size_generate (n : Nat) (f : Nat → UInt8) : (generate n f).size = n := by
  rw [← length_toList, toList_generate, List.length_map, List.length_range]

/-- Each generated byte is the function's value at that index. -/
theorem getElem_generate (n : Nat) (f : Nat → UInt8) (i : Nat) (hi : i < n) :
    (generate n f)[i]'(by rw [size_generate]; exact hi) = f i := by
  rw [← getElem_toList]
  simp only [toList_generate, List.getElem_map, List.getElem_range]

-- Doubling packed halves avoids a callback or Nat loop for each zero byte.
private def zeros (n : Nat) : Bytes :=
  if _h : n = 0 then empty else
    let half := zeros (n / 2)
    let doubled := half ++ half
    if n % 2 = 0 then doubled else doubled.push 0
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

private theorem toList_zeros (n : Nat) : toList (zeros n) = List.replicate n 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [zeros]
    split
    · next h => simp [h, toList_empty]
    · next h =>
      have hh : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
      have hi := ih (n / 2) hh
      have he := Nat.div_add_mod n 2
      have hm : n % 2 < 2 := Nat.mod_lt _ (by decide)
      split
      · next hr =>
        rw [toList_append, hi, List.replicate_append_replicate]
        congr 1
        omega
      · next hr =>
        rw [toList_push, toList_append, hi, List.replicate_append_replicate]
        change List.replicate (n / 2 + n / 2) (0 : UInt8) ++ List.replicate 1 0 = _
        rw [List.replicate_append_replicate]
        congr 1
        omega

private theorem size_zeros (n : Nat) : (zeros n).size = n := by
  rw [← length_toList, toList_zeros, List.length_replicate]

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
  · rw [toList_append, toList_zeros]

/-- Right padding appends exactly the missing zero bytes. -/
theorem toList_rightPadZero (b : Bytes) (n : Nat) :
    toList (rightPadZero b n) = toList b ++ List.replicate (n - b.size) 0 := by
  unfold rightPadZero
  split
  · next h => simp [Nat.sub_eq_zero_of_le h]
  · rw [toList_append, toList_zeros]

/-- Left padding produces the greater of the original and requested sizes. -/
theorem size_leftPadZero (b : Bytes) (n : Nat) : (leftPadZero b n).size = max b.size n := by
  unfold leftPadZero
  split
  · next h => simp [Nat.max_eq_left h]
  · next h => rw [size_append, size_zeros]; omega

/-- Right padding produces the greater of the original and requested sizes. -/
theorem size_rightPadZero (b : Bytes) (n : Nat) : (rightPadZero b n).size = max b.size n := by
  unfold rightPadZero
  split
  · next h => simp [Nat.max_eq_left h]
  · next h => rw [size_append, size_zeros]; omega

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

private theorem extract_clamp (b : Bytes) (start len : Nat) :
    b.extract start (start + min len (b.size - start)) = b.extract start (start + len) := by
  apply ext
  simp only [toList_extract, Nat.add_sub_cancel_left]
  by_cases h : len ≤ b.size - start
  · rw [Nat.min_eq_left h]
  · have hl : (b.toList.drop start).length = b.size - start := by
      rw [List.length_drop, length_toList]
    rw [Nat.min_eq_right (by omega), ← hl, List.take_length,
      List.take_of_length_le (by rw [hl]; omega)]

/-- Zero-extended read, the Base model to which `EthVmCore.bufferRead` reduces;
corresponds to EELS
`src/ethereum/forks/amsterdam/vm/memory.py:63,82–83`. Bounds are checked in `Nat`
before slicing, and the copied window ends within the source. Missing bytes are
filled by packed zero-buffer doubling; huge unavailable offsets are never narrowed. -/
def extractPadded (b : Bytes) (start len : Nat) : Bytes :=
  if start < b.size then
    rightPadZero (b.extract start (start + min len (b.size - start))) len
  else zeros len

/-- Packed padded reading equals the legible unpadded-window-plus-padding model.
`memory_read_bytes` alone is an unpadded slice and is not this operation. -/
theorem extractPadded_eq_rightPadZero_extract (b : Bytes) (start len : Nat) :
    extractPadded b start len = rightPadZero (b.extract start (start + len)) len := by
  unfold extractPadded
  split
  · rw [extract_clamp]
  · next h =>
    have he : b.extract start (start + len) = empty := by
      apply ext
      rw [toList_extract, List.drop_of_length_le (by rw [length_toList]; omega)]
      simp only [List.take_nil, toList_empty]
    rw [he]
    apply ext
    rw [toList_zeros, toList_rightPadZero, toList_empty, size_empty]
    simp

/-- The padded read always has exactly the requested size. -/
theorem size_extractPadded (b : Bytes) (start len : Nat) :
    (extractPadded b start len).size = len := by
  rw [extractPadded_eq_rightPadZero_extract, size_rightPadZero]
  apply Nat.max_eq_right
  rw [size_extract]
  omega

/-- Every result byte is the source byte at the offset, or zero outside the source. -/
theorem getElem_extractPadded (b : Bytes) (start len i : Nat) (hi : i < len) :
    (extractPadded b start len)[i]'(by rw [size_extractPadded]; exact hi) =
      if h : start + i < b.size then b[start + i] else 0 := by
  have hs : (b.extract start (start + len)).size ≤ len := by rw [size_extract]; omega
  simp only [extractPadded_eq_rightPadZero_extract]
  rw [getElem_rightPadZero _ len i (by rw [Nat.max_eq_right hs]; exact hi)]
  by_cases hb : start + i < b.size
  · have he : i < (b.extract start (start + len)).size := by rw [size_extract]; omega
    rw [dite_eq_left hb, dite_eq_left he, ← getElem_toList _ _ he]
    simp only [toList_extract, List.getElem_take, List.getElem_drop]
    exact getElem_toList b (start + i) hb
  · have he : ¬ i < (b.extract start (start + len)).size := by rw [size_extract]; omega
    rw [dite_eq_right hb, dite_eq_right he]

/-- The list model enumerates only result indices, using zero for unavailable source bytes. -/
theorem toList_extractPadded (b : Bytes) (start len : Nat) :
    toList (extractPadded b start len) =
      List.ofFn (fun i : Fin len ↦ ((toList b)[start + i.val]?).getD 0) := by
  apply List.ext_getElem
  · simp [length_toList, size_extractPadded]
  · intro i hi hj
    have hil : i < len := by rw [length_toList, size_extractPadded] at hi; exact hi
    rw [getElem_toList _ i (by rw [size_extractPadded]; exact hil),
      getElem_extractPadded b start len i hil,
      List.getElem_ofFn]
    split
    · next h =>
      rw [List.getElem?_eq_getElem (by rw [length_toList]; exact h), Option.getD_some,
        getElem_toList]
    · next h =>
      change 0 = ((toList b)[start + i]?).getD 0
      rw [List.getElem?_eq_none (by rw [length_toList]; exact Nat.not_lt.mp h),
        Option.getD_none]

/-- A zero-length padded read is empty for every offset. -/
theorem extractPadded_zero (b : Bytes) (start : Nat) : extractPadded b start 0 = empty := by
  apply size_eq_zero_iff.mp
  rw [size_extractPadded]

/-- A wholly out-of-bounds read observes exactly a requested-length list of zeros. -/
theorem toList_extractPadded_of_size_le (b : Bytes) (start len : Nat) (h : b.size ≤ start) :
    toList (extractPadded b start len) = List.replicate len 0 := by
  apply List.ext_getElem
  · simp [length_toList, size_extractPadded]
  · intro i hi hj
    have hil : i < len := by rw [length_toList, size_extractPadded] at hi; exact hi
    rw [getElem_toList _ i (by rw [size_extractPadded]; exact hil),
      getElem_extractPadded b start len i hil,
      dite_eq_right (by omega), List.getElem_replicate]

/-- Left padding's byte observation: missing prefix zeros, then the original input. -/
theorem getElem?_toList_leftPadZero (b : Bytes) (n i : Nat) :
    (toList (leftPadZero b n))[i]? =
      if i < n - b.size then some 0 else (toList b)[i - (n - b.size)]? := by
  rw [toList_leftPadZero, List.getElem?_append]
  simp only [List.length_replicate]
  split
  · next h => simp [h]
  · rfl

/-- The source-style list equation: take the available window, then append missing zeros. -/
theorem toList_extractPadded_window (b : Bytes) (start len : Nat) :
    toList (extractPadded b start len) =
      ((toList b).drop start).take len ++
        List.replicate (len - min len (b.size - start)) 0 := by
  rw [extractPadded_eq_rightPadZero_extract, toList_rightPadZero]
  simp only [toList_extract, Nat.add_sub_cancel_left, size_extract]
  congr 2
  omega

/-- Extending the source with trailing zeros does not change any read confined to
that extended size: the explicit zeros agree with zero extension. -/
theorem extractPadded_rightPadZero (b : Bytes) (n start len : Nat)
    (h : start + len ≤ max b.size n) :
    extractPadded (rightPadZero b n) start len = extractPadded b start len := by
  apply ext
  apply List.ext_getElem
  · rw [length_toList, length_toList, size_extractPadded, size_extractPadded]
  · intro i hi hj
    have hil : i < len := by rw [length_toList, size_extractPadded] at hi; exact hi
    have hb : start + i < max b.size n := by omega
    rw [getElem_toList _ i (by rw [size_extractPadded]; exact hil),
      getElem_toList _ i (by rw [size_extractPadded]; exact hil),
      getElem_extractPadded _ start len i hil,
      getElem_extractPadded _ start len i hil]
    have hp : start + i < (rightPadZero b n).size := by rw [size_rightPadZero]; exact hb
    rw [dite_eq_left hp, getElem_rightPadZero b n (start + i) hb]

end Bytes
end STFSpec.Base
