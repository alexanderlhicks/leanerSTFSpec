/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.Bytes
import STFSpec.Base.U256

/-!
# Aligned memory and zero-padded immutable buffer reads

Library `EthVmCore`. This standalone adapter uses the public Base padded-window
provider. Memory has private aligned packed storage and locally admitted windows.
Exact natural offsets are checked by that provider before packed index conversion.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Vm.Core
open STFSpec.Base

/-- Read exactly `size` bytes, padding unavailable bytes with zeros.
EELS `src/ethereum/forks/amsterdam/vm/memory.py:63,82–83` casts both operands to
unbounded Uint before endpoint addition. No gas, Memory or host-width premise is
part of this total mathematical operation. -/
def bufferRead (b : Bytes) (start size : U256) : Bytes :=
  Bytes.extractPadded b start.toNat size.toNat

/-- Buffer reading is the existing public Base padded-window operation. -/
theorem bufferRead_eq_extractPadded (b : Bytes) (start size : U256) :
    bufferRead b start size = Bytes.extractPadded b start.toNat size.toNat := rfl

/-- The complete result model contains the available window followed by missing zeros. -/
theorem bufferRead_toList (b : Bytes) (start size : U256) :
    (bufferRead b start size).toList =
      (b.toList.drop start.toNat).take size.toNat ++
        List.replicate (size.toNat - min size.toNat (b.size - start.toNat)) 0 := by
  exact Bytes.toList_extractPadded_window b start.toNat size.toNat

/-- Every padded read has exactly the requested natural byte length. -/
theorem bufferRead_size (b : Bytes) (start size : U256) :
    (bufferRead b start size).size = size.toNat := by
  exact Bytes.size_extractPadded b start.toNat size.toNat

private def fillZero : Nat → ByteArray → ByteArray
  | 0, b => b
  | n + 1, b => fillZero n (b.push 0)

private theorem fillZero_model (n : Nat) (b : ByteArray) :
    (fillZero n b).data.toList = b.data.toList ++ List.replicate n 0 := by
  induction n generalizing b with
  | zero => simp [fillZero]
  | succ n ih =>
    rw [fillZero, ih]
    simp [ByteArray.push, List.replicate_succ, List.append_assoc]

private theorem fillZero_size (n : Nat) (b : ByteArray) :
    (fillZero n b).size = b.size + n := by
  have h := congrArg List.length (fillZero_model n b)
  simpa using h

/-- Aligned memory with private packed storage and private constructor. -/
structure Memory where
  private mk ::
  private raw : ByteArray
  private aligned : raw.size % 32 = 0

namespace Memory

/-- The only public Memory construction seam. -/
def empty : Memory := ⟨ByteArray.empty, by decide⟩
/-- Complete byte-list model. -/
def toBytes (m : Memory) : List UInt8 := m.raw.data.toList
/-- Exact byte count. -/
def size (m : Memory) : Nat := m.raw.size

/-- Append exactly n zero bytes, requiring only local structural alignment.
The source caller statement is
`src/ethereum/forks/amsterdam/vm/instructions/memory.py:54,85,113,174`;
this is not a named EELS primitive or the caller pricing operation. -/
def expand (m : Memory) (n : Nat) (h : n % 32 = 0) : Memory :=
  ⟨fillZero n m.raw, by
    rw [fillZero_size, Nat.add_mod, m.aligned, h]⟩

/-- Exact immutable admitted window; empty is handled before offset arithmetic.
EELS `src/ethereum/forks/amsterdam/vm/memory.py:39–60`. -/
def readBytes (m : Memory) (s k : Nat)
    (_h : k = 0 ∨ s + k ≤ m.size) : Bytes :=
  if k = 0 then Bytes.empty else Bytes.ofByteArray (m.raw.extract s (s + k))

private def overwrite (b : ByteArray) (s : Nat) (v : Bytes) : ByteArray :=
  v.toByteArray.copySlice 0 b s v.size false

private theorem overwrite_model (b : ByteArray) (s : Nat) (v : Bytes) :
    (overwrite b s v).data.toList =
      b.data.toList.take s ++ v.toList ++ b.data.toList.drop (s + v.size) := by
  simp [overwrite, ByteArray.copySlice, Bytes.toList_toByteArray]
  rw [Bytes.size_toByteArray, Nat.min_self, ← Bytes.length_toList v, List.take_length]
  congr 1
  exact List.take_of_length_le (by simp)

private theorem overwrite_size (b : ByteArray) (s : Nat) (v : Bytes)
    (h : s + v.size ≤ b.size) : (overwrite b s v).size = b.size := by
  have hm := congrArg List.length (overwrite_model b s v)
  simp only [List.length_append, List.length_take, List.length_drop,
    Bytes.length_toList, Array.length_toList, ByteArray.size_data] at hm
  omega

/-- Exact admitted overwrite, with actual identity for empty values at every offset.
EELS `src/ethereum/forks/amsterdam/vm/memory.py:20–36`. -/
def write (m : Memory) (s : Nat) (v : Bytes)
    (h : v.size = 0 ∨ s + v.size ≤ m.size) : Memory :=
  if hz : v.size = 0 then m else
    ⟨overwrite m.raw s v, by
      rw [overwrite_size m.raw s v (h.resolve_left hz)]
      exact m.aligned⟩

/-- M1: initial empty model. -/
theorem toBytes_empty : toBytes empty = [] := rfl

/-- M2: exact model length. -/
theorem length_toBytes (m : Memory) : m.toBytes.length = m.size := rfl

/-- M3: structural alignment. -/
theorem size_mod32 (m : Memory) : m.size % 32 = 0 := m.aligned

/-- M4: full expansion model. -/
theorem toBytes_expand (m : Memory) (n : Nat) (h : n % 32 = 0) :
    (m.expand n h).toBytes = m.toBytes ++ List.replicate n 0 :=
  fillZero_model n m.raw

/-- M5: full admitted read model, including every empty offset. -/
theorem readBytes_toList (m : Memory) (s k : Nat)
    (h : k = 0 ∨ s + k ≤ m.size) :
    (m.readBytes s k h).toList = (m.toBytes.drop s).take k := by
  by_cases hz : k = 0
  · simp [readBytes, hz, Bytes.toList_empty]
  · simp [readBytes, hz, Bytes.toList_ofByteArray, toBytes, List.take_drop]

/-- M6: full write model, including all untouched bytes. -/
theorem toBytes_write (m : Memory) (s : Nat) (v : Bytes)
    (h : v.size = 0 ∨ s + v.size ≤ m.size) :
    (m.write s v h).toBytes =
      m.toBytes.take s ++ v.toList ++ m.toBytes.drop (s + v.size) := by
  by_cases hz : v.size = 0
  · have hv : v.toList = [] := List.eq_nil_iff_length_eq_zero.mpr
      (by rw [Bytes.length_toList, hz])
    simp [write, hz, hv]
  · simpa [write, hz, toBytes] using overwrite_model m.raw s v

/-- M7: actual empty write identity at every natural offset. -/
theorem write_empty (m : Memory) (s : Nat) :
    m.write s Bytes.empty (Or.inl Bytes.size_empty) = m := by
  simp [write, Bytes.size_empty]

/-- M8: exact write size preservation. -/
theorem size_write (m : Memory) (s : Nat) (v : Bytes)
    (h : v.size = 0 ∨ s + v.size ≤ m.size) : (m.write s v h).size = m.size := by
  by_cases hz : v.size = 0
  · simp [write, hz]
  · simpa [write, hz, size] using overwrite_size m.raw s v (h.resolve_left hz)

private theorem read_overwrite_same (xs ys : List UInt8) (s : Nat)
    (h : s + ys.length ≤ xs.length) :
    ((xs.take s ++ ys ++ xs.drop (s + ys.length)).drop s).take ys.length = ys := by
  have hs : s ≤ xs.length := by omega
  simp [List.length_take, Nat.min_eq_left hs]

private theorem read_overwrite_before (xs ys : List UInt8) (s t k : Nat)
    (h : s + ys.length ≤ xs.length) (hd : t + k ≤ s) :
    ((xs.take s ++ ys ++ xs.drop (s + ys.length)).drop t).take k =
      (xs.drop t).take k := by
  have hs : s ≤ xs.length := by omega
  have ht : t + k ≤ (xs.take s).length := by simp; omega
  rw [List.take_drop, List.take_drop]
  rw [List.append_assoc, List.take_append_of_le_length ht]
  rw [List.take_take, Nat.min_eq_left hd]

private theorem read_overwrite_after (xs ys : List UInt8) (s t k : Nat)
    (h : s + ys.length ≤ xs.length) (hd : s + ys.length ≤ t) :
    ((xs.take s ++ ys ++ xs.drop (s + ys.length)).drop t).take k =
      (xs.drop t).take k := by
  have hs : s ≤ xs.length := by omega
  have hp : (xs.take s ++ ys).length ≤ t := by simp; omega
  rw [List.drop_append, List.drop_eq_nil_of_le hp]
  simp only [List.nil_append, List.length_append, List.length_take, Nat.min_eq_left hs,
    List.drop_drop]
  congr 2
  omega

/-- M9: actual immutable Bytes equality after writing the admitted window. -/
theorem readBytes_write (m : Memory) (s : Nat) (v : Bytes)
    (h : v.size = 0 ∨ s + v.size ≤ m.size) :
    (m.write s v h).readBytes s v.size (by rw [size_write]; exact h) = v := by
  apply Bytes.ext
  rw [readBytes_toList, toBytes_write]
  by_cases hz : v.size = 0
  · have hv : v.toList = [] := List.eq_nil_iff_length_eq_zero.mpr
      (by rw [Bytes.length_toList, hz])
    simp [hz, hv]
  · have hw := h.resolve_left hz
    have hm := read_overwrite_same m.toBytes v.toList s
      (by simpa [length_toBytes, Bytes.length_toList] using hw)
    simpa [Bytes.length_toList] using hm

/-- M10: every disjoint admitted read is preserved; empty windows are explicit. -/
theorem readBytes_write_disjoint (m : Memory) (s : Nat) (v : Bytes) (t k : Nat)
    (hW : v.size = 0 ∨ s + v.size ≤ m.size)
    (hR : k = 0 ∨ t + k ≤ m.size)
    (hD : k = 0 ∨ v.size = 0 ∨ t + k ≤ s ∨ s + v.size ≤ t) :
    (m.write s v hW).readBytes t k (by rw [size_write]; exact hR) =
      m.readBytes t k hR := by
  apply Bytes.ext
  rw [readBytes_toList, readBytes_toList, toBytes_write]
  rcases hD with hk | hv | hb | ha
  · simp [hk]
  · have he : v.toList = [] := List.eq_nil_iff_length_eq_zero.mpr
      (by rw [Bytes.length_toList, hv])
    simp [hv, he]
  · by_cases hv : v.size = 0
    · have he : v.toList = [] := List.eq_nil_iff_length_eq_zero.mpr
        (by rw [Bytes.length_toList, hv])
      simp [hv, he]
    · exact read_overwrite_before m.toBytes v.toList s t k
        (by simpa [length_toBytes, Bytes.length_toList] using hW.resolve_left hv) hb
  · by_cases hv : v.size = 0
    · have he : v.toList = [] := List.eq_nil_iff_length_eq_zero.mpr
        (by rw [Bytes.length_toList, hv])
      simp [hv, he]
    · exact read_overwrite_after m.toBytes v.toList s t k
        (by simpa [length_toBytes, Bytes.length_toList] using hW.resolve_left hv)
        (by simpa [Bytes.length_toList] using ha)

end Memory
end STFSpec.Vm.Core
