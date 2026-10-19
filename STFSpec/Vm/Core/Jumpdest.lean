/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.Bytes
import Std

/-!
# Packed jump-destination analysis

Library `EthVmCore`. Static raw-byte scanning follows pinned EELS
`src/ethereum/forks/amsterdam/vm/runtime.py:22–69`. Only PUSH1–PUSH32 skip data.
The packed builder is ordinarily refined to a private finite-support List model;
consumers use the three public equations without observing the representation.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§2.7/3/5/7.
-/

namespace STFSpec.Vm.Core
open STFSpec.Base

private def bit (b : UInt8) (i : Nat) : Bool := b.toBitVec.getLsbD i

private def setBit (b : UInt8) (i : Nat) : UInt8 :=
  ⟨b.toBitVec ||| ((1 : BitVec 8) <<< i)⟩

private theorem bit_setBit (b : UInt8) (i j : Nat) (hi : i < 8) (hj : j < 8) :
    bit (setBit b i) j = (bit b j || decide (j = i)) := by
  have hone (k : Nat) : (1 : BitVec 8).getLsbD k = decide (k = 0) := by
    change Nat.testBit 1 k = decide (k = 0)
    apply Bool.eq_iff_iff.mpr
    simp only [Nat.testBit_one_eq_true_iff_self_eq_zero, decide_eq_true_eq]
  simp only [bit, setBit, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hone]
  have h : (decide (j < 8) && !decide (j < i) &&
      decide (j - i = 0)) = decide (j = i) := by
    by_cases hji : j = i <;> simp_all <;> omega
  rw [h]

private def raw (a : ByteArray) (i : Nat) : Bool :=
  if h : i / 8 < a.size then bit a[i / 8] (i % 8) else false

private def mark (a : ByteArray) (i : Nat) : ByteArray :=
  if h : i / 8 < a.size then a.set (i / 8) (setBit a[i / 8] (i % 8)) else a

private theorem size_mark (a : ByteArray) (i : Nat) : (mark a i).size = a.size := by
  simp only [mark]
  split <;> simp only [ByteArray.size, ByteArray.set, Array.size_set]

private theorem raw_mark (a : ByteArray) (i j : Nat) (hi : i / 8 < a.size) :
    raw (mark a i) j = (raw a j || decide (j = i)) := by
  simp only [mark, dite_eq_left hi, raw]
  by_cases hj : j / 8 < a.size
  · have hs : (a.set (i / 8) (setBit a[i / 8] (i % 8))).size = a.size := by
      simp only [ByteArray.size, ByteArray.set, Array.size_set]
    simp only [hs, dite_eq_left hj]
    by_cases he : j / 8 = i / 8
    · have hb : j % 8 < 8 := Nat.mod_lt _ (by decide)
      have hc : i % 8 < 8 := Nat.mod_lt _ (by decide)
      have hEq : (j % 8 = i % 8) ↔ j = i := by omega
      simp only [ByteArray.getElem_eq_getElem_data, ByteArray.data_set,
        Array.getElem_set]
      simp only [he, ↓reduceIte]
      rw [bit_setBit _ _ _ hc hb]
      simp [hEq]
    · have hne : j ≠ i := by omega
      simp [ByteArray.getElem_eq_getElem_data, ByteArray.data_set,
        Array.getElem_set, Ne.symm he, hne]
  · have hs : (a.set (i / 8) (setBit a[i / 8] (i % 8))).size = a.size := by
      simp only [ByteArray.size, ByteArray.set, Array.size_set]
    have hne : j ≠ i := by omega
    simp [hs, hj, hne]

private def width (b : UInt8) : Nat :=
  if 96 ≤ b.toNat ∧ b.toNat ≤ 127 then b.toNat - 95 else 0

private def reference : List UInt8 → Nat → Nat → Bool
  | [], _, _ => false
  | b :: _, 0, 0 => b == 91
  | _ :: _, _ + 1, 0 => false
  | b :: xs, 0, i + 1 => reference xs (width b) i
  | _ :: xs, k + 1, i + 1 => reference xs k i

private theorem reference_pending (xs : List UInt8) (k i : Nat) :
    reference xs k i = if i < k then false else reference (xs.drop k) 0 (i-k) := by
  induction k generalizing xs i with
  | zero => simp
  | succ k ih =>
    cases xs with
    | nil => simp [reference]
    | cons b xs =>
      cases i with
      | zero => simp [reference]
      | succ i =>
        simp only [reference, List.drop_succ_cons]
        rw [ih]
        have h : (i + 1 < k + 1) ↔ i < k := by omega
        simp only [h, Nat.add_sub_add_right]

private theorem reference_cons (b : UInt8) (xs : List UInt8) (i : Nat) :
    reference (b::xs) 0 i =
      if i = 0 then b == 91 else if i ≤ width b then false
      else reference (xs.drop (width b)) 0 (i-(width b+1)) := by
  cases i with
  | zero => simp [reference]
  | succ i =>
    simp only [reference, Nat.succ_ne_zero, ↓reduceIte]
    rw [reference_pending]
    have h : (i + 1 ≤ width b) ↔ i < width b := by omega
    simp only [h]
    split <;> simp_all <;> congr 1 <;> omega

private theorem reference_ge (xs : List UInt8) (k i : Nat) (h : xs.length ≤ i) :
    reference xs k i = false := by
  induction xs generalizing k i with
  | nil => rfl
  | cons b xs ih =>
    cases i with
    | zero => simp at h
    | succ i =>
      have ht : xs.length ≤ i := by simp only [List.length_cons] at h; omega
      cases k <;> simp only [reference] <;> apply ih _ _ ht

private def zeros (n : Nat) : ByteArray :=
  (Bytes.generate n (fun _ ↦ 0)).toByteArray

private theorem zeros_data (n : Nat) : (zeros n).data = Array.replicate n 0 := by
  apply Array.toList_inj.mp
  rw [zeros, Bytes.toList_toByteArray, Bytes.toList_generate, Array.toList_replicate]
  rw [List.map_const', List.length_range]

private theorem zeros_size (n : Nat) : (zeros n).size = n := by
  change (zeros n).data.size = n
  rw [zeros_data, Array.size_replicate]

private theorem raw_zeros (n i : Nat) : raw (zeros n) i = false := by
  unfold raw
  split
  · simp only [ByteArray.getElem_eq_getElem_data, zeros_data, Array.getElem_replicate]
    simp [bit, BitVec.getLsbD]
  · rfl

private def atRef (xs : List UInt8) (pc i : Nat) : Bool :=
  if i < pc then false else reference (xs.drop pc) 0 (i-pc)

private theorem atRef_end (xs : List UInt8) (pc i : Nat) (h : xs.length ≤ pc) :
    atRef xs pc i = false := by
  simp [atRef, List.drop_eq_nil_iff.mpr h, reference]

private theorem atRef_step (xs : List UInt8) (pc i : Nat) (h : pc < xs.length) :
    atRef xs pc i =
      if i = pc then xs[pc] == 91 else atRef xs (pc+1+width xs[pc]) i := by
  have hd := List.drop_eq_getElem_cons h
  by_cases hi : i < pc
  · have hn : i < pc+1+width xs[pc] := by omega
    have he : i ≠ pc := by omega
    simp [atRef, hi, hn, he]
  · by_cases he : i = pc
    · subst i
      simp only [atRef, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self]
      rw [hd]
      rfl
    · have hz : i-pc ≠ 0 := by omega
      have hg : (xs.drop (pc+1)).drop (width xs[pc]) = xs.drop (pc+1+width xs[pc]) := by
        rw [List.drop_drop]
      simp only [atRef, hi, ↓reduceIte, he, hd]
      rw [reference_cons]
      simp only [hz, ↓reduceIte, hg]
      have hc : (i-pc ≤ width xs[pc]) ↔ i < pc+1+width xs[pc] := by omega
      simp only [hc]
      split
      · rfl
      · congr 1 <;> omega

private theorem atRef_step_or (xs : List UInt8) (pc i : Nat) (h : pc < xs.length) :
    atRef xs pc i =
      ((decide (i = pc) && (xs[pc] == 91)) || atRef xs (pc+1+width xs[pc]) i) := by
  rw [atRef_step xs pc i h]
  by_cases he : i = pc
  · subst i
    have hn : pc < pc+1+width xs[pc] := by omega
    simp [atRef, hn]
  · simp [he]

private def scan : Nat → ByteArray → Nat → ByteArray → ByteArray
  | 0, _, _, a => a
  | fuel+1, c, pc, a =>
    if h : pc < c.size then
      let b := c[pc]
      scan fuel c (pc+1+width b) (if b == 91 then mark a pc else a)
    else a

private theorem size_scan (fuel : Nat) (c : ByteArray) (pc : Nat) (a : ByteArray) :
    (scan fuel c pc a).size = a.size := by
  induction fuel generalizing pc a with
  | zero => rfl
  | succ fuel ih =>
    simp only [scan]
    split
    · rw [ih]
      split <;> simp only [size_mark]
    · rfl

private theorem raw_update (a : ByteArray) (pc i : Nat) (b : UInt8)
    (h : pc / 8 < a.size) :
    raw (if b == 91 then mark a pc else a) i =
      (raw a i || ((b == 91) && decide (i = pc))) := by
  split <;> simp_all [raw_mark a pc i h]

private theorem scan_refines (fuel : Nat) (c : ByteArray) (pc : Nat) (a : ByteArray)
    (enough : c.size ≤ pc+fuel) (capacity : c.size ≤ 8*a.size) (i : Nat) :
    raw (scan fuel c pc a) i = (raw a i || atRef c.data.toList pc i) := by
  induction fuel generalizing pc a with
  | zero =>
    have h : c.data.toList.length ≤ pc := by simpa using enough
    simp [scan, atRef_end _ _ _ h]
  | succ fuel ih =>
    by_cases hp : pc < c.size
    · have hl : pc < c.data.toList.length := by simpa using hp
      have hm : pc/8 < a.size := by omega
      have he : c.size ≤ pc+1+width c[pc]+fuel := by omega
      have hs : (if c[pc] == 91 then mark a pc else a).size = a.size := by
        split <;> simp only [size_mark]
      simp only [scan, dite_eq_left hp]
      rw [ih _ _ he (by simpa only [hs] using capacity)]
      rw [raw_update a pc i c[pc] hm, atRef_step_or _ _ _ hl]
      simp only [Bool.or_assoc, Bool.and_comm, Array.getElem_toList,
        ByteArray.getElem_eq_getElem_data]
    · have h : c.data.toList.length ≤ pc := by
        change c.size ≤ pc
        omega
      simp [scan, hp, atRef_end _ _ _ h]

/-- Immutable jump-destination map with private packed storage and code length. -/
structure JumpdestMap where
  private mk ::
  private codeSize : Nat
  private bitmap : ByteArray

/-- Test a natural byte offset; every offset outside the original code is false.
The code bound is checked before packed lookup, including for arbitrarily large offsets. -/
def JumpdestMap.contains (m : JumpdestMap) (i : Nat) : Bool :=
  if i < m.codeSize then raw m.bitmap i else false

private def buildJumpdestMap (c : ByteArray) : JumpdestMap :=
  JumpdestMap.mk c.size (scan c.size c 0 (zeros ((c.size+7)/8)))

private theorem bitmap_shape (c : ByteArray) :
    (buildJumpdestMap c).bitmap.size = (c.size+7)/8 := by
  simp only [buildJumpdestMap, size_scan, zeros_size]

private theorem bitmap_refines (c : ByteArray) (i : Nat) :
    raw (buildJumpdestMap c).bitmap i = reference c.data.toList 0 i := by
  have hc : c.size ≤ 8*(zeros ((c.size+7)/8)).size := by rw [zeros_size]; omega
  have h := scan_refines c.size c 0 (zeros ((c.size+7)/8)) (by omega) hc i
  simpa only [buildJumpdestMap, raw_zeros, Bool.false_or, atRef,
    Nat.not_lt_zero, ↓reduceIte, List.drop_zero, Nat.sub_zero] using h

private theorem bitmap_padding (c : ByteArray) (i : Nat) (hi : c.size ≤ i) :
    raw (buildJumpdestMap c).bitmap i = false := by
  rw [bitmap_refines]
  apply reference_ge
  simpa using hi

private theorem bitmap_padding_bit (c : ByteArray) (j k : Nat)
    (hj : j < (buildJumpdestMap c).bitmap.size) (hk : k < 8)
    (hi : c.size ≤ j*8+k) :
    bit (buildJumpdestMap c).bitmap[j] k = false := by
  have hd : (j*8+k)/8 = j := by omega
  have hm : (j*8+k)%8 = k := by omega
  have h := bitmap_padding c (j*8+k) hi
  simpa only [raw, hd, hm, dite_eq_left hj] using h

private theorem contains_build_refines (c : ByteArray) (i : Nat) :
    (buildJumpdestMap c).contains i = reference c.data.toList 0 i := by
  unfold JumpdestMap.contains
  change (if i < c.size then raw (buildJumpdestMap c).bitmap i else false) = _
  by_cases hi : i < c.size
  · rw [ite_eq_left hi]
    exact bitmap_refines c i
  · have hr : reference c.data.toList 0 i = false := by
      apply reference_ge
      change c.size ≤ i
      omega
    rw [ite_eq_right hi, hr]

/-- Analyze every finite code value, marking reached JUMPDEST bytes and skipping
only PUSH1–PUSH32 immediate data. EELS `src/ethereum/forks/amsterdam/vm/runtime.py:22–69`.
The executable builder scans packed bytes without constructing the List reference. -/
def validJumpDestinations (c : Bytes) : JumpdestMap :=
  buildJumpdestMap c.toByteArray

private theorem valid_bitmap_size (c : Bytes) :
    (validJumpDestinations c).bitmap.size = (c.size + 7) / 8 := by
  rw [validJumpDestinations, bitmap_shape, Bytes.size_toByteArray]

private theorem contains_refines (c : Bytes) (i : Nat) :
    (validJumpDestinations c).contains i = reference c.toList 0 i := by
  rw [validJumpDestinations, contains_build_refines, Bytes.toList_toByteArray]

private theorem valid_bitmap_padding (c : Bytes) (j k : Nat)
    (hj : j < (validJumpDestinations c).bitmap.size) (hk : k < 8)
    (hi : c.size ≤ j * 8 + k) :
    bit (validJumpDestinations c).bitmap[j] k = false := by
  exact bitmap_padding_bit c.toByteArray j k hj hk
    (by simpa only [Bytes.size_toByteArray] using hi)

/-- Empty code has no destination at any natural offset. -/
theorem validJumpDestinations_contains_empty (i : Nat) :
    (validJumpDestinations Bytes.empty).contains i = false := by
  rw [contains_refines, Bytes.toList_empty]
  rfl

/-- Complete raw-byte head, PUSH-data exclusion and shifted-tail recurrence.
Truncated immediate data is dropped naturally; the width is a local theorem term. -/
theorem validJumpDestinations_contains_cons (b : UInt8) (xs : List UInt8) (i : Nat) :
    let k := if 96 ≤ b.toNat ∧ b.toNat ≤ 127 then b.toNat - 95 else 0
    (validJumpDestinations (Bytes.ofList (b :: xs))).contains i =
      (if i = 0 then b == (0x5b : UInt8) else if i ≤ k then false
       else (validJumpDestinations (Bytes.ofList (xs.drop k))).contains (i - (k + 1))) := by
  change (validJumpDestinations (Bytes.ofList (b :: xs))).contains i =
    if i = 0 then b == 91 else if i ≤ width b then false
    else (validJumpDestinations (Bytes.ofList (xs.drop (width b)))).contains (i - (width b + 1))
  simp only [contains_refines, Bytes.toList_ofList]
  exact reference_cons b xs i

/-- Every out-of-code natural offset is absent, including padding and huge queries. -/
theorem validJumpDestinations_contains_of_size_le (c : Bytes) (i : Nat)
    (hi : c.size ≤ i) :
    (validJumpDestinations c).contains i = false := by
  rw [contains_refines]
  exact reference_ge c.toList 0 i (by simpa only [Bytes.length_toList] using hi)

end STFSpec.Vm.Core
