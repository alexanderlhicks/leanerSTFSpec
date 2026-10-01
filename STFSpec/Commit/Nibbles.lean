/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.Bytes
import Init.Data.UInt.Lemmas

/-!
# Bounded trie paths and pure path operations

Library `EthCommit`. Pinned EELS `src/ethereum/merkle_patricia_trie.py:350–404`.
Packed buffers are generated once; prefix comparison scans without copying.
The public abstraction is `List (Fin 16)`. List models are proof/reference code.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§2.1/5/6/7.
-/

namespace STFSpec.Commit

open STFSpec.Base

/-- A packed path with one byte per nibble; every stored byte is below 16. -/
structure Nibbles where
  private mk ::
  private data : ByteArray
  private valid : ∀ i, (h : i < data.size) → (data[i]'h).toNat < 16

namespace Nibbles

/-- Number of nibbles. -/
def size (x : Nibbles) : Nat := x.data.size

/-- Bounded nibble observation. -/
def get (x : Nibbles) (i : Fin x.size) : Fin 16 :=
  ⟨(x.data[i.val]'i.isLt).toNat, x.valid i.val i.isLt⟩

/-- Stable finite-list abstraction; observing it allocates a list. -/
def toList (x : Nibbles) : List (Fin 16) := List.ofFn x.get

/-- Construct a packed path from the mathematical model, copying its digits once. -/
def ofList (xs : List (Fin 16)) : Nibbles :=
  ⟨(xs.map (fun x ↦ UInt8.ofNat x.val)).toByteArray, by
    intro i hi
    simp only [List.size_toByteArray, List.length_map] at hi
    simp only [List.getElem_toByteArray, List.getElem_map]
    rw [UInt8.toNat_ofNat_of_lt' (by have := (xs[i]).isLt; change _ < 256; omega)]
    exact (xs[i]).isLt⟩

/-- Abstraction preserves path length. -/
theorem length_toList (x : Nibbles) : x.toList.length = x.size := by
  simp [toList]

/-- Indexed abstraction agrees with the bounded observer. -/
theorem getElem_toList (x : Nibbles) (i : Nat) (hi : i < x.size) :
    x.toList[i]'(by rw [length_toList]; exact hi) = x.get ⟨i, hi⟩ := by
  simp [toList]

/-- Every observed digit has the stated range. -/
theorem get_lt (x : Nibbles) (i : Fin x.size) : (x.get i).val < 16 := (x.get i).isLt

/-- Model construction preserves its length. -/
theorem size_ofList (xs : List (Fin 16)) : (ofList xs).size = xs.length := by
  simp [ofList, size]

/-- Observing model construction gives exactly the input digits. -/
theorem toList_ofList (xs : List (Fin 16)) : (ofList xs).toList = xs := by
  apply List.ext_getElem
  · rw [length_toList, size_ofList]
  · intro i hi hj
    rw [getElem_toList _ _ (by rw [size_ofList]; exact hj)]
    apply Fin.ext
    simp only [get, ofList, List.getElem_toByteArray, List.getElem_map]
    exact UInt8.toNat_ofNat_of_lt' (n := (xs[i]).val) (by have := (xs[i]).isLt; change _ < 256; omega)

/-- Extensional equality through the stable model. -/
theorem ext {x y : Nibbles} (h : x.toList = y.toList) : x = y := by
  have hs : x.size = y.size := by
    rw [← length_toList, ← length_toList, h]
  have hd : x.data = y.data := by
    apply ByteArray.ext
    apply Array.ext
    · exact hs
    · intro i hi hj
      apply UInt8.toNat_inj.mp
      change x.data[i].toNat = y.data[i].toNat
      have he := congrArg (fun xs ↦ (xs[i]?).map Fin.val) h
      rw [List.getElem?_eq_getElem (by rw [length_toList]; exact hi),
        List.getElem?_eq_getElem (by rw [length_toList]; exact hj)] at he
      rw [getElem_toList x i hi, getElem_toList y i hj] at he
      change some (x.data[i].toNat) = some (y.data[i].toNat) at he
      exact Option.some.inj he
  cases x
  cases y
  cases hd
  rfl

/-- Model observation is injective. -/
theorem toList_inj {x y : Nibbles} : x.toList = y.toList ↔ x = y :=
  ⟨ext, fun h ↦ congrArg toList h⟩

/-- Rebuilding the public model preserves the path. -/
theorem ofList_toList (x : Nibbles) : ofList x.toList = x := by
  apply ext
  rw [toList_ofList]

end Nibbles

/-- Mathematical high nibble of a byte. -/
def highNibble (b : UInt8) : Fin 16 := ⟨b.toNat / 16, by have := b.toNat_lt; omega⟩

/-- Mathematical low nibble of a byte. -/
def lowNibble (b : UInt8) : Fin 16 := ⟨b.toNat % 16, Nat.mod_lt _ (by decide)⟩

/-- Legible splitter model: high then low for each byte. -/
def bytesToNibbleListModel (xs : List UInt8) : List (Fin 16) :=
  xs.flatMap (fun b ↦ [highNibble b, lowNibble b])

private def splitDigit (b : ByteArray) (i : Nat) : Fin 16 :=
  if h : i / 2 < b.size then
    if i % 2 = 0 then highNibble b[i / 2] else lowNibble b[i / 2]
  else 0

/-- EELS :395–404: one linear packed generation, high nibble before low. -/
def bytesToNibbleList (b : ByteArray) : Nibbles :=
  ⟨(Bytes.generate (2 * b.size) (fun i ↦ UInt8.ofNat (splitDigit b i).val)).toByteArray, by
    intro i hi
    rw [Bytes.size_toByteArray, Bytes.size_generate] at hi
    change ((Bytes.generate _ _)[i]'(by rw [Bytes.size_generate]; exact hi)).toNat < 16
    rw [Bytes.getElem_generate _ _ i hi, UInt8.toNat_ofNat_of_lt' (by have := (splitDigit b i).isLt; change _ < 256; omega)]
    exact (splitDigit b i).isLt⟩

/-- Splitting doubles the byte count. -/
theorem size_bytesToNibbleList (b : ByteArray) : (bytesToNibbleList b).size = 2 * b.size := by
  simp [bytesToNibbleList, Nibbles.size, Bytes.size_toByteArray, Bytes.size_generate]

private theorem get_split (b : ByteArray) (i : Nat) (hi : i < 2 * b.size) :
    (bytesToNibbleList b).get ⟨i, by rw [size_bytesToNibbleList]; exact hi⟩ = splitDigit b i := by
  apply Fin.ext
  change ((Bytes.generate _ _)[i]'(by rw [Bytes.size_generate]; exact hi)).toNat = _
  rw [Bytes.getElem_generate _ _ i hi, UInt8.toNat_ofNat_of_lt' (by have := (splitDigit b i).isLt; change _ < 256; omega)]

/-- The high output position contains the input byte's high nibble. -/
theorem get_bytesToNibbleList_high (b : ByteArray) (i : Nat) (hi : i < b.size) :
    (bytesToNibbleList b).get ⟨2 * i, by rw [size_bytesToNibbleList]; omega⟩ = highNibble b[i] := by
  rw [get_split b _ (by omega)]
  simp [splitDigit, hi]

/-- The next output position contains the same input byte's low nibble. -/
theorem get_bytesToNibbleList_low (b : ByteArray) (i : Nat) (hi : i < b.size) :
    (bytesToNibbleList b).get ⟨2 * i + 1, by rw [size_bytesToNibbleList]; omega⟩ = lowNibble b[i] := by
  rw [get_split b _ (by omega)]
  have hd : (2 * i + 1) / 2 = i := by omega
  simp [splitDigit, hd, hi, Nat.add_mod]

private theorem splitModel_length (xs : List UInt8) :
    (bytesToNibbleListModel xs).length = 2 * xs.length := by
  induction xs with
  | nil => simp [bytesToNibbleListModel]
  | cons b xs ih => simp [bytesToNibbleListModel] at *; omega

private theorem splitModel_get (xs : List UInt8) (i : Nat) (hi : i < 2 * xs.length) :
    (bytesToNibbleListModel xs)[i]'(by rw [splitModel_length]; exact hi) =
      if i % 2 = 0 then highNibble (xs[i / 2]'(by omega)) else lowNibble (xs[i / 2]'(by omega)) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons b xs ih =>
    cases i with
    | zero => simp [bytesToNibbleListModel]
    | succ i =>
      cases i with
      | zero => simp [bytesToNibbleListModel]
      | succ i =>
        have hi' : i < 2 * xs.length := by simp at hi; omega
        have hd : (i + 1 + 1) / 2 = i / 2 + 1 := by omega
        have hm : (i + 1 + 1) % 2 = i % 2 := by omega
        simpa [bytesToNibbleListModel, hd, hm] using ih i hi'

/-- Ordinary all-input correspondence with the legible splitter model. -/
theorem toList_bytesToNibbleList (b : ByteArray) :
    (bytesToNibbleList b).toList = bytesToNibbleListModel b.data.toList := by
  apply List.ext_getElem
  · rw [Nibbles.length_toList, size_bytesToNibbleList, splitModel_length]
    rfl
  · intro i hi hj
    have hi' : i < 2 * b.size := by
      rw [Nibbles.length_toList, size_bytesToNibbleList] at hi; exact hi
    rw [Nibbles.getElem_toList _ _ (by rw [size_bytesToNibbleList]; exact hi'),
      get_split b i hi', splitModel_get _ i (by simpa only [Array.length_toList, ByteArray.size_data] using hi')]
    simp only [splitDigit, dite_eq_left (show i / 2 < b.size by omega), Array.getElem_toList]
    rfl

/-- The two nibble values recover every input byte without wrapping. -/
theorem high_low_decomposition (b : UInt8) :
    16 * (highNibble b).val + (lowNibble b).val = b.toNat := by
  simp only [highNibble, lowNibble]
  omega

/-- Pack a high and low nibble into exactly one byte. -/
def packNibbles (high low : Fin 16) : UInt8 := UInt8.ofNat (16 * high.val + low.val)

/-- Packing bounded digits does not wrap. -/
theorem toNat_packNibbles (high low : Fin 16) :
    (packNibbles high low).toNat = 16 * high.val + low.val := by
  apply UInt8.toNat_ofNat_of_lt'
  have := high.isLt
  have := low.isLt
  change _ < 256
  omega

private def leafBit (leaf : Bool) : Nat := if leaf then 1 else 0

/-- Canonical compact header. The parity is 0 or 1 and first is ignored when even. -/
def compactHeader (n : Nat) (leaf : Bool) (first : Fin 16) : UInt8 :=
  UInt8.ofNat (16 * (2 * leafBit leaf + n % 2) + if n % 2 = 0 then 0 else first.val)

private theorem compactHeader_value (n : Nat) (leaf : Bool) (first : Fin 16) :
    (compactHeader n leaf first).toNat =
      16 * (2 * leafBit leaf + n % 2) + if n % 2 = 0 then 0 else first.val := by
  apply UInt8.toNat_ofNat_of_lt'
  have := first.isLt
  have := Nat.mod_lt n (by decide : 0 < 2)
  cases leaf <;> simp only [leafBit, Bool.false_eq_true, ite_false, ite_true]
    <;> split <;> change _ < 256 <;> omega

/-- Legible List model: one flag/padding-or-first byte, then adjacent ordered pairs.
For odd paths pairing starts at 1; for even paths at 0. -/
def nibbleListToCompactModel (xs : List (Fin 16)) (leaf : Bool) : List UInt8 :=
  compactHeader xs.length leaf (xs[0]?.getD 0) ::
    List.ofFn (fun i : Fin (xs.length / 2) ↦
      packNibbles (xs[2 * i.val + xs.length % 2]?.getD 0)
        (xs[2 * i.val + xs.length % 2 + 1]?.getD 0))

private def digitAt (x : Nibbles) (i : Nat) : Fin 16 :=
  if h : i < x.size then x.get ⟨i, h⟩ else 0

private theorem digitAt_model (x : Nibbles) (i : Nat) :
    digitAt x i = x.toList[i]?.getD 0 := by
  unfold digitAt
  split
  · next hi =>
    rw [List.getElem?_eq_getElem (by rw [Nibbles.length_toList]; exact hi),
      Option.getD_some, Nibbles.getElem_toList _ _ hi]
  · next hi => rw [List.getElem?_eq_none (by rw [Nibbles.length_toList]; omega), Option.getD_none]

private def compactByte (x : Nibbles) (leaf : Bool) (i : Nat) : UInt8 :=
  if i = 0 then compactHeader x.size leaf (digitAt x 0)
  else packNibbles (digitAt x (2 * (i - 1) + x.size % 2))
    (digitAt x (2 * (i - 1) + x.size % 2 + 1))

/-- EELS :360–392. Generates one packed output; no slices or List model are allocated. -/
def nibbleListToCompact (x : Nibbles) (isLeaf : Bool) : ByteArray :=
  (Bytes.generate (x.size / 2 + 1) (compactByte x isLeaf)).toByteArray

/-- Exact compact byte count, including the mandatory header. -/
theorem size_nibbleListToCompact (x : Nibbles) (leaf : Bool) :
    (nibbleListToCompact x leaf).size = x.size / 2 + 1 := by
  rw [nibbleListToCompact, Bytes.size_toByteArray, Bytes.size_generate]

/-- Every compact output is nonempty. -/
theorem nibbleListToCompact_nonempty (x : Nibbles) (leaf : Bool) :
    0 < (nibbleListToCompact x leaf).size := by rw [size_nibbleListToCompact]; omega

/-- Ordinary all-input compact correspondence with the finite-list model. -/
theorem nibbleListToCompact_eq_model (x : Nibbles) (leaf : Bool) :
    (nibbleListToCompact x leaf).data.toList = nibbleListToCompactModel x.toList leaf := by
  change (Bytes.generate _ _).toList = _
  rw [Bytes.toList_generate]
  apply List.ext_getElem
  · simp [nibbleListToCompactModel, Nibbles.length_toList]
  · intro i hi hj
    rw [List.getElem_map, List.getElem_range]
    cases i with
    | zero => simp [compactByte, nibbleListToCompactModel, digitAt_model, Nibbles.length_toList]
    | succ i =>
      simp only [compactByte, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel,
        nibbleListToCompactModel, List.getElem_cons_succ, List.getElem_ofFn,
        Nibbles.length_toList, digitAt_model]

/-- Header byte retains precisely the parity/leaf flag and padding-or-first nibble. -/
theorem nibbleListToCompact_header (x : Nibbles) (leaf : Bool) :
    (nibbleListToCompact x leaf)[0]'(nibbleListToCompact_nonempty x leaf) =
      compactHeader x.size leaf (x.toList[0]?.getD 0) := by
  change (Bytes.generate _ _)[0]'(by rw [Bytes.size_generate]; omega) = _
  rw [Bytes.getElem_generate _ _ 0 (by omega)]
  simp [compactByte, digitAt_model]

/-- The high header nibble is one of the four canonical flags. -/
theorem nibbleListToCompact_flag (x : Nibbles) (leaf : Bool) :
    ((nibbleListToCompact x leaf)[0]'(nibbleListToCompact_nonempty x leaf)).toNat / 16 =
      2 * (if leaf then 1 else 0) + x.size % 2 := by
  rw [nibbleListToCompact_header, compactHeader_value]
  have := (x.toList[0]?.getD (0 : Fin 16)).isLt
  split <;> unfold leafBit <;> split <;> omega

/-- Even paths carry zero padding; odd paths carry the first digit. -/
theorem nibbleListToCompact_first (x : Nibbles) (leaf : Bool) :
    ((nibbleListToCompact x leaf)[0]'(nibbleListToCompact_nonempty x leaf)).toNat % 16 =
      if x.size % 2 = 0 then 0 else (x.toList[0]?.getD 0).val := by
  rw [nibbleListToCompact_header, compactHeader_value]
  have := (x.toList[0]?.getD (0 : Fin 16)).isLt
  split <;> unfold leafBit <;> split <;> omega

/-- Empty extension and leaf paths encode as `00` and `20`. -/
theorem nibbleListToCompact_empty (leaf : Bool) :
    (nibbleListToCompact (Nibbles.ofList []) leaf).data.toList =
      [if leaf then 32 else 0] := by
  rw [nibbleListToCompact_eq_model, Nibbles.toList_ofList]
  cases leaf <;> rfl

/-- Legible prefix model: stop at either end or the first unequal pair. -/
def commonPrefixLengthModel : List (Fin 16) → List (Fin 16) → Nat
  | a :: as, b :: bs => if a = b then 1 + commonPrefixLengthModel as bs else 0
  | _, _ => 0

private def prefixScan (a b : Nibbles) : Nat → Nat → Nat
  | 0, i => i
  | remaining + 1, i =>
    if digitAt a i = digitAt b i then prefixScan a b remaining (i + 1) else i

/-- EELS :350–357. One forward packed scan, stopping at the first mismatch or end. -/
def commonPrefixLength (a b : Nibbles) : Nat := prefixScan a b (min a.size b.size) 0

private theorem prefixScan_model (a b : Nibbles) (remaining i : Nat)
    (h : remaining + i = min a.size b.size) :
    prefixScan a b remaining i = i + commonPrefixLengthModel (a.toList.drop i) (b.toList.drop i) := by
  induction remaining generalizing i with
  | zero =>
    have he : a.toList.drop i = [] ∨ b.toList.drop i = [] := by
      by_cases ha : a.size ≤ b.size
      · left
        rw [List.drop_of_length_le (by rw [Nibbles.length_toList]; omega)]
      · right
        rw [List.drop_of_length_le (by rw [Nibbles.length_toList]; omega)]
    rcases he with he | he
    · simp [prefixScan, he, commonPrefixLengthModel]
    · cases hx : a.toList.drop i <;> simp [prefixScan, he, commonPrefixLengthModel]
  | succ remaining ih =>
    have ha : i < a.size := by omega
    have hb : i < b.size := by omega
    have ea : a.toList.drop i = a.get ⟨i, ha⟩ :: a.toList.drop (i + 1) := by
      rw [← List.getElem_cons_drop (by rw [Nibbles.length_toList]; exact ha),
        Nibbles.getElem_toList _ _ ha]
    have eb : b.toList.drop i = b.get ⟨i, hb⟩ :: b.toList.drop (i + 1) := by
      rw [← List.getElem_cons_drop (by rw [Nibbles.length_toList]; exact hb),
        Nibbles.getElem_toList _ _ hb]
    rw [prefixScan, ea, eb, commonPrefixLengthModel]
    simp only [digitAt, dite_eq_left ha, dite_eq_left hb]
    split
    · rw [ih (i + 1) (by omega)]; omega
    · omega

/-- Ordinary all-input prefix correspondence with the finite-list model. -/
theorem commonPrefixLength_eq_model (a b : Nibbles) :
    commonPrefixLength a b = commonPrefixLengthModel a.toList b.toList := by
  rw [commonPrefixLength, prefixScan_model _ _ _ _ (by omega)]
  simp

private theorem prefixModel_le_left (xs ys : List (Fin 16)) :
    commonPrefixLengthModel xs ys ≤ xs.length := by
  induction xs generalizing ys with
  | nil => simp [commonPrefixLengthModel]
  | cons x xs ih =>
    cases ys with
    | nil => simp [commonPrefixLengthModel]
    | cons y ys => simp only [commonPrefixLengthModel]; split <;> have := ih ys <;> simp <;> omega

private theorem prefixModel_symm (xs ys : List (Fin 16)) :
    commonPrefixLengthModel xs ys = commonPrefixLengthModel ys xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys => simp [commonPrefixLengthModel, eq_comm, ih]

/-- Prefix length cannot exceed the left path. -/
theorem commonPrefixLength_le_left (a b : Nibbles) : commonPrefixLength a b ≤ a.size := by
  rw [commonPrefixLength_eq_model, ← Nibbles.length_toList]
  exact prefixModel_le_left _ _

/-- Prefix comparison is symmetric despite the source's asymmetric loop. -/
theorem commonPrefixLength_symm (a b : Nibbles) : commonPrefixLength a b = commonPrefixLength b a := by
  rw [commonPrefixLength_eq_model, commonPrefixLength_eq_model, prefixModel_symm]

/-- Prefix length cannot exceed the right path. -/
theorem commonPrefixLength_le_right (a b : Nibbles) : commonPrefixLength a b ≤ b.size := by
  rw [commonPrefixLength_symm]
  exact commonPrefixLength_le_left _ _

private theorem prefixModel_self (xs : List (Fin 16)) :
    commonPrefixLengthModel xs xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [commonPrefixLengthModel, ih]; omega

/-- A path agrees with itself for its complete length. -/
theorem commonPrefixLength_self (a : Nibbles) : commonPrefixLength a a = a.size := by
  rw [commonPrefixLength_eq_model, prefixModel_self, Nibbles.length_toList]

private theorem prefixModel_take_iff (xs ys : List (Fin 16)) (k : Nat)
    (hx : k ≤ xs.length) (hy : k ≤ ys.length) :
    xs.take k = ys.take k ↔ k ≤ commonPrefixLengthModel xs ys := by
  induction k generalizing xs ys with
  | zero => simp
  | succ k ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases ys with
      | nil => simp at hy
      | cons y ys =>
        simp only [List.take_succ_cons, List.cons.injEq, commonPrefixLengthModel]
        by_cases he : x = y
        · rw [ite_eq_left he]
          simp only [he, true_and]
          rw [ih xs ys (by simp at hx; omega) (by simp at hy; omega)]
          omega
        · rw [ite_eq_right he]
          simp [he]

/-- Every bounded prefix agrees exactly up to the returned length. -/
theorem commonPrefixLength_take_iff (a b : Nibbles) (k : Nat)
    (ha : k ≤ a.size) (hb : k ≤ b.size) :
    a.toList.take k = b.toList.take k ↔ k ≤ commonPrefixLength a b := by
  rw [commonPrefixLength_eq_model]
  apply prefixModel_take_iff <;> rwa [Nibbles.length_toList]

/-- The entire returned prefix agrees, including empty prefixes. -/
theorem commonPrefixLength_equal_prefixes (a b : Nibbles) :
    a.toList.take (commonPrefixLength a b) = b.toList.take (commonPrefixLength a b) := by
  exact (commonPrefixLength_take_iff a b _ (commonPrefixLength_le_left _ _)
    (commonPrefixLength_le_right _ _)).mpr (Nat.le_refl _)

/-- When both paths continue, the next digits differ: the returned prefix is maximal. -/
theorem commonPrefixLength_maximal (a b : Nibbles)
    (ha : commonPrefixLength a b < a.size) (hb : commonPrefixLength a b < b.size) :
    a.get ⟨commonPrefixLength a b, ha⟩ ≠ b.get ⟨commonPrefixLength a b, hb⟩ := by
  intro he
  have hp := commonPrefixLength_equal_prefixes a b
  have hn : a.toList.take (commonPrefixLength a b + 1) =
      b.toList.take (commonPrefixLength a b + 1) := by
    rw [List.take_succ_eq_append_getElem (by rw [Nibbles.length_toList]; exact ha),
      List.take_succ_eq_append_getElem (by rw [Nibbles.length_toList]; exact hb),
      Nibbles.getElem_toList _ _ ha, Nibbles.getElem_toList _ _ hb, hp, he]
  have := (commonPrefixLength_take_iff a b _ (by omega) (by omega)).mp hn
  omega

end STFSpec.Commit
