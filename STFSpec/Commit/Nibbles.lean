/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.Bytes
import Init.Data.Order.Ord

/-!
# Bounded trie paths and pure path operations

Library `EthCommit`. Pinned EELS `src/ethereum/merkle_patricia_trie.py:350–404`.
Pure path operations follow the pinned source slice above. Q49 provider support
adds bounded generation, clipped copying and lawful lexicographic order for the
typed slices at `src/ethereum/merkle_patricia_trie.py:538/543/547/556`.
The public abstraction is `List (Fin 16)`. List models are proof/reference code.
Generation builds packed buffers once; copies retain only surviving digits;
comparison scans without copying. Aggregate consumer costs remain open.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§2.1/3/5/6/7; Q49.
-/

namespace STFSpec.Commit

open STFSpec.Base

/-- A packed path with one byte per nibble; every stored byte is below 16. -/
structure Nibbles where
  private mk ::
  private data : ByteArray
  private valid : ∀ i, (h : i < data.size) → (data[i]'h).toNat < 16

private theorem toNat_ofNat_val (x : Fin 16) : (UInt8.ofNat x.val).toNat = x.val := by
  apply UInt8.toNat_ofNat_of_lt'
  have := x.isLt
  change _ < 256
  omega

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
    rw [toNat_ofNat_val (xs[i])]
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
    exact toNat_ofNat_val (xs[i])

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

/-! ### Bounded construction and clipped packed copies -/

/-- Build exactly `n` bounded digits in ascending callback order, through the
public packed byte generator. The callback is never evaluated outside `0..n-1`. -/
def generate (n : Nat) (f : Nat → Fin 16) : Nibbles :=
  ⟨(Bytes.generate n (fun i ↦ UInt8.ofNat (f i).val)).toByteArray, by
    intro i hi
    rw [Bytes.size_toByteArray, Bytes.size_generate] at hi
    change ((Bytes.generate _ _)[i]'(by rw [Bytes.size_generate]; exact hi)).toNat < 16
    rw [Bytes.getElem_generate _ _ i hi,
      toNat_ofNat_val (f i)]
    exact (f i).isLt⟩

/-- Generation has exactly the requested length. -/
theorem size_generate (n : Nat) (f : Nat → Fin 16) : (generate n f).size = n := by
  simp [generate, size, Bytes.size_toByteArray, Bytes.size_generate]

/-- A bounded generated digit is its callback value. -/
theorem get_generate (n : Nat) (f : Nat → Fin 16) (i : Nat) (hi : i < n) :
    (generate n f).get ⟨i, by rw [size_generate]; exact hi⟩ = f i := by
  apply Fin.ext
  change ((Bytes.generate _ _)[i]'(by rw [Bytes.size_generate]; exact hi)).toNat = _
  rw [Bytes.getElem_generate _ _ i hi,
    toNat_ofNat_val (f i)]

/-- Ordinary all-input correspondence with the legible List-range model. -/
theorem toList_generate (n : Nat) (f : Nat → Fin 16) :
    (generate n f).toList = (List.range n).map f := by
  apply List.ext_getElem
  · rw [length_toList, size_generate, List.length_map, List.length_range]
  · intro i hi hj
    have hi' : i < n := by simpa only [List.length_map, List.length_range] using hj
    rw [getElem_toList _ _ (by rw [size_generate]; exact hi'), get_generate n f i hi']
    simp only [List.getElem_map, List.getElem_range]

/-- Callback agreement is required only at generated indices. -/
theorem generate_congr (n : Nat) (f g : Nat → Fin 16)
    (h : ∀ i, i < n → f i = g i) : generate n f = generate n g := by
  apply ext
  rw [toList_generate, toList_generate]
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

private def sliceData (p : Nibbles) (start stop : Nat) : ByteArray :=
  if start < p.size ∧ start < stop then p.data.extract start (min stop p.size)
  else ByteArray.empty

private theorem sliceData_size (p : Nibbles) (start stop : Nat) :
    (sliceData p start stop).size = min stop p.size - start := by
  unfold sliceData
  split
  · simp [ByteArray.size_extract, size, Nat.min_assoc]
  · next h => simp only [ByteArray.size_empty]; omega

private theorem sliceData_get (p : Nibbles) (start stop i : Nat)
    (hi : i < (sliceData p start stop).size) :
    (sliceData p start stop)[i]'hi = p.data[start + i]'(by
      change start + i < p.size
      rw [sliceData_size] at hi
      omega) := by
  by_cases hguard : start < p.size ∧ start < stop
  · have hh : i < (p.data.extract start (min stop p.size)).size := by
      simpa only [sliceData, ite_eq_left hguard] using hi
    simpa only [sliceData, ite_eq_left hguard] using (ByteArray.getElem_extract hh)
  · have hz : (sliceData p start stop).size = 0 := by simp [sliceData, hguard]
    omega

/-- Copy the start-inclusive, stop-exclusive window with natural clipping.
Huge unavailable offsets return empty before any runtime index conversion. -/
def extract (p : Nibbles) (start stop : Nat) : Nibbles :=
  ⟨sliceData p start stop, by
    intro i hi
    rw [sliceData_get]
    exact p.valid _ _⟩

/-- The clipped window has exactly its model length. -/
theorem size_extract (p : Nibbles) (start stop : Nat) :
    (p.extract start stop).size = min stop p.size - start := sliceData_size p start stop

/-- Every surviving digit comes from the original start-offset index. -/
theorem get_extract (p : Nibbles) (start stop i : Nat) (hi : i < (p.extract start stop).size) :
    (p.extract start stop).get ⟨i, hi⟩ =
      p.get ⟨start + i, by rw [size_extract] at hi; omega⟩ := by
  apply Fin.ext
  exact congrArg UInt8.toNat (sliceData_get p start stop i hi)

/-- Ordinary all-input correspondence with the legible List window model. -/
theorem toList_extract (p : Nibbles) (start stop : Nat) :
    (p.extract start stop).toList = (p.toList.drop start).take (stop - start) := by
  apply List.ext_getElem
  · simp only [length_toList, size_extract, List.length_take, List.length_drop]
    omega
  · intro i hi hj
    rw [getElem_toList _ _ (by rwa [length_toList] at hi), get_extract]
    simp only [List.getElem_take, List.getElem_drop]
    exact (getElem_toList p (start + i) _).symm

/-- Copy a clipped prefix; an oversized count retains the whole path. -/
def take (p : Nibbles) (n : Nat) : Nibbles := p.extract 0 n
/-- Copy a suffix; an oversized count returns the empty path. -/
def drop (p : Nibbles) (n : Nat) : Nibbles := p.extract n p.size

/-- Prefix copying agrees with List take. -/
theorem toList_take (p : Nibbles) (n : Nat) : (p.take n).toList = p.toList.take n := by
  simp [take, toList_extract]

/-- Prefix size is the smaller of the count and the original size. -/
theorem size_take (p : Nibbles) (n : Nat) : (p.take n).size = min n p.size := by
  simp [take, size_extract]

/-- Suffix copying agrees with List drop. -/
theorem toList_drop (p : Nibbles) (n : Nat) : (p.drop n).toList = p.toList.drop n := by
  rw [drop, toList_extract]
  apply List.take_of_length_le
  simp [length_toList]

/-- Suffix size uses truncating natural subtraction. -/
theorem size_drop (p : Nibbles) (n : Nat) : (p.drop n).size = p.size - n := by
  simp [drop, size_extract]

/-- A suffix digit is the corresponding offset digit in the original. -/
theorem get_drop (p : Nibbles) (n i : Nat) (hi : i < (p.drop n).size) :
    (p.drop n).get ⟨i, hi⟩ = p.get ⟨n + i, by rw [size_drop] at hi; omega⟩ :=
  get_extract p n p.size i hi

/-- Successive suffix copies compose by addition of natural offsets. -/
theorem drop_drop (p : Nibbles) (a b : Nat) : (p.drop a).drop b = p.drop (a + b) := by
  apply ext
  simp [toList_drop, List.drop_drop]

/-- Positive advancement strictly decreases a nonempty remaining suffix.
Both the starting-level bound and positive advance are essential. -/
theorem size_drop_add_lt (p : Nibbles) (level n : Nat) (hlevel : level < p.size) (hn : 0 < n) :
    (p.drop (level + n)).size < (p.drop level).size := by
  rw [size_drop, size_drop]
  omega

/-- One step strictly decreases a nonempty remaining suffix. -/
theorem size_drop_succ_lt (p : Nibbles) (level : Nat) (hlevel : level < p.size) :
    (p.drop (level + 1)).size < (p.drop level).size :=
  size_drop_add_lt p level 1 hlevel (by decide)

/-- Clipped prefixes cannot grow the path. -/
theorem size_take_le (p : Nibbles) (n : Nat) : (p.take n).size ≤ p.size := by
  rw [size_take]
  omega
/-- Clipped suffixes cannot grow the path. -/
theorem size_drop_le (p : Nibbles) (n : Nat) : (p.drop n).size ≤ p.size := by
  rw [size_drop]
  omega

/-- A prefix digit is unchanged at its bounded original index. -/
theorem get_take (x : Nibbles) (n i : Nat) (hi : i < (x.take n).size) :
    (x.take n).get ⟨i, hi⟩ = x.get ⟨i, by rw [size_take] at hi; omega⟩ := by
  simpa only [take, Nat.zero_add] using get_extract x 0 n i hi

/-- Zero generation is independent of the callback. -/
theorem generate_zero (f : Nat → Fin 16) : generate 0 f = ofList [] := by
  apply ext
  simp [toList_generate, toList_ofList]

/-- Taking zero returns the empty path. -/
theorem take_zero (x : Nibbles) : x.take 0 = ofList [] := by
  apply ext
  simp [toList_take, toList_ofList]

/-- Dropping zero preserves the path. -/
theorem drop_zero (x : Nibbles) : x.drop 0 = x := by
  apply ext
  simp [toList_drop]

/-- Taking the path size preserves all digits. -/
theorem take_size (x : Nibbles) : x.take x.size = x := by
  apply ext
  rw [toList_take, ← length_toList, List.take_length]

/-- Dropping the path size returns empty. -/
theorem drop_size (x : Nibbles) : x.drop x.size = ofList [] := by
  apply ext
  rw [toList_drop, ← length_toList, List.drop_length, toList_ofList]

/-- An oversized prefix count preserves the path. -/
theorem take_of_size_le (x : Nibbles) (n : Nat) (h : x.size ≤ n) : x.take n = x := by
  apply ext
  rw [toList_take, List.take_of_length_le (by rwa [length_toList])]

/-- An exhausted suffix is empty. -/
theorem drop_of_size_le (x : Nibbles) (n : Nat) (h : x.size ≤ n) : x.drop n = ofList [] := by
  apply ext
  rw [toList_drop, List.drop_of_length_le (by rwa [length_toList]), toList_ofList]

/-- Reversed and equal windows are empty. -/
theorem extract_of_stop_le_start (x : Nibbles) (start stop : Nat) (h : stop ≤ start) :
    x.extract start stop = ofList [] := by
  apply ext
  simp [toList_extract, Nat.sub_eq_zero_of_le h, toList_ofList]

/-- A window beginning past the path is empty. -/
theorem extract_of_size_le_start (x : Nibbles) (start stop : Nat) (h : x.size ≤ start) :
    x.extract start stop = ofList [] := by
  apply ext
  rw [toList_extract, List.drop_of_length_le (by rwa [length_toList])]
  simp [toList_ofList]

/-- Successive prefixes compose by the smaller count. -/
theorem take_take (x : Nibbles) (a b : Nat) : (x.take a).take b = x.take (min b a) := by
  apply ext
  simp [toList_take, List.take_take]

/-- Copying a prefix of a suffix is exactly the corresponding absolute window. -/
theorem take_drop (x : Nibbles) (start n : Nat) :
    (x.drop start).take n = x.extract start (start + n) := by
  apply ext
  simp [toList_take, toList_drop, toList_extract]

/-- Dropping a clipped prefix is exactly the corresponding absolute window. -/
theorem drop_take (x : Nibbles) (stop start : Nat) :
    (x.take stop).drop start = x.extract start stop := by
  apply ext
  rw [toList_drop, toList_take, List.drop_take, toList_extract]

private def digitAt (p : Nibbles) (i : Nat) : Fin 16 :=
  if hi : i < p.size then p.get ⟨i, hi⟩ else 0

private def compareScan (p q : Nibbles) : Nat → Nat → Ordering
  | 0, _ => compare p.size q.size
  | remaining + 1, i =>
    match compare (digitAt p i) (digitAt q i) with
    | .lt => .lt
    | .eq => compareScan p q remaining (i + 1)
    | .gt => .gt

private theorem compareScan_model (p q : Nibbles) (remaining i : Nat)
    (h : remaining + i = min p.size q.size) :
    compareScan p q remaining i = compare (p.toList.drop i) (q.toList.drop i) := by
  induction remaining generalizing i with
  | zero =>
    by_cases hlt : p.size < q.size
    · have hp : p.toList.drop i = [] := by
        apply List.drop_of_length_le
        rw [length_toList]
        omega
      have hq : q.toList.drop i ≠ [] := by
        intro he
        have hl := congrArg List.length he
        simp only [List.length_drop, length_toList, List.length_nil] at hl
        omega
      rw [compareScan, hp]
      cases he : q.toList.drop i with
      | nil => exact False.elim (hq he)
      | cons a as => simpa only [List.compare_nil_cons] using (Nat.compare_eq_lt.mpr hlt)
    · by_cases heq : p.size = q.size
      · have hp : p.toList.drop i = [] := by
          apply List.drop_of_length_le
          rw [length_toList]
          omega
        have hq : q.toList.drop i = [] := by
          apply List.drop_of_length_le
          rw [length_toList]
          omega
        simp [compareScan, hp, hq, heq]
      · have hgt : q.size < p.size := by omega
        have hq : q.toList.drop i = [] := by
          apply List.drop_of_length_le
          rw [length_toList]
          omega
        have hp : p.toList.drop i ≠ [] := by
          intro he
          have hl := congrArg List.length he
          simp only [List.length_drop, length_toList, List.length_nil] at hl
          omega
        rw [compareScan, hq]
        cases he : p.toList.drop i with
        | nil => exact False.elim (hp he)
        | cons a as => simpa only [List.compare_cons_nil] using (Nat.compare_eq_gt.mpr hgt)
  | succ remaining ih =>
    have hp : i < p.size := by omega
    have hq : i < q.size := by omega
    have ep : p.toList.drop i = p.get ⟨i, hp⟩ :: p.toList.drop (i + 1) := by
      rw [← List.getElem_cons_drop (by rw [length_toList]; exact hp), getElem_toList p i hp]
    have eq : q.toList.drop i = q.get ⟨i, hq⟩ :: q.toList.drop (i + 1) := by
      rw [← List.getElem_cons_drop (by rw [length_toList]; exact hq), getElem_toList q i hq]
    rw [compareScan, ep, eq, List.compare_cons_cons]
    simp only [digitAt, dite_eq_left hp, dite_eq_left hq]
    cases hc : compare (p.get ⟨i, hp⟩) (q.get ⟨i, hq⟩) with
    | lt => rfl
    | gt => rfl
    | eq => exact ih (i + 1) (by omega)

/-- Lexicographic packed scan: first differing digit, then proper prefix first. -/
instance : Ord Nibbles where
  compare p q := compareScan p q (min p.size q.size) 0

/-- Ordinary all-input bridge from the packed scan to List lexicographic order. -/
theorem compare_toList (p q : Nibbles) : compare p q = compare p.toList q.toList := by
  change compareScan p q (min p.size q.size) 0 = _
  rw [compareScan_model p q _ _ (by omega)]
  simp

/-- Orientation and transitivity transfer through the ordinary List bridge. -/
instance : Std.TransOrd Nibbles where
  eq_swap := by
    intro p q
    rw [compare_toList, compare_toList]
    exact Std.OrientedCmp.eq_swap
  isLE_trans := by
    intro p q r hpq hqr
    rw [compare_toList] at hpq hqr ⊢
    exact Std.TransCmp.isLE_trans hpq hqr

/-- The List bridge and extensionality make comparator equality lawful. -/
instance : Std.LawfulEqOrd Nibbles where
  compare_self := by
    intro p
    rw [compare_toList]
    exact Std.ReflCmp.compare_self
  eq_of_compare := by
    intro p q h
    rw [compare_toList] at h
    exact ext (Std.LawfulEqCmp.eq_of_compare h)

/-- Comparator equality is actual path equality, including significant zeros. -/
theorem compare_eq_eq_iff (p q : Nibbles) : compare p q = .eq ↔ p = q :=
  Std.LawfulEqOrd.compare_eq_iff_eq

/-- Decide actual path equality by the packed comparator, without a List allocation. -/
instance : DecidableEq Nibbles := fun p q ↦
  decidable_of_iff (compare p q = .eq) (compare_eq_eq_iff p q)

/-- Lexicographic observations respect both public List models. -/
theorem compare_of_toList_eq (p p' q q' : Nibbles)
    (hp : p.toList = p'.toList) (hq : q.toList = q'.toList) : compare p q = compare p' q' := by
  simp only [compare_toList, hp, hq]

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

/-- EELS `src/ethereum/merkle_patricia_trie.py:395–404`: high nibble before low.
Generates one linear packed buffer. -/
def bytesToNibbleList (b : ByteArray) : Nibbles :=
  ⟨(Bytes.generate (2 * b.size) (fun i ↦ UInt8.ofNat (splitDigit b i).val)).toByteArray, by
    intro i hi
    rw [Bytes.size_toByteArray, Bytes.size_generate] at hi
    change ((Bytes.generate _ _)[i]'(by rw [Bytes.size_generate]; exact hi)).toNat < 16
    rw [Bytes.getElem_generate _ _ i hi, toNat_ofNat_val (splitDigit b i)]
    exact (splitDigit b i).isLt⟩

/-- Splitting doubles the byte count. -/
theorem size_bytesToNibbleList (b : ByteArray) : (bytesToNibbleList b).size = 2 * b.size := by
  simp [bytesToNibbleList, Nibbles.size, Bytes.size_toByteArray, Bytes.size_generate]

private theorem get_split (b : ByteArray) (i : Nat) (hi : i < 2 * b.size) :
    (bytesToNibbleList b).get ⟨i, by rw [size_bytesToNibbleList]; exact hi⟩ = splitDigit b i := by
  apply Fin.ext
  change ((Bytes.generate _ _)[i]'(by rw [Bytes.size_generate]; exact hi)).toNat = _
  rw [Bytes.getElem_generate _ _ i hi, toNat_ofNat_val (splitDigit b i)]

/-- The high output position contains the input byte's high nibble. -/
theorem get_bytesToNibbleList_high (b : ByteArray) (i : Nat) (hi : i < b.size) :
    (bytesToNibbleList b).get ⟨2 * i, by rw [size_bytesToNibbleList]; omega⟩ =
      highNibble b[i] := by
  rw [get_split b _ (by omega)]
  simp [splitDigit, hi]

/-- The next output position contains the same input byte's low nibble. -/
theorem get_bytesToNibbleList_low (b : ByteArray) (i : Nat) (hi : i < b.size) :
    (bytesToNibbleList b).get ⟨2 * i + 1, by rw [size_bytesToNibbleList]; omega⟩ =
      lowNibble b[i] := by
  rw [get_split b _ (by omega)]
  have hd : (2 * i + 1) / 2 = i := by omega
  simp [splitDigit, hd, hi, Nat.add_mod]

private theorem splitModel_length (xs : List UInt8) :
    (bytesToNibbleListModel xs).length = 2 * xs.length := by
  induction xs with
  | nil => simp [bytesToNibbleListModel]
  | cons b xs ih =>
    simp [bytesToNibbleListModel] at *
    omega

private theorem splitModel_get (xs : List UInt8) (i : Nat) (hi : i < 2 * xs.length) :
    (bytesToNibbleListModel xs)[i]'(by rw [splitModel_length]; exact hi) =
      if i % 2 = 0 then highNibble (xs[i / 2]'(by omega))
      else lowNibble (xs[i / 2]'(by omega)) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons b xs ih =>
    cases i with
    | zero => simp [bytesToNibbleListModel]
    | succ i =>
      cases i with
      | zero => simp [bytesToNibbleListModel]
      | succ i =>
        have hi' : i < 2 * xs.length := by
          simp at hi
          omega
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
      rw [Nibbles.length_toList, size_bytesToNibbleList] at hi
      exact hi
    rw [Nibbles.getElem_toList _ _ (by rw [size_bytesToNibbleList]; exact hi'),
      get_split b i hi', splitModel_get _ i
        (by simpa only [Array.length_toList, ByteArray.size_data] using hi')]
    simp only [splitDigit, dite_eq_left (show i / 2 < b.size by omega), Array.getElem_toList]
    rfl

/-- The two nibble values recover every input byte without wrapping. -/
theorem highNibble_mul_add_lowNibble (b : UInt8) :
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

private def compactPairs : List (Fin 16) → List UInt8
  | high :: low :: rest => packNibbles high low :: compactPairs rest
  | _ => []

private theorem compactPairs_length (xs : List (Fin 16)) :
    (compactPairs xs).length = xs.length / 2 := by
  cases xs with
  | nil => rfl
  | cons high xs =>
    cases xs with
    | nil => simp [compactPairs]
    | cons low rest =>
      simp only [compactPairs, List.length_cons]
      rw [compactPairs_length rest]
      omega

private theorem compactPairs_get (xs : List (Fin 16)) (i : Nat)
    (hi : i < xs.length / 2) :
    (compactPairs xs)[i]'(by rw [compactPairs_length]; exact hi) =
      packNibbles (xs[2 * i]?.getD 0) (xs[2 * i + 1]?.getD 0) := by
  cases xs with
  | nil => simp at hi
  | cons high xs =>
    cases xs with
    | nil => simp at hi
    | cons low rest =>
      cases i with
      | zero => simp [compactPairs]
      | succ i =>
        have hi' : i < rest.length / 2 := by
          simp only [List.length_cons] at hi
          omega
        simpa [compactPairs, Nat.mul_add, Nat.add_assoc] using compactPairs_get rest i hi'

/-- EELS `src/ethereum/merkle_patricia_trie.py:384–390`: structural compact reference.
A header precedes adjacent pairs. Even paths pair the full list; odd paths pair the tail. -/
def nibbleListToCompactModel (xs : List (Fin 16)) (leaf : Bool) : List UInt8 :=
  compactHeader xs.length leaf (xs.headD 0) ::
    compactPairs (if xs.length % 2 = 0 then xs else xs.tail)

private theorem compactModel_eq_indexed (xs : List (Fin 16)) (leaf : Bool) :
    nibbleListToCompactModel xs leaf =
      compactHeader xs.length leaf (xs[0]?.getD 0) ::
        List.ofFn (fun i : Fin (xs.length / 2) ↦
          packNibbles (xs[2 * i.val + xs.length % 2]?.getD 0)
            (xs[2 * i.val + xs.length % 2 + 1]?.getD 0)) := by
  have hh : xs.headD 0 = xs[0]?.getD 0 := by cases xs <;> rfl
  unfold nibbleListToCompactModel
  rw [hh]
  congr 1
  split
  · next he =>
    apply List.ext_getElem
    · simp [compactPairs_length]
    · intro i hi hj
      rw [compactPairs_get xs i (by simpa [compactPairs_length] using hi)]
      simp [List.getElem_ofFn, he]
  · next ho =>
    have hm : xs.length % 2 = 1 := by omega
    have ht : xs.tail.length / 2 = xs.length / 2 := by
      rw [List.length_tail]
      omega
    apply List.ext_getElem
    · rw [compactPairs_length, List.length_ofFn, ht]
    · intro i hi hj
      rw [compactPairs_get xs.tail i (by simpa [compactPairs_length] using hi)]
      simp [List.getElem_ofFn, hm, List.getElem?_tail, Nat.add_comm]

private theorem digitAt_model (x : Nibbles) (i : Nat) :
    Nibbles.digitAt x i = x.toList[i]?.getD 0 := by
  unfold Nibbles.digitAt
  split
  · next hi =>
    rw [List.getElem?_eq_getElem (by rw [Nibbles.length_toList]; exact hi),
      Option.getD_some, Nibbles.getElem_toList _ _ hi]
  · next hi => rw [List.getElem?_eq_none (by rw [Nibbles.length_toList]; omega), Option.getD_none]

private def compactByte (x : Nibbles) (leaf : Bool) (i : Nat) : UInt8 :=
  if i = 0 then compactHeader x.size leaf (Nibbles.digitAt x 0)
  else packNibbles (Nibbles.digitAt x (2 * (i - 1) + x.size % 2))
    (Nibbles.digitAt x (2 * (i - 1) + x.size % 2 + 1))

/-- EELS `src/ethereum/merkle_patricia_trie.py:360–392`: canonical compact encoding.
Generates one packed output without allocating slices or the List model. -/
def nibbleListToCompact (x : Nibbles) (isLeaf : Bool) : ByteArray :=
  (Bytes.generate (x.size / 2 + 1) (compactByte x isLeaf)).toByteArray

/-- Exact compact byte count, including the mandatory header. -/
theorem size_nibbleListToCompact (x : Nibbles) (leaf : Bool) :
    (nibbleListToCompact x leaf).size = x.size / 2 + 1 := by
  rw [nibbleListToCompact, Bytes.size_toByteArray, Bytes.size_generate]

/-- Every compact output is nonempty. -/
theorem nibbleListToCompact_nonempty (x : Nibbles) (leaf : Bool) :
    0 < (nibbleListToCompact x leaf).size := by
  rw [size_nibbleListToCompact]
  omega

/-- Ordinary all-input compact correspondence with the finite-list model. -/
theorem nibbleListToCompact_eq_model (x : Nibbles) (leaf : Bool) :
    (nibbleListToCompact x leaf).data.toList = nibbleListToCompactModel x.toList leaf := by
  rw [compactModel_eq_indexed]
  change (Bytes.generate _ _).toList = _
  rw [Bytes.toList_generate]
  apply List.ext_getElem
  · simp [Nibbles.length_toList]
  · intro i hi hj
    rw [List.getElem_map, List.getElem_range]
    cases i with
    | zero => simp [compactByte, digitAt_model, Nibbles.length_toList]
    | succ i =>
      simp only [compactByte, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel,
        List.getElem_cons_succ, List.getElem_ofFn,
        Nibbles.length_toList, digitAt_model]

/-- EELS `src/ethereum/merkle_patricia_trie.py:383–392`: each suffix byte
packs the next ordered pair after the parity-dependent header digit. -/
theorem nibbleListToCompact_pair (x : Nibbles) (leaf : Bool) (i : Nat)
    (hi : i < x.size / 2) :
    (nibbleListToCompact x leaf)[i + 1]'(by rw [size_nibbleListToCompact]; omega) =
      packNibbles (x.toList[2 * i + x.size % 2]?.getD 0)
        (x.toList[2 * i + x.size % 2 + 1]?.getD 0) := by
  have he := congrArg (fun bs ↦ bs[i + 1]?) (nibbleListToCompact_eq_model x leaf)
  rw [compactModel_eq_indexed] at he
  rw [List.getElem?_eq_getElem (by
    rw [Array.length_toList, ByteArray.size_data, size_nibbleListToCompact]
    omega)] at he
  simp only [Nibbles.length_toList, List.getElem?_cons_succ, List.getElem?_ofFn,
    hi, dite_eq_left, Array.getElem_toList] at he
  exact Option.some.inj he

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
    if Nibbles.digitAt a i = Nibbles.digitAt b i then prefixScan a b remaining (i + 1) else i

/-- EELS `src/ethereum/merkle_patricia_trie.py:350–357`: longest common prefix.
Scans the packed paths forward, stopping at the first mismatch or end. -/
def commonPrefixLength (a b : Nibbles) : Nat := prefixScan a b (min a.size b.size) 0

private theorem prefixScan_model (a b : Nibbles) (remaining i : Nat)
    (h : remaining + i = min a.size b.size) :
    prefixScan a b remaining i =
      i + commonPrefixLengthModel (a.toList.drop i) (b.toList.drop i) := by
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
    simp only [Nibbles.digitAt, dite_eq_left ha, dite_eq_left hb]
    split
    · rw [ih (i + 1) (by omega)]
      omega
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
    | cons y ys =>
      simp only [commonPrefixLengthModel]
      split
      · have := ih ys
        simp only [List.length_cons]
        omega
      · omega

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
theorem commonPrefixLength_symm (a b : Nibbles) :
    commonPrefixLength a b = commonPrefixLength b a := by
  rw [commonPrefixLength_eq_model, commonPrefixLength_eq_model, prefixModel_symm]

/-- Prefix length cannot exceed the right path. -/
theorem commonPrefixLength_le_right (a b : Nibbles) : commonPrefixLength a b ≤ b.size := by
  rw [commonPrefixLength_symm]
  exact commonPrefixLength_le_left _ _

private theorem prefixModel_self (xs : List (Fin 16)) :
    commonPrefixLengthModel xs xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [commonPrefixLengthModel, ih]
    omega

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

namespace Nibbles

/-- The complete common prefix is an equal path through the public copying seam. -/
theorem take_commonPrefixLength (a b : Nibbles) :
    a.take (commonPrefixLength a b) = b.take (commonPrefixLength a b) := by
  apply ext
  rw [toList_take, toList_take]
  exact commonPrefixLength_equal_prefixes a b

/-- Bounded copied prefixes agree exactly through the maximal common prefix. -/
theorem take_eq_iff_le_commonPrefixLength (a b : Nibbles) (k : Nat)
    (ha : k ≤ a.size) (hb : k ≤ b.size) :
    a.take k = b.take k ↔ k ≤ commonPrefixLength a b := by
  rw [← toList_inj, toList_take, toList_take]
  exact commonPrefixLength_take_iff a b k ha hb

end Nibbles

end STFSpec.Commit
