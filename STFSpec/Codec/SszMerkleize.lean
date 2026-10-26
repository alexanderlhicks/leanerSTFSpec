/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.SszZeroHash
import STFSpec.Codec.SszPack

/-!
# Physical-capacity SSZ Merkleization

Library `EthCodec`. Sparse packed interval traversal, with a complete private
List/tree reference and ordinary equality to the ordered padded layer fold.
Reference: locked eth-remerkleable 0.1.31 `remerkleable/tree.py:242–263`.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Codec

section Reference

variable {α : Type} (pair : α → α → α) (zero : α)

/-- Full binary tree, with no missing positions in its mathematical shape. -/
private inductive Tree (α : Type) where
  | leaf : α → Tree α
  | fork : Tree α → Tree α → Tree α

private def Tree.eval : Tree α → α
  | .leaf x => x
  | .fork l r => pair (Tree.eval l) (Tree.eval r)

/-- Expands all physical positions, choosing the seed for missing input leaves. -/
private def fullTree : Nat → List α → Tree α
  | 0, xs => .leaf (xs.headD zero)
  | d + 1, xs => .fork (fullTree d (xs.take (2 ^ d))) (fullTree d (xs.drop (2 ^ d)))

private def reference (d : Nat) (xs : List α) : α := (fullTree zero d xs).eval pair

/-- Independently defined homogeneous missing-subtree recurrence. -/
private def zeroTree : Nat → α
  | 0 => zero
  | d + 1 => let z := zeroTree d; pair z z

/-- No exponential zero-leaf materialization: an empty subtree ends immediately. -/
private def sparse : Nat → List α → α
  | d, [] => zeroTree pair zero d
  | 0, x :: _ => x
  | d + 1, x :: xs =>
    pair (sparse d ((x :: xs).take (2 ^ d))) (sparse d ((x :: xs).drop (2 ^ d)))

/-- Straight ordered pairs. The final unpaired leaf is ignored by this internal layer. -/
private def pairs : List α → List α
  | a :: b :: xs => pair a b :: pairs xs
  | _ => []

/-- Exactly d pair reductions, with an internal seed default only for malformed layers. -/
private def foldPairs : Nat → List α → α
  | 0, xs => xs.headD zero
  | d + 1, xs => foldPairs d (pairs pair xs)

/-- Indexed ordered mathematical pair layer. -/
private def pairLayer (xs : List α) : List α :=
  (List.range (xs.length / 2)).map (fun i => pair (xs.getD (2 * i) zero) (xs.getD (2 * i + 1)
      zero))

/-- Complete research padded pair-layer fold, used only on physically admitted leaves. -/
private def padded (d : Nat) (xs : List α) : α :=
  ((List.range d).foldl (fun layer _ => pairLayer pair zero layer)
    (xs ++ List.replicate (2 ^ d - xs.length) zero)).headD zero

private theorem zeroTree_model (g : Nat → α) (h0 : g 0 = zero)
    (hs : ∀ d, g (d + 1) = pair (g d) (g d)) (d : Nat) :
    zeroTree pair zero d = g d := by
  induction d with
  | zero => exact h0.symm
  | succ d ih => rw [zeroTree, ih, ← hs]

private theorem reference_empty (d : Nat) : reference pair zero d [] = zeroTree pair zero d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simpa [reference, fullTree, Tree.eval, zeroTree] using congrArg (fun a => pair a a) ih

private theorem sparse_reference (d : Nat) (xs : List α) (h : xs.length ≤ 2 ^ d) :
    sparse pair zero d xs = reference pair zero d xs := by
  induction d generalizing xs with
  | zero => cases xs <;> rfl
  | succ d ih =>
    cases xs with
    | nil => exact (reference_empty pair zero (d + 1)).symm
    | cons x xs =>
      simp only [sparse, reference, fullTree, Tree.eval]
      congr 1
      · exact ih _ (by simp only [List.length_take]; omega)
      · apply ih
        simp only [List.length_drop]
        simp only [Nat.pow_succ] at h
        omega

private theorem pairLayer_cons_cons (a b : α) (xs : List α) :
    pairLayer pair zero (a :: b :: xs) = pair a b :: pairLayer pair zero xs := by
  simp only [pairLayer, List.length_cons]
  have h : (xs.length + 1 + 1) / 2 = xs.length / 2 + 1 := by omega
  rw [h, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map]
  congr 1

private theorem pairs_eq_pairLayer (xs : List α) : pairs pair xs = pairLayer pair zero xs := by
  match xs with
  | [] => simp [pairs, pairLayer]
  | [_] => simp [pairs, pairLayer]
  | a :: b :: xs =>
    rw [pairs, pairLayer_cons_cons, pairs_eq_pairLayer xs]

private theorem pairs_length (xs : List α) : (pairs pair xs).length = xs.length / 2 := by
  match xs with
  | [] => simp [pairs]
  | [_] => simp [pairs]
  | a :: b :: xs => simp only [pairs, List.length_cons, pairs_length xs]; omega

private theorem pairs_append_even (xs ys : List α) (n : Nat) (h : xs.length = 2 * n) :
    pairs pair (xs ++ ys) = pairs pair xs ++ pairs pair ys := by
  induction n generalizing xs with
  | zero => have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega); subst xs; rfl
  | succ n ih =>
    match xs with
    | [] => simp at h
    | [_] => simp at h; omega
    | a :: b :: xs =>
      have hx : xs.length = 2 * n := by simp only [List.length_cons] at h; omega
      simp only [List.cons_append, pairs, ih xs hx]

private theorem foldPairs_append (d : Nat) (xs ys : List α)
    (hx : xs.length = 2 ^ d) (hy : ys.length = 2 ^ d) :
    foldPairs pair zero (d + 1) (xs ++ ys) =
      pair (foldPairs pair zero d xs) (foldPairs pair zero d ys) := by
  induction d generalizing xs ys with
  | zero =>
    match xs, ys with
    | [a], [b] => rfl
    | [], _ => simp at hx
    | _ :: _ :: _, _ => simp at hx
    | _, [] => simp at hy
    | _, _ :: _ :: _ => simp at hy
  | succ d ih =>
    have he : xs.length = 2 * 2 ^ d := by simpa [Nat.pow_succ, Nat.mul_comm] using hx
    simp only [foldPairs]
    rw [pairs_append_even pair xs ys (2 ^ d) he]
    apply ih
    · rw [pairs_length, hx, Nat.pow_succ]; omega
    · rw [pairs_length, hy, Nat.pow_succ]; omega

private theorem foldPairs_reference_full (d : Nat) (xs : List α) (h : xs.length = 2 ^ d) :
    foldPairs pair zero d xs = reference pair zero d xs := by
  induction d generalizing xs with
  | zero => rfl
  | succ d ih =>
    have ht : (xs.take (2 ^ d)).length = 2 ^ d := by
      simp only [List.length_take]; rw [h, Nat.pow_succ]; omega
    have hd : (xs.drop (2 ^ d)).length = 2 ^ d := by
      simp only [List.length_drop]; rw [h, Nat.pow_succ]; omega
    calc
      foldPairs pair zero (d + 1) xs =
          foldPairs pair zero (d + 1) (xs.take (2 ^ d) ++ xs.drop (2 ^ d)) := by
            rw [List.take_append_drop]
      _ = pair (foldPairs pair zero d (xs.take (2 ^ d)))
            (foldPairs pair zero d (xs.drop (2 ^ d))) :=
          foldPairs_append pair zero d _ _ ht hd
      _ = reference pair zero (d + 1) xs := by
        rw [ih _ ht, ih _ hd]; rfl

private theorem fullTree_ext (d : Nat) (xs ys : List α)
    (h : ∀ i, xs.getD i zero = ys.getD i zero) :
    fullTree zero d xs = fullTree zero d ys := by
  induction d generalizing xs ys with
  | zero =>
    simp only [fullTree]
    congr 1
    simpa only [List.headD_eq_getD] using h 0
  | succ d ih =>
    simp only [fullTree]
    congr 1
    · apply ih
      intro i
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
      by_cases hi : i < 2 ^ d
      · simpa only [hi, ite_true, ← List.getD_eq_getElem?_getD] using h i
      · simp [hi]
    · apply ih
      intro i
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_drop] using h (2 ^ d + i)

private theorem getD_append_zeros (xs : List α) (n i : Nat) :
    (xs ++ List.replicate n zero).getD i zero = xs.getD i zero := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases hi : i < xs.length
  · rw [List.getElem?_append_left hi]
  · rw [List.getElem?_append_right (by omega), List.getElem?_replicate,
      List.getElem?_eq_none (by omega)]
    split <;> rfl

private theorem reference_append_zeros (d : Nat) (xs : List α) (n : Nat) :
    reference pair zero d (xs ++ List.replicate n zero) = reference pair zero d xs := by
  unfold reference
  rw [fullTree_ext zero d _ xs (getD_append_zeros zero xs n)]

private theorem range_fold_eq (d : Nat) (xs : List α) :
    ((List.range d).foldl (fun layer _ => pairLayer pair zero layer) xs).headD zero =
      foldPairs pair zero d xs := by
  induction d generalizing xs with
  | zero => rfl
  | succ d ih =>
    rw [List.range_succ_eq_map]
    simp only [List.foldl_cons, List.foldl_map]
    change ((List.range d).foldl (fun layer _ => pairLayer pair zero layer)
      (pairLayer pair zero xs)).headD zero = _
    rw [ih, ← pairs_eq_pairLayer]
    rfl

/-- Complete equality to the fully expanded padded List pair-layer model. -/
private theorem reference_padded (d : Nat) (xs : List α) (h : xs.length ≤ 2 ^ d) :
    reference pair zero d xs = padded pair zero d xs := by
  unfold padded
  rw [range_fold_eq]
  have hl : (xs ++ List.replicate (2 ^ d-xs.length) zero).length = 2 ^ d := by
    simp only [List.length_append, List.length_replicate]
    omega
  rw [foldPairs_reference_full pair zero d _ hl, reference_append_zeros]


end Reference

section Intervals
variable {α : Type} (pair : α → α → α) (zero : α)

-- The same mathematical full tree through a pointwise ordered frontier.
private def lookupTree (f : Nat → α) : Nat → Nat → α
  | 0, start => f start
  | d + 1, start =>
    pair (lookupTree f d start) (lookupTree f d (start + 2 ^ d))

private theorem lookupTree_ext (d : Nat) (f g : Nat → α) (start : Nat)
    (h : ∀ i, i < 2 ^ d → f (start + i) = g (start + i)) :
    lookupTree pair f d start = lookupTree pair g d start := by
  induction d generalizing start with
  | zero => simpa [lookupTree] using h 0 (by decide)
  | succ d ih =>
    simp only [lookupTree]
    congr 1
    · apply ih
      intro i hi
      exact h i (by rw [Nat.pow_succ]; omega)
    · apply ih
      intro i hi
      have hh := h (2 ^ d + i) (by rw [Nat.pow_succ]; omega)
      simpa only [Nat.add_assoc] using hh

private theorem lookupTree_constant (d start : Nat) :
    lookupTree pair (fun _ => zero) d start = zeroTree pair zero d := by
  induction d generalizing start with
  | zero => rfl
  | succ d ih => simp only [lookupTree, ih, zeroTree]

private theorem reference_lookup (d : Nat) (xs : List α) (f : Nat → α) (start : Nat)
    (h : ∀ i, i < 2 ^ d → xs.getD i zero = f (start + i)) :
    reference pair zero d xs = lookupTree pair f d start := by
  induction d generalizing xs start with
  | zero => simpa only [reference, fullTree, Tree.eval, lookupTree,
      List.headD_eq_getD, Nat.add_zero] using h 0 (by decide)
  | succ d ih =>
    change pair (reference pair zero d (xs.take (2 ^ d)))
      (reference pair zero d (xs.drop (2 ^ d))) = _
    rw [lookupTree]
    congr 1
    · apply ih
      intro i hi
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_take, hi, ite_true]
        using h i (by rw [Nat.pow_succ]; omega)
    · apply ih
      intro i hi
      have hh := h (2 ^ d + i) (by rw [Nat.pow_succ]; omega)
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_assoc]
        using hh

-- The executable passes Array windows as offsets: no copied child subtrees.
-- An absent entire interval consumes one already-built zero root.
private def interval (zeros : Nat → α) (chunks : Array α) : Nat → Nat → α
  | 0, start => chunks[start]?.getD (zeros 0)
  | d + 1, start =>
    if chunks.size ≤ start then zeros (d + 1)
    else pair (interval zeros chunks d start)
      (interval zeros chunks d (start + 2 ^ d))

private theorem interval_lookup (zeros : Nat → α)
    (hz : ∀ d, zeros d = zeroTree pair zero d) (chunks : Array α) (d start : Nat) :
    interval pair zeros chunks d start =
      lookupTree pair (fun i => chunks[i]?.getD zero) d start := by
  induction d generalizing start with
  | zero => simp only [interval, lookupTree, hz, zeroTree]
  | succ d ih =>
    rw [interval]
    split
    next hs =>
      rw [hz, ← lookupTree_constant pair zero (d + 1) start]
      symm
      apply lookupTree_ext
      intro i hi
      rw [Array.getElem?_eq_none (by omega)]
      rfl
    next hs => simp only [lookupTree, ih]

private theorem interval_reference (zeros : Nat → α)
    (hz : ∀ d, zeros d = zeroTree pair zero d) (chunks : Array α) (d : Nat) :
    interval pair zeros chunks d 0 = reference pair zero d chunks.toList := by
  rw [interval_lookup pair zero zeros hz]
  symm
  apply reference_lookup
  intro i hi
  simp only [Nat.zero_add, List.getD_eq_getElem?_getD, Array.getElem?_toList]

end Intervals

private def hashPair (left right : Base.Bytes32) : Base.Bytes32 :=
  Hash.sha256 ((left.toBytes ++ right.toBytes).toByteArray)

private def zero : Base.Bytes32 := Base.FixedBytes.ofNat 0

private theorem zeroTree_eq (d : Nat) : zeroTree hashPair zero d = Ssz.zeroHash d :=
  zeroTree_model hashPair zero Ssz.zeroHash (Ssz.zeroHash_eq 0)
    (fun d => Ssz.zeroHash_eq (d + 1)) d

-- Strictly threaded recurrence for entries above the existing finite prefix.
private def extendNext {α : Type} (step : α → α) : Nat → α → List α
  | 0, _ => []
  | k + 1, current =>
    let next := step current
    next :: extendNext step k next

private theorem extendNext_model {α : Type} (step : α → α) (g : Nat → α)
    (hg : ∀ d, g (d + 1) = step (g d)) (k d : Nat) :
    extendNext step k (g d) = (List.range k).map (fun i => g (d + 1 + i)) := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    rw [extendNext, ← hg, ih]
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
    apply congrArg (List.cons (g (d + 1)))
    apply List.map_congr_left
    intro i hi
    change g (d + 1 + 1 + i) = g (d + 1 + (i + 1))
    exact congrArg g (by omega)

private def extendZeros (k : Nat) (z : Base.Bytes32) : List Base.Bytes32 :=
  extendNext (fun x => hashPair x x) k z

private theorem extendZeros_model (k d : Nat) :
    extendZeros k (Ssz.zeroHash d) =
      (List.range k).map (fun i => Ssz.zeroHash (d + 1 + i)) :=
  extendNext_model (fun x => hashPair x x) Ssz.zeroHash
    (fun d => Ssz.zeroHash_eq (d + 1)) k d

private def zeroCache (d : Nat) : Array Base.Bytes32 :=
  if d < 65 then Ssz.zeroHashes
  else Ssz.zeroHashes ++ (extendZeros (d - 64) (Ssz.zeroHash 64)).toArray

private theorem zeroCache_lookup (d i : Nat) (hi : i ≤ max d 64) :
    (zeroCache d)[i]? = some (Ssz.zeroHash i) := by
  rw [← Array.getElem?_toList]
  unfold zeroCache
  split
  next hd =>
    rw [Ssz.zeroHashes_toList]
    simp only [List.getElem?_map, List.getElem?_range (by omega : i < 65), Option.map_some]
  next hd =>
    rw [Array.toList_append, Ssz.zeroHashes_toList, List.toList_toArray, extendZeros_model]
    by_cases h : i < 65
    · rw [List.getElem?_append_left (by simpa using h)]
      simp only [List.getElem?_map, List.getElem?_range h, Option.map_some]
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_map, List.length_range, List.getElem?_map]
      rw [List.getElem?_range (by omega : i - 65 < d - 64)]
      simp only [Option.map_some]
      congr 2
      omega

private def cachedZero (cache : Array Base.Bytes32) : Nat → Base.Bytes32 :=
  fun i => match cache[i]? with
    | some z => z
    | none => Ssz.zeroHash i

private theorem cachedZero_eq (d i : Nat) :
    cachedZero (zeroCache d) i = Ssz.zeroHash i := by
  by_cases h : i ≤ max d 64
  · simp only [cachedZero, zeroCache_lookup d i h]
  · have hn : (zeroCache d)[i]? = none := by
      rw [← Array.getElem?_toList]
      apply List.getElem?_eq_none
      unfold zeroCache
      split
      next hd => rw [Ssz.zeroHashes_toList]; simp only [List.length_map, List.length_range]; omega
      next hd =>
        rw [Array.toList_append, Ssz.zeroHashes_toList, List.toList_toArray, extendZeros_model]
        simp only [List.length_append, List.length_map, List.length_range]
        omega
    simp only [cachedZero, hn]

/-- Ordered zero-padded SSZ tree on its rounded physical capacity. The proof
admits every supplied chunk, independently of a parent schema's declared count.
Locked eth-remerkleable 0.1.31 `remerkleable/tree.py:242–263`. -/
def Ssz.merkleize (chunks : Array Base.Bytes32) (limit : Nat)
    (h : chunks.size ≤ 2 ^ (if limit ≤ 1 then 0 else Nat.log2 (limit - 1) + 1)) :
    Base.Bytes32 :=
  let _ := h
  let depth := if limit ≤ 1 then 0 else Nat.log2 (limit - 1) + 1
  let cache := zeroCache depth
  interval hashPair (cachedZero cache) chunks depth 0

/-- Complete ordered padded layer equation. No field/count mix-in, schema,
source-success or hash-injectivity premise is part of this helper's contract. -/
theorem Ssz.merkleize_eq (chunks : Array Base.Bytes32) (limit : Nat)
    (h : chunks.size ≤ 2 ^ (if limit ≤ 1 then 0 else Nat.log2 (limit - 1) + 1)) :
    merkleize chunks limit h =
      let depth := if limit ≤ 1 then 0 else Nat.log2 (limit - 1) + 1
      let zero := (Base.FixedBytes.ofNat 0 : Base.Bytes32)
      let pair := fun (left right : Base.Bytes32) =>
        Hash.sha256 ((left.toBytes ++ right.toBytes).toByteArray)
      ((List.range depth).foldl
        (fun layer _ => (List.range (layer.length / 2)).map (fun i =>
          pair (layer.getD (2 * i) zero) (layer.getD (2 * i + 1) zero)))
        (chunks.toList ++ List.replicate (2 ^ depth - chunks.size) zero)).headD zero := by
  unfold merkleize
  rw [interval_reference hashPair zero _ (fun d => (cachedZero_eq _ d).trans
    (zeroTree_eq d).symm), reference_padded hashPair zero _ chunks.toList (by simpa using h)]
  rfl

end STFSpec.Codec
