/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Progressive SSZ symbolic facade clients

Library `EthConformance`. Complete ordered roots and arbitrary-data/depth
consequences, using only public Codec/Base/Hash laws and private List mathematics.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Conformance.Codec.ProgressiveClients

section LocalMathematics

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
  have hl : (xs ++ List.replicate (2 ^ d - xs.length) zero).length = 2 ^ d := by
    simp only [List.length_append, List.length_replicate]
    omega
  rw [foldPairs_reference_full pair zero d _ hl, reference_append_zeros]

/-- Purely mathematical covering depth; no declared-limit operation is defined here. -/
private def CoveringDepth (limit depth : Nat) : Prop :=
  limit ≤ 2 ^ depth ∧ ∀ k, k < depth → 2 ^ k < limit

private theorem covering_depth_unique {limit d e : Nat}
    (hd : CoveringDepth limit d) (he : CoveringDepth limit e) : d = e := by
  by_cases h : d < e
  · have := he.2 d h; have := hd.1; omega
  · by_cases h' : e < d
    · have := hd.2 e h'; have := he.1; omega
    · omega

private theorem covering_three : CoveringDepth 3 2 := by
  constructor
  · decide
  · intro k hk
    have h : k = 0 ∨ k = 1 := by omega
    rcases h with rfl | rfl <;> decide

private theorem covering_four : CoveringDepth 4 2 := by
  constructor
  · decide
  · intro k hk
    have h : k = 0 ∨ k = 1 := by omega
    rcases h with rfl | rfl <;> decide

/-- Counts all mathematically expanded leaves; this is not an implementation cost counter. -/
private def Tree.leafCount : Tree α → Nat
  | .leaf _ => 1
  | .fork l r => l.leafCount + r.leafCount

private theorem fullTree_leafCount (d : Nat) (xs : List α) :
    (fullTree zero d xs).leafCount = 2 ^ d := by
  induction d generalizing xs with
  | zero => rfl
  | succ d ih => simp only [fullTree, Tree.leafCount, ih, Nat.pow_succ]; omega

/-- Ordered frontier of the mathematical complete tree. -/
private def Tree.leaves : Tree α → List α
  | .leaf a => [a]
  | .fork l r => l.leaves ++ r.leaves

private theorem fullTree_leaves_full (d : Nat) (xs : List α) (h : xs.length = 2 ^ d) :
    (fullTree zero d xs).leaves = xs := by
  induction d generalizing xs with
  | zero =>
    match xs with
    | [a] => rfl
    | [] => simp at h
    | _ :: _ :: _ => simp at h
  | succ d ih =>
    have ht : (xs.take (2 ^ d)).length = 2 ^ d := by
      simp only [List.length_take]; rw [h, Nat.pow_succ]; omega
    have hd : (xs.drop (2 ^ d)).length = 2 ^ d := by
      simp only [List.length_drop]; rw [h, Nat.pow_succ]; omega
    simp only [fullTree, Tree.leaves, ih _ ht, ih _ hd, List.take_append_drop]

/-- The tree contains every admitted input leaf in order, then exactly the missing zero leaves. -/
private theorem fullTree_leaves (d : Nat) (xs : List α) (h : xs.length ≤ 2 ^ d) :
    (fullTree zero d xs).leaves = xs ++ List.replicate (2 ^ d - xs.length) zero := by
  have ht : fullTree zero d (xs ++ List.replicate (2 ^ d - xs.length) zero) =
      fullTree zero d xs := fullTree_ext zero d _ xs (getD_append_zeros zero xs _)
  rw [← ht]
  apply fullTree_leaves_full
  simp only [List.length_append, List.length_replicate]
  omega

private abbrev D (L : Nat) : Nat := if L ≤ 1 then 0 else Nat.log2 (L - 1) + 1

/-- Every natural limit has the required least covering depth. -/
private theorem covering_depth (L : Nat) : CoveringDepth L (D L) := by
  unfold D
  split
  next h =>
    exact ⟨h, by intro k hk; omega⟩
  next h =>
    have hn : L - 1 ≠ 0 := by omega
    constructor
    · have hp : L - 1 < 2 ^ (Nat.log2 (L - 1) + 1) :=
        (Nat.log2_lt hn).mp (Nat.lt_succ_self _)
      omega
    · intro k hk
      have hk' : k ≤ Nat.log2 (L - 1) := by omega
      have hp : 2 ^ k ≤ L - 1 := (Nat.le_log2 hn).mp hk'
      omega

/-- Depth is monotone on all naturals. -/
private theorem depth_mono {L M : Nat} (h : L ≤ M) : D L ≤ D M := by
  by_cases hd : D L ≤ D M
  · exact hd
  · have hp := (covering_depth L).2 (D M) (by omega)
    have hm := (covering_depth M).1
    omega

/-- Every exact power of two has its exponent as depth, including k=0. -/
private theorem depth_two_pow (k : Nat) : D (2 ^ k) = k := by
  apply covering_depth_unique (covering_depth (2 ^ k))
  constructor
  · exact Nat.le_refl _
  · intro j hj
    exact Nat.pow_lt_pow_right (by decide) hj

/-- Crossing any power-of-two boundary increases depth by one, including k=0. -/
private theorem depth_two_pow_add_one (k : Nat) : D (2 ^ k + 1) = k + 1 := by
  apply covering_depth_unique (covering_depth (2 ^ k + 1))
  constructor
  · have hp := Nat.two_pow_pos k
    rw [Nat.pow_succ]
    omega
  · intro j hj
    have hp : 2 ^ j ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    omega


private theorem reference_singleton_step {α : Type} (pair : α → α → α) (zero a : α)
    (d : Nat) : reference pair zero (d + 1) [a] =
      pair (reference pair zero d [a]) (zeroTree pair zero d) := by
  have hp : 1 ≤ 2 ^ d := Nat.two_pow_pos d
  change pair (reference pair zero d ([a].take (2 ^ d)))
    (reference pair zero d ([a].drop (2 ^ d))) = _
  rw [List.take_of_length_le (by simpa using hp),
    List.drop_eq_nil_of_le (by simpa using hp), reference_empty]

private theorem reference_ordered {α : Type} (pair : α → α → α) (zero a b c e : α) :
    reference pair zero 1 [a, b] = pair a b ∧
    reference pair zero 2 [a, b, c] = pair (pair a b) (pair c zero) ∧
    reference pair zero 2 [a, b, c, e] = pair (pair a b) (pair c e) := by
  exact ⟨rfl, rfl, rfl⟩

private theorem ordinary_padding_witness (b : α) :
    reference pair zero 2 [b] = reference pair zero 2 [b, zero] := rfl

end LocalMathematics

section Segmentation
variable {α : Type}

private def offset : Nat → Nat → Nat
  | _, 0 => 0
  | d, i + 1 => 2 ^ d + offset (d + 2) i

private theorem offset_shift (d i : Nat) : offset d (i + 1) = 2 ^ d + offset (d + 2) i := rfl

private theorem offset_sum (d i : Nat) :
    offset d i = ((List.range i).map (fun j => 2 ^ (d + 2 * j))).foldr (· + ·) 0 := by
  induction i generalizing d with
  | zero => simp [offset]
  | succ i ih =>
    rw [offset, ih, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.foldr_cons, Function.comp_def,
      Nat.mul_zero, Nat.add_zero]
    congr 1
    apply congrArg (fun f => ((List.range i).map f).foldr (· + ·) 0)
    funext j
    congr 1
    omega

private def segment (d : Nat) (xs : List α) (i : Nat) : Nat × List α :=
  (d + 2 * i, (xs.drop (offset d i)).take (2 ^ (d + 2 * i)))

private theorem segment_shift (d : Nat) (xs : List α) (i : Nat) :
    segment d xs (i + 1) = segment (d + 2) (xs.drop (2 ^ d)) i := by
  simp only [segment, offset_shift, List.drop_drop]
  have h : d + 2 * (i + 1) = d + 2 + 2 * i := by omega
  rw [h]

private def segmentsN (n d : Nat) (xs : List α) : List (Nat × List α) :=
  ((List.range n).map (segment d xs)).filter (fun s => !s.2.isEmpty)

private theorem segmentsN_step (n d : Nat) (xs : List α) :
    segmentsN (n + 1) d xs =
      (if xs.isEmpty then [] else [(d, xs.take (2 ^ d))]) ++
        segmentsN n (d + 2) (xs.drop (2 ^ d)) := by
  simp only [segmentsN, List.range_succ_eq_map, List.map_cons, List.map_map,
    Function.comp_def, segment_shift]
  have h : segment d xs 0 = (d, xs.take (2 ^ d)) := by simp [segment, offset]
  rw [h]
  cases xs with
  | nil => simp
  | cons x xs =>
    have hp : 0 < 2 ^ d := Nat.two_pow_pos d
    have ht : ¬ ((x::xs).take (2 ^ d)).isEmpty = true := by
      cases hpow : 2 ^ d with
      | zero => omega
      | succ k => simp [List.take_succ_cons]
    simp [ht]

private theorem segmentsN_nil (n d : Nat) : segmentsN n d ([] : List α) = [] := by
  simp [segmentsN, segment]

/-- Source-shaped length-founded recurrence over an arbitrary ordinary subtree function. -/
private def progressive (pair : α → α → α) (seed : α) (ordinary : Nat → List α → α)
    (d : Nat) (xs : List α) : α :=
  match xs with
  | [] => seed
  | x::xs => pair (ordinary d ((x::xs).take (2 ^ d)))
      (progressive pair seed ordinary (d + 2) ((x::xs).drop (2 ^ d)))
termination_by xs.length
decreasing_by
  simp only [List.length_drop]
  have hp := Nat.two_pow_pos d
  simp only [List.length_cons]
  omega

/-- Nonrecursive finite expression. Only nonempty ordered slices survive. -/
private def finite (pair : α → α → α) (seed : α) (ordinary : Nat → List α → α)
    (d : Nat) (xs : List α) : α :=
  (segmentsN xs.length d xs).foldr (fun s tail => pair (ordinary s.1 s.2) tail) seed

private theorem enough (pair : α → α → α) (seed : α)
    (ordinary : Nat → List α → α) (n d : Nat) (xs : List α) (h : xs.length ≤ n) :
    (segmentsN n d xs).foldr (fun s tail => pair (ordinary s.1 s.2) tail) seed =
      progressive pair seed ordinary d xs := by
  induction n generalizing d xs with
  | zero =>
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs
    simp [segmentsN_nil, progressive]
  | succ n ih =>
    cases xs with
    | nil => simp [segmentsN_nil, progressive]
    | cons x xs =>
      rw [segmentsN_step]
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.singleton_append,
        List.foldr_cons]
      rw [ih]
      · rw [progressive]
      · simp only [List.length_drop, List.length_cons] at *
        have hp := Nat.two_pow_pos d
        omega

/-- Complete equality at every finite list and natural starting depth. -/
private theorem progressive_eq_finite (pair : α → α → α) (seed : α)
    (ordinary : Nat → List α → α) (d : Nat) (xs : List α) :
    progressive pair seed ordinary d xs = finite pair seed ordinary d xs :=
  (enough pair seed ordinary xs.length d xs (Nat.le_refl _)).symm

private theorem reconstructN (n d : Nat) (xs : List α) (h : xs.length ≤ n) :
    ((segmentsN n d xs).map Prod.snd).flatten = xs := by
  induction n generalizing d xs with
  | zero =>
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs
    rfl
  | succ n ih =>
    cases xs with
    | nil => simp [segmentsN_nil]
    | cons x xs =>
      rw [segmentsN_step]
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.singleton_append,
        List.map_cons, List.flatten_cons]
      rw [ih, List.take_append_drop]
      simp only [List.length_drop, List.length_cons] at *
      have hp := Nat.two_pow_pos d
      omega

/-- Every input item is reconstructed in order; no slice is dropped or duplicated. -/
private theorem finite_segments_reconstruct (d : Nat) (xs : List α) :
    ((segmentsN xs.length d xs).map Prod.snd).flatten = xs :=
  reconstructN xs.length d xs (Nat.le_refl _)

/-- Every selected slice fits its own ordinary physical capacity. -/
private theorem finite_segments_bound (d : Nat) (xs : List α) (s : Nat × List α)
    (h : s ∈ segmentsN xs.length d xs) : s.2.length ≤ 2 ^ s.1 := by
  have hm := (List.mem_filter.mp h).1
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
  simp only [segment, List.length_take]
  exact Nat.min_le_left _ _

/-- Every natural starting depth has a positive first capacity. -/
private theorem prefix_positive (d : Nat) : 0 < 2 ^ d := Nat.two_pow_pos d

/-- Reconstruction also preserves every finite input prefix. -/
private theorem finite_prefixes (d : Nat) (xs : List α) (k : Nat) :
    (((segmentsN xs.length d xs).map Prod.snd).flatten).take k = xs.take k := by
  rw [finite_segments_reconstruct]

/-- All natural depths consume at least one item on each nonempty recursive step. -/
private theorem strict_suffix (d : Nat) (x : α) (xs : List α) :
    ((x::xs).drop (2 ^ d)).length < (x::xs).length := by
  simp only [List.length_drop, List.length_cons]
  have hp := Nat.two_pow_pos d
  omega
/-- Complete finite equation expands every private segmentation helper. -/
private theorem expanded_equation (pair : α → α → α) (seed : α)
    (ordinary : Nat → List α → α) (d : Nat) (xs : List α) :
    progressive pair seed ordinary d xs =
      (((List.range xs.length).map (fun i =>
        (d + 2 * i, (xs.drop (((List.range i).map (fun j => 2 ^ (d + 2 * j))).foldr (· + ·)
            0)).take
          (2 ^ (d + 2 * i))))).filter (fun s => !s.2.isEmpty)).foldr
        (fun s tail => pair (ordinary s.1 s.2) tail) seed := by
  rw [progressive_eq_finite]
  unfold finite segmentsN
  have hs : segment d xs = (fun i =>
      (d + 2 * i, (xs.drop (((List.range i).map (fun j => 2 ^ (d + 2 * j))).foldr (· + ·) 0)).take
        (2 ^ (d + 2 * i)))) := by
    funext i
    simp only [segment, offset_sum]
  rw [hs]

/-- Source recurrence can instead be exposed at arbitrary depth. -/
private theorem recurrence_nil (pair : α → α → α) (seed : α)
    (ordinary : Nat → List α → α) (d : Nat) :
    progressive pair seed ordinary d [] = seed := by rw [progressive]

private theorem recurrence_cons (pair : α → α → α) (seed : α)
    (ordinary : Nat → List α → α) (d : Nat) (x : α) (xs : List α) :
    progressive pair seed ordinary d (x::xs) =
      pair (ordinary d ((x::xs).take (2 ^ d)))
        (progressive pair seed ordinary (d + 2) ((x::xs).drop (2 ^ d))) := by
  rw [progressive]

/-- Recurrence-only clients can determine every result without private helpers. -/
private theorem recurrence_unique (pair : α → α → α) (seed : α)
    (ordinary : Nat → List α → α) (P Q : Nat → List α → α)
    (p0 : ∀ d, P d [] = seed) (q0 : ∀ d, Q d [] = seed)
    (ps : ∀ d x xs, P d (x::xs) = pair (ordinary d ((x::xs).take (2 ^ d)))
      (P (d + 2) ((x::xs).drop (2 ^ d))))
    (qs : ∀ d x xs, Q d (x::xs) = pair (ordinary d ((x::xs).take (2 ^ d)))
      (Q (d + 2) ((x::xs).drop (2 ^ d)))) (d : Nat) (xs : List α) : P d xs = Q d xs := by
  match xs with
  | [] => rw [p0, q0]
  | x::xs =>
    rw [ps, qs, recurrence_unique pair seed ordinary P Q p0 q0 ps qs (d + 2)
      ((x::xs).drop (2 ^ d))]
termination_by xs.length
decreasing_by exact strict_suffix d x xs

private theorem small_shapes {α : Type} (p : α → α → α) (z a b c d e f : α) :
    progressive p z (reference p z) 0 [a] = p a z ∧
    progressive p z (reference p z) 0 [a, b] =
      p a (p (p (p b z) (p z z)) z) ∧
    progressive p z (reference p z) 0 [a, b, c, d, e] =
      p a (p (p (p b c) (p d e)) z) ∧
    progressive p z (reference p z) 0 [a, b, c, d, e, f] =
      p a (p (p (p b c) (p d e)) (p (reference p z 4 [f]) z)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [progressive, List.take, List.drop]
  all_goals rfl

end Segmentation

open STFSpec.Codec

private def zero : Base.Bytes32 := Base.FixedBytes.ofNat 0

private def pair (a b : Base.Bytes32) : Base.Bytes32 :=
  Hash.sha256 ((a.toBytes ++ b.toBytes).toByteArray)

private def ordinary (d : Nat) (xs : List Base.Bytes32) : Base.Bytes32 :=
  reference pair zero d xs

private theorem public_empty (d : Nat) : Ssz.merkleizeProgressive #[] d = zero := by
  rw [Ssz.merkleizeProgressive_eq]
  rfl

private theorem public_cons (d : Nat) (x : Base.Bytes32) (xs : List Base.Bytes32) :
    Ssz.merkleizeProgressive (x :: xs).toArray d =
      pair (ordinary d ((x :: xs).take (2 ^ d)))
        (Ssz.merkleizeProgressive ((x :: xs).drop (2 ^ d)).toArray (d + 2)) := by
  rw [Ssz.merkleizeProgressive_eq]
  simp only [← Array.isEmpty_toList, List.isEmpty_cons,
    Bool.false_eq_true, ↓reduceIte]
  change pair (padded pair zero d ((x :: xs).take (2 ^ d))) _ = _
  rw [← reference_padded pair zero d _ (by simp only [List.length_take]; omega)]
  rfl

-- Entire arbitrary-array/arbitrary-depth reference, derived solely from the public law.
private theorem public_reference (chunks : Array Base.Bytes32) (d : Nat) :
    Ssz.merkleizeProgressive chunks d = progressive pair zero ordinary d chunks.toList := by
  have h := recurrence_unique pair zero ordinary
    (fun d xs => Ssz.merkleizeProgressive xs.toArray d)
    (progressive pair zero ordinary)
    (fun d => public_empty d) (recurrence_nil pair zero ordinary)
    public_cons (recurrence_cons pair zero ordinary) d chunks.toList
  simpa only [Array.toArray_toList] using h

private theorem zero_reference (d : Nat) : zeroTree pair zero d = Ssz.zeroHash d :=
  zeroTree_model pair zero Ssz.zeroHash (Ssz.zeroHash_eq 0)
    (fun d => Ssz.zeroHash_eq (d + 1)) d

private def singletonPath (a : Base.Bytes32) : Nat → Base.Bytes32
  | 0 => a
  | d + 1 => pair (singletonPath a d) (Ssz.zeroHash d)

private theorem singleton_reference (a : Base.Bytes32) (d : Nat) :
    ordinary d [a] = singletonPath a d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change reference pair zero (d + 1) [a] = _
    rw [reference_singleton_step, zero_reference]
    change pair (ordinary d [a]) (Ssz.zeroHash d) = _
    rw [ih]
    rfl

-- C1: arbitrary shifted singleton root, including source start zero.
private theorem singleton (a : Base.Bytes32) (d : Nat) :
    Ssz.merkleizeProgressive #[a] d = pair (singletonPath a d) zero := by
  rw [public_reference, progressive]
  have hp : 1 ≤ 2 ^ d := Nat.two_pow_pos d
  rw [List.take_of_length_le (by simpa using hp),
    List.drop_eq_nil_of_le (by simpa using hp), progressive, singleton_reference]

-- C0/C8: full all-input recurrence/reference and finite ordered right fold.
private theorem finite_root (chunks : Array Base.Bytes32) (d : Nat) :
    Ssz.merkleizeProgressive chunks d =
      (segmentsN chunks.size d chunks.toList).foldr
        (fun s tail => pair (ordinary s.1 s.2) tail) zero := by
  rw [public_reference, progressive_eq_finite]
  rfl

-- C3: exact reconstruction retains every complete input element, in order.
private theorem reconstruct (chunks : Array Base.Bytes32) (d : Nat) :
    ((segmentsN chunks.size d chunks.toList).map Prod.snd).flatten = chunks.toList :=
  finite_segments_reconstruct d chunks.toList

-- C4: all selected prefixes fit and every nonempty remaining suffix decreases.
private theorem local_bounds (chunks : Array Base.Bytes32) (d : Nat)
    (s : Nat × List Base.Bytes32) (h : s ∈ segmentsN chunks.size d chunks.toList)
    (a : Base.Bytes32) (xs : List Base.Bytes32) :
    s.2.length ≤ 2 ^ s.1 ∧
      ((a :: xs).drop (2 ^ d)).length < (a :: xs).length :=
  ⟨finite_segments_bound d chunks.toList s h, strict_suffix d a xs⟩

-- C5: complete ordinary padded frontier and pair fold, and actual public helper bridge.
private theorem ordinary_prefix (d : Nat) (chunks : Array Base.Bytes32) :
    let xs := chunks.toList.take (2 ^ d)
    let h : xs.toArray.size ≤ 2 ^ D (2 ^ d) := by
      rw [List.size_toArray, depth_two_pow, List.length_take]
      exact Nat.min_le_left _ _
    Ssz.merkleize xs.toArray (2 ^ d) h = ordinary d xs ∧
      (fullTree zero d xs).leaves = xs ++ List.replicate (2 ^ d - xs.length) zero ∧
      ordinary d xs = padded pair zero d xs := by
  dsimp only
  have hb : (chunks.toList.take (2 ^ d)).length ≤ 2 ^ d := by
    simp only [List.length_take]
    exact Nat.min_le_left _ _
  refine ⟨?_, fullTree_leaves zero d _ hb, reference_padded pair zero d _ hb⟩
  rw [Ssz.merkleize_eq]
  dsimp only
  rw [show (if 2 ^ d ≤ 1 then 0 else Nat.log2 (2 ^ d - 1) + 1) = d
    from depth_two_pow d]
  rw [List.toList_toArray, List.size_toArray]
  exact (reference_padded pair zero d _ hb).symm

-- C6: actual optional-call behavior and underlying first-class function type.
private theorem default_type (chunks : Array Base.Bytes32) :
    Ssz.merkleizeProgressive chunks = Ssz.merkleizeProgressive chunks 0 ∧
    ((@Ssz.merkleizeProgressive : Array Base.Bytes32 → Nat → Base.Bytes32) chunks 3) =
      Ssz.merkleizeProgressive chunks 3 := ⟨rfl, rfl⟩

private theorem shifted (a : Base.Bytes32) (d : Nat) :
    Ssz.merkleizeProgressive #[] d = zero ∧
    Ssz.merkleizeProgressive #[a] (2 * d + 1) = pair (singletonPath a (2 * d + 1)) zero ∧
    Ssz.merkleizeProgressive #[a] 64 = pair (singletonPath a 64) zero ∧
    Ssz.merkleizeProgressive #[a] 65 = pair (singletonPath a 65) zero ∧
    Ssz.merkleizeProgressive #[a] 255 = pair (singletonPath a 255) zero ∧
    Ssz.merkleizeProgressive #[a] 256 = pair (singletonPath a 256) zero :=
  ⟨public_empty d, singleton a _, singleton a _, singleton a _, singleton a _, singleton a _⟩

-- C7: complete ordered 64-byte pair preimage and local FIPS composition.
private theorem pair_preimage (a b : Base.Bytes32) :
    ((a.toBytes ++ b.toBytes).toByteArray).size = 64 ∧
    ((a.toBytes ++ b.toBytes).toByteArray).data.toList =
      a.toBytes.toList ++ b.toBytes.toList := by
  constructor
  · rw [Base.Bytes.size_toByteArray, Base.Bytes.size_append,
      Base.FixedBytes.size_toBytes, Base.FixedBytes.size_toBytes]
  · rw [Base.Bytes.toList_toByteArray, Base.Bytes.toList_append]

private theorem pair_fips (a b : Base.Bytes32) :
    Hash.Sha256.Model.DigestOnPad
      (Hash.Sha256.Model.fipsPad (a.toBytes.toList ++ b.toBytes.toList))
      (pair a b).toBytes.toList := by
  have h := Hash.Sha256.sha256_fipsDigest ((a.toBytes ++ b.toBytes).toByteArray)
    (by rw [(pair_preimage a b).1]; decide)
  rw [(pair_preimage a b).2] at h
  exact h

private theorem singleton_fips (a : Base.Bytes32) (d : Nat) :
    Hash.Sha256.Model.DigestOnPad
      (Hash.Sha256.Model.fipsPad ((singletonPath a d).toBytes.toList ++ zero.toBytes.toList))
      (Ssz.merkleizeProgressive #[a] d).toBytes.toList := by
  rw [singleton]
  exact pair_fips _ _

-- C9: a contents tree alone does not bind length. Activity/source interpretation remains prose.
-- These genuine equal-root/different-count witnesses require no collision premise.
private theorem count_witness (a b : Base.Bytes32) :
    Ssz.merkleizeProgressive #[a, b] = Ssz.merkleizeProgressive #[a, b, zero] ∧
    (#[a, b] : Array Base.Bytes32).size ≠ (#[a, b, zero] : Array Base.Bytes32).size := by
  constructor
  · rw [public_reference, public_reference]
    simp only [progressive, List.take, List.drop]
    exact congrArg (fun root => pair (ordinary 0 [a]) (pair root zero))
      (ordinary_padding_witness pair zero b)
  · change 2 ≠ 3
    decide


-- C2: complete ordered root at source boundary 1.
private theorem boundary_1 (a : Nat → Base.Bytes32) :
    Ssz.merkleizeProgressive [a 0].toArray =
      pair (ordinary 0 [a 0]) (zero) := by
  rw [public_reference]
  change progressive pair zero ordinary 0 [a 0] = _
  simp only [progressive, List.take, List.drop]

-- C2: complete ordered root at source boundary 2.
private theorem boundary_2 (a : Nat → Base.Bytes32) :
    Ssz.merkleizeProgressive [a 0, a 1].toArray =
      pair (ordinary 0 [a 0]) (pair (ordinary 2 [a 1]) (zero)) := by
  rw [public_reference]
  change progressive pair zero ordinary 0 [a 0, a 1] = _
  simp only [progressive, List.take, List.drop]

-- C2: complete ordered root at source boundary 5.
private theorem boundary_5 (a : Nat → Base.Bytes32) :
    Ssz.merkleizeProgressive [a 0, a 1, a 2, a 3, a 4].toArray =
      pair (ordinary 0 [a 0]) (pair (ordinary 2 [a 1, a 2, a 3, a 4]) (zero)) := by
  rw [public_reference]
  change progressive pair zero ordinary 0 [a 0, a 1, a 2, a 3, a 4] = _
  simp only [progressive, List.take, List.drop]

-- C2: complete ordered root at source boundary 6.
private theorem boundary_6 (a : Nat → Base.Bytes32) :
    Ssz.merkleizeProgressive [a 0, a 1, a 2, a 3, a 4, a 5].toArray =
      pair (ordinary 0 [a 0]) (pair (ordinary 2 [a 1, a 2, a 3, a 4]) (pair (ordinary 4 [a 5])
          (zero))) := by
  rw [public_reference]
  change progressive pair zero ordinary 0 [a 0, a 1, a 2, a 3, a 4, a 5] = _
  simp only [progressive, List.take, List.drop]

-- C2: complete ordered root at source boundary 21.
private theorem boundary_21 (a : Nat → Base.Bytes32) :
    Ssz.merkleizeProgressive [a 0, a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8, a 9, a 10, a 11,
        a 12, a 13, a 14, a 15, a 16, a 17, a 18, a 19, a 20].toArray =
      pair (ordinary 0 [a 0]) (pair (ordinary 2 [a 1, a 2, a 3, a 4]) (pair (ordinary 4 [a 5,
          a 6, a 7, a 8, a 9, a 10, a 11, a 12, a 13, a 14, a 15, a 16, a 17, a 18, a 19, a 20])
          (zero))) := by
  rw [public_reference]
  change progressive pair zero ordinary 0 [a 0, a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8, a 9,
      a 10, a 11, a 12, a 13, a 14, a 15, a 16, a 17, a 18, a 19, a 20] = _
  simp only [progressive, List.take, List.drop]

-- C2: complete ordered root at source boundary 22.
private theorem boundary_22 (a : Nat → Base.Bytes32) :
    Ssz.merkleizeProgressive [a 0, a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8, a 9, a 10, a 11,
        a 12, a 13, a 14, a 15, a 16, a 17, a 18, a 19, a 20, a 21].toArray =
      pair (ordinary 0 [a 0]) (pair (ordinary 2 [a 1, a 2, a 3, a 4]) (pair (ordinary 4 [a 5,
          a 6, a 7, a 8, a 9, a 10, a 11, a 12, a 13, a 14, a 15, a 16, a 17, a 18, a 19, a 20])
          (pair (ordinary 6 [a 21]) (zero)))) := by
  rw [public_reference]
  change progressive pair zero ordinary 0 [a 0, a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8, a 9,
      a 10, a 11, a 12, a 13, a 14, a 15, a 16, a 17, a 18, a 19, a 20, a 21] = _
  simp only [progressive, List.take, List.drop]

private theorem ordered_small (a b c d e f : Base.Bytes32) :
    Ssz.merkleizeProgressive #[a] = pair a zero ∧
    Ssz.merkleizeProgressive #[a, b] =
      pair a (pair (pair (pair b zero) (pair zero zero)) zero) ∧
    Ssz.merkleizeProgressive #[a, b, c, d, e] =
      pair a (pair (pair (pair b c) (pair d e)) zero) ∧
    Ssz.merkleizeProgressive #[a, b, c, d, e, f] =
      pair a (pair (pair (pair b c) (pair d e))
        (pair (singletonPath f 4) zero)) := by
  have h := small_shapes pair zero a b c d e f
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [public_reference]
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · rw [← singleton_reference]
    exact h.2.2.2

private theorem singleton_zero (a : Base.Bytes32) :
    Ssz.merkleizeProgressive #[a] = pair a zero := singleton a 0

private theorem capacities :
    2 ^ (0 + 2 * 0) = 1 ∧ 2 ^ (0 + 2 * 1) = 4 ∧
    2 ^ (0 + 2 * 2) = 16 ∧ 2 ^ (0 + 2 * 3) = 64 := by decide

end STFSpec.Conformance.Codec.ProgressiveClients
