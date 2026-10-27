/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# SSZ Merkleization public-law mathematical controls

Library `EthConformance`. Complete symbolic roots, ordered padded frontiers,
all-Nat capacity and local packing/FIPS bridges, through the public facade.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Conformance.Codec

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
  have hl : (xs ++ List.replicate (2 ^ d-xs.length) zero).length = 2 ^ d := by
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
    (fullTree zero d xs).leaves = xs ++ List.replicate (2 ^ d-xs.length) zero := by
  have ht : fullTree zero d (xs ++ List.replicate (2 ^ d-xs.length) zero) =
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

end LocalMathematics

open STFSpec.Codec

private def zero : Base.Bytes32 := Base.FixedBytes.ofNat 0

private def pair (left right : Base.Bytes32) : Base.Bytes32 :=
  Hash.sha256 ((left.toBytes ++ right.toBytes).toByteArray)

private theorem zero_successor (d : Nat) :
    Ssz.zeroHash (d + 1) = pair (Ssz.zeroHash d) (Ssz.zeroHash d) :=
  Ssz.zeroHash_eq (d + 1)

private theorem zero_reference (d : Nat) : zeroTree pair zero d = Ssz.zeroHash d :=
  zeroTree_model pair zero Ssz.zeroHash (Ssz.zeroHash_eq 0) zero_successor d

-- P1: every physical-domain input, with every proof argument, has the complete reference.
private theorem public_reference (chunks : Array Base.Bytes32) (limit : Nat)
    (h : chunks.size ≤ 2 ^ D limit) :
    Ssz.merkleize chunks limit h = reference pair zero (D limit) chunks.toList := by
  rw [Ssz.merkleize_eq]
  exact (reference_padded pair zero (D limit) chunks.toList (by simpa using h)).symm

-- P0: covering and strict minimality on all naturals, powers and adjacent powers.
private theorem capacity_boundaries (limit k : Nat) :
    CoveringDepth limit (D limit) ∧ D 0 = 0 ∧ D 1 = 0 ∧
    D (2 ^ k) = k ∧ D (2 ^ k + 1) = k + 1 :=
  ⟨covering_depth limit, rfl, rfl, depth_two_pow k, depth_two_pow_add_one k⟩

private theorem same_bucket (a b d : Nat)
    (ha : a ≤ 2 ^ d ∧ ∀ k, k < d → 2 ^ k < a)
    (hb : b ≤ 2 ^ d ∧ ∀ k, k < d → 2 ^ k < b) : D a = D b := by
  exact (covering_depth_unique (covering_depth a) ha).trans
    (covering_depth_unique (covering_depth b) hb).symm

-- P2: arbitrary selected depth; this proof never evaluates deep hashes.
private theorem empty_root (limit : Nat) :
    Ssz.merkleize #[] limit (by simp) = Ssz.zeroHash (D limit) := by
  rw [public_reference, Array.toList_empty, reference_empty, zero_reference]

private theorem high_empty_roots (k : Nat) :
    Ssz.merkleize #[] (2 ^ k) (by simp) = Ssz.zeroHash k := by
  rw [empty_root, depth_two_pow]

private theorem high_depth_empty :
    Ssz.merkleize #[] (2 ^ 64) (by simp) = Ssz.zeroHash 64 ∧
    Ssz.merkleize #[] (2 ^ 65) (by simp) = Ssz.zeroHash 65 ∧
    Ssz.merkleize #[] (2 ^ 255) (by simp) = Ssz.zeroHash 255 ∧
    Ssz.merkleize #[] (2 ^ 256) (by simp) = Ssz.zeroHash 256 :=
  ⟨high_empty_roots 64, high_empty_roots 65, high_empty_roots 255, high_empty_roots 256⟩

private theorem reference_singleton_succ (d : Nat) (a : Base.Bytes32) :
    reference pair zero (d + 1) [a] =
      pair (reference pair zero d [a]) (Ssz.zeroHash d) := by
  rw [reference_singleton_step, zero_reference]

private def singletonPath (a : Base.Bytes32) : Nat → Base.Bytes32
  | 0 => a
  | d + 1 => pair (singletonPath a d) (Ssz.zeroHash d)

private theorem singleton_reference (a : Base.Bytes32) (d : Nat) :
    reference pair zero d [a] = singletonPath a d := by
  induction d with
  | zero => rfl
  | succ d ih => rw [reference_singleton_succ, ih]; rfl

-- P3: the entire singleton expression at arbitrary depth, plus physical depth zero.
private theorem singleton_root (a : Base.Bytes32) (limit : Nat) :
    Ssz.merkleize #[a] limit (Nat.two_pow_pos _) = singletonPath a (D limit) := by
  rw [public_reference]
  exact singleton_reference a (D limit)

private theorem depth_zero_roots (a : Base.Bytes32) :
    Ssz.merkleize #[] 0 (by change 0 ≤ 1; decide) = zero ∧
    Ssz.merkleize #[] 1 (by change 0 ≤ 1; decide) = zero ∧
    Ssz.merkleize #[a] 0 (by change 1 ≤ 1; decide) = a ∧
    Ssz.merkleize #[a] 1 (by change 1 ≤ 1; decide) = a := by
  constructor
  · rw [public_reference]; rfl
  constructor
  · rw [public_reference]; rfl
  constructor <;> rw [public_reference] <;> rfl

-- P4: ordered whole roots, including count four at declared limit three.
private theorem ordered_roots (a b c d : Base.Bytes32) :
    Ssz.merkleize #[a, b] 2 (by change 2 ≤ 2; decide) = pair a b ∧
    Ssz.merkleize #[a, b, c] 3 (by change 3 ≤ 4; decide) = pair (pair a b) (pair c zero) ∧
    Ssz.merkleize #[a, b, c] 4 (by change 3 ≤ 4; decide) = pair (pair a b) (pair c zero) ∧
    Ssz.merkleize #[a, b, c, d] 3 (by change 4 ≤ 4; decide) = pair (pair a b) (pair c d) ∧
    Ssz.merkleize #[a, b, c, d] 4 (by change 4 ≤ 4; decide) = pair (pair a b) (pair c d) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [public_reference]
  · exact (reference_ordered pair zero a b c d).1
  · exact (reference_ordered pair zero a b c d).2.1
  · exact (reference_ordered pair zero a b c d).2.1
  · exact (reference_ordered pair zero a b c d).2.2
  · exact (reference_ordered pair zero a b c d).2.2

-- P5: complete ordered frontier, then exact even-layer halving and one final root.
private theorem ordered_frontier (chunks : Array Base.Bytes32) (limit : Nat)
    (h : chunks.size ≤ 2 ^ D limit) :
    (fullTree zero (D limit) chunks.toList).leaves =
      chunks.toList ++ List.replicate (2 ^ D limit - chunks.size) zero := by
  simpa only [Array.length_toList] using fullTree_leaves zero (D limit) chunks.toList h

private def layers : Nat → List Base.Bytes32 → List Base.Bytes32
  | 0, xs => xs
  | k + 1, xs => layers k (pairs pair xs)

private theorem layers_count (k d : Nat) (xs : List Base.Bytes32)
    (h : xs.length = 2 ^ (d + k)) : (layers k xs).length = 2 ^ d := by
  induction k generalizing xs with
  | zero => simpa [layers] using h
  | succ k ih =>
    apply ih
    rw [pairs_length, h, show d + (k + 1) = (d + k) + 1 by omega, Nat.pow_succ]
    omega

private theorem layer_shape (d : Nat) (xs : List Base.Bytes32)
    (h : xs.length = 2 ^ (d + 1)) :
    xs.length % 2 = 0 ∧ (pairs pair xs).length = 2 ^ d ∧
    pairLayer pair zero xs = pairs pair xs := by
  refine ⟨?_, ?_, (pairs_eq_pairLayer pair zero xs).symm⟩
  · rw [h, Nat.pow_succ]; omega
  · rw [pairs_length, h, Nat.pow_succ]; omega

private theorem final_root (chunks : Array Base.Bytes32) (limit : Nat)
    (h : chunks.size ≤ 2 ^ D limit) :
    layers (D limit)
      (chunks.toList ++ List.replicate (2 ^ D limit - chunks.size) zero) =
        [Ssz.merkleize chunks limit h] := by
  have hl : (chunks.toList ++ List.replicate (2 ^ D limit - chunks.size) zero).length =
      2 ^ (0 + D limit) := by simp only [List.length_append, Array.length_toList,
        List.length_replicate, Nat.zero_add]; omega
  have hc := layers_count (D limit) 0 _ hl
  have he : ∀ k xs, (layers k xs).headD zero = foldPairs pair zero k xs := by
    intro k xs
    induction k generalizing xs with
    | zero => rfl
    | succ k ih => exact ih _
  have hr : (layers (D limit)
      (chunks.toList ++ List.replicate (2 ^ D limit - chunks.size) zero)).headD zero =
      Ssz.merkleize chunks limit h := by
    rw [he, public_reference, reference_padded pair zero _ _ (by simpa using h),
      padded, range_fold_eq, Array.length_toList]
  have hlen : (layers (D limit)
      (chunks.toList ++ List.replicate (2 ^ D limit - chunks.size) zero)).length = 1 := hc
  generalize layers (D limit)
    (chunks.toList ++ List.replicate (2 ^ D limit - chunks.size) zero) = xs at *
  cases xs with
  | nil => simp at hlen
  | cons x xs =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst xs
    exact congrArg (fun x => [x]) hr

-- P6: proof independence and arbitrary same-capacity reindexing.
private theorem reindex (chunks : Array Base.Bytes32) (a b : Nat)
    (ha : chunks.size ≤ 2 ^ D a) (hb : chunks.size ≤ 2 ^ D b)
    (hd : D a = D b) : Ssz.merkleize chunks a ha = Ssz.merkleize chunks b hb := by
  rw [public_reference, public_reference, hd]

private theorem capacity_reindex (chunks : Array Base.Bytes32) (a b : Nat)
    (ha : chunks.size ≤ 2 ^ D a) (hb : chunks.size ≤ 2 ^ D b)
    (hc : 2 ^ D a = 2 ^ D b) : Ssz.merkleize chunks a ha = Ssz.merkleize chunks b hb := by
  apply reindex chunks a b ha hb
  by_cases h : D a < D b
  · have hp : 2 ^ D a < 2 ^ D b := Nat.pow_lt_pow_right (by decide) h
    omega
  · by_cases h' : D b < D a
    · have hp : 2 ^ D b < 2 ^ D a := Nat.pow_lt_pow_right (by decide) h'
      omega
    · omega

private theorem proof_independent (chunks : Array Base.Bytes32) (limit : Nat)
    (h k : chunks.size ≤ 2 ^ D limit) :
    Ssz.merkleize chunks limit h = Ssz.merkleize chunks limit k := rfl

-- P7: unequal counts can have equal entire roots without any collision assumption.
private theorem zero_padding_witness (a : Base.Bytes32) :
    Ssz.merkleize #[a] 2 (by change 1 ≤ 2; decide) =
      Ssz.merkleize #[a, zero] 2 (by change 2 ≤ 2; decide) ∧
    (#[a] : Array Base.Bytes32).size ≠ (#[a, zero] : Array Base.Bytes32).size := by
  constructor
  · rw [public_reference, public_reference]; rfl
  · change 1 ≠ 2; decide

private theorem domain_impossibility (a b c d e : Base.Bytes32) :
    ¬ (#[a, b, c, d, e] : Array Base.Bytes32).size ≤ 2 ^ D 3 ∧
    ¬ (#[a, b] : Array Base.Bytes32).size ≤ 2 ^ D 0 ∧
    ¬ (#[a, b] : Array Base.Bytes32).size ≤ 2 ^ D 1 := by
  change ¬5 ≤ 4 ∧ ¬2 ≤ 1 ∧ ¬2 ≤ 1
  decide

-- P8: every ordered pair preimage and the complete public FIPS composition.
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

private theorem two_root_fips (a b : Base.Bytes32) :
    Hash.Sha256.Model.DigestOnPad
      (Hash.Sha256.Model.fipsPad (a.toBytes.toList ++ b.toBytes.toList))
      (Ssz.merkleize #[a, b] 2 (by change 2 ≤ 2; decide)).toBytes.toList := by
  rw [(ordered_roots a b a b).1]
  exact pair_fips a b

-- P9: actual parent byte-count/packing bridge, with stronger declared admission.
private theorem packed_count (b : ByteArray) : (Ssz.pack b).size = (b.size + 31) / 32 := by
  have h := congrArg List.length (Ssz.pack_toBytes b)
  simpa only [List.length_map, Array.length_toList, List.length_range] using h

private theorem admitted_packing (b : ByteArray) (declared : Nat) (h : b.size ≤ declared) :
    (Ssz.pack b).size ≤ 2 ^ D ((declared + 31) / 32) := by
  rw [packed_count]
  exact Nat.le_trans (by omega) (covering_depth _).1

private theorem physical_vs_declared (a b c : ByteArray)
    (ha : a.size = 31) (hb : b.size = 32) (hc : c.size = 33) :
    (Ssz.pack a).size ≤ 2 ^ D ((31 + 31) / 32) ∧
    (Ssz.pack b).size ≤ 2 ^ D ((31 + 31) / 32) ∧
    ¬ b.size ≤ 31 ∧ ¬ (Ssz.pack c).size ≤ 2 ^ D ((32 + 31) / 32) := by
  rw [packed_count, packed_count, packed_count, ha, hb, hc]
  decide

end STFSpec.Conformance.Codec
