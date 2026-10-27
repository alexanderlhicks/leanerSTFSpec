/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.SszMerkleize

/-!
# Progressive SSZ contents trees

Library `EthCodec`. Disjoint packed ordinary subtrees refine a readable
length-founded recurrence at every natural starting depth.
Reference: locked eth-remerkleable 0.1.31 `remerkleable/progressive.py:25–32`.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Codec

private def progressivePair (left right : Base.Bytes32) : Base.Bytes32 :=
  Hash.sha256 ((left.toBytes ++ right.toBytes).toByteArray)

private def progressiveZero : Base.Bytes32 := Base.FixedBytes.ofNat 0

/-- Readable ordered padded ordinary subtree; mathematical reference only. -/
private def progressiveOrdinary (depth : Nat) (xs : List Base.Bytes32) : Base.Bytes32 :=
  ((List.range depth).foldl
    (fun layer _ => (List.range (layer.length / 2)).map (fun i =>
      progressivePair (layer.getD (2 * i) progressiveZero)
        (layer.getD (2 * i + 1) progressiveZero)))
    (xs ++ List.replicate (2 ^ depth - xs.length) progressiveZero)).headD progressiveZero

/-- Source-shaped recurrence, separate from the packed executable traversal. -/
private def progressiveReference (depth : Nat) (xs : List Base.Bytes32) : Base.Bytes32 :=
  match xs with
  | [] => progressiveZero
  | x :: xs =>
    progressivePair (progressiveOrdinary depth ((x :: xs).take (2 ^ depth)))
      (progressiveReference (depth + 2) ((x :: xs).drop (2 ^ depth)))
termination_by xs.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  have hp := Nat.two_pow_pos depth
  omega

private theorem progressiveReference_eq (depth : Nat) (xs : List Base.Bytes32) :
    progressiveReference depth xs =
      if xs.isEmpty then progressiveZero else
        progressivePair (progressiveOrdinary depth (xs.take (2 ^ depth)))
          (progressiveReference (depth + 2) (xs.drop (2 ^ depth))) := by
  cases xs with
  | nil =>
    conv => lhs; rw [progressiveReference]
    rfl
  | cons x xs =>
    conv => lhs; rw [progressiveReference]
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]

private abbrev progressiveDepth (limit : Nat) : Nat :=
  if limit ≤ 1 then 0 else Nat.log2 (limit - 1) + 1

private theorem progressiveDepth_power (depth : Nat) : progressiveDepth (2 ^ depth) = depth := by
  cases depth with
  | zero => rfl
  | succ d =>
    have hp := Nat.two_pow_pos d
    have hn : 2 ^ (d + 1) - 1 ≠ 0 := by rw [Nat.pow_succ]; omega
    have hlo : 2 ^ d ≤ 2 ^ (d + 1) - 1 := by rw [Nat.pow_succ]; omega
    have hhi : 2 ^ (d + 1) - 1 < 2 ^ (d + 1) := by omega
    have hlog : Nat.log2 (2 ^ (d + 1) - 1) = d := by
      have h1 := (Nat.le_log2 hn).mpr hlo
      have h2 := (Nat.log2_lt hn).mpr hhi
      omega
    simp only [progressiveDepth]
    rw [ite_eq_right (by rw [Nat.pow_succ]; omega), hlog]

private theorem progressiveWindow_bound (chunks : Array Base.Bytes32) (start depth : Nat) :
    (chunks.extract start (start + 2 ^ depth)).size ≤
      2 ^ progressiveDepth (2 ^ depth) := by
  rw [progressiveDepth_power, Array.size_extract]
  have hp := Nat.two_pow_pos depth
  omega

private theorem progressiveWindow_model (chunks : Array Base.Bytes32) (start depth : Nat) :
    Ssz.merkleize (chunks.extract start (start + 2 ^ depth)) (2 ^ depth)
      (progressiveWindow_bound chunks start depth) =
        progressiveOrdinary depth ((chunks.toList.drop start).take (2 ^ depth)) := by
  rw [Ssz.merkleize_eq]
  dsimp only
  rw [show (if 2 ^ depth ≤ 1 then 0 else Nat.log2 (2 ^ depth - 1) + 1) = depth
    from progressiveDepth_power depth]
  simp only [progressiveOrdinary, Array.size_eq_length_toList, Array.toList_extract,
    List.extract_eq_take_drop, Nat.add_sub_cancel_left]
  rfl

/-- Only the current disjoint prefix is copied; the remaining suffix stays an offset.
The ordinary provider handles sparse holes and its own zero-cache extension. -/
private def progressivePacked (chunks : Array Base.Bytes32) (start depth : Nat) : Base.Bytes32 :=
  if start < chunks.size then
    progressivePair
      (Ssz.merkleize (chunks.extract start (start + 2 ^ depth)) (2 ^ depth)
        (progressiveWindow_bound chunks start depth))
      (progressivePacked chunks (start + 2 ^ depth) (depth + 2))
  else progressiveZero
termination_by chunks.size - start
decreasing_by
  have hp := Nat.two_pow_pos depth
  omega

/-- Complete executable/reference refinement, including arbitrary offsets and depths. -/
private theorem progressivePacked_reference (chunks : Array Base.Bytes32) (start depth : Nat) :
    progressivePacked chunks start depth =
      progressiveReference depth (chunks.toList.drop start) := by
  rw [progressivePacked, progressiveReference_eq]
  by_cases hs : start < chunks.size
  · have he : (chunks.toList.drop start).isEmpty = false := by
      simp only [List.isEmpty_eq_false_iff, List.ne_nil_iff_length_pos,
        List.length_drop, Array.length_toList]
      omega
    simp only [hs, he, Bool.false_eq_true, ↓reduceIte]
    rw [progressiveWindow_model,
      progressivePacked_reference chunks (start + 2 ^ depth) (depth + 2), List.drop_drop]
  · have he : chunks.toList.drop start = [] :=
      List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_gt hs)
    rw [ite_eq_right hs, he]
    rfl
termination_by chunks.size - start
decreasing_by
  have hp := Nat.two_pow_pos depth
  omega

/-- Progressive SSZ contents tree, with optional source starting depth.
Empty input returns the zero chunk at every depth. No length/activity mix-in
or source-node/host-success assertion is part of this operation.
Locked eth-remerkleable 0.1.31 `remerkleable/progressive.py:25–32`. -/
def Ssz.merkleizeProgressive (chunks : Array Base.Bytes32) (depth : Nat := 0) :
    Base.Bytes32 :=
  progressivePacked chunks 0 depth

/-- Complete ordered ordinary-prefix recurrence at every natural starting depth.
Slicing supplies ordinary physical capacity without an extra caller premise. -/
theorem Ssz.merkleizeProgressive_eq (chunks : Array Base.Bytes32) (depth : Nat) :
    merkleizeProgressive chunks depth =
      let zero := (Base.FixedBytes.ofNat 0 : Base.Bytes32)
      let pair := fun (left right : Base.Bytes32) =>
        STFSpec.Hash.sha256 ((left.toBytes ++ right.toBytes).toByteArray)
      if chunks.isEmpty then zero else
        let «prefix» := chunks.toList.take (2 ^ depth)
        let root := ((List.range depth).foldl
          (fun layer _ => (List.range (layer.length / 2)).map (fun i =>
            pair (layer.getD (2 * i) zero) (layer.getD (2 * i + 1) zero)))
          («prefix» ++ List.replicate (2 ^ depth - «prefix».length) zero)).headD zero
        pair root
          (merkleizeProgressive ((chunks.toList.drop (2 ^ depth)).toArray) (depth + 2)) := by
  simp only [merkleizeProgressive, progressivePacked_reference, List.drop_zero]
  rw [progressiveReference_eq, Array.isEmpty_toList]
  rfl

end STFSpec.Codec
