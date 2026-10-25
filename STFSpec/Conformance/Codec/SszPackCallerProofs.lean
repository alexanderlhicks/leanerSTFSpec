/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Raw SSZ pack facade clients

Library `EthConformance`. Six private client groups use only the complete public
pack law and public Base/core contracts. Their list arithmetic is local, so the
clients cannot acquire a shortcut through private implementation proofs.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Conformance.Codec

open STFSpec.Codec

private theorem byteList_ingress (b : ByteArray) :
    (Base.Bytes.ofByteArray b).toList = b.toList := by
  rw [← Base.Bytes.toByteArray_toList, Base.Bytes.toByteArray_ofByteArray]

private theorem byteList_toByteArray (xs : List UInt8) : xs.toByteArray.toList = xs := by
  rw [← byteList_ingress, Base.Bytes.toList_ofByteArray, List.toList_data_toByteArray]

private theorem byteList_inj (a b : ByteArray) (h : a.toList = b.toList) : a = b := by
  have hb : Base.Bytes.ofByteArray a = Base.Bytes.ofByteArray b :=
    Base.Bytes.ext (by simpa only [byteList_ingress] using h)
  simpa only [Base.Bytes.toByteArray_ofByteArray] using congrArg Base.Bytes.toByteArray hb

private theorem byteList_rebuild (b : ByteArray) : b.toList.toByteArray = b := by
  apply byteList_inj
  rw [byteList_toByteArray]

private theorem byteList_length (b : ByteArray) : b.toList.length = b.size := by
  rw [← byteList_ingress, Base.Bytes.length_toList, Base.Bytes.size_ofByteArray]

/-! C1–C6: observations, size, recovery, padding, binding premise and aligned order. -/

private def packModel (xs : List UInt8) (k : Nat) : List (List UInt8) :=
  (List.range k).map (fun i ↦
    (xs.drop (32 * i)).take 32 ++
      List.replicate (32 - min 32 (xs.length - 32 * i)) 0)

private theorem pack_model (b : ByteArray) :
    (Ssz.pack b).toList.map (fun c ↦ c.toBytes.toList) =
      packModel b.toList ((b.size + 31) / 32) := by
  simpa only [packModel, byteList_length] using Ssz.pack_toBytes b

private theorem packModel_step (xs : List UInt8) (k : Nat) :
    packModel xs (k + 1) =
      (xs.take 32 ++ List.replicate (32 - min 32 xs.length) 0) ::
        packModel (xs.drop 32) k := by
  simp only [packModel, List.range_succ_eq_map, List.map_cons, List.map_map,
    Nat.mul_zero, List.drop_zero, Nat.sub_zero]
  congr 1
  apply List.map_congr_left
  intro i hi
  change (xs.drop (32 * (i + 1))).take 32 ++
      List.replicate (32 - min 32 (xs.length - 32 * (i + 1))) 0 =
    ((xs.drop 32).drop (32 * i)).take 32 ++
      List.replicate (32 - min 32 ((xs.drop 32).length - 32 * i)) 0
  rw [List.drop_drop, List.length_drop]
  rw [show 32 * (i + 1) = 32 + 32 * i by omega]
  congr 3 <;> omega

private theorem flatten_packModel (k : Nat) (xs : List UInt8) (h : xs.length ≤ 32 * k) :
    (packModel xs k).flatten = xs ++ List.replicate (32 * k - xs.length) 0 := by
  induction k generalizing xs with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
    simp [hx, packModel]
  | succ k ih =>
    rw [packModel_step, List.flatten_cons, ih _ (by simp only [List.length_drop]; omega)]
    by_cases hx : 32 ≤ xs.length
    · have hm : min 32 xs.length = 32 := Nat.min_eq_left hx
      simp only [hm, Nat.sub_self, List.replicate_zero, List.append_nil,
        ← List.append_assoc, List.take_append_drop]
      congr 2
      simp only [List.length_drop]
      omega
    · have hl : xs.length ≤ 32 := by omega
      rw [List.take_of_length_le hl, List.drop_of_length_le hl]
      simp only [List.length_nil, Nat.sub_zero, List.nil_append, Nat.min_eq_right hl,
        List.append_assoc, List.replicate_append_replicate]
      congr 2
      omega

private theorem observation_inj (a b : Array Base.Bytes32)
    (h : a.toList.map (fun c ↦ c.toBytes.toList) =
      b.toList.map (fun c ↦ c.toBytes.toList)) : a = b := by
  apply Array.toList_inj.mp
  apply (List.map_inj_right _).mp h
  intro x y hxy
  exact Base.FixedBytes.toBytes_inj.mp (Base.Bytes.toList_inj.mp hxy)

private theorem pack_count (b : ByteArray) : (Ssz.pack b).size = (b.size + 31) / 32 := by
  have h := congrArg List.length (Ssz.pack_toBytes b)
  simpa only [List.length_map, Array.length_toList, List.length_range] using h

private theorem pack_width (b : ByteArray) (c : Base.Bytes32) (_hc : c ∈ (Ssz.pack b).toList) :
    c.toBytes.toList.length = 32 := by
  exact (Base.Bytes.length_toList _).trans (Base.FixedBytes.size_toBytes _)

private theorem pack_empty : Ssz.pack ByteArray.empty = #[] := by
  apply Array.size_eq_zero_iff.mp
  rw [pack_count]
  rfl

private theorem pack_exact_multiple (b : ByteArray) (q : Nat) (h : b.size = 32 * q) :
    (Ssz.pack b).size = q := by
  rw [pack_count, h]
  omega

private theorem pack_padding (b : ByteArray) :
    ((Ssz.pack b).toList.map (fun c ↦ c.toBytes.toList)).flatten =
      b.toList ++ List.replicate (32 * ((b.size + 31) / 32) - b.size) 0 := by
  rw [pack_model, flatten_packModel _ _ (by rw [byteList_length]; omega),
    byteList_length]

private theorem pack_prefix (b : ByteArray) :
    (((Ssz.pack b).toList.map (fun c ↦ c.toBytes.toList)).flatten.take b.size) =
      b.toList := by
  rw [pack_padding, ← byteList_length b, List.take_left]

private theorem pack_prefix_adapter (b : ByteArray) :
    (Base.Bytes.ofList
      (((Ssz.pack b).toList.map (fun c ↦ c.toBytes.toList)).flatten.take b.size)).toByteArray =
      b := by
  rw [pack_prefix]
  have h : Base.Bytes.ofList b.toList = Base.Bytes.ofByteArray b := by
    apply Base.Bytes.ext
    rw [Base.Bytes.toList_ofList, byteList_ingress]
  rw [h, Base.Bytes.toByteArray_ofByteArray]

private theorem pack_window (b : ByteArray) (i : Nat) :
    let w := (Base.Bytes.ofByteArray b).extractPadded (32 * i) 32
    w.size = 32 ∧
      w.toList = (b.toList.drop (32 * i)).take 32 ++
        List.replicate (32 - min 32 (b.size - 32 * i)) 0 ∧
      ∃ c : Base.Bytes32, Base.FixedBytes.ofBytes? w = some c ∧ c.toBytes = w := by
  dsimp only
  refine ⟨Base.Bytes.size_extractPadded _ _ _, ?_, ?_⟩
  · simpa only [byteList_ingress, Base.Bytes.size_ofByteArray] using
      Base.Bytes.toList_extractPadded_window (Base.Bytes.ofByteArray b) (32 * i) 32
  · cases h : (Base.FixedBytes.ofBytes?
        ((Base.Bytes.ofByteArray b).extractPadded (32 * i) 32) : Option Base.Bytes32) with
    | none =>
      exact False.elim ((Base.FixedBytes.ofBytes?_eq_none_iff.mp h)
        (Base.Bytes.size_extractPadded _ _ _))
    | some c => exact ⟨c, rfl, (Base.FixedBytes.ofBytes?_eq_some_iff.mp h).2⟩

private theorem pack_same_length (a b : ByteArray) (hs : a.size = b.size)
    (h : Ssz.pack a = Ssz.pack b) : a = b := by
  have hp : (((Ssz.pack a).toList.map (fun c ↦ c.toBytes.toList)).flatten.take a.size) =
      (((Ssz.pack b).toList.map (fun c ↦ c.toBytes.toList)).flatten.take b.size) := by rw [h, hs]
  rw [pack_prefix, pack_prefix] at hp
  have hb : Base.Bytes.ofByteArray a = Base.Bytes.ofByteArray b :=
    Base.Bytes.ext (by simpa only [byteList_ingress] using hp)
  simpa only [Base.Bytes.toByteArray_ofByteArray] using congrArg Base.Bytes.toByteArray hb

private theorem fixed_width_flatten_inj (xs ys : List (List UInt8))
    (hx : ∀ x ∈ xs, x.length = 32) (hy : ∀ y ∈ ys, y.length = 32)
    (h : xs.flatten = ys.flatten) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have hl := congrArg List.length h
      have hw := hy y (by simp)
      simp only [List.flatten_nil, List.flatten_cons, List.length_nil, List.length_append] at hl
      omega
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hl := congrArg List.length h
      have hw := hx x (by simp)
      simp only [List.flatten_nil, List.flatten_cons, List.length_nil, List.length_append] at hl
      omega
    | cons y ys =>
      have hxl := hx x (by simp)
      have hyl := hy y (by simp)
      have he : x = y := by
        have ht := congrArg (List.take 32) h
        rw [List.flatten_cons, List.flatten_cons, List.take_left' hxl,
          List.take_left' hyl] at ht
        exact ht
      subst y
      congr 1
      apply ih ys (fun z hz ↦ hx z (by simp [hz])) (fun z hz ↦ hy z (by simp [hz]))
      exact List.append_cancel_left (by simpa only [List.flatten_cons] using h)

private theorem packed_observation_width (b : ByteArray) :
    ∀ x ∈ (Ssz.pack b).toList.map (fun c ↦ c.toBytes.toList), x.length = 32 := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  exact pack_width b c hc

private theorem byteList_append (a b : ByteArray) :
    (a ++ b).toList = a.toList ++ b.toList := by
  conv => lhs; rw [← byteList_rebuild a, ← byteList_rebuild b]
  rw [← List.toByteArray_append, byteList_toByteArray]

private theorem pack_aligned_append (a b : ByteArray) (ha : a.size % 32 = 0) :
    Ssz.pack (a ++ b) = Ssz.pack a ++ Ssz.pack b := by
  apply observation_inj
  rw [Array.toList_append, List.map_append]
  apply fixed_width_flatten_inj _ _ (packed_observation_width _)
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact packed_observation_width a x hx
    · exact packed_observation_width b x hx
  · rw [List.flatten_append, pack_padding, pack_padding, pack_padding,
      ByteArray.size_append, byteList_append]
    have hz : 32 * ((a.size + 31) / 32) - a.size = 0 := by omega
    have hr : 32 * ((a.size + b.size + 31) / 32) - (a.size + b.size) =
        32 * ((b.size + 31) / 32) - b.size := by omega
    simp only [hz, hr, List.replicate_zero, List.append_nil, List.append_assoc]

private theorem pack_full_window (b : ByteArray) (i : Nat) (h : 32 * i + 32 ≤ b.size) :
    ((Base.Bytes.ofByteArray b).extractPadded (32 * i) 32).toList =
      (b.toList.drop (32 * i)).take 32 := by
  rw [(pack_window b i).2.1]
  have hm : min 32 (b.size - 32 * i) = 32 := by omega
  simp only [hm, Nat.sub_self, List.replicate_zero, List.append_nil]

private theorem pack_final_tail (b : ByteArray) (q r : Nat)
    (h : b.size = 32 * q + r) (hr : 0 < r ∧ r < 32) :
    ((Base.Bytes.ofByteArray b).extractPadded (32 * q) 32).toList =
      b.toList.drop (32 * q) ++ List.replicate (32 - r) 0 ∧
      (Ssz.pack b).size = q + 1 := by
  constructor
  · rw [(pack_window b q).2.1]
    have hl : (b.toList.drop (32 * q)).length ≤ 32 := by
      rw [List.length_drop, byteList_length]
      omega
    rw [List.take_of_length_le hl]
    congr 2
    omega
  · rw [pack_count, h]
    omega

private theorem pack_unequal_length_counterexamples :
    Ssz.pack ([165] : List UInt8).toByteArray = Ssz.pack ([165, 0] : List UInt8).toByteArray ∧
    ([165] : List UInt8).toByteArray.size ≠ ([165, 0] : List UInt8).toByteArray.size ∧
    Ssz.pack ([0] : List UInt8).toByteArray =
      Ssz.pack ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List UInt8).toByteArray ∧
    ([0] : List UInt8).toByteArray.size ≠
      ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List UInt8).toByteArray.size := by
  refine ⟨?_, by decide, ?_, by decide⟩ <;>
    apply observation_inj <;>
    rw [Ssz.pack_toBytes, Ssz.pack_toBytes] <;>
    simp only [byteList_toByteArray, List.size_toByteArray] <;>
    decide

-- The order/boundary client observes every byte of the swapped two chunks,
-- slots30/31 and31/32, and all three chunks of the65-byte input.
private theorem pack_boundary_observations :
    (Ssz.pack ([32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
      48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
      0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
      16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
        : List UInt8).toByteArray).toList.map
      (fun c ↦ c.toBytes.toList) = [[32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
        48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63],
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]] ∧
    (Ssz.pack ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 170, 187] : List UInt8).toByteArray).toList.map
      (fun c ↦ c.toBytes.toList) = [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 170, 187]] ∧
    (Ssz.pack ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 170,
      187] : List UInt8).toByteArray).toList.map
      (fun c ↦ c.toBytes.toList) = [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 170],
      [187, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] ∧
    (Ssz.pack ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
      16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
      32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
      48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
      64] : List UInt8).toByteArray).toList.map
      (fun c ↦ c.toBytes.toList) = [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31],
      [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
        48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63],
      [64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [Ssz.pack_toBytes] <;>
    simp only [byteList_toByteArray, List.size_toByteArray] <;>
    decide

end STFSpec.Conformance.Codec
