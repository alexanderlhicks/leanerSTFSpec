/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Raw SSZ pack complete literal controls

Library `EthConformance`. Exactly fifteen handwritten byte cases, transcribed
literally from the closed source/model catalog; expected chunks are independent
literals. Ordinary kernel proofs compare every byte and the complete chunk order.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–4/§7.
-/

namespace STFSpec.Conformance.Codec

open STFSpec.Codec

private theorem literal_bytes (xs : List UInt8) : xs.toByteArray.toList = xs := by
  have h := Base.Bytes.toByteArray_toList (Base.Bytes.ofByteArray xs.toByteArray)
  rw [Base.Bytes.toByteArray_ofByteArray, Base.Bytes.toList_ofByteArray,
    List.toList_data_toByteArray] at h
  exact h

private theorem packP00 :
    (Ssz.pack ([] : List UInt8).toByteArray).toList.map
      (fun c ↦ c.toBytes.toList) =
      [] := by
  rw [Ssz.pack_toBytes]
  simp only [literal_bytes, List.size_toByteArray]
  decide

private theorem packP01 :
    (Ssz.pack ([165] : List UInt8).toByteArray).toList.map
      (fun c ↦ c.toBytes.toList) =
      [
    [165, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] := by
  rw [Ssz.pack_toBytes]
  simp only [literal_bytes, List.size_toByteArray]
  decide

private theorem packP31 :
    (Ssz.pack ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]
        : List UInt8).toByteArray).toList.map
      (fun c ↦ c.toBytes.toList) =
      [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
      16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 0]] := by
  rw [Ssz.pack_toBytes]
  simp only [literal_bytes, List.size_toByteArray]
  decide

private theorem packP32 :
    (Ssz.pack ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
        : List UInt8).toByteArray).toList.map
      (fun c ↦ c.toBytes.toList) =
      [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
      16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]] := by
  rw [Ssz.pack_toBytes]
  simp only [literal_bytes, List.size_toByteArray]
  decide

private theorem packP33 :
    (Ssz.pack ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    32] : List UInt8).toByteArray).toList.map
      (fun c ↦ c.toBytes.toList) =
      [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
      16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31],
    [32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] := by
  rw [Ssz.pack_toBytes]
  simp only [literal_bytes, List.size_toByteArray]
  decide

private theorem packP63 :
    (Ssz.pack ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
    48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62]
        : List UInt8).toByteArray).toList.map
      (fun c ↦ c.toBytes.toList) =
      [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
      16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31],
    [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
      48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 0]] := by
  rw [Ssz.pack_toBytes]
  simp only [literal_bytes, List.size_toByteArray]
  decide

private theorem packP64 :
    (Ssz.pack ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
    48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
        : List UInt8).toByteArray).toList.map
      (fun c ↦ c.toBytes.toList) =
      [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
      16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31],
    [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
      48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]] := by
  rw [Ssz.pack_toBytes]
  simp only [literal_bytes, List.size_toByteArray]
  decide

private theorem packP65 :
    (Ssz.pack ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
    48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
    64] : List UInt8).toByteArray).toList.map
      (fun c ↦ c.toBytes.toList) =
      [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
      16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31],
    [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
      48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63],
    [64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] := by
  rw [Ssz.pack_toBytes]
  simp only [literal_bytes, List.size_toByteArray]
  decide

private theorem packZ01 :
    (Ssz.pack ([0] : List UInt8).toByteArray).toList.map
      (fun c ↦ c.toBytes.toList) =
      [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] := by
  rw [Ssz.pack_toBytes]
  simp only [literal_bytes, List.size_toByteArray]
  decide

private theorem packZ32 :
    (Ssz.pack ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List UInt8).toByteArray).toList.map
      (fun c ↦ c.toBytes.toList) =
      [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] := by
  rw [Ssz.pack_toBytes]
  simp only [literal_bytes, List.size_toByteArray]
  decide

private theorem packZL02 :
    (Ssz.pack ([0, 165] : List UInt8).toByteArray).toList.map
      (fun c ↦ c.toBytes.toList) =
      [
    [0, 165, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] := by
  rw [Ssz.pack_toBytes]
  simp only [literal_bytes, List.size_toByteArray]
  decide

private theorem packZT02 :
    (Ssz.pack ([165, 0] : List UInt8).toByteArray).toList.map
      (fun c ↦ c.toBytes.toList) =
      [
    [165, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] := by
  rw [Ssz.pack_toBytes]
  simp only [literal_bytes, List.size_toByteArray]
  decide

private theorem packSW64 :
    (Ssz.pack ([32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
    48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
        : List UInt8).toByteArray).toList.map
      (fun c ↦ c.toBytes.toList) =
      [
    [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
      48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
      16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]] := by
  rw [Ssz.pack_toBytes]
  simp only [literal_bytes, List.size_toByteArray]
  decide

private theorem packE32 :
    (Ssz.pack ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 170, 187] : List UInt8).toByteArray).toList.map
      (fun c ↦ c.toBytes.toList) =
      [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 170, 187]] := by
  rw [Ssz.pack_toBytes]
  simp only [literal_bytes, List.size_toByteArray]
  decide

private theorem packE33 :
    (Ssz.pack ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 170,
    187] : List UInt8).toByteArray).toList.map
      (fun c ↦ c.toBytes.toList) =
      [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 170],
    [187, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] := by
  rw [Ssz.pack_toBytes]
  simp only [literal_bytes, List.size_toByteArray]
  decide

end STFSpec.Conformance.Codec
