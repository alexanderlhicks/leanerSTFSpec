/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# SSZ active-field complete mathematical controls

Library `EthConformance`. Complete ordered preimages and symbolic SHA results.
No source class admission, original execution or host/resource theorem is inferred.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7 (Q77).
-/

namespace STFSpec.Conformance.Codec.ActiveControls

open STFSpec.Codec

private def value (active : List Bool) : Nat :=
  active.foldr (fun bit n => (if bit then 1 else 0) + 2 * n) 0

private def digits (active : List Bool) : List UInt8 :=
  (List.range 32).map (fun i => UInt8.ofNat (value active >>> (8 * i)))

private def message (root : Base.Bytes32) (active : List Bool) : ByteArray :=
  (Base.Bytes.ofList (root.toBytes.toList ++ digits active)).toByteArray

private theorem mask_bytes (active : List Bool) :
    (Base.FixedBytes.ofLeNat (value active) : Base.Bytes32).toBytes.toList =
      digits active := by
  rw [Base.FixedBytes.toBytes_ofLeNat, Base.Bytes.toList_generate]
  rfl

private theorem preimage_eq (root : Base.Bytes32) (active : List Bool) :
    ((root.toBytes ++ (Base.FixedBytes.ofLeNat (value active) :
        Base.Bytes32).toBytes).toByteArray) =
      message root active := by
  apply congrArg Base.Bytes.toByteArray
  apply Base.Bytes.ext
  rw [Base.Bytes.toList_append, Base.Bytes.toList_ofList, mask_bytes]

-- P0: complete equation and all 32 mask digits; arbitrary symbolic local proof.
private theorem P0 (root : Base.Bytes32) (active : List Bool)
    (h : active.length ≤ 256) :
    Ssz.mixInActiveFields root active h = Hash.sha256 (message root active) := by
  rw [Ssz.mixInActiveFields_eq]
  exact congrArg Hash.sha256 (preimage_eq root active)

private theorem proof_independent (root : Base.Bytes32) (active : List Bool)
    (h k : active.length ≤ 256) :
    Ssz.mixInActiveFields root active h = Ssz.mixInActiveFields root active k := by
  exact (P0 root active h).trans (P0 root active k).symm

-- P1: exact ordered 64-byte preimage, retaining every zero byte.
private theorem P1 (root : Base.Bytes32) (active : List Bool) :
    (message root active).size = 64 ∧
    (message root active).data.toList = root.toBytes.toList ++
      (List.range 32).map (fun i => UInt8.ofNat (value active >>> (8 * i))) := by
  constructor
  · rw [← preimage_eq, Base.Bytes.size_toByteArray, Base.Bytes.size_append,
      Base.FixedBytes.size_toBytes, Base.FixedBytes.size_toBytes]
  · rw [message, Base.Bytes.toList_toByteArray, Base.Bytes.toList_ofList]
    rfl

private theorem false_value (n : Nat) : value (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [value, List.replicate_succ] using congrArg (2 * ·) ih

private theorem false_digits (n : Nat) :
    digits (List.replicate n false) = List.replicate 32 0 := by
  unfold digits
  rw [false_value]
  decide

-- P2: empty/allfalse mathematical masks and complete arbitrary-root SHA results.
private theorem P2 (root : Base.Bytes32) (n : Nat) (hn : n ≤ 256) :
    digits [] = List.replicate 32 0 ∧
    digits (List.replicate n false) = List.replicate 32 0 ∧
    Ssz.mixInActiveFields root [] (by simp only [List.length_nil]; decide) = Hash.sha256
        ((Base.Bytes.ofList
      (root.toBytes.toList ++ List.replicate 32 0)).toByteArray) ∧
    Ssz.mixInActiveFields root (List.replicate n false) (by simpa using hn) =
      Hash.sha256 ((Base.Bytes.ofList
        (root.toBytes.toList ++ List.replicate 32 0)).toByteArray) := by
  refine ⟨false_digits 0, false_digits n, ?_, ?_⟩
  · rw [P0, message, show digits [] = List.replicate 32 0 from false_digits 0]
  · rw [P0, message, false_digits]

private theorem value_append (xs ys : List Bool) :
    value (xs ++ ys) = value xs + 2 ^ xs.length * value ys := by
  induction xs with
  | nil => simp [value]
  | cons bit xs ih =>
    simp only [List.cons_append, value, List.foldr_cons, List.length_cons] at *
    rw [ih, Nat.pow_succ]
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm]
    omega

private theorem true_value (n : Nat) :
    value (List.replicate n true) = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp : 0 < 2 ^ n := Nat.two_pow_pos n
    change 1 + 2 * value (List.replicate n true) = 2 ^ (n + 1) - 1
    rw [ih, Nat.pow_succ]
    omega

private theorem seven_digits : digits (List.replicate 7 true) = [127] ++ List.replicate 31 0 := by
  unfold digits
  rw [true_value]
  decide

private theorem eight_digits : digits (List.replicate 8 true) = [255] ++ List.replicate 31 0 := by
  unfold digits
  rw [true_value]
  decide

private theorem nine_digits : digits (List.replicate 9 true) = [255, 1] ++ List.replicate 30 0
    := by
  unfold digits
  rw [true_value]
  decide

private theorem nineteen_digits : digits (List.replicate 19 true) = [255, 255, 7] ++
    List.replicate 29 0 := by
  unfold digits
  rw [true_value]
  decide

private theorem five_digits : digits (List.replicate 5 true) = [31] ++ List.replicate 31 0 := by
  unfold digits
  rw [true_value]
  decide

private theorem sparse_digits : digits ([true] ++ List.replicate 6 false ++ [true, true] ++
    List.replicate 246 false ++ [true]) = [129, 1] ++ List.replicate 29 0 ++ [128] := by
  have hv : value ([true] ++ List.replicate 6 false ++ [true, true] ++ List.replicate 246 false ++
      [true]) = 129 + 2 ^ 8 + 2 ^ 255 := by
    rw [value_append, value_append, value_append, value_append]
    simp only [false_value, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    decide
  unfold digits
  rw [hv]
  decide

private theorem full_digits : digits (List.replicate 256 true) = List.replicate 32 255 := by
  unfold digits
  rw [true_value]
  decide

private theorem top_digits : digits (List.replicate 255 false ++ [true]) = List.replicate 31 0 ++
    [128] := by
  unfold digits
  rw [value_append, false_value, List.length_replicate]
  decide

-- P3: complete mask bytes and full digest consequences.
private theorem P3 (root : Base.Bytes32) :
    digits (List.replicate 7 true) = [127] ++ List.replicate 31 0 ∧
    Ssz.mixInActiveFields root (List.replicate 7 true)
      (by simp only [List.length_replicate]; decide) = Hash.sha256 ((Base.Bytes.ofList
      (root.toBytes.toList ++ ([127] ++ List.replicate 31 0))).toByteArray) ∧
    digits (List.replicate 8 true) = [255] ++ List.replicate 31 0 ∧
    Ssz.mixInActiveFields root (List.replicate 8 true)
      (by simp only [List.length_replicate]; decide) = Hash.sha256 ((Base.Bytes.ofList
      (root.toBytes.toList ++ ([255] ++ List.replicate 31 0))).toByteArray) ∧
    digits (List.replicate 9 true) = [255, 1] ++ List.replicate 30 0 ∧
    Ssz.mixInActiveFields root (List.replicate 9 true)
      (by simp only [List.length_replicate]; decide) = Hash.sha256 ((Base.Bytes.ofList
      (root.toBytes.toList ++ ([255, 1] ++ List.replicate 30 0))).toByteArray) := by
  refine ⟨seven_digits, ?_, eight_digits, ?_, nine_digits, ?_⟩
  · rw [P0, message, seven_digits]
  · rw [P0, message, eight_digits]
  · rw [P0, message, nine_digits]

-- P4: complete mask bytes and full digest consequences.
private theorem P4 (root : Base.Bytes32) :
    digits (List.replicate 19 true) = [255, 255, 7] ++ List.replicate 29 0 ∧
    Ssz.mixInActiveFields root (List.replicate 19 true)
      (by simp only [List.length_replicate]; decide) = Hash.sha256 ((Base.Bytes.ofList
      (root.toBytes.toList ++ ([255, 255, 7] ++ List.replicate 29 0))).toByteArray) ∧
    digits (List.replicate 5 true) = [31] ++ List.replicate 31 0 ∧
    Ssz.mixInActiveFields root (List.replicate 5 true)
      (by simp only [List.length_replicate]; decide) = Hash.sha256 ((Base.Bytes.ofList
      (root.toBytes.toList ++ ([31] ++ List.replicate 31 0))).toByteArray) := by
  refine ⟨nineteen_digits, ?_, five_digits, ?_⟩
  · rw [P0, message, nineteen_digits]
  · rw [P0, message, five_digits]

-- P5: complete mask bytes and full digest consequences.
private theorem P5 (root : Base.Bytes32) :
    digits ([true] ++ List.replicate 6 false ++ [true, true] ++ List.replicate 246 false ++
        [true]) = [129, 1] ++ List.replicate 29 0 ++ [128] ∧
    Ssz.mixInActiveFields root ([true] ++ List.replicate 6 false ++ [true, true] ++
        List.replicate 246 false ++ [true])
      (by
        simp only [List.length_append, List.length_replicate,
          List.length_cons, List.length_nil]; decide) = Hash.sha256
        ((Base.Bytes.ofList
      (root.toBytes.toList ++ ([129, 1] ++ List.replicate 29 0 ++ [128]))).toByteArray) := by
  refine ⟨sparse_digits, ?_⟩
  · rw [P0, message, sparse_digits]

-- P6: complete mask bytes and full digest consequences.
private theorem P6 (root : Base.Bytes32) :
    digits (List.replicate 256 true) = List.replicate 32 255 ∧
    Ssz.mixInActiveFields root (List.replicate 256 true)
      (by simp only [List.length_replicate]; decide) = Hash.sha256 ((Base.Bytes.ofList
      (root.toBytes.toList ++ (List.replicate 32 255))).toByteArray) ∧
    digits (List.replicate 255 false ++ [true]) = List.replicate 31 0 ++ [128] ∧
    Ssz.mixInActiveFields root (List.replicate 255 false ++ [true])
      (by
        simp only [List.length_append, List.length_replicate,
          List.length_cons, List.length_nil]; decide) =
        Hash.sha256 ((Base.Bytes.ofList
      (root.toBytes.toList ++ (List.replicate 31 0 ++ [128]))).toByteArray) ∧
    ¬ (List.replicate 257 false).length ≤ 256 := by
  refine ⟨full_digits, ?_, top_digits, ?_, ?_⟩
  · rw [P0, message, full_digits]
  · rw [P0, message, top_digits]
  · rw [List.length_replicate]; decide

private theorem padding_value (active : List Bool) (n : Nat) :
    value (active ++ List.replicate n false) = value active := by
  rw [value_append, false_value, Nat.mul_zero, Nat.add_zero]

private theorem padding_preserves (root : Base.Bytes32) (active : List Bool)
    (n : Nat) (h : active.length ≤ 256) (k : active.length + n ≤ 256) :
    value (active ++ List.replicate n false) = value active ∧
    digits (active ++ List.replicate n false) = digits active ∧
    Ssz.mixInActiveFields root (active ++ List.replicate n false)
      (by simpa only [List.length_append, List.length_replicate] using k) =
      Ssz.mixInActiveFields root active h := by
  have hd : digits (active ++ List.replicate n false) = digits active := by
    unfold digits; rw [padding_value]
  refine ⟨padding_value active n, hd, ?_⟩
  exact (P0 root _ _).trans ((congrArg (fun bs =>
    Hash.sha256 ((Base.Bytes.ofList (root.toBytes.toList ++ bs)).toByteArray)) hd).trans
      (P0 root active h).symm)

-- P7: trailing false/padding to 256 preserves complete packing and whole result.
-- The distinct []/[false] witness is equal-preimage ambiguity, not a SHA collision.
private theorem P7 (root : Base.Bytes32) (active : List Bool)
    (h : active.length ≤ 256) :
    (∀ (n : Nat) (k : active.length + n ≤ 256),
      value (active ++ List.replicate n false) = value active ∧
      digits (active ++ List.replicate n false) = digits active ∧
      Ssz.mixInActiveFields root (active ++ List.replicate n false)
        (by simpa only [List.length_append, List.length_replicate] using k) =
        Ssz.mixInActiveFields root active h) ∧
    value (active ++ [false]) = value active ∧
    digits (active ++ List.replicate (256 - active.length) false) = digits active ∧
    Ssz.mixInActiveFields root
      (active ++ List.replicate (256 - active.length) false)
      (by simp only [List.length_append, List.length_replicate]; omega) =
      Ssz.mixInActiveFields root active h ∧
    ([] : List Bool) ≠ [false] ∧
    message root [] = message root [false] ∧
    Ssz.mixInActiveFields root [] (by decide) =
      Ssz.mixInActiveFields root [false] (by decide) := by
  refine ⟨fun n k => padding_preserves root active n h k,
    padding_value active 1, ?_, ?_, by decide, rfl, ?_⟩
  · unfold digits; rw [padding_value]
  · exact (P0 root _ _).trans ((congrArg (fun bs =>
      Hash.sha256 ((Base.Bytes.ofList (root.toBytes.toList ++ bs)).toByteArray))
      (show digits (active ++ List.replicate (256 - active.length) false) = digits active by
        unfold digits; rw [padding_value])).trans (P0 root active h).symm)
  · exact (P0 root [] (by decide)).trans (P0 root [false] (by decide)).symm

private theorem value_bound (active : List Bool) : value active < 2 ^ active.length := by
  induction active with
  | nil => decide
  | cons bit xs ih =>
    simp only [value, List.foldr_cons, List.length_cons, Nat.pow_succ] at *
    split <;> omega

private theorem bit_preserved (active : List Bool) (i : Nat) (hi : i < active.length) :
    (value active).testBit i = active[i] := by
  induction active generalizing i with
  | nil => simp at hi
  | cons bit rest ih =>
    cases i with
    | zero =>
      cases bit <;> simp [value, Nat.add_mod]
    | succ i =>
      have hr : i < rest.length := by simpa using hi
      have hd (n : Nat) : ((if bit then 1 else 0) + 2 * n) / 2 = n := by
        cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
      change (((if bit then 1 else 0) + 2 * value rest).testBit (i + 1)) = rest[i]
      rw [Nat.testBit_add_one, hd, ih i hr]

private theorem byte_bit_preserved (active : List Bool) (i : Nat) (hi : i < active.length) :
    (UInt8.ofNat (value active >>> (8 * (i / 8)))).toNat.testBit (i % 8) = active[i] := by
  rw [UInt8.toNat_ofNat', Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    Nat.div_add_mod]
  have hm : i % 8 < 8 := Nat.mod_lt i (by decide)
  simp only [hm, decide_true, Bool.true_and]
  exact bit_preserved active i hi

-- P8: width implies numeric fit; every position has its full power-of-two
-- contribution. Public Base law describes every byte without a second caller proof.
private theorem P8 (active : List Bool) (h : active.length ≤ 256)
    (front suffix : List Bool) (bit : Bool) :
    (∀ (i : Nat) (hi : i < active.length),
      (UInt8.ofNat (value active >>> (8 * (i / 8)))).toNat.testBit (i % 8) = active[i]) ∧
    value active < 2 ^ active.length ∧
    value active < 2 ^ 256 ∧
    (Base.U256.ofNat (value active)).toNat = value active ∧
    value (front ++ bit :: suffix) =
      value front + 2 ^ front.length * ((if bit then 1 else 0) + 2 * value suffix) ∧
    (Base.FixedBytes.ofLeNat (value active) : Base.Bytes32).toBytes =
      Base.Bytes.generate 32 (fun i => UInt8.ofNat (value active >>> (8 * i))) := by
  have hb : value active < 2 ^ 256 :=
    Nat.lt_of_lt_of_le (value_bound active) (Nat.pow_le_pow_right (by decide) h)
  refine ⟨byte_bit_preserved active, value_bound active, hb, Base.U256.toNat_ofNat_of_lt hb, ?_,
    Base.FixedBytes.toBytes_ofLeNat _⟩
  exact value_append front (bit :: suffix)

-- P9: complete FIPS composition on all 64 input bytes and all 32 digest bytes.
-- Source class/root meaning, guest binding and host/resource gates stay separate.
private theorem P9 (root : Base.Bytes32) (active : List Bool)
    (h : active.length ≤ 256) :
    8 * (message root active).size < 2 ^ 64 ∧
    Hash.Sha256.Model.DigestOnPad
      (Hash.Sha256.Model.fipsPad (root.toBytes.toList ++
        (List.range 32).map (fun i => UInt8.ofNat (value active >>> (8 * i)))))
      (Ssz.mixInActiveFields root active h).toBytes.toList := by
  have hb : 8 * (message root active).size < 2 ^ 64 := by rw [(P1 root active).1]; decide
  refine ⟨hb, ?_⟩
  rw [P0]
  have hf := Hash.Sha256.sha256_fipsDigest (message root active) hb
  rw [(P1 root active).2] at hf
  exact hf

end STFSpec.Conformance.Codec.ActiveControls
