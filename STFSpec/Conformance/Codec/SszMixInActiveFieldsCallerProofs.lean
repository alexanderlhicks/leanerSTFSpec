/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# SSZ active-field facade clients

Library `EthConformance`. Caller-owned structural arithmetic and complete symbolic SHA results.
No source class admission, original execution or host/resource theorem is inferred.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7 (Q77).
-/

namespace STFSpec.Conformance.Codec.ActiveClients

open STFSpec.Codec

private def number : List Bool → Nat
  | [] => 0
  | bit :: rest => (if bit then 1 else 0) + 2 * number rest

private theorem number_eq (active : List Bool) :
    number active = active.foldr (fun bit n => (if bit then 1 else 0) + 2 * n) 0 := by
  induction active with
  | nil => rfl
  | cons bit rest ih => simp only [number, List.foldr_cons, ih]

private def digits (active : List Bool) : List UInt8 :=
  (List.range 32).map (fun i => UInt8.ofNat (number active >>> (8 * i)))

private def message (root : Base.Bytes32) (active : List Bool) : ByteArray :=
  (Base.Bytes.ofList (root.toBytes.toList ++ digits active)).toByteArray

private theorem mask_bytes (active : List Bool) :
    (Base.FixedBytes.ofLeNat (number active) : Base.Bytes32).toBytes.toList =
      digits active := by
  rw [Base.FixedBytes.toBytes_ofLeNat, Base.Bytes.toList_generate]
  rfl

private theorem preimage_eq (root : Base.Bytes32) (active : List Bool) :
    ((root.toBytes ++ (Base.FixedBytes.ofLeNat (number active) :
        Base.Bytes32).toBytes).toByteArray) =
      message root active := by
  apply congrArg Base.Bytes.toByteArray
  apply Base.Bytes.ext
  rw [Base.Bytes.toList_append, Base.Bytes.toList_ofList, mask_bytes]

-- C0: complete equation and all 32 mask digits; arbitrary symbolic local proof.
private theorem C0 (root : Base.Bytes32) (active : List Bool)
    (h : active.length ≤ 256) :
    Ssz.mixInActiveFields (root := root) (active := active) (h := h) =
      Hash.sha256 (message root active) := by
  rw [Ssz.mixInActiveFields_eq, ← number_eq]
  exact congrArg Hash.sha256 (preimage_eq root active)

private theorem proof_independent (root : Base.Bytes32) (active : List Bool)
    (h k : active.length ≤ 256) :
    Ssz.mixInActiveFields root active h = Ssz.mixInActiveFields root active k := by
  exact (C0 root active h).trans (C0 root active k).symm

-- C1: exact ordered 64-byte preimage, retaining every zero byte.
private theorem C1 (root : Base.Bytes32) (active : List Bool) :
    (message root active).size = 64 ∧
    (message root active).data.toList = root.toBytes.toList ++
      (List.range 32).map (fun i => UInt8.ofNat (number active >>> (8 * i))) := by
  constructor
  · rw [← preimage_eq, Base.Bytes.size_toByteArray, Base.Bytes.size_append,
      Base.FixedBytes.size_toBytes, Base.FixedBytes.size_toBytes]
  · rw [message, Base.Bytes.toList_toByteArray, Base.Bytes.toList_ofList]
    rfl

private theorem false_number (n : Nat) : number (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [number, List.replicate_succ] using congrArg (2 * ·) ih

private theorem false_digits (n : Nat) :
    digits (List.replicate n false) = List.replicate 32 0 := by
  unfold digits
  rw [false_number]
  decide

-- C2: empty/allfalse mathematical masks and complete arbitrary-root SHA results.
private theorem C2 (root : Base.Bytes32) (n : Nat) (hn : n ≤ 256) :
    digits [] = List.replicate 32 0 ∧
    digits (List.replicate n false) = List.replicate 32 0 ∧
    Ssz.mixInActiveFields root [] (by simp only [List.length_nil]; decide) = Hash.sha256
        ((Base.Bytes.ofList
      (root.toBytes.toList ++ List.replicate 32 0)).toByteArray) ∧
    Ssz.mixInActiveFields root (List.replicate n false) (by simpa using hn) =
      Hash.sha256 ((Base.Bytes.ofList
        (root.toBytes.toList ++ List.replicate 32 0)).toByteArray) := by
  refine ⟨false_digits 0, false_digits n, ?_, ?_⟩
  · rw [C0, message, show digits [] = List.replicate 32 0 from false_digits 0]
  · rw [C0, message, false_digits]

private theorem number_append (xs ys : List Bool) :
    number (xs ++ ys) = number xs + 2 ^ xs.length * number ys := by
  induction xs with
  | nil => simp [number]
  | cons bit xs ih =>
    simp only [List.cons_append, number, List.length_cons] at *
    rw [ih, Nat.pow_succ]
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm]
    omega

private theorem true_number (n : Nat) :
    number (List.replicate n true) = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp : 0 < 2 ^ n := Nat.two_pow_pos n
    change 1 + 2 * number (List.replicate n true) = 2 ^ (n + 1) - 1
    rw [ih, Nat.pow_succ]
    omega

private theorem seven_digits : digits (List.replicate 7 true) = [127] ++ List.replicate 31 0 := by
  unfold digits
  rw [true_number]
  decide

private theorem eight_digits : digits (List.replicate 8 true) = [255] ++ List.replicate 31 0 := by
  unfold digits
  rw [true_number]
  decide

private theorem nine_digits : digits (List.replicate 9 true) = [255, 1] ++ List.replicate 30 0
    := by
  unfold digits
  rw [true_number]
  decide

private theorem nineteen_digits : digits (List.replicate 19 true) = [255, 255, 7] ++
    List.replicate 29 0 := by
  unfold digits
  rw [true_number]
  decide

private theorem five_digits : digits (List.replicate 5 true) = [31] ++ List.replicate 31 0 := by
  unfold digits
  rw [true_number]
  decide

private theorem sparse_digits : digits ([true] ++ List.replicate 6 false ++ [true, true] ++
    List.replicate 246 false ++ [true]) = [129, 1] ++ List.replicate 29 0 ++ [128] := by
  have hv : number ([true] ++ List.replicate 6 false ++ [true, true] ++ List.replicate 246
      false ++ [true]) = 129 + 2 ^ 8 + 2 ^ 255 := by
    rw [number_append, number_append, number_append, number_append]
    simp only [false_number, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    decide
  unfold digits
  rw [hv]
  decide

private theorem full_digits : digits (List.replicate 256 true) = List.replicate 32 255 := by
  unfold digits
  rw [true_number]
  decide

private theorem top_digits : digits (List.replicate 255 false ++ [true]) = List.replicate 31 0 ++
    [128] := by
  unfold digits
  rw [number_append, false_number, List.length_replicate]
  decide

-- C3: complete mask bytes and full digest consequences.
private theorem C3 (root : Base.Bytes32) :
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
  · rw [C0, message, seven_digits]
  · rw [C0, message, eight_digits]
  · rw [C0, message, nine_digits]

-- C4: complete mask bytes and full digest consequences.
private theorem C4 (root : Base.Bytes32) :
    digits (List.replicate 19 true) = [255, 255, 7] ++ List.replicate 29 0 ∧
    Ssz.mixInActiveFields root (List.replicate 19 true)
      (by simp only [List.length_replicate]; decide) = Hash.sha256 ((Base.Bytes.ofList
      (root.toBytes.toList ++ ([255, 255, 7] ++ List.replicate 29 0))).toByteArray) ∧
    digits (List.replicate 5 true) = [31] ++ List.replicate 31 0 ∧
    Ssz.mixInActiveFields root (List.replicate 5 true)
      (by simp only [List.length_replicate]; decide) = Hash.sha256 ((Base.Bytes.ofList
      (root.toBytes.toList ++ ([31] ++ List.replicate 31 0))).toByteArray) := by
  refine ⟨nineteen_digits, ?_, five_digits, ?_⟩
  · rw [C0, message, nineteen_digits]
  · rw [C0, message, five_digits]

-- C5: complete mask bytes and full digest consequences.
private theorem C5 (root : Base.Bytes32) :
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
  · rw [C0, message, sparse_digits]

-- C6: complete mask bytes and full digest consequences.
private theorem C6 (root : Base.Bytes32) :
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
  · rw [C0, message, full_digits]
  · rw [C0, message, top_digits]
  · rw [List.length_replicate]; decide

private theorem padding_number (active : List Bool) (n : Nat) :
    number (active ++ List.replicate n false) = number active := by
  rw [number_append, false_number, Nat.mul_zero, Nat.add_zero]

private theorem padding_preserves (root : Base.Bytes32) (active : List Bool)
    (n : Nat) (h : active.length ≤ 256) (k : active.length + n ≤ 256) :
    number (active ++ List.replicate n false) = number active ∧
    digits (active ++ List.replicate n false) = digits active ∧
    Ssz.mixInActiveFields root (active ++ List.replicate n false)
      (by simpa only [List.length_append, List.length_replicate] using k) =
      Ssz.mixInActiveFields root active h := by
  have hd : digits (active ++ List.replicate n false) = digits active := by
    unfold digits; rw [padding_number]
  refine ⟨padding_number active n, hd, ?_⟩
  exact (C0 root _ _).trans ((congrArg (fun bs =>
    Hash.sha256 ((Base.Bytes.ofList (root.toBytes.toList ++ bs)).toByteArray)) hd).trans
      (C0 root active h).symm)

-- C7: trailing false/padding to 256 preserves complete packing and whole result.
-- The distinct []/[false] witness is equal-preimage ambiguity, not a SHA collision.
private theorem C7 (root : Base.Bytes32) (active : List Bool)
    (h : active.length ≤ 256) :
    (∀ (n : Nat) (k : active.length + n ≤ 256),
      number (active ++ List.replicate n false) = number active ∧
      digits (active ++ List.replicate n false) = digits active ∧
      Ssz.mixInActiveFields root (active ++ List.replicate n false)
        (by simpa only [List.length_append, List.length_replicate] using k) =
        Ssz.mixInActiveFields root active h) ∧
    number (active ++ [false]) = number active ∧
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
    padding_number active 1, ?_, ?_, by decide, rfl, ?_⟩
  · unfold digits; rw [padding_number]
  · exact (C0 root _ _).trans ((congrArg (fun bs =>
      Hash.sha256 ((Base.Bytes.ofList (root.toBytes.toList ++ bs)).toByteArray))
      (show digits (active ++ List.replicate (256 - active.length) false) = digits active by
        unfold digits; rw [padding_number])).trans (C0 root active h).symm)
  · exact (C0 root [] (by decide)).trans (C0 root [false] (by decide)).symm

private theorem number_bound (active : List Bool) : number active < 2 ^ active.length := by
  induction active with
  | nil => decide
  | cons bit xs ih =>
    simp only [number, List.length_cons, Nat.pow_succ] at *
    split <;> omega

private theorem bit_preserved (active : List Bool) (i : Nat) (hi : i < active.length) :
    (number active).testBit i = active[i] := by
  induction active generalizing i with
  | nil => simp at hi
  | cons bit rest ih =>
    cases i with
    | zero =>
      cases bit <;> simp [number, Nat.add_mod]
    | succ i =>
      have hr : i < rest.length := by simpa using hi
      have hd (n : Nat) : ((if bit then 1 else 0) + 2 * n) / 2 = n := by
        cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
      change (((if bit then 1 else 0) + 2 * number rest).testBit (i + 1)) = rest[i]
      rw [Nat.testBit_add_one, hd, ih i hr]

private theorem byte_bit_preserved (active : List Bool) (i : Nat) (hi : i < active.length) :
    (UInt8.ofNat (number active >>> (8 * (i / 8)))).toNat.testBit (i % 8) = active[i] := by
  rw [UInt8.toNat_ofNat', Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    Nat.div_add_mod]
  have hm : i % 8 < 8 := Nat.mod_lt i (by decide)
  simp only [hm, decide_true, Bool.true_and]
  exact bit_preserved active i hi

-- C8: width implies numeric fit; every position has its full power-of-two
-- contribution. Public Base law describes every byte without a second caller proof.
private theorem C8 (active : List Bool) (h : active.length ≤ 256)
    (front suffix : List Bool) (bit : Bool) :
    (∀ (i : Nat) (hi : i < active.length),
      (UInt8.ofNat (number active >>> (8 * (i / 8)))).toNat.testBit (i % 8) = active[i]) ∧
    number active < 2 ^ active.length ∧
    number active < 2 ^ 256 ∧
    (Base.U256.ofNat (number active)).toNat = number active ∧
    number (front ++ bit :: suffix) =
      number front + 2 ^ front.length * ((if bit then 1 else 0) + 2 * number suffix) ∧
    (Base.FixedBytes.ofLeNat (number active) : Base.Bytes32).toBytes =
      Base.Bytes.generate 32 (fun i => UInt8.ofNat (number active >>> (8 * i))) := by
  have hb : number active < 2 ^ 256 :=
    Nat.lt_of_lt_of_le (number_bound active) (Nat.pow_le_pow_right (by decide) h)
  refine ⟨byte_bit_preserved active, number_bound active, hb, Base.U256.toNat_ofNat_of_lt hb, ?_,
    Base.FixedBytes.toBytes_ofLeNat _⟩
  exact number_append front (bit :: suffix)

-- C9: complete FIPS composition on all 64 input bytes and all 32 digest bytes.
-- Source class/root meaning, guest binding and host/resource gates stay separate.
private theorem C9 (root : Base.Bytes32) (active : List Bool)
    (h : active.length ≤ 256) :
    8 * (message root active).size < 2 ^ 64 ∧
    Hash.Sha256.Model.DigestOnPad
      (Hash.Sha256.Model.fipsPad (root.toBytes.toList ++
        (List.range 32).map (fun i => UInt8.ofNat (number active >>> (8 * i)))))
      (Ssz.mixInActiveFields root active h).toBytes.toList := by
  have hb : 8 * (message root active).size < 2 ^ 64 := by rw [(C1 root active).1]; decide
  refine ⟨hb, ?_⟩
  rw [C0]
  have hf := Hash.Sha256.sha256_fipsDigest (message root active) hb
  rw [(C1 root active).2] at hf
  exact hf

end STFSpec.Conformance.Codec.ActiveClients
