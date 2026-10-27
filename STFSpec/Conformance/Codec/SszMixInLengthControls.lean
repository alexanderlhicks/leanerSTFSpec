/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# SSZ length mix-in complete mathematical controls

Library `EthConformance`. Full preimages and symbolic digests, local consumer
bounds and FIPS composition. No original source execution or host claim.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7 (Q76).
-/

namespace STFSpec.Conformance.Codec.LengthControls

open STFSpec.Codec

variable {α : Type}

private def digits (n : Nat) : List UInt8 :=
  (List.range 32).map (fun i => UInt8.ofNat (n >>> (8 * i)))

private def message (root : Base.Bytes32) (n : Nat) : ByteArray :=
  (Base.Bytes.ofList (root.toBytes.toList ++ digits n)).toByteArray

private theorem count_bytes (n : Nat) :
    (Base.FixedBytes.ofLeNat n : Base.Bytes32).toBytes.toList = digits n := by
  rw [Base.FixedBytes.toBytes_ofLeNat, Base.Bytes.toList_generate]
  rfl

private theorem preimage_eq (root : Base.Bytes32) (n : Nat) :
    ((root.toBytes ++ (Base.FixedBytes.ofLeNat n : Base.Bytes32).toBytes).toByteArray) =
      message root n := by
  apply congrArg Base.Bytes.toByteArray
  apply Base.Bytes.ext
  rw [Base.Bytes.toList_append, Base.Bytes.toList_ofList, count_bytes]

-- P0: all admitted inputs, the public equation and complete List-byte reference.
private theorem lengthP0 (root : Base.Bytes32) (n : Nat) (h : n < 2 ^ 256) :
    Ssz.mixInLength root n h = Hash.sha256 (message root n) := by
  rw [Ssz.mixInLength_eq, preimage_eq]

-- P1: the exact ordered 64-byte preimage, retaining every zero.
private theorem lengthP1 (root : Base.Bytes32) (n : Nat) :
    (message root n).size = 64 ∧
    (message root n).data.toList = root.toBytes.toList ++
      (List.range 32).map (fun i => UInt8.ofNat (n >>> (8 * i))) := by
  constructor
  · rw [← preimage_eq, Base.Bytes.size_toByteArray, Base.Bytes.size_append,
      Base.FixedBytes.size_toBytes, Base.FixedBytes.size_toBytes]
  · rw [message, Base.Bytes.toList_toByteArray, Base.Bytes.toList_ofList]
    rfl

private theorem digit_cases :
    digits 0 = List.replicate 32 0 ∧
    digits 1 = [1] ++ List.replicate 31 0 ∧
    digits 255 = [255] ++ List.replicate 31 0 ∧
    digits 256 = [0, 1] ++ List.replicate 30 0 ∧
    digits (2 ^ 256 - 1) = List.replicate 32 255 := by decide

-- P2: complete zero/one SHA expressions at an arbitrary root.
private theorem lengthP2 (root : Base.Bytes32) :
    Ssz.mixInLength root 0 (by decide) =
      Hash.sha256 ((Base.Bytes.ofList (root.toBytes.toList ++ List.replicate 32 0)).toByteArray) ∧
    Ssz.mixInLength root 1 (by decide) =
      Hash.sha256 ((Base.Bytes.ofList (root.toBytes.toList ++ ([1] ++ List.replicate 31
          0))).toByteArray) := by
  constructor <;> rw [lengthP0, message]
  · rw [digit_cases.1]
  · rw [digit_cases.2.1]

-- P3: complete byte-order transition, not a selected-byte observation.
private theorem lengthP3 (root : Base.Bytes32) :
    Ssz.mixInLength root 255 (by decide) =
      Hash.sha256 ((Base.Bytes.ofList (root.toBytes.toList ++ ([255] ++ List.replicate 31
          0))).toByteArray) ∧
    Ssz.mixInLength root 256 (by decide) =
      Hash.sha256 ((Base.Bytes.ofList (root.toBytes.toList ++ ([0, 1] ++ List.replicate 30
          0))).toByteArray) := by
  constructor <;> rw [lengthP0, message]
  · rw [digit_cases.2.2.1]
  · rw [digit_cases.2.2.2.1]

-- P4: highest admitted count and the exact excluded boundary.
private theorem lengthP4 (root : Base.Bytes32) :
    Ssz.mixInLength root (2 ^ 256 - 1) (by decide) =
      Hash.sha256 ((Base.Bytes.ofList (root.toBytes.toList ++ List.replicate 32
          255)).toByteArray) ∧
    ¬ (2 ^ 256 < (2 ^ 256 : Nat)) := by
  constructor
  · rw [lengthP0, message, digit_cases.2.2.2.2]
  · exact Nat.lt_irrefl _

-- P5: proofs and exact input equalities transport the whole result.
private theorem lengthP5 (root other : Base.Bytes32) (n m : Nat)
    (h : n < 2 ^ 256) (k : m < 2 ^ 256) (hr : root = other) (hn : n = m) :
    Ssz.mixInLength root n h = Ssz.mixInLength other m k := by
  rw [Ssz.mixInLength_eq, Ssz.mixInLength_eq, hr, hn]

private theorem proof_independent (root : Base.Bytes32) (n : Nat)
    (h k : n < 2 ^ 256) : Ssz.mixInLength root n h = Ssz.mixInLength root n k :=
  lengthP5 root root n n h k rfl rfl

-- P6: the fixed 512-bit FIPS premise is independent of the count bound.
private theorem lengthP6 (root : Base.Bytes32) (n : Nat) (h : n < 2 ^ 256) :
    8 * (message root n).size < 2 ^ 64 ∧
    Hash.Sha256.Model.DigestOnPad
      (Hash.Sha256.Model.fipsPad (root.toBytes.toList ++
        (List.range 32).map (fun i => UInt8.ofNat (n >>> (8 * i)))))
      (Ssz.mixInLength root n h).toBytes.toList := by
  have hb : 8 * (message root n).size < 2 ^ 64 := by rw [(lengthP1 root n).1]; decide
  refine ⟨hb, ?_⟩
  rw [lengthP0]
  have hf := Hash.Sha256.sha256_fipsDigest (message root n) hb
  rw [(lengthP1 root n).2] at hf
  exact hf

private def listConsumer (root : Base.Bytes32) (xs : List α) (h : xs.length < 2 ^ 256) :
    Base.Bytes32 := Ssz.mixInLength root xs.length h

private def bytesConsumer (root : Base.Bytes32) (b : Base.Bytes) (h : b.size < 2 ^ 256) :
    Base.Bytes32 := Ssz.mixInLength root b.size h

-- P7: actual natural sizes are passed directly with exactly their own bound.
private theorem lengthP7 (root : Base.Bytes32) (xs : List α) (b : Base.Bytes)
    (hx : xs.length < 2 ^ 256) (hb : b.size < 2 ^ 256) :
    listConsumer root xs hx = Hash.sha256 ((Base.Bytes.ofList
      (root.toBytes.toList ++ (List.range 32).map
        (fun i => UInt8.ofNat (xs.length >>> (8 * i))))).toByteArray) ∧
    bytesConsumer root b hb = Hash.sha256 ((Base.Bytes.ofList
      (root.toBytes.toList ++ (List.range 32).map
        (fun i => UInt8.ofNat (b.size >>> (8 * i))))).toByteArray) :=
  ⟨lengthP0 root xs.length hx, lengthP0 root b.size hb⟩

-- P8: range proof supplies the intended numeric U256 observation, without wrapping admission.
private theorem lengthP8 (root : Base.Bytes32) (n : Nat) (h : n < 2 ^ 256) :
    (Base.U256.ofNat n).toNat = n ∧
    Ssz.mixInLength root (Base.U256.ofNat n).toNat (Base.U256.toNat_lt _) =
      Ssz.mixInLength root n h := by
  have hn := Base.U256.toNat_ofNat_of_lt h
  exact ⟨hn, lengthP5 root root _ n (Base.U256.toNat_lt _) h rfl hn⟩

-- P9: boundary and larger counts have no proof argument, not a runtime result.
-- Source order/backings, rootability, active fields and collision freedom remain separate.
private theorem lengthP9 (n : Nat) (h : 2 ^ 256 ≤ n) : ¬ n < 2 ^ 256 := by omega

end STFSpec.Conformance.Codec.LengthControls
