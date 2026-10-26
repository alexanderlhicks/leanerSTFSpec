/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# SSZ length mix-in facade clients

Library `EthConformance`. Caller-owned full-byte references and consequences
use only the public mix-in equation and public Base/Hash laws. Hashes remain
symbolic; source classes, actual decoded count bounds and host success are separate.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7 (Q76).
-/

namespace STFSpec.Conformance.Codec.LengthClients

open STFSpec.Codec

private def countDigits (n : Nat) : List UInt8 :=
  (List.range 32).map (fun i => UInt8.ofNat (n >>> (8 * i)))

private def preimage (root : Base.Bytes32) (n : Nat) : Base.Bytes :=
  root.toBytes ++ (Base.FixedBytes.ofLeNat n : Base.Bytes32).toBytes

private theorem preimage_bytes (root : Base.Bytes32) (n : Nat) :
    (preimage root n).toList = root.toBytes.toList ++ countDigits n := by
  rw [preimage, Base.Bytes.toList_append, Base.FixedBytes.toBytes_ofLeNat,
    Base.Bytes.toList_generate]
  rfl

-- C0: whole root equality to a complete independently assembled List-byte reference.
private theorem C0 (root : Base.Bytes32) (n : Nat) (h : n < 2 ^ 256) :
    Ssz.mixInLength (root := root) (len := n) (h := h) = Hash.sha256 ((Base.Bytes.ofList
      (root.toBytes.toList ++ countDigits n)).toByteArray) := by
  rw [Ssz.mixInLength_eq]
  apply congrArg Hash.sha256
  apply congrArg Base.Bytes.toByteArray
  apply Base.Bytes.ext
  exact (preimage_bytes root n).trans (Base.Bytes.toList_ofList _).symm

-- C1: all root bytes followed by all low-to-high count bytes, exactly 64 in total.
private theorem C1 (root : Base.Bytes32) (n : Nat) :
    (preimage root n).toByteArray.size = 64 ∧
    (preimage root n).toByteArray.data.toList = root.toBytes.toList ++
      (List.range 32).map (fun i => UInt8.ofNat (n >>> (8 * i))) := by
  refine ⟨?_, ?_⟩
  · rw [Base.Bytes.size_toByteArray, preimage, Base.Bytes.size_append,
      Base.FixedBytes.size_toBytes, Base.FixedBytes.size_toBytes]
  · rw [Base.Bytes.toList_toByteArray]
    exact preimage_bytes root n

private theorem zero_digits : countDigits 0 = List.replicate 32 0 := by decide
private theorem one_digits : countDigits 1 = [1] ++ List.replicate 31 0 := by decide
private theorem byte_max_digits : countDigits 255 = [255] ++ List.replicate 31 0 := by decide
private theorem next_byte_digits : countDigits 256 = [0, 1] ++ List.replicate 30 0 := by decide
private theorem max_digits : countDigits (2 ^ 256 - 1) = List.replicate 32 255 := by decide

-- C2: arbitrary root, whole zero/one digests and all 32 count bytes.
private theorem C2 (root : Base.Bytes32) :
    Ssz.mixInLength root 0 (by decide) = Hash.sha256 ((Base.Bytes.ofList
      (root.toBytes.toList ++ List.replicate 32 0)).toByteArray) ∧
    Ssz.mixInLength root 1 (by decide) = Hash.sha256 ((Base.Bytes.ofList
      (root.toBytes.toList ++ ([1] ++ List.replicate 31 0))).toByteArray) := by
  constructor
  · simpa only [zero_digits] using C0 root 0 (by decide)
  · simpa only [one_digits] using C0 root 1 (by decide)

-- C3: independent 255/256 complete-byte boundary checks and full SHA results.
private theorem C3 (root : Base.Bytes32) :
    Ssz.mixInLength root 255 (by decide) = Hash.sha256 ((Base.Bytes.ofList
      (root.toBytes.toList ++ ([255] ++ List.replicate 31 0))).toByteArray) ∧
    Ssz.mixInLength root 256 (by decide) = Hash.sha256 ((Base.Bytes.ofList
      (root.toBytes.toList ++ ([0, 1] ++ List.replicate 30 0))).toByteArray) := by
  constructor
  · simpa only [byte_max_digits] using C0 root 255 (by decide)
  · simpa only [next_byte_digits] using C0 root 256 (by decide)

-- C4: exact maximum supported count; no application exists at the excluded endpoint.
private theorem C4 (root : Base.Bytes32) :
    Ssz.mixInLength root (2 ^ 256 - 1) (by decide) = Hash.sha256 ((Base.Bytes.ofList
      (root.toBytes.toList ++ List.replicate 32 255)).toByteArray) ∧
    ¬ (2 ^ 256 < (2 ^ 256 : Nat)) := by
  refine ⟨?_, Nat.lt_irrefl _⟩
  rw [C0]
  rw [max_digits]

-- C5: exact-equality transport, also covering two different witnesses for one bound.
private theorem C5 (root other : Base.Bytes32) (n m : Nat)
    (h : n < 2 ^ 256) (k : m < 2 ^ 256) (hr : root = other) (hn : n = m) :
    Ssz.mixInLength root n h = Ssz.mixInLength other m k := by
  calc
    Ssz.mixInLength root n h = _ := C0 root n h
    _ = Hash.sha256 ((Base.Bytes.ofList (other.toBytes.toList ++
        (List.range 32).map (fun i => UInt8.ofNat (m >>> (8 * i))))).toByteArray) := by
      rw [hr, hn]; rfl
    _ = Ssz.mixInLength other m k := (C0 other m k).symm

private theorem proof_independent (root : Base.Bytes32) (n : Nat)
    (h k : n < 2 ^ 256) : Ssz.mixInLength root n h = Ssz.mixInLength root n k :=
  C5 root root n n h k rfl rfl

-- C6: full public digest trace, with a local fixed-message FIPS bound.
private theorem C6 (root : Base.Bytes32) (n : Nat) (h : n < 2 ^ 256) :
    8 * (preimage root n).toByteArray.size < 2 ^ 64 ∧
    Hash.Sha256.Model.DigestOnPad
      (Hash.Sha256.Model.fipsPad (root.toBytes.toList ++
        (List.range 32).map (fun i => UInt8.ofNat (n >>> (8 * i)))))
      (Ssz.mixInLength root n h).toBytes.toList := by
  have hb : 8 * (preimage root n).toByteArray.size < 2 ^ 64 := by rw [(C1 root n).1]; decide
  refine ⟨hb, ?_⟩
  have hd := Hash.Sha256.sha256_fipsDigest (preimage root n).toByteArray hb
  rw [(C1 root n).2] at hd
  rw [Ssz.mixInLength_eq]
  exact hd

-- C7: natural List and Bytes sizes enter directly with their own local bound.
private theorem C7 {α : Type} (root : Base.Bytes32) (xs : List α) (b : Base.Bytes)
    (hx : xs.length < 2 ^ 256) (hb : b.size < 2 ^ 256) :
    Ssz.mixInLength root xs.length hx = Hash.sha256 ((Base.Bytes.ofList
      (root.toBytes.toList ++ (List.range 32).map
        (fun i => UInt8.ofNat (xs.length >>> (8 * i))))).toByteArray) ∧
    Ssz.mixInLength root b.size hb = Hash.sha256 ((Base.Bytes.ofList
      (root.toBytes.toList ++ (List.range 32).map
        (fun i => UInt8.ofNat (b.size >>> (8 * i))))).toByteArray) := by
  exact ⟨C0 root xs.length hx, C0 root b.size hb⟩

-- C8: the supplied range proves intended-count preservation before a U256 observation.
private theorem C8 (root : Base.Bytes32) (n : Nat) (h : n < 2 ^ 256) :
    (Base.U256.ofNat n).toNat = n ∧
    Ssz.mixInLength root (Base.U256.ofNat n).toNat (Base.U256.toNat_lt _) =
      Ssz.mixInLength root n h := by
  refine ⟨Base.U256.toNat_ofNat_of_lt h, ?_⟩
  apply C5 root root _ n _ h rfl
  exact Base.U256.toNat_ofNat_of_lt h

-- C9: no outside-range proof can be supplied. No collision, activity, source
-- order or decoded-rootability conclusion is inferred from the successful law.
private theorem C9 (n : Nat) (h : 2 ^ 256 ≤ n) : ¬ n < 2 ^ 256 :=
  Nat.not_lt.mpr h

end STFSpec.Conformance.Codec.LengthClients
