/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# SSZ zero-hash mathematical observations

Library `EthConformance`. Symbolic roots, complete bytes, prefix boundaries and
public SHA-256 FIPS composition, without evaluating deep digest recurrences.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Conformance.Codec

open STFSpec.Codec

private def pair (x : Base.Bytes32) : ByteArray :=
  (x.toBytes ++ x.toBytes).toByteArray

private def step (x : Base.Bytes32) : Base.Bytes32 := Hash.sha256 (pair x)

private def initial : Base.Bytes32 := Base.FixedBytes.ofNat 0

private theorem root_zero : Ssz.zeroHash 0 = initial := Ssz.zeroHash_eq 0

private theorem root_succ (d : Nat) : Ssz.zeroHash (d + 1) = step (Ssz.zeroHash d) :=
  Ssz.zeroHash_eq (d + 1)

private theorem initial_bytes : initial.toBytes.toList = List.replicate 32 0 := by
  rw [initial, Base.FixedBytes.toBytes_ofNat, Base.Bytes.toList_generate]
  simp
  decide

private theorem pair_bytes (x : Base.Bytes32) :
    (pair x).toList = x.toBytes.toList ++ x.toBytes.toList := by
  rw [pair, Base.Bytes.toByteArray_toList, Base.Bytes.toList_append]

private theorem pair_data (x : Base.Bytes32) :
    (pair x).data.toList = x.toBytes.toList ++ x.toBytes.toList := by
  rw [pair, Base.Bytes.toList_toByteArray, Base.Bytes.toList_append]

private theorem pair_size (x : Base.Bytes32) : (pair x).size = 64 := by
  rw [pair, Base.Bytes.size_toByteArray, Base.Bytes.size_append,
    Base.FixedBytes.size_toBytes]

private theorem root_width (d : Nat) : (Ssz.zeroHash d).toBytes.toList.length = 32 := by
  rw [Base.Bytes.length_toList, Base.FixedBytes.size_toBytes]

private theorem prefix_size : Ssz.zeroHashes.size = 65 := by
  have h := congrArg List.length Ssz.zeroHashes_toList
  simpa only [Array.length_toList, List.length_map, List.length_range] using h

private theorem prefix_lookup (i : Nat) (h : i < 65) :
    Ssz.zeroHashes[i]? = some (Ssz.zeroHash i) := by
  rw [← Array.getElem?_toList, Ssz.zeroHashes_toList]
  simp only [List.getElem?_map, List.getElem?_range h, Option.map_some]

private theorem prefix_absent : Ssz.zeroHashes[65]? = none := by
  apply Array.getElem?_eq_none
  rw [prefix_size]
  exact Nat.le_refl 65

private theorem fips_transport (a b digest : List UInt8) (h : a = b)
    (hd : Hash.Sha256.Model.DigestOnPad (Hash.Sha256.Model.fipsPad a) digest) :
    Hash.Sha256.Model.DigestOnPad (Hash.Sha256.Model.fipsPad b) digest := by
  cases h
  exact hd

private theorem pair_fips (x : Base.Bytes32) :
    Hash.Sha256.Model.DigestOnPad
      (Hash.Sha256.Model.fipsPad (x.toBytes.toList ++ x.toBytes.toList))
      (step x).toBytes.toList := by
  have h : 8 * (pair x).size < 2 ^ 64 := by rw [pair_size]; decide
  dsimp only [step]
  exact fips_transport (pair x).data.toList (x.toBytes.toList ++ x.toBytes.toList)
    (Hash.sha256 (pair x)).toBytes.toList (pair_data x)
    (Hash.Sha256.sha256_fipsDigest (pair x) h)

private def reference : Nat → Base.Bytes32
  | 0 => initial
  | d + 1 => step (reference d)

private theorem reference_eq (d : Nat) : reference d = Ssz.zeroHash d := by
  induction d with
  | zero => exact root_zero.symm
  | succ d ih => rw [reference, ih, root_succ]

-- C0: zero leaf and complete width through public Base contracts.
private theorem zero_observation :
    (Ssz.zeroHash 0).toBytes.toList = List.replicate 32 0 ∧
    (Ssz.zeroHash 0).toBytes.toList.length = 32 := by
  rw [root_zero]
  exact ⟨initial_bytes, by rw [initial_bytes, List.length_replicate]⟩

-- C1: first two symbolic roots and complete preimages.
private theorem first_roots :
    Ssz.zeroHash 1 = step initial ∧ Ssz.zeroHash 2 = step (step initial) ∧
    (pair initial).toList = List.replicate 64 0 ∧
    (pair (Ssz.zeroHash 1)).toList =
      (Ssz.zeroHash 1).toBytes.toList ++ (Ssz.zeroHash 1).toBytes.toList := by
  refine ⟨?_, ?_, ?_, pair_bytes _⟩
  · rw [root_succ, root_zero]
  · rw [root_succ 1, root_succ 0, root_zero]
  · rw [pair_bytes, initial_bytes, List.replicate_append_replicate]

-- C2: whole table, arbitrary root and both sides of the boundary.
private theorem prefix_observation (i : Nat) (h : i < 65) :
    Ssz.zeroHashes.toList = (List.range 65).map Ssz.zeroHash ∧
    Ssz.zeroHashes.size = 65 ∧ Ssz.zeroHashes[i]? = some (Ssz.zeroHash i) ∧
    Ssz.zeroHashes[64]? = some (Ssz.zeroHash 64) ∧ Ssz.zeroHashes[65]? = none :=
  ⟨Ssz.zeroHashes_toList, prefix_size, prefix_lookup i h,
    prefix_lookup 64 (by decide), prefix_absent⟩

-- C3: exact bytes/order/export, size and complete successor FIPS digest trace.
private theorem successor_fips (d : Nat) :
    (pair (Ssz.zeroHash d)).size = 64 ∧
    (pair (Ssz.zeroHash d)).toList =
      (Ssz.zeroHash d).toBytes.toList ++ (Ssz.zeroHash d).toBytes.toList ∧
    Hash.Sha256.Model.DigestOnPad
      (Hash.Sha256.Model.fipsPad
        ((Ssz.zeroHash d).toBytes.toList ++ (Ssz.zeroHash d).toBytes.toList))
      (Ssz.zeroHash (d + 1)).toBytes.toList := by
  refine ⟨pair_size _, pair_bytes _, ?_⟩
  rw [root_succ]
  exact pair_fips _

-- C4: caller-owned direct recurrence, reduced only on the caller side.
private theorem alternative_recurrence (d : Nat) : reference d = Ssz.zeroHash d :=
  reference_eq d

-- C5: arbitrary uncached successor, plus 255/256 without source-domain premises.
private theorem beyond_prefix (d : Nat) (_h : 65 ≤ d) :
    Ssz.zeroHash (d + 1) = step (Ssz.zeroHash d) ∧
    Ssz.zeroHash 65 = step (Ssz.zeroHash 64) ∧
    Ssz.zeroHash 255 = step (Ssz.zeroHash 254) ∧
    Ssz.zeroHash 256 = step (Ssz.zeroHash 255) :=
  ⟨root_succ d, root_succ 64, root_succ 254, root_succ 255⟩

end STFSpec.Conformance.Codec
