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

-- P0: complete zero leaf, including every leading zero byte.
private theorem zero_leaf :
    Ssz.zeroHash 0 = initial ∧
    (Ssz.zeroHash 0).toBytes.toList = List.replicate 32 0 := by
  exact ⟨root_zero, root_zero ▸ initial_bytes⟩

-- P1: first root and the entire 64-zero-byte preimage.
private theorem first_root :
    Ssz.zeroHash 1 = step initial ∧
    (pair initial).toList = List.replicate 64 0 ∧
    (pair initial).size = 64 := by
  refine ⟨?_, ?_, pair_size _⟩
  · rw [root_succ, root_zero]
  · rw [pair_bytes, initial_bytes, List.replicate_append_replicate]

-- P2: second root and complete ordered preimage.
private theorem second_root :
    Ssz.zeroHash 2 = step (step initial) ∧
    (pair (Ssz.zeroHash 1)).toList =
      (Ssz.zeroHash 1).toBytes.toList ++ (Ssz.zeroHash 1).toBytes.toList := by
  refine ⟨?_, pair_bytes _⟩
  rw [root_succ 1, root_succ 0, root_zero]

-- P3: arbitrary successor, exact input size and local FIPS bound.
private theorem successor (d : Nat) :
    Ssz.zeroHash (d + 1) = step (Ssz.zeroHash d) ∧
    (pair (Ssz.zeroHash d)).size = 64 ∧
    8 * (pair (Ssz.zeroHash d)).size < 2 ^ 64 := by
  refine ⟨root_succ d, pair_size _, ?_⟩
  rw [pair_size]
  decide

-- P4: all ordered entries, not a checksum of the table.
private theorem prefix_order :
    Ssz.zeroHashes.toList = (List.range 65).map Ssz.zeroHash ∧
    Ssz.zeroHashes.size = 65 := ⟨Ssz.zeroHashes_toList, prefix_size⟩

-- P5: every eligible lookup.
private theorem cached_root (i : Nat) (h : i < 65) :
    Ssz.zeroHashes[i]? = some (Ssz.zeroHash i) := prefix_lookup i h

-- P6: finite-prefix boundary and total successor at 65.
private theorem prefix_boundary :
    Ssz.zeroHashes[64]? = some (Ssz.zeroHash 64) ∧
    Ssz.zeroHashes[65]? = none ∧
    Ssz.zeroHash 65 = step (Ssz.zeroHash 64) :=
  ⟨prefix_lookup 64 (by decide), prefix_absent, root_succ 64⟩

-- P7: mathematical depths, without source-table agreement at 256.
private theorem deep_roots :
    Ssz.zeroHash 255 = step (Ssz.zeroHash 254) ∧
    Ssz.zeroHash 256 = step (Ssz.zeroHash 255) := ⟨root_succ 254, root_succ 255⟩

-- P8: an independent generic linear builder, including empty/one/two/all lengths.
private def orbitPrefix {α : Type} (f : α → α) : Nat → α → List α
  | 0, _ => []
  | k + 1, z => z :: orbitPrefix f k (f z)

private theorem prefix_model {α : Type} (f : α → α) (g : Nat → α)
    (hg : ∀ d, g (d + 1) = f (g d)) (k d : Nat) :
    orbitPrefix f k (g d) = (List.range k).map (fun i ↦ g (d + i)) := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    rw [orbitPrefix, ← hg, ih]
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map,
      Nat.add_zero]
    apply congrArg (List.cons (g d))
    apply List.map_congr_left
    intro i hi
    exact congrArg g (by omega)

private theorem builder (k : Nat) :
    orbitPrefix step 0 initial = [] ∧
    orbitPrefix step 1 initial = [initial] ∧
    orbitPrefix step 2 initial = [initial, step initial] ∧
    orbitPrefix step k initial = (List.range k).map Ssz.zeroHash ∧
    (orbitPrefix step k initial).length = k ∧
    (∀ i, i < k → (orbitPrefix step k initial)[i]? = some (Ssz.zeroHash i)) := by
  have hm : orbitPrefix step k initial = (List.range k).map Ssz.zeroHash := by
    rw [← root_zero, prefix_model step Ssz.zeroHash root_succ k 0]
    simp only [Nat.zero_add]
  refine ⟨rfl, rfl, rfl, hm, ?_, ?_⟩
  · rw [hm, List.length_map, List.length_range]
  · intro i hi
    rw [hm]
    simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]

-- P9: all-Nat reference refinement, explicitly crossing the finite prefix.
private theorem refinement (d : Nat) :
    reference d = Ssz.zeroHash d ∧
    reference 64 = Ssz.zeroHash 64 ∧ reference 65 = Ssz.zeroHash 65 :=
  ⟨reference_eq d, reference_eq 64, reference_eq 65⟩

-- P10: arbitrary pure recurrence uniqueness, specialized without injectivity.
private theorem recurrence_unique {α : Type} (f : α → α) (z : α)
    (a b : Nat → α) (ha : a 0 = z) (hb : b 0 = z)
    (has : ∀ d, a (d + 1) = f (a d)) (hbs : ∀ d, b (d + 1) = f (b d)) :
    a = b := by
  funext d
  induction d with
  | zero => exact ha.trans hb.symm
  | succ d ih => rw [has, hbs, ih]

private theorem sha_recurrence_unique (a : Nat → Base.Bytes32)
    (ha : a 0 = initial) (has : ∀ d, a (d + 1) = step (a d)) : a = Ssz.zeroHash :=
  recurrence_unique step initial a Ssz.zeroHash ha root_zero has root_succ

-- P11: every root width; arbitrary fixed-byte duplicated input and full FIPS trace.
private theorem provider_composition (d : Nat) (x : Base.Bytes32) :
    (Ssz.zeroHash d).toBytes.toList.length = 32 ∧
    (pair x).size = 64 ∧
    (pair x).toList = x.toBytes.toList ++ x.toBytes.toList ∧
    Hash.Sha256.Model.DigestOnPad
      (Hash.Sha256.Model.fipsPad (x.toBytes.toList ++ x.toBytes.toList))
      (step x).toBytes.toList :=
  ⟨root_width d, pair_size x, pair_bytes x, pair_fips x⟩

end STFSpec.Conformance.Codec
