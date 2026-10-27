/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base
import STFSpec.Hash

/-!
# SSZ zero hashes

Library `EthCodec`. Total mathematical recurrence and its finite ordered prefix.
Reference: locked eth-remerkleable 0.1.31, `remerkleable/settings.py:13,16–17,21,24–31`;
`remerkleable/tree.py:109–110`.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Codec

private def zeroHashReference : Nat → Base.Bytes32
  | 0 => Base.FixedBytes.ofNat 0
  | d + 1 =>
    let z := zeroHashReference d
    Hash.sha256 ((z.toBytes ++ z.toBytes).toByteArray)

/-- Total zero-subtree root recurrence; locked `remerkleable/settings.py:13,16–17,21,24–31`;
`remerkleable/tree.py:109–110`.
The original initialized table has 256 entries; this mathematical function has
no depth cap and supplies no source-success claim outside that table. -/
def Ssz.zeroHash (depth : Nat) : Base.Bytes32 := zeroHashReference depth

/-- Complete recurrence, with exactly the ordered duplicated preceding root. -/
theorem Ssz.zeroHash_eq (depth : Nat) :
    zeroHash depth = match depth with
      | 0 => (Base.FixedBytes.ofNat 0 : Base.Bytes32)
      | d + 1 =>
          let z := zeroHash d
          Hash.sha256 ((z.toBytes ++ z.toBytes).toByteArray) := by
  cases depth <;> rfl

-- One source traversal passes each current root into the next step and converts
-- the list to array storage once; no entry restarts the recurrence. This does
-- not assert compiled sharing or lifetime. Strict evaluation may compute the
-- unused successor after the final included root.
private def orbitPrefix {α : Type} (step : α → α) : Nat → α → List α
  | 0, _ => []
  | k + 1, z => z :: orbitPrefix step k (step z)

private theorem prefix_model {α : Type} (step : α → α) (g : Nat → α)
    (hg : ∀ d, g (d + 1) = step (g d)) (k d : Nat) :
    orbitPrefix step k (g d) = (List.range k).map (fun i ↦ g (d + i)) := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    rw [orbitPrefix, ← hg, ih]
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
    apply congrArg (List.cons (g d))
    apply List.map_congr_left
    intro i hi
    change g (d + 1 + i) = g (d + (i + 1))
    exact congrArg g (by omega)

private def zeroHashPrefix (k : Nat) (z : Base.Bytes32) : List Base.Bytes32 :=
  orbitPrefix (fun x ↦ Hash.sha256 ((x.toBytes ++ x.toBytes).toByteArray)) k z

private theorem zeroHashPrefix_model (k d : Nat) :
    zeroHashPrefix k (Ssz.zeroHash d) =
      (List.range k).map (fun i ↦ Ssz.zeroHash (d + i)) :=
  prefix_model (fun (x : Base.Bytes32) ↦
    Hash.sha256 ((x.toBytes ++ x.toBytes).toByteArray)) Ssz.zeroHash
    (fun n ↦ Ssz.zeroHash_eq (n + 1)) k d

/-- The 65 roots at depths 0 through 64, as an optimization prefix rather than a
mathematical depth limit; locked `remerkleable/settings.py:21,24–31`. -/
def Ssz.zeroHashes : Array Base.Bytes32 :=
  (zeroHashPrefix 65 (Base.FixedBytes.ofNat 0)).toArray

/-- Complete ascending ordered observation of the finite zero-hash prefix. -/
theorem Ssz.zeroHashes_toList :
    zeroHashes.toList = (List.range 65).map zeroHash := by
  change (zeroHashPrefix 65 (zeroHash 0)).toArray.toList = _
  rw [List.toList_toArray, zeroHashPrefix_model]
  rfl

private theorem zeroHash_refinement (d : Nat) :
    Ssz.zeroHash d = zeroHashReference d := rfl

private theorem zeroHashPrefix_initial :
    zeroHashPrefix 0 (Ssz.zeroHash 0) = [] ∧
    zeroHashPrefix 1 (Ssz.zeroHash 0) = [Ssz.zeroHash 0] ∧
    zeroHashPrefix 2 (Ssz.zeroHash 0) = [Ssz.zeroHash 0, Ssz.zeroHash 1] := by
  exact ⟨rfl, rfl, rfl⟩

private theorem zeroHashPrefix_length (k : Nat) :
    (zeroHashPrefix k (Ssz.zeroHash 0)).length = k := by
  rw [zeroHashPrefix_model, List.length_map, List.length_range]

private theorem zeroHashPrefix_lookup (k i : Nat) (h : i < k) :
    (zeroHashPrefix k (Ssz.zeroHash 0))[i]? = some (Ssz.zeroHash i) := by
  rw [zeroHashPrefix_model]
  simp only [Nat.zero_add, List.getElem?_map, List.getElem?_range h, Option.map_some]

private theorem recurrence_unique {α : Type} (step : α → α) (initial : α)
    (f g : Nat → α) (hf0 : f 0 = initial) (hg0 : g 0 = initial)
    (hf : ∀ d, f (d + 1) = step (f d)) (hg : ∀ d, g (d + 1) = step (g d)) :
    f = g := by
  funext d
  induction d with
  | zero => exact hf0.trans hg0.symm
  | succ d ih => rw [hf, hg, ih]

end STFSpec.Codec
