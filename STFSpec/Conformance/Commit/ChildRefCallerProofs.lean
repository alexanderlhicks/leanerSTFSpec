/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit

/-!
# Pure child-reference public-law clients

Library `EthConformance`. Ordinary clients use all five exact defining equations
and public HP/Array laws without unfolding the production worker or providers.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/7/8.
-/

namespace STFSpec.Conformance.Commit.ChildRefCallerProofs
open STFSpec.Base STFSpec.Codec STFSpec.Commit

private theorem absence : childRef none = .bytes ByteArray.empty := childRef_none

private theorem stub (h : Hash32) : childRef (some (.hashed h)) =
    .bytes h.toBytes.toByteArray := childRef_hashed h

private theorem leaf_hash (p : Nibbles) (v raw : ByteArray) (h : Hash32) :
    childRef (some (.leaf p v ⟨raw, some h⟩)) = .bytes h.toBytes.toByteArray := by
  rw [childRef_leaf]

private theorem leaf_model (p : Nibbles) (v raw : ByteArray) :
    childRef (some (.leaf p v ⟨raw, none⟩)) =
      .list [.bytes (nibbleListToCompactModel p.toList true).toByteArray, .bytes v] := by
  rw [childRef_leaf]
  have hp : nibbleListToCompact p true =
      (nibbleListToCompactModel p.toList true).toByteArray := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simpa only [List.toList_data_toByteArray] using nibbleListToCompact_eq_model p true
  simp only [hp]

private theorem cached_ext (p : Nibbles) (child : Node) (raw : ByteArray) (h : Hash32) :
    childRef (some (.ext p child ⟨raw, some h⟩)) = .bytes h.toBytes.toByteArray := by
  rw [childRef_ext]

private theorem empty_ext_leaf (p : Nibbles) (v raw₁ raw₂ : ByteArray) :
    childRef (some (.ext (Nibbles.ofList []) (.leaf p v ⟨raw₁, none⟩) ⟨raw₂, none⟩)) =
      .list [.bytes (nibbleListToCompact (Nibbles.ofList []) false),
        .list [.bytes (nibbleListToCompact p true), .bytes v]] := by
  rw [childRef_ext]
  simp only [childRef_leaf]

private theorem cached_branch (children : Array Ref) (v raw : ByteArray) (h : Hash32) :
    childRef (some (.branch children v ⟨raw, some h⟩)) = .bytes h.toBytes.toByteArray := by
  rw [childRef_branch]

private theorem branch_fields (children : Array Ref) (v raw : ByteArray) :
    childRef (some (.branch children v ⟨raw, none⟩)) =
      .list ((children.map childRef).toList ++ [.bytes v]) := by
  rw [childRef_branch, Array.toList_map]

private theorem branch_length (children : Array Ref) (v raw : ByteArray) :
    (match childRef (some (.branch children v ⟨raw, none⟩)) with
      | .bytes _ => 0
      | .list xs => xs.length) = children.size + 1 := by
  rw [childRef_branch]
  simp

private theorem raw_ignored (p : Nibbles) (child : Node) (first second : ByteArray)
    (hash : Option Hash32) :
    childRef (some (.ext p child ⟨first, hash⟩)) =
      childRef (some (.ext p child ⟨second, hash⟩)) := by
  rw [childRef_ext, childRef_ext]

end STFSpec.Conformance.Commit.ChildRefCallerProofs
