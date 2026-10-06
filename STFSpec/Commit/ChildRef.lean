/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.Node
import STFSpec.Codec.RlpItem

/-!
# Pure completed-cache child references

Library `EthCommit`. Pinned EELS
`src/ethereum/forks/amsterdam/incremental_mpt.py:257–284,287–313`.
Stored hash presence takes priority; otherwise reconstruct current fields and
every actual ordered child. Raw cache bytes are not parsed or inspected. The
all-bare equations are a pure representation observer, not a refinement of every
mutable dirty/cache state or of source query actions. A private List/HP reference
and ordinary equality cover every finite input without admission premises.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` C18/Q55/§7.
-/

namespace STFSpec.Commit
open STFSpec.Base STFSpec.Codec

private theorem ext_smaller (path : Nibbles) (child : Node) (enc : Enc) :
    sizeOf (some child : Ref) < sizeOf (some (.ext path child enc) : Ref) := by
  simp only [Option.some.sizeOf_spec, Node.ext.sizeOf_spec]
  omega

private theorem branch_smaller (children : Array Ref) (value : ByteArray) (enc : Enc)
    (i : Fin children.size) :
    sizeOf children[i] < sizeOf (some (.branch children value enc) : Ref) := by
  have h := Array.sizeOf_getElem children i.val i.isLt
  simp only [Option.some.sizeOf_spec, Node.branch.sizeOf_spec, Fin.getElem_fin]
  omega

private theorem branch_member_smaller (children : Array Ref) (value : ByteArray)
    (enc : Enc) (child : Ref) (hchild : child ∈ children.toList) :
    sizeOf child < sizeOf (some (.branch children value enc) : Ref) := by
  have h := Array.sizeOf_lt_of_mem (show child ∈ children from by simpa using hchild)
  simp only [Option.some.sizeOf_spec, Node.branch.sizeOf_spec]
  omega

private def project (root : Ref) : RlpItem :=
  match root with
  | none => .bytes ByteArray.empty
  | some (.hashed h) => .bytes h.toBytes.toByteArray
  | some (.leaf path value enc) =>
    match enc.hash? with
    | some h => .bytes h.toBytes.toByteArray
    | none => .list [.bytes (nibbleListToCompact path true), .bytes value]
  | some (.ext path child enc) =>
    match enc.hash? with
    | some h => .bytes h.toBytes.toByteArray
    | none => .list [.bytes (nibbleListToCompact path false), project (some child)]
  | some (.branch children value enc) =>
    match enc.hash? with
    | some h => .bytes h.toBytes.toByteArray
    | none => .list (List.ofFn (fun i : Fin children.size => project children[i]) ++
        [.bytes value])
termination_by sizeOf root
decreasing_by
  · exact ext_smaller _ _ _
  · exact branch_smaller _ _ _ _

private def reference (root : Ref) : RlpItem :=
  match root with
  | none => .bytes ByteArray.empty
  | some (.hashed h) => .bytes h.toBytes.toByteArray
  | some (.leaf path value enc) =>
    match enc.hash? with
    | some h => .bytes h.toBytes.toByteArray
    | none => .list [.bytes (nibbleListToCompactModel path.toList true).toByteArray, .bytes value]
  | some (.ext path child enc) =>
    match enc.hash? with
    | some h => .bytes h.toBytes.toByteArray
    | none => .list
        [.bytes (nibbleListToCompactModel path.toList false).toByteArray,
        reference (some child)]
  | some (.branch children value enc) =>
    match enc.hash? with
    | some h => .bytes h.toBytes.toByteArray
    | none => .list (children.toList.attach.map (fun child => reference child.val) ++
        [.bytes value])
termination_by sizeOf root
decreasing_by
  · exact ext_smaller _ _ _
  · exact branch_member_smaller _ _ _ _ child.property

private theorem compact_model (p : Nibbles) (leaf : Bool) :
    nibbleListToCompact p leaf = (nibbleListToCompactModel p.toList leaf).toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa only [List.toList_data_toByteArray] using nibbleListToCompact_eq_model p leaf

private theorem indexed_map (children : Array Ref) (f : Ref → RlpItem) :
    List.ofFn (fun i : Fin children.size => f children[i]) = children.toList.map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

private theorem project_reference (root : Ref) : project root = reference root := by
  cases root with
  | none => rw [project, reference]
  | some node =>
    cases node with
    | hashed h => rw [project, reference]
    | leaf path value enc => rw [project, reference]; cases enc.hash? <;> simp only [compact_model]
    | ext path child enc =>
      rw [project, reference]
      cases enc.hash? with
      | some h => rfl
      | none => rw [compact_model, project_reference]
    | branch children value enc =>
      rw [project, reference]
      cases enc.hash? with
      | some h => rfl
      | none =>
        rw [indexed_map]
        rw [List.attach_map_val]
        dsimp only
        congr 2
        apply List.map_congr_left
        intro child hchild
        exact project_reference child
termination_by sizeOf root
decreasing_by
  · exact ext_smaller _ _ _
  · exact branch_member_smaller _ _ _ _ (by assumption)

/-- Pure child reference of a completed-cache representation. A stored hash wins;
otherwise current fields are reconstructed, ignoring raw cache bytes. Pinned EELS
`src/ethereum/forks/amsterdam/incremental_mpt.py:257–284,287–313`. -/
def childRef (root : Ref) : RlpItem := project root

private theorem childRef_reference (root : Ref) : childRef root = reference root :=
  project_reference root

/-- Absence is the empty byte string. -/
theorem childRef_none : childRef none = .bytes ByteArray.empty := by rw [childRef, project]

/-- A stub retains all 32 supplied hash bytes. -/
theorem childRef_hashed (h : Hash32) :
    childRef (some (.hashed h)) = .bytes h.toBytes.toByteArray := by rw [childRef, project]

/-- A leaf returns its stored hash or current HP/value fields. -/
theorem childRef_leaf (p : Nibbles) (v : ByteArray) (enc : Enc) :
    childRef (some (.leaf p v enc)) =
      match enc.hash? with
      | some h => .bytes h.toBytes.toByteArray
      | none => .list [.bytes (nibbleListToCompact p true), .bytes v] := by rw [childRef, project]

/-- A hashless extension descends even when its path is empty. -/
theorem childRef_ext (p : Nibbles) (child : Node) (enc : Enc) :
    childRef (some (.ext p child enc)) =
      match enc.hash? with
      | some h => .bytes h.toBytes.toByteArray
      | none => .list [.bytes (nibbleListToCompact p false), childRef (some child)] := by
  rw [childRef, project]
  rfl

/-- A hashless branch retains every actual child in order and the whole value last. -/
theorem childRef_branch (children : Array Ref) (v : ByteArray) (enc : Enc) :
    childRef (some (.branch children v enc)) =
      match enc.hash? with
      | some h => .bytes h.toBytes.toByteArray
      | none => .list (children.toList.map childRef ++ [.bytes v]) := by
  rw [childRef, project]
  cases enc.hash? with
  | some h => rfl
  | none => rw [indexed_map]; rfl

end STFSpec.Commit
