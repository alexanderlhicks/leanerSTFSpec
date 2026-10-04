/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import ToVCVio.Trie.PatriciaNode

/-!
# Conditional resolved-tree child-reference interpretation

Library `ToVCVio` in `STFSpecSecurity`.

Structural Prop derivations preserve complete fields under one fixed deterministic hash
proof model. Every present child retains the complete assembled `FitsRlp` certificate;
a node derivation does not certify its own top shell. No runtime construction,
inhabitation, actual C7/effect/C8 agreement or cryptographic binding follows.
Pinned EELS context: `src/ethereum/merkle_patricia_trie.py:213–249`
(`encode_internal_node`) and `src/ethereum/merkle_patricia_trie.py:507–581`
(`patricialize`). These local Prop relations supply no source-operation refinement.
Spec guidance: `STFSpec/informal/modules/ToVCVio.md` §§4/5/7.
-/
namespace ToVCVio.Trie
open STFSpec.Base STFSpec.Commit ToVCVio.Rlp ToVCVio.Trie

mutual
  /-- Complete structural shell interpretation under a fixed pure hash proof model.
  The top shell has no implicit `FitsRlp` certificate.
  Pinned EELS context: `src/ethereum/merkle_patricia_trie.py:213–249`
  and `src/ethereum/merkle_patricia_trie.py:507–581`.
  Local Prop model only; no source-operation refinement. -/
  inductive NodeInterprets (h : ByteArray → Hash32) : FullTree → PatriciaNode → Prop where
    /-- Preserve the entire finite leaf path and complete nonempty value. -/
    | leaf (p : Nibbles) (v : PresentValue) :
        NodeInterprets h (.leaf p v) (.leaf p v)
    /-- Preserve the whole extension segment and its present child derivation. -/
    | extension (p : Nibbles) (child : FullTree) (reference : ChildRef)
        (derivation : RefInterprets h (some child) reference) :
        NodeInterprets h (.extension p child) (.extension p reference)
    /-- Preserve terminal presence and every child at its original numeric slot. -/
    | branch (children : Fin 16 → Option FullTree) (references : Vector ChildRef 16)
        (terminal : Terminal)
        (derivations : ∀ i : Fin 16, RefInterprets h (children i) references[i.val]) :
        NodeInterprets h (.branch children terminal) (.branch references terminal)

  /-- Optional resolved-child interpretation; every present shell carries complete Fits.
  `h` is a fixed pure proof model, not an installed oracle or effect coupling.
  Pinned EELS context: `src/ethereum/merkle_patricia_trie.py:213–249`
  and `src/ethereum/merkle_patricia_trie.py:507–581`.
  Local Prop model only; no source-operation refinement. -/
  inductive RefInterprets (h : ByteArray → Hash32) : Option FullTree → ChildRef → Prop where
    /-- Only absence introduces an empty reference. -/
    | empty : RefInterprets h none .empty
    /-- Certify the complete assembled shell before applying the actual reference kernel. -/
    | present (tree : FullTree) (node : PatriciaNode)
        (derivation : NodeInterprets h tree node) (fits : FitsRlp node) :
        RefInterprets h (some tree) (refWithHash h (asListNode node fits))
end

/-- Every interpreted child reference is admissible. -/
theorem ref_interprets_admissible {h : ByteArray → Hash32} {resolved : Option FullTree}
    {reference : ChildRef} (derivation : RefInterprets h resolved reference) :
    AdmissibleRef reference := by
  cases derivation with
  | empty => exact True.intro
  | present tree node derivation fits => exact refWithHash_admissible h (asListNode node fits)

/-- Constructor occupancy exactly preserves optional resolved presence. -/
theorem ref_interprets_occupied {h : ByteArray → Hash32} {resolved : Option FullTree}
    {reference : ChildRef} (derivation : RefInterprets h resolved reference) :
    occupied reference = resolved.isSome := by
  cases derivation with
  | empty => rfl
  | present tree node derivation fits =>
    rw [refWithHash_eq]
    split <;> rfl

private theorem filter_length {α : Type} (p : α → Bool) (xs : List α) :
    (xs.filter p).length = ((xs.map p).filter id).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hp : p x <;> simp [hp, ih]

private theorem vector_toList (v : Vector ChildRef 16) :
    v.toList = List.ofFn (fun i : Fin 16 => v[i.val]) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [Vector.getElem_toList, List.getElem_ofFn]

private theorem occupancy_bridge {h : ByteArray → Hash32}
    (children : Fin 16 → Option FullTree) (references : Vector ChildRef 16)
    (ds : ∀ i : Fin 16, RefInterprets h (children i) references[i.val]) :
    countOccupied references = fullCount children := by
  have equality : references.toList.map occupied = (List.ofFn children).map Option.isSome := by
    rw [vector_toList, List.map_ofFn, List.map_ofFn]
    congr 1
    funext i
    exact ref_interprets_occupied (ds i)
  change (references.toList.filter occupied).length =
    ((List.ofFn children).filter Option.isSome).length
  calc
    _ = ((references.toList.map occupied).filter id).length := filter_length _ _
    _ = (((List.ofFn children).map Option.isSome).filter id).length := by rw [equality]
    _ = _ := (filter_length Option.isSome (List.ofFn children)).symm

/-- A canonical tree's interpreted shell is locally admissible. -/
theorem node_interprets_locally_admissible {h : ByteArray → Hash32} {tree : FullTree}
    {node : PatriciaNode} (canonical : Canonical tree)
    (derivation : NodeInterprets h tree node) :
    LocallyAdmissible node := by
  cases derivation with
  | leaf p v => exact locallyAdmissible_leaf p v
  | extension p child reference derivation =>
    have positive := ((canonical_extension_iff p child).mp canonical).1
    exact ⟨positive, ref_interprets_occupied derivation, ref_interprets_admissible derivation⟩
  | branch children references terminal derivations =>
    refine ⟨fun i => ref_interprets_admissible (derivations i), ?_⟩
    rw [occupancy_bridge children references derivations]
    exact ((canonical_branch_iff children terminal).mp canonical).2

end ToVCVio.Trie
