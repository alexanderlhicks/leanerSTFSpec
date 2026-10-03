/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import ToVCVio.Trie.PatriciaStructure

/-!
# Public finite lookup, packed join and prefix-compression clients

Public symbolic and deterministic clients check finite lookup, packed joins and prefix compression.
Library `ToVCVio` in `STFSpecSecurity`.

Spec guidance: `STFSpec/informal/modules/ToVCVio.md` §§4/7.
-/
namespace ToVCVio.Test.Structure
open STFSpec.Commit ToVCVio.Trie

/-- Complete nonempty bytes retain zero and maximal byte values. -/
def value : PresentValue := ⟨[0x61, 0, 0xff].toByteArray, by decide⟩
/-- The public empty packed path. -/
def emptyPath : Nibbles := Nibbles.ofList []
/-- A 129-digit path retains both nibble extremes. -/
def longPath : Nibbles := Nibbles.ofList (List.replicate 128 15 ++ [0])
/-- Each numeric slot has distinct complete nonempty bytes. -/
def digitValue (i : Fin 16) : PresentValue :=
  ⟨[UInt8.ofNat i.val, 0xff].toByteArray, by
    intro h
    have hs := congrArg ByteArray.size h
    simp only [List.size_toByteArray, List.length_cons, List.length_nil,
      ByteArray.size_empty] at hs
    contradiction⟩
/-- Sixteen distinguishable resolved leaves in numeric order. -/
def allChildren : Fin 16 → Option FullTree :=
  fun i => some (.leaf emptyPath (digitValue i))
/-- Only the final numeric child is present. -/
def oneChild : Fin 16 → Option FullTree :=
  fun i => if i.val = 15 then some (.leaf emptyPath value) else none
/-- Exactly the first two numeric children are present. -/
def twoChildren : Fin 16 → Option FullTree :=
  fun i => if i.val < 2 then some (.leaf emptyPath value) else none
/-- Empty extension chains exercise unconditional lookup laws. -/
def noncanonical : FullTree := .extension emptyPath (.extension emptyPath (.leaf emptyPath value))

/-- Symbolic exact prefix inverse on arbitrary finite paths. -/
theorem prefix_inverse (p key rest : List (Fin 16)) :
    stripPrefix p key = some rest ↔ key = p ++ rest := stripPrefix_some_iff _ _ _
/-- Symbolic finite prefix composition. -/
theorem prefix_composition (p q key : List (Fin 16)) :
    stripPrefix (p ++ q) key = (stripPrefix p key).bind (stripPrefix q) := stripPrefix_append _ _ _
/-- Exact leaf presence on arbitrary paths and values. -/
theorem exact_leaf (p : Nibbles) (v : PresentValue) (key : List (Fin 16)) :
    lookup (.leaf p v) key = some v ↔ key = p.toList := lookup_leaf_some_iff _ _ _
/-- Complete segment removal delegates to any finite child. -/
theorem extension_delegates (p : Nibbles) (child : FullTree) (key : List (Fin 16)) :
    lookup (.extension p child) (p.toList ++ key) = lookup child key :=
  lookup_extension_append _ _ _
/-- Every numeric position returns its own distinguishable value. -/
theorem all_positions (i : Fin 16) :
    lookup (.branch allChildren (some value)) [i] = some (digitValue i) := by
  rw [lookup_branch_cons]
  change lookupRoot (some (.leaf emptyPath (digitValue i))) [] = _
  rw [lookupRoot_some]
  exact lookup_leaf_empty _
/-- An empty branch query retains its supplied terminal. -/
theorem branch_terminal (cs : Fin 16 → Option FullTree) (t : Terminal) :
    lookup (.branch cs t) [] = t := lookup_branch_nil _ _
/-- All-input ordinary packed/reference equality client. -/
theorem packed_reference (p q : Nibbles) : joinPath p q = joinPathReference p q :=
  joinPath_eq_reference _ _
/-- Full path and size observations agree with the List model. -/
theorem packed_full_model (p q : Nibbles) :
    (joinPath p q).toList = p.toList ++ q.toList ∧ (joinPath p q).size = p.size + q.size :=
  ⟨joinPath_toList _ _, joinPath_size _ _⟩
/-- Every bounded result index agrees with the complete List model. -/
theorem packed_index (p q : Nibbles) (i : Nat) (hi : i < (joinPath p q).size) :
    (joinPath p q).get ⟨i, hi⟩ =
      (p.toList ++ q.toList)[i]'(by rw [← joinPath_toList, Nibbles.length_toList]; exact hi) := by
  have he := congrArg (fun xs : List (Fin 16) => xs[i]?) (joinPath_toList p q)
  rw [List.getElem?_eq_getElem (by rw [Nibbles.length_toList]; exact hi),
    List.getElem?_eq_getElem (by rw [← joinPath_toList, Nibbles.length_toList]; exact hi)] at he
  exact (Nibbles.getElem_toList _ i hi).symm.trans (Option.some.inj he)
/-- Compression preserves lookup for every finite tree. -/
theorem every_tree (p : Nibbles) (tree : FullTree) (key : List (Fin 16)) :
    lookup (prepend p tree) key = (stripPrefix p.toList key).bind (lookup tree) :=
  lookup_prepend _ _ _
/-- Actual canonical input suffices for canonical output. -/
theorem shape_preservation (p : Nibbles) (tree : FullTree) (h : Canonical tree) :
    Canonical (prepend p tree) := prepend_canonical _ _ h
/-- Complete suffix bytes agree after prefix compression. -/
theorem complete_observer (p key : Nibbles) (tree : FullTree) :
    observe (some (prepend p tree)) (joinPath p key) = observe (some tree) key :=
  observe_prepend_join _ _ _

/-- Exact, residual, short and first/last mismatch boundaries. -/
theorem prefix_boundaries :
    stripPrefix [] [] = some [] ∧ stripPrefix [0, 15] [0, 15, 1] = some [1] ∧
    stripPrefix [0, 15] [0] = none ∧ stripPrefix [0, 15] [1, 15] = none ∧
    stripPrefix [0, 15] [0, 14] = none := by decide
/-- Short, longer and wrong leaf queries are absent. -/
theorem leaf_boundaries :
    lookup (.leaf (Nibbles.ofList [0, 15]) value) [0] = none ∧
    lookup (.leaf (Nibbles.ofList [0, 15]) value) [0, 15, 1] = none ∧
    lookup (.leaf (Nibbles.ofList [0, 15]) value) [0, 14] = none := by
  simp [lookup_leaf, Nibbles.toList_ofList]
/-- Empty and positive extension segment boundaries. -/
theorem extension_boundaries :
    lookup (.extension emptyPath (.leaf emptyPath value)) [] = some value ∧
    lookup (.extension (Nibbles.ofList [0, 15]) (.leaf emptyPath value)) [0] = none ∧
    lookup (.extension (Nibbles.ofList [0, 15]) (.leaf emptyPath value)) [0, 15] = some value := by
  simp [lookup_extension, lookup_leaf, emptyPath, Nibbles.toList_ofList, stripPrefix,
    Option.bind]
/-- Absent roots and selected children remain absent. -/
theorem absent_cases : lookupRoot none [15] = none ∧
    lookup (.branch (fun _ => none) (some value)) [15] = none := ⟨rfl, rfl⟩
/-- Empty prefixes retain every outer constructor. -/
theorem all_empty_prefixes (p : Nibbles) (child : FullTree) :
    prepend emptyPath (.leaf p value) = .leaf p value ∧
    prepend emptyPath (.extension p child) = .extension p child ∧
    prepend emptyPath (.branch allChildren (some value)) = .branch allChildren (some value) :=
  ⟨prepend_empty _, prepend_empty _, prepend_empty _⟩
/-- A positive branch prefix wraps the branch once. -/
theorem positive_prefix_branch :
    prepend (Nibbles.ofList [15]) (.branch allChildren (some value)) =
      .extension (Nibbles.ofList [15]) (.branch allChildren (some value)) := by
  rw [prepend_branch]; simp [Nibbles.size_ofList]
/-- The preservation law applies to a noncanonical extension chain. -/
theorem noncanonical_preservation (p : Nibbles) (key : List (Fin 16)) :
    lookup (prepend p noncanonical) key = (stripPrefix p.toList key).bind (lookup noncanonical) :=
  lookup_prepend _ _ _
/-- Asymmetric joins retain all 129 input digits. -/
theorem long_join : (joinPath longPath (Nibbles.ofList [0, 15])).size = 131 ∧
    (joinPath (Nibbles.ofList [0]) longPath).toList = [0] ++ List.replicate 128 15 ++ [0] := by
  simp [joinPath_size, joinPath_toList, longPath, Nibbles.size_ofList,
    Nibbles.toList_ofList]

/-- One child plus terminal satisfies the actual canonical grammar. -/
theorem one_child_canonical : Canonical (.branch oneChild (some value)) := by
  apply canonical_one_child_terminal _ _ _ (by decide)
  intro i tree h
  unfold oneChild at h
  split at h
  · cases h; exact .leaf _ _
  · cases h
/-- Two children without terminal satisfy the actual canonical grammar. -/
theorem two_children_canonical : Canonical (.branch twoChildren none) := by
  apply Canonical.branch
  · intro i tree h
    unfold twoChildren at h
    split at h
    · cases h; exact .leaf _ _
    · cases h
  · decide
/-- Canonical empty/long leaves, both occupancy boundaries and positive extensions
survive compression. -/
theorem canonical_samples (p : Nibbles) :
    Canonical (prepend p (.leaf emptyPath value)) ∧
    Canonical (prepend p (.leaf longPath value)) ∧
    Canonical (prepend p (.branch oneChild (some value))) ∧
    Canonical (prepend p (.branch twoChildren none)) ∧
    Canonical (prepend p (.extension (Nibbles.ofList [15]) (.branch twoChildren none))) :=
  ⟨prepend_canonical _ _ (.leaf _ _), prepend_canonical _ _ (.leaf _ _),
    prepend_canonical _ _ one_child_canonical, prepend_canonical _ _ two_children_canonical,
    prepend_canonical _ _ (.extension _ _ _ (by decide) two_children_canonical)⟩

end ToVCVio.Test.Structure
