/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import ToVCVio.Trie.PatriciaSupport

/-!
# Public canonical finite-support clients

Library `ToVCVio` in `STFSpecSecurity`. Symbolic support laws and complete concrete
queries retain equal values, repeated children, terminal endings and arbitrary paths.
Spec guidance: `STFSpec/informal/modules/ToVCVio.md` §§4/7.
-/

namespace ToVCVio.Test.Support
open STFSpec.Commit ToVCVio.Trie

private def value : PresentValue := ⟨[0, 0x53, 0xff, 0].toByteArray, by decide⟩
private def emptyPath : Nibbles := Nibbles.ofList []
private def leaf : FullTree := .leaf emptyPath value
private def oneAt (digit : Fin 16) : Fin 16 → Option FullTree :=
  fun i => if i = digit then some leaf else none
private def twoAt (a b : Fin 16) : Fin 16 → Option FullTree :=
  fun i => if i = a ∨ i = b then some leaf else none
private def allChildren : Fin 16 → Option FullTree := fun _ => some leaf
private def noChildren : Fin 16 → Option FullTree := fun _ => none

/-- A symbolic client over arbitrary actual canonical finite trees and full values. -/
theorem supported (tree : FullTree) (h : Canonical tree) :
    ∃ key v, lookup tree key = some v := canonical_supported _ h
/-- The branch client imposes no distinct-value or distinct-child premise. -/
theorem two_keys (children : Fin 16 → Option FullTree) (terminal : Terminal)
    (h : Canonical (.branch children terminal)) :
    ∃ key other v w, key ≠ other ∧ lookup (.branch children terminal) key = some v ∧
      lookup (.branch children terminal) other = some w := canonical_branch_two_keys _ _ h
/-- Every arbitrary finite leaf path supplies its complete present lookup. -/
theorem leaf_support (p : Nibbles) (v : PresentValue) :
    ∃ key, lookup (.leaf p v) key = some v := ⟨p.toList, lookup_leaf_exact _ _⟩
/-- Arbitrarily long, including empty and odd, leaves retain every nibble. -/
theorem unbounded_leaf (n : Nat) (v : PresentValue) :
    lookup (.leaf (Nibbles.ofList (List.replicate n 15)) v) (List.replicate n 15) =
      some v := by simpa only [Nibbles.toList_ofList] using
        lookup_leaf_exact (Nibbles.ofList (List.replicate n 15)) v
/-- Empty, odd and long complete leaf keys are instances of the arbitrary-length law. -/
theorem leaf_lengths (v : PresentValue) :
    lookup (.leaf (Nibbles.ofList []) v) [] = some v ∧
    lookup (.leaf (Nibbles.ofList [15]) v) [15] = some v ∧
    lookup (.leaf (Nibbles.ofList (List.replicate 129 15)) v) (List.replicate 129 15) = some v ∧
    lookup (.leaf (Nibbles.ofList (List.replicate 137 15)) v) (List.replicate 137 15) = some v :=
  ⟨unbounded_leaf 0 v, unbounded_leaf 1 v, unbounded_leaf 129 v, unbounded_leaf 137 v⟩
/-- Packed observation of a symbolic support witness retains the complete bytes. -/
theorem supported_bytes (tree : FullTree) (h : Canonical tree) :
    ∃ (key : Nibbles) (v : PresentValue), observe (some tree) key = some v.val := by
  obtain ⟨key, v, hk⟩ := canonical_supported tree h
  refine ⟨Nibbles.ofList key, v, ?_⟩
  rw [observe_some, Nibbles.toList_ofList, hk]
  rfl
/-- A complete extension prefix carries any child's symbolic support witness. -/
theorem extension_support (p : Nibbles) (child : FullTree) (key : List (Fin 16))
    (v : PresentValue) (h : lookup child key = some v) :
    lookup (.extension p child) (p.toList ++ key) = some v :=
  (lookup_extension_append _ _ _).trans h

private theorem one_canonical (digit : Fin 16) (hc : fullCount (oneAt digit) = 1) :
    Canonical (.branch (oneAt digit) (some value)) := by
  apply canonical_one_child_terminal _ _ _ hc
  intro i tree h
  unfold oneAt at h
  split at h
  · cases h; exact .leaf _ _
  · cases h

private theorem two_canonical (a b : Fin 16) (hc : fullCount (twoAt a b) = 2) :
    Canonical (.branch (twoAt a b) none) := by
  apply Canonical.branch
  · intro i tree h
    unfold twoAt at h
    split at h
    · cases h; exact .leaf _ _
    · cases h
  · simpa only [terminalCount, Option.isSome_none, Bool.false_eq_true, ite_false,
      Nat.add_zero, hc] using (show 2 ≤ 2 by decide)

private theorem all_canonical (terminal : Terminal) :
    Canonical (.branch allChildren terminal) := by
  apply Canonical.branch
  · intro i tree h
    cases h; exact .leaf _ _
  · have hc : fullCount allChildren = 16 := by decide
    rw [hc]
    omega

/-- Terminal-plus-child boundaries retain equal complete values at positions zero and fifteen. -/
theorem terminal_boundaries :
    Canonical (.branch (oneAt 0) (some value)) ∧
    Canonical (.branch (oneAt 15) (some value)) :=
  ⟨one_canonical 0 (by decide), one_canonical 15 (by decide)⟩
/-- Two numeric positions count separately despite identical child trees and values. -/
theorem repeated_child_boundaries :
    Canonical (.branch (twoAt 0 15) none) ∧ Canonical (.branch (twoAt 6 9) none) :=
  ⟨two_canonical 0 15 (by decide), two_canonical 6 9 (by decide)⟩
/-- The actual List.ofFn count retains all sixteen repeated equal children. -/
theorem all_count : fullCount allChildren = 16 := by decide
/-- All numeric positions return the same complete value, with arbitrary optional terminal. -/
theorem all_numeric (i : Fin 16) (terminal : Terminal) :
    lookup (.branch allChildren terminal) [i] = some value := by
  rw [lookup_branch_cons]
  change lookupRoot (some leaf) [] = _
  rw [lookupRoot_some]
  exact lookup_leaf_empty _
/-- Both optional terminal boundaries are canonical; support and two-key laws apply. -/
theorem all_boundaries (terminal : Terminal) :
    Canonical (.branch allChildren terminal) ∧
    (∃ key v, lookup (.branch allChildren terminal) key = some v) ∧
    (∃ key other v w, key ≠ other ∧ lookup (.branch allChildren terminal) key = some v ∧
      lookup (.branch allChildren terminal) other = some w) :=
  ⟨all_canonical terminal, canonical_supported _ (all_canonical terminal),
    canonical_branch_two_keys _ _ (all_canonical terminal)⟩
/-- A terminal ending and numeric key can have equal values while their complete keys differ. -/
theorem equal_value_keys :
    ([] : List (Fin 16)) ≠ [15] ∧
    lookup (.branch (oneAt 15) (some value)) [] = some value ∧
    lookup (.branch (oneAt 15) (some value)) [15] = some value := by
  refine ⟨by simp, lookup_branch_nil _ _, ?_⟩
  rw [lookup_branch_cons]
  change lookupRoot (some leaf) [] = _
  rw [lookupRoot_some]
  exact lookup_leaf_empty _

private def inner : FullTree := .branch (oneAt 15) (some value)
private def extension : FullTree := .extension (Nibbles.ofList [15, 0]) (.branch allChildren none)
private def nestedChildren : Fin 16 → Option FullTree :=
  fun i => if i = 0 then some inner else if i = 15 then some extension else none
private theorem inner_canonical : Canonical inner := one_canonical 15 (by decide)
private theorem extension_canonical : Canonical extension :=
  .extension _ _ _ (by decide) (all_canonical none)
private theorem nested_canonical : Canonical (.branch nestedChildren none) := by
  apply Canonical.branch
  · intro i tree h
    unfold nestedChildren at h
    split at h
    · cases h; exact inner_canonical
    · split at h
      · cases h; exact extension_canonical
      · cases h
  · decide
/-- Nested canonical children carry complete suffix witnesses of unequal lengths. -/
theorem nested_support :
    (∃ key v, lookup (.branch nestedChildren none) key = some v) ∧
    (∃ key other v w, key ≠ other ∧ lookup (.branch nestedChildren none) key = some v ∧
      lookup (.branch nestedChildren none) other = some w) :=
  ⟨canonical_supported _ nested_canonical,
    canonical_branch_two_keys _ _ nested_canonical⟩
/-- Nested observations retain a terminal suffix and the complete extension/branch suffix. -/
theorem nested_full_keys :
    lookup (.branch nestedChildren none) [0] = some value ∧
    lookup (.branch nestedChildren none) [15, 15, 0, 9] = some value := by
  constructor
  · rw [lookup_branch_cons]
    change lookupRoot (some inner) [] = _
    rw [lookupRoot_some]
    exact lookup_branch_nil _ _
  · rw [lookup_branch_cons]
    change lookupRoot (some extension) [15, 0, 9] = _
    rw [lookupRoot_some]
    change lookup (.extension (Nibbles.ofList [15, 0]) (.branch allChildren none))
      ((Nibbles.ofList [15, 0]).toList ++ [9]) = _
    rw [lookup_extension_append]
    exact all_numeric 9 none
/-- A positive outer prefix retains every nibble of the nested supported key. -/
theorem prefixed_full_key :
    lookup (.extension (Nibbles.ofList [0]) (.branch nestedChildren none))
      [0, 15, 15, 0, 9] = some value := by
  change lookup (.extension (Nibbles.ofList [0]) (.branch nestedChildren none))
    ((Nibbles.ofList [0]).toList ++ [15, 15, 0, 9]) = _
  exact extension_support _ _ _ _ nested_full_keys.2
/-- Positive extensions to actual canonical branches preserve complete supported keys. -/
theorem positive_extension_support :
    Canonical (.extension (Nibbles.ofList [0]) (.branch nestedChildren none)) ∧
    ∃ key v,
      lookup (.extension (Nibbles.ofList [0]) (.branch nestedChildren none)) key = some v := by
  have hc : Canonical (.extension (Nibbles.ofList [0]) (.branch nestedChildren none)) :=
    .extension _ _ _ (by decide) nested_canonical
  exact ⟨hc, canonical_supported _ hc⟩

/-- Without a canonicality premise an empty branch has no supported key. -/
theorem empty_branch_absent (key : List (Fin 16)) :
    lookup (.branch noChildren none) key = none := by
  cases key with
  | nil => exact lookup_branch_nil _ _
  | cons digit rest => rw [lookup_branch_cons]; exact lookupRoot_none _
/-- Occupied slots alone do not give support when their descendants are dead. -/
theorem dead_children_absent (key : List (Fin 16)) :
    lookup (.branch (fun _ => some (.branch noChildren none)) none) key = none := by
  cases key with
  | nil => exact lookup_branch_nil _ _
  | cons digit rest =>
    rw [lookup_branch_cons, lookupRoot_some]
    exact empty_branch_absent rest
/-- One child without terminal cannot satisfy the two-key theorem's canonical premise. -/
theorem one_child_absent_not_canonical : ¬ Canonical (.branch (oneAt 15) none) :=
  not_canonical_one_child_absent _ (by decide)
/-- A zero extension is noncanonical while total lookup still observes its full value. -/
theorem zero_extension_control :
    ¬ Canonical (.extension emptyPath leaf) ∧
    lookup (.extension emptyPath leaf) [] = some value := by
  refine ⟨not_canonical_zero_extension _, ?_⟩
  have hk := lookup_extension_append emptyPath leaf []
  simpa only [emptyPath, Nibbles.toList_ofList, List.nil_append] using
    hk.trans (lookup_leaf_empty value)

end ToVCVio.Test.Support
