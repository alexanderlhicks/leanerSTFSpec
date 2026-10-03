/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import ToVCVio.Trie.PatriciaStructure

/-!
# Canonical finite resolved-tree support witnesses

Library `ToVCVio` in `STFSpecSecurity`. Every canonical resolved tree has a complete
supported key; every canonical branch has two distinct supported keys, including
when their values agree. These ordinary existential laws provide no runtime selector.
Spec guidance: `STFSpec/informal/modules/ToVCVio.md`.
-/

namespace ToVCVio.Trie

private def slots (children : Fin 16 → Option FullTree) : List (Fin 16) :=
  (List.ofFn (fun i : Fin 16 => i)).filter (fun i => (children i).isSome)

private theorem fullCount_eq_slots (children : Fin 16 → Option FullTree) :
    fullCount children = (slots children).length := by
  have hm : (List.ofFn (fun i : Fin 16 => i)).map children = List.ofFn children := by
    simpa only [Function.comp_def] using
      (List.map_ofFn (f := fun i : Fin 16 => i) (g := children))
  rw [fullCount, ← hm, List.filter_map, List.length_map]
  rfl

private theorem slots_nodup (children : Fin 16 → Option FullTree) :
    (slots children).Nodup := by
  have hn : (List.ofFn (fun i : Fin 16 => i)).Nodup := by
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j hi hj he
    rw [List.getElem_ofFn, List.getElem_ofFn] at he
    exact congrArg Fin.val he
  exact hn.filter _

private theorem slot_some (children : Fin 16 → Option FullTree) (i : Fin 16)
    (hi : i ∈ slots children) : ∃ child, children i = some child := by
  have hs := (List.mem_filter.mp hi).2
  cases hc : children i with
  | none => simp [hc] at hs
  | some child => exact ⟨child, rfl⟩

private theorem list_present {α : Type} (xs : List α) (h : 0 < xs.length) :
    ∃ i, i ∈ xs := by
  cases xs with
  | nil => simp at h
  | cons i rest => exact ⟨i, by simp⟩

private theorem list_two_distinct {α : Type} (xs : List α) (hn : xs.Nodup)
    (hl : 2 ≤ xs.length) : ∃ i ∈ xs, ∃ j ∈ xs, i ≠ j := by
  cases xs with
  | nil => simp at hl
  | cons i rest =>
    cases rest with
    | nil => simp at hl
    | cons j tail =>
      refine ⟨i, by simp, j, by simp, ?_⟩
      have hi := (List.nodup_cons.mp hn).1
      intro he
      exact hi (by simp [he])

private theorem fullCount_exists (children : Fin 16 → Option FullTree)
    (h : 0 < fullCount children) : ∃ (i : Fin 16) (child : FullTree),
      children i = some child := by
  rw [fullCount_eq_slots] at h
  obtain ⟨i, hi⟩ := list_present (slots children) h
  obtain ⟨child, hc⟩ := slot_some children i hi
  exact ⟨i, child, hc⟩

private theorem fullCount_exists_pair (children : Fin 16 → Option FullTree)
    (h : 2 ≤ fullCount children) : ∃ (i j : Fin 16) (child other : FullTree),
      i ≠ j ∧ children i = some child ∧ children j = some other := by
  rw [fullCount_eq_slots] at h
  obtain ⟨i, hi, j, hj, hij⟩ := list_two_distinct (slots children) (slots_nodup children) h
  obtain ⟨child, hc⟩ := slot_some children i hi
  obtain ⟨other, ho⟩ := slot_some children j hj
  exact ⟨i, j, child, other, hij, hc, ho⟩

/-- Every canonical finite resolved tree has a complete key with its present value. -/
theorem canonical_supported (tree : FullTree) (h : Canonical tree) :
    ∃ (key : List (Fin 16)) (value : PresentValue), lookup tree key = some value := by
  induction h with
  | leaf p v => exact ⟨p.toList, v, lookup_leaf_exact p v⟩
  | extension p _children _terminal _positive _child ih =>
    obtain ⟨key, value, hk⟩ := ih
    exact ⟨p.toList ++ key, value, (lookup_extension_append p _ key).trans hk⟩
  | branch children terminal _childrenCanonical occupancy ih =>
    cases terminal with
    | some value => exact ⟨[], value, lookup_branch_nil _ _⟩
    | none =>
      have hp : 0 < fullCount children := by
        simp only [terminalCount, Option.isSome_none, Bool.false_eq_true, ite_false,
          Nat.add_zero] at occupancy
        omega
      obtain ⟨i, child, hc⟩ := fullCount_exists children hp
      obtain ⟨key, value, hk⟩ := ih i child hc
      refine ⟨i :: key, value, ?_⟩
      rw [lookup_branch_cons, hc, lookupRoot_some]
      exact hk

/-- A canonical branch has two distinct complete keys; their present values may agree. -/
theorem canonical_branch_two_keys (children : Fin 16 → Option FullTree) (terminal : Terminal)
    (h : Canonical (.branch children terminal)) :
    ∃ (key₁ key₂ : List (Fin 16)) (value₁ value₂ : PresentValue),
      key₁ ≠ key₂ ∧ lookup (.branch children terminal) key₁ = some value₁ ∧
      lookup (.branch children terminal) key₂ = some value₂ := by
  cases h with
  | branch children terminal childrenCanonical occupancy =>
    cases terminal with
    | some value =>
      have hp : 0 < fullCount children := by
        simp only [terminalCount, Option.isSome_some, ite_true] at occupancy
        omega
      obtain ⟨i, child, hc⟩ := fullCount_exists children hp
      obtain ⟨key, other, hk⟩ := canonical_supported child (childrenCanonical i child hc)
      refine ⟨[], i :: key, value, other, by simp, lookup_branch_nil _ _, ?_⟩
      rw [lookup_branch_cons, hc, lookupRoot_some]
      exact hk
    | none =>
      have hp : 2 ≤ fullCount children := by
        simpa only [terminalCount, Option.isSome_none, Bool.false_eq_true, ite_false,
          Nat.add_zero] using occupancy
      obtain ⟨i, j, child, other, hij, hc, ho⟩ := fullCount_exists_pair children hp
      obtain ⟨key, value, hk⟩ := canonical_supported child (childrenCanonical i child hc)
      obtain ⟨otherKey, otherValue, hoKey⟩ :=
        canonical_supported other (childrenCanonical j other ho)
      refine ⟨i :: key, j :: otherKey, value, otherValue, ?_, ?_, ?_⟩
      · intro he
        exact hij (List.cons.inj he).1
      · rw [lookup_branch_cons, hc, lookupRoot_some]
        exact hk
      · rw [lookup_branch_cons, ho, lookupRoot_some]
        exact hoKey

end ToVCVio.Trie
