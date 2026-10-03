/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import ToVCVio.Trie.PatriciaExtensionality

/-!
# Public canonical resolved-tree extensionality clients

Library `ToVCVio` in `STFSpecSecurity`. Symbolic clients retain both canonicality
premises, every finite key and complete optional values. Omission controls separate
support-only and bounded observations from the universal hypotheses.
Spec guidance: `STFSpec/informal/modules/ToVCVio.md` §§4/7.
-/

namespace ToVCVio.Test.Extensionality
open STFSpec.Commit ToVCVio.Trie

private def value : PresentValue := ⟨[0, 0xff, 0x45, 0].toByteArray, by decide⟩
private def otherValue : PresentValue := ⟨[0, 0xff, 0x45, 0, 0].toByteArray, by decide⟩
private def emptyPath : Nibbles := Nibbles.ofList []
private def leaf : FullTree := .leaf emptyPath value
private def noChildren : Fin 16 → Option FullTree := fun _ ↦ none
private def allChildren : Fin 16 → Option FullTree := fun _ ↦ some leaf
private def splitChildren : Fin 16 → Option FullTree :=
  fun i ↦ if i.val < 8 then some leaf else some leaf
private def oneAt (digit : Fin 16) : Fin 16 → Option FullTree :=
  fun i ↦ if i = digit then some leaf else none
private def twoAt (a b : Fin 16) : Fin 16 → Option FullTree :=
  fun i ↦ if i = a ∨ i = b then some leaf else none

/-- Arbitrary actual trees retain both canonicality and all-finite full lookup hypotheses. -/
theorem tree_ext (a b : FullTree) (ha : Canonical a) (hb : Canonical b)
    (he : ∀ key : List (Fin 16), lookup a key = lookup b key) : a = b :=
  canonical_lookup_ext a b ha hb he
/-- Arbitrary optional roots retain both canonicality hypotheses and optional tags. -/
theorem root_ext (a b : Option FullTree) (ha : CanonicalRoot a) (hb : CanonicalRoot b)
    (he : ∀ key : List (Fin 16), lookupRoot a key = lookupRoot b key) : a = b :=
  canonicalRoot_lookup_ext a b ha hb he
/-- Entire bytes at every arbitrary packed path determine an already canonical root. -/
theorem bytes_ext (a b : Option FullTree) (ha : CanonicalRoot a) (hb : CanonicalRoot b)
    (he : ∀ key : Nibbles, observe a key = observe b key) : a = b :=
  canonicalRoot_observe_ext a b ha hb he
/-- Empty roots satisfy the optional theorem with its actual none premises. -/
theorem none_roots : (none : Option FullTree) = none :=
  root_ext none none True.intro True.intro (fun _ ↦ rfl)
/-- Present roots use canonicality of both arbitrary descendants. -/
theorem some_roots (a b : FullTree) (ha : Canonical a) (hb : Canonical b)
    (he : ∀ key : List (Fin 16), lookup a key = lookup b key) : some a = some b := by
  apply root_ext (some a) (some b) ha hb
  intro key
  simpa only [lookupRoot_some] using he key
/-- A canonical present root cannot have the absent root's complete observations. -/
theorem none_some_impossible (tree : FullTree) (hc : Canonical tree)
    (he : ∀ key, lookupRoot none key = lookupRoot (some tree) key) : False := by
  have hh := root_ext none (some tree) True.intro hc he
  cases hh
/-- The opposite absent/present orientation retains the same support obstruction. -/
theorem some_none_impossible (tree : FullTree) (hc : Canonical tree)
    (he : ∀ key, lookupRoot (some tree) key = lookupRoot none key) : False := by
  have hh := root_ext (some tree) none hc True.intro he
  cases hh
/-- Arbitrary packed leaf paths and values are inputs to the full-byte theorem. -/
theorem leaf_bytes_ext (p q : Nibbles) (v w : PresentValue)
    (he : ∀ key : Nibbles, observe (some (.leaf p v)) key = observe (some (.leaf q w)) key) :
    (some (.leaf p v) : Option FullTree) = some (.leaf q w) :=
  bytes_ext _ _ (.leaf _ _) (.leaf _ _) he
/-- Complete arbitrary-length paths retain every nibble and full present value. -/
theorem arbitrary_length (n : Nat) (v : PresentValue) :
    lookup (.leaf (Nibbles.ofList (List.replicate n 15)) v) (List.replicate n 15) = some v := by
  simpa only [Nibbles.toList_ofList] using
    lookup_leaf_exact (Nibbles.ofList (List.replicate n 15)) v
/-- Empty, odd, even and long complete paths are instances of the arbitrary-length law. -/
theorem concrete_lengths (v : PresentValue) :
    lookup (.leaf (Nibbles.ofList []) v) [] = some v ∧
    lookup (.leaf (Nibbles.ofList [15]) v) [15] = some v ∧
    lookup (.leaf (Nibbles.ofList (List.replicate 128 15)) v) (List.replicate 128 15) = some v ∧
    lookup (.leaf (Nibbles.ofList (List.replicate 129 15)) v) (List.replicate 129 15) = some v ∧
    lookup (.leaf (Nibbles.ofList (List.replicate 137 15)) v) (List.replicate 137 15) = some v :=
  ⟨arbitrary_length 0 v, arbitrary_length 1 v, arbitrary_length 128 v,
    arbitrary_length 129 v, arbitrary_length 137 v⟩
/-- Complete paths distinguish short, long, early and late mismatch queries. -/
theorem path_mismatches (v : PresentValue) :
    lookup (.leaf (Nibbles.ofList [0, 15]) v) [0] = none ∧
    lookup (.leaf (Nibbles.ofList [0, 15]) v) [0, 15, 1] = none ∧
    lookup (.leaf (Nibbles.ofList [0, 15]) v) [1, 15] = none ∧
    lookup (.leaf (Nibbles.ofList [0, 15]) v) [0, 14] = none := by
  simp [lookup_leaf, Nibbles.toList_ofList]

private theorem all_canonical (terminal : Terminal) :
    Canonical (.branch allChildren terminal) := by
  apply Canonical.branch
  · intro i tree hc
    cases hc
    exact .leaf _ _
  · have hc : fullCount allChildren = 16 := rfl
    rw [hc]
    omega
private theorem split_canonical (terminal : Terminal) :
    Canonical (.branch splitChildren terminal) := by
  apply Canonical.branch
  · intro i tree hc
    unfold splitChildren at hc
    split at hc <;> cases hc <;> exact .leaf _ _
  · have hc : fullCount splitChildren = 16 := rfl
    rw [hc]
    omega
private theorem one_canonical (digit : Fin 16) (hc : fullCount (oneAt digit) = 1) :
    Canonical (.branch (oneAt digit) (some value)) := by
  apply canonical_one_child_terminal _ _ _ hc
  intro i tree he
  unfold oneAt at he
  split at he
  · cases he; exact .leaf _ _
  · cases he
private theorem two_canonical (a b : Fin 16) (terminal : Terminal)
    (hc : fullCount (twoAt a b) = 2) : Canonical (.branch (twoAt a b) terminal) := by
  apply Canonical.branch
  · intro i tree he
    unfold twoAt at he
    split at he
    · cases he; exact .leaf _ _
    · cases he
  · rw [hc]
    omega

/-- All sixteen numeric positions retain the same complete value with either terminal. -/
theorem all_positions (i : Fin 16) (terminal : Terminal) :
    lookup (.branch allChildren terminal) [i] = some value := by
  rw [lookup_branch_cons]
  change lookupRoot (some leaf) [] = _
  rw [lookupRoot_some]
  exact lookup_leaf_empty _
/-- Constant and split repeated-child functions are identified through all-finite extensionality. -/
theorem alternative_all_functions (terminal : Terminal) :
    FullTree.branch allChildren terminal = .branch splitChildren terminal := by
  apply tree_ext _ _ (all_canonical terminal) (split_canonical terminal)
  intro key
  cases key with
  | nil => simp only [lookup_branch_nil]
  | cons digit rest =>
    rw [lookup_branch_cons, lookup_branch_cons]
    simp only [allChildren, splitChildren]
    split <;> rfl
/-- Reversing condition order preserves numeric children, including identical trees and values. -/
theorem alternative_two_functions (a b : Fin 16) (terminal : Terminal)
    (hc : fullCount (twoAt a b) = 2) :
    FullTree.branch (twoAt a b) terminal = .branch (twoAt b a) terminal := by
  have hcs : twoAt a b = twoAt b a := by
    funext i
    simp only [twoAt, or_comm]
  have hc' : fullCount (twoAt b a) = 2 := by rw [← hcs]; exact hc
  apply tree_ext _ _ (two_canonical a b terminal hc) (two_canonical b a terminal hc')
  intro key
  cases key with
  | nil => simp only [lookup_branch_nil]
  | cons digit rest =>
    rw [lookup_branch_cons, lookup_branch_cons]
    simp only [twoAt, or_comm]
/-- Both terminal boundaries and extreme/interior two-position counts retain equal values. -/
theorem count_boundaries :
    Canonical (.branch (oneAt 0) (some value)) ∧
    Canonical (.branch (oneAt 15) (some value)) ∧
    Canonical (.branch (twoAt 0 15) none) ∧
    Canonical (.branch (twoAt 6 9) none) ∧
    Canonical (.branch allChildren none) ∧ Canonical (.branch allChildren (some value)) :=
  ⟨one_canonical 0 rfl, one_canonical 15 rfl, two_canonical 0 15 none rfl,
    two_canonical 6 9 none rfl, all_canonical none, all_canonical (some value)⟩

private def inner : FullTree := .branch (oneAt 15) (some value)
private def extension : FullTree := .extension (Nibbles.ofList [15, 0]) (.branch allChildren none)
private def nestedChildren : Fin 16 → Option FullTree :=
  fun i ↦ if i = 0 then some inner else if i = 15 then some extension else none
private theorem nested_canonical : Canonical (.branch nestedChildren none) := by
  apply Canonical.branch
  · intro i tree hc
    unfold nestedChildren at hc
    split at hc
    · cases hc; exact one_canonical 15 rfl
    · split at hc
      · cases hc; exact .extension _ _ _ (by decide) (all_canonical none)
      · cases hc
  · decide
/-- Nested canonical branches/extensions retain complete supported suffixes of unequal lengths. -/
theorem nested_keys :
    Canonical (.branch nestedChildren none) ∧
    lookup (.branch nestedChildren none) [0] = some value ∧
    lookup (.branch nestedChildren none) [15, 15, 0, 9] = some value := by
  refine ⟨nested_canonical, ?_, ?_⟩
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
    exact all_positions 9 none
/-- Long complete prefixes retain unequal residual lengths at their exact joined queries. -/
theorem nested_long_prefix (n : Nat) :
    lookup (.extension (Nibbles.ofList (List.replicate (n + 1) 15)) (.branch nestedChildren none))
      (List.replicate (n + 1) 15 ++ [0]) = some value ∧
    lookup (.extension (Nibbles.ofList (List.replicate (n + 1) 15)) (.branch nestedChildren none))
      (List.replicate (n + 1) 15 ++ [15, 15, 0, 9]) = some value := by
  constructor
  · simpa only [Nibbles.toList_ofList, lookup_extension_append] using
      (lookup_extension_append (Nibbles.ofList (List.replicate (n + 1) 15))
        (.branch nestedChildren none) [0]).trans nested_keys.2.1
  · simpa only [Nibbles.toList_ofList, lookup_extension_append] using
      (lookup_extension_append (Nibbles.ofList (List.replicate (n + 1) 15))
        (.branch nestedChildren none) [15, 15, 0, 9]).trans nested_keys.2.2
/-- Arbitrary positive shared segments transport child extensionality through public equations. -/
theorem canonical_prefix_ext (p : Nibbles) (hp : 0 < p.size)
    (cs ds : Fin 16 → Option FullTree) (t u : Terminal)
    (hc : Canonical (.branch cs t)) (hd : Canonical (.branch ds u))
    (he : ∀ key, lookup (.branch cs t) key = lookup (.branch ds u) key) :
    FullTree.extension p (.branch cs t) = .extension p (.branch ds u) := by
  apply tree_ext _ _ (.extension p cs t hp hc) (.extension p ds u hp hd)
  intro key
  rw [lookup_extension, lookup_extension]
  apply congrArg (Option.bind (stripPrefix p.toList key))
  funext rest
  exact he rest

/-- Without positivity a zero extension has every complete observation of its child. -/
theorem zero_extension_lookup (tree : FullTree) (key : List (Fin 16)) :
    lookup (.extension emptyPath tree) key = lookup tree key := by
  rw [lookup_extension]
  simp only [emptyPath, Nibbles.toList_ofList, stripPrefix_nil, Option.bind_some]
/-- Either canonicality omission permits different branch/zero-extension constructors. -/
theorem zero_extension_omission (cs : Fin 16 → Option FullTree) (t : Terminal)
    (hc : Canonical (.branch cs t)) :
    Canonical (.branch cs t) ∧ ¬ Canonical (.extension emptyPath (.branch cs t)) ∧
    (∀ key, lookup (.extension emptyPath (.branch cs t)) key = lookup (.branch cs t) key) ∧
    FullTree.extension emptyPath (.branch cs t) ≠ .branch cs t ∧
    FullTree.branch cs t ≠ .extension emptyPath (.branch cs t) := by
  refine ⟨hc, not_canonical_zero_extension _, zero_extension_lookup _, ?_, ?_⟩
  · intro he; cases he
  · intro he; cases he
/-- Omitting resolved branch-child kind equates an extension-to-leaf with a joined leaf. -/
theorem extension_leaf_lookup (p q : Nibbles) (v : PresentValue) (key : List (Fin 16)) :
    lookup (.extension p (.leaf q v)) key = lookup (.leaf (joinPath p q) v) key := by
  have he := lookup_prepend p (.leaf q v) key
  rw [prepend_leaf] at he
  exact (lookup_extension _ _ _).trans he.symm
/-- An extension-to-leaf violates actual canonicality even for a positive segment. -/
theorem extension_leaf_not_canonical (p q : Nibbles) (v : PresentValue) :
    ¬ Canonical (.extension p (.leaf q v)) := by
  intro hc
  obtain ⟨_, cs, t, he, _⟩ := (canonical_extension_iff _ _).mp hc
  cases he
/-- The equivalent extension/leaf constructors are distinct in both orientations. -/
theorem extension_leaf_distinct (p q : Nibbles) (v : PresentValue) :
    FullTree.extension p (.leaf q v) ≠ .leaf (joinPath p q) v ∧
    FullTree.leaf (joinPath p q) v ≠ .extension p (.leaf q v) := by
  constructor <;> intro he <;> cases he
/-- A dead branch supplies no present lookup value at any finite key. -/
theorem dead_lookup (key : List (Fin 16)) : lookup (.branch noChildren none) key = none := by
  cases key with
  | nil => exact lookup_branch_nil _ _
  | cons digit rest => rw [lookup_branch_cons]; exact lookupRoot_none _
/-- Even sixteen present slots may have dead noncanonical descendants. -/
theorem dead_children_lookup (key : List (Fin 16)) :
    lookup (.branch (fun _ ↦ some (.branch noChildren none)) none) key = none := by
  cases key with
  | nil => exact lookup_branch_nil _ _
  | cons digit rest => rw [lookup_branch_cons, lookupRoot_some]; exact dead_lookup rest
/-- An absent canonical root and dead noncanonical root agree at every complete key. -/
theorem dead_root_omission :
    (∀ key, lookupRoot (some (.branch noChildren none)) key = lookupRoot none key) ∧
    (some (FullTree.branch noChildren none) : Option FullTree) ≠ none ∧
    (none : Option FullTree) ≠ some (.branch noChildren none) := by
  refine ⟨?_, ?_, ?_⟩
  · intro key
    rw [lookupRoot_some, lookupRoot_none]
    exact dead_lookup key
  · intro he; cases he
  · intro he; cases he
/-- A one-child/no-terminal branch and its compressed leaf agree on every finite key. -/
theorem one_child_lookup (digit : Fin 16) (p : Nibbles) (v : PresentValue)
    (key : List (Fin 16)) :
    lookup (.branch (fun i ↦ if i = digit then some (.leaf p v) else none) none) key =
      lookup (.leaf (Nibbles.ofList (digit :: p.toList)) v) key := by
  cases key with
  | nil => simp [lookup_branch_nil, lookup_leaf, Nibbles.toList_ofList]
  | cons i rest =>
    rw [lookup_branch_cons]
    by_cases hi : i = digit
    · subst i
      simp only [ite_true, lookupRoot_some, lookup_leaf, Nibbles.toList_ofList,
        List.cons.injEq, true_and]
    · have hn : i :: rest ≠ digit :: p.toList := by
        intro he; exact hi (List.cons.inj he).1
      simp only [ite_eq_right hi, lookupRoot_none, lookup_leaf, Nibbles.toList_ofList,
        ite_eq_right hn]
/-- The compressible one-child boundary is noncanonical and differs from the canonical leaf. -/
theorem one_child_omission :
    ¬ Canonical (.branch (oneAt 15) none) ∧
    (∀ key, lookup (.branch (oneAt 15) none) key =
      lookup (.leaf (Nibbles.ofList [15]) value) key) ∧
    FullTree.branch (oneAt 15) none ≠ .leaf (Nibbles.ofList [15]) value := by
  refine ⟨not_canonical_one_child_absent _ rfl, ?_, ?_⟩
  · intro key
    exact one_child_lookup 15 emptyPath value key
  · intro he; cases he

/-- Full present bytes separate leaves even when isSome support agrees at every finite key. -/
theorem support_only_omission (p : Nibbles) (v w : PresentValue) (hv : v.val ≠ w.val) :
    (∀ key, (lookup (.leaf p v) key).isSome = (lookup (.leaf p w) key).isSome) ∧
    FullTree.leaf p v ≠ .leaf p w ∧
    observe (some (.leaf p v)) p ≠ observe (some (.leaf p w)) p := by
  refine ⟨?_, ?_, ?_⟩
  · intro key
    rw [lookup_leaf, lookup_leaf]
    split <;> rfl
  · intro he
    exact hv (congrArg Subtype.val (FullTree.leaf.inj he).2)
  · intro he
    rw [observe_some, observe_some, lookup_leaf_exact, lookup_leaf_exact] at he
    exact hv (Option.some.inj he)
/-- Every finite query bound loses distinct values at the complete n+1-digit path. -/
theorem bounded_queries_omission (n : Nat) (v w : PresentValue) (hv : v.val ≠ w.val) :
    Canonical (.leaf (Nibbles.ofList (List.replicate (n + 1) 15)) v) ∧
    Canonical (.leaf (Nibbles.ofList (List.replicate (n + 1) 15)) w) ∧
    (∀ key : List (Fin 16), key.length ≤ n →
      lookup (.leaf (Nibbles.ofList (List.replicate (n + 1) 15)) v) key =
      lookup (.leaf (Nibbles.ofList (List.replicate (n + 1) 15)) w) key) ∧
    observe (some (.leaf (Nibbles.ofList (List.replicate (n + 1) 15)) v))
      (Nibbles.ofList (List.replicate (n + 1) 15)) ≠
    observe (some (.leaf (Nibbles.ofList (List.replicate (n + 1) 15)) w))
      (Nibbles.ofList (List.replicate (n + 1) 15)) := by
  refine ⟨.leaf _ _, .leaf _ _, ?_, (support_only_omission _ v w hv).2.2⟩
  intro key hk
  have hn : key ≠ List.replicate (n + 1) (15 : Fin 16) := by
    intro he
    have hl := congrArg List.length he
    rw [List.length_replicate] at hl
    omega
  simp only [lookup_leaf, Nibbles.toList_ofList, ite_eq_right hn]
/-- Concrete129+ observations retain zero/255 and leading/trailing zeros in unequal values. -/
theorem long_bounded_values :
    observe (some (.leaf (Nibbles.ofList (List.replicate 129 15)) value))
      (Nibbles.ofList (List.replicate 129 15)) ≠
    observe (some (.leaf (Nibbles.ofList (List.replicate 129 15)) otherValue))
      (Nibbles.ofList (List.replicate 129 15)) := by
  exact (bounded_queries_omission 128 value otherValue (by decide)).2.2.2

end ToVCVio.Test.Extensionality
