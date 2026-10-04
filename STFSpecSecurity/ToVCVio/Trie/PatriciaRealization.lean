/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import ToVCVio.Trie.PatriciaSupport
import Std.Data.ExtTreeMap.Lemmas

/-!
# Canonical finite-map observational realization

Library `ToVCVio` in `STFSpecSecurity`. Every actual finite map satisfying
`NonemptyValues`, including the empty map, has a canonical resolved optional root
with the same complete byte observations at every finite key.
Construction proof support is private; the public law is Prop-only and supplies
no runtime witness selector.
Spec guidance: `STFSpec/informal/modules/ToVCVio.md` §§5/7.
-/

open STFSpec.Commit

namespace ToVCVio.Trie

private abbrev Key := List (Fin 16)
private abbrev Entry := Key × PresentValue
private abbrev Entries := List Entry

/-! ### Residual entries and strict descent -/

private def mass : Entries → Nat
  | [] => 0
  | e :: rest => e.1.length + 1 + mass rest
private def childEntries (digit : Fin 16) : Entries → Entries
  | [] => []
  | ([], _) :: rest => childEntries digit rest
  | (head :: tail, value) :: rest =>
    if head = digit then (tail, value) :: childEntries digit rest else childEntries digit rest
private def terminal : Entries → Terminal
  | [] => none
  | ([], value) :: _ => some value
  | (_ :: _, _) :: rest => terminal rest
private def Distinct (es : Entries) : Prop := (es.map Prod.fst).Nodup
private def Realizes (root : Option FullTree) (es : Entries) : Prop :=
  ∀ key value, lookupRoot root key = some value ↔ (key, value) ∈ es
private theorem mass_child_le (digit : Fin 16) (es : Entries) :
    mass (childEntries digit es) ≤ mass es := by
  induction es with
  | nil => exact Nat.le_refl _
  | cons e rest ih =>
    rcases e with ⟨key, value⟩
    cases key with
    | nil => simp only [childEntries, mass]; omega
    | cons head tail =>
      simp only [childEntries]
      split
      · simp only [mass, List.length_cons]; omega
      · simp only [mass, List.length_cons]; omega
private theorem mass_child_lt (digit : Fin 16) (e : Entry) (rest : Entries) :
    mass (childEntries digit (e :: rest)) < mass (e :: rest) := by
  have h := mass_child_le digit rest
  rcases e with ⟨key, value⟩
  cases key with
  | nil => simp only [childEntries, mass]; omega
  | cons head tail =>
    simp only [childEntries]
    split
    · simp only [mass, List.length_cons]; omega
    · simp only [mass, List.length_cons]; omega
private theorem mem_child (digit : Fin 16) (es : Entries) (key : Key) (value : PresentValue) :
    (key, value) ∈ childEntries digit es ↔ (digit :: key, value) ∈ es := by
  induction es with
  | nil => simp [childEntries]
  | cons e rest ih =>
    rcases e with ⟨path, v⟩
    cases path with
    | nil => simp [childEntries, ih]
    | cons head tail =>
      by_cases hh : head = digit
      · subst head
        simp [childEntries, ih]
      · simp [childEntries, hh, ih, Ne.symm hh]
private theorem distinct_tail (e : Entry) (es : Entries) (hd : Distinct (e :: es)) :
    Distinct es := (List.nodup_cons.mp hd).2
private theorem distinct_key (e : Entry) (es : Entries) (hd : Distinct (e :: es)) :
    e.1 ∉ es.map Prod.fst := (List.nodup_cons.mp hd).1
private theorem distinct_child (digit : Fin 16) (es : Entries) (hd : Distinct es) :
    Distinct (childEntries digit es) := by
  induction es with
  | nil => simp [Distinct, childEntries]
  | cons e rest ih =>
    have ht := ih (distinct_tail e rest hd)
    have hk := distinct_key e rest hd
    rcases e with ⟨key, value⟩
    cases key with
    | nil => exact ht
    | cons head tail =>
      simp only [childEntries]
      split
      · next hh =>
        subst head
        apply List.nodup_cons.mpr
        refine ⟨?_, ht⟩
        intro hm
        obtain ⟨⟨q, v⟩, hv, hq⟩ := List.mem_map.mp hm
        change q = tail at hq
        subst q
        have he := (mem_child digit rest tail v).mp hv
        exact hk (List.mem_map.mpr ⟨(digit :: tail, v), he, rfl⟩)
      · exact ht
private theorem terminal_some (es : Entries) (hd : Distinct es) (value : PresentValue) :
    terminal es = some value ↔ ([], value) ∈ es := by
  induction es with
  | nil => simp [terminal]
  | cons e rest ih =>
    have ht := distinct_tail e rest hd
    have hk := distinct_key e rest hd
    rcases e with ⟨key, v⟩
    cases key with
    | nil =>
      have hn : ([], value) ∉ rest := by
        intro hm
        exact hk (List.mem_map.mpr ⟨([], value), hm, rfl⟩)
      simp [terminal, hn, eq_comm]
    | cons head tail => simp [terminal, ih ht]
/-! ### Actual numeric occupancy and canonical existential assembly -/

private def slots (children : Fin 16 → Option FullTree) : List (Fin 16) :=
  (List.ofFn (fun i : Fin 16 ↦ i)).filter (fun i ↦ (children i).isSome)
private theorem fullCount_slots (children : Fin 16 → Option FullTree) :
    fullCount children = (slots children).length := by
  have hm : (List.ofFn (fun i : Fin 16 ↦ i)).map children = List.ofFn children := by
    simpa only [Function.comp_def] using
      (List.map_ofFn (f := fun i : Fin 16 ↦ i) (g := children))
  rw [fullCount, ← hm, List.filter_map, List.length_map]
  rfl
private theorem slot_some (children : Fin 16 → Option FullTree) (i : Fin 16)
    (hi : i ∈ slots children) : ∃ child, children i = some child := by
  have hs := (List.mem_filter.mp hi).2
  cases hc : children i with
  | none => simp [hc] at hs
  | some child => exact ⟨child, rfl⟩
private theorem slot_none (children : Fin 16 → Option FullTree) (i : Fin 16)
    (hi : i ∉ slots children) : children i = none := by
  cases hc : children i with
  | none => rfl
  | some child =>
    apply False.elim
    apply hi
    apply List.mem_filter.mpr
    exact ⟨List.mem_ofFn.mpr ⟨i, rfl⟩, by simp [hc]⟩
private theorem normalize_branch (cs : Fin 16 → Option FullTree) (t : Terminal)
    (hc : ∀ i tree, cs i = some tree → Canonical tree) :
    ∃ root, CanonicalRoot root ∧
      ∀ key, lookupRoot root key = lookup (.branch cs t) key := by
  classical
  have canonical_many (hm : 2 ≤ fullCount cs + terminalCount t) :
      Canonical (.branch cs t) := Canonical.branch cs t hc hm
  cases hs : slots cs with
  | nil =>
    have hn (i : Fin 16) : cs i = none := slot_none cs i (by simp [hs])
    cases t with
    | none =>
      refine ⟨none, True.intro, ?_⟩
      intro key
      cases key with
      | nil => rw [lookupRoot_none, lookup_branch_nil]
      | cons i rest => rw [lookupRoot_none, lookup_branch_cons, hn, lookupRoot_none]
    | some v =>
      refine ⟨some (.leaf (Nibbles.ofList []) v), Canonical.leaf _ _, ?_⟩
      intro key
      rw [lookupRoot_some, lookup_leaf, Nibbles.toList_ofList]
      cases key with
      | nil => rw [lookup_branch_nil]; rfl
      | cons i rest => rw [lookup_branch_cons, hn, lookupRoot_none]; rfl
  | cons i rest =>
    cases rest with
    | nil =>
      cases t with
      | some v =>
        refine ⟨some (.branch cs (some v)), ?_, fun _ ↦ lookupRoot_some _ _⟩
        apply canonical_many
        rw [fullCount_slots, hs]
        simp [terminalCount]
      | none =>
        obtain ⟨tree, ht⟩ := slot_some cs i (by simp [hs])
        have hn (j : Fin 16) (hj : j ≠ i) : cs j = none :=
          slot_none cs j (by simp [hs, hj])
        refine ⟨some (prepend (Nibbles.ofList [i]) tree),
          prepend_canonical _ tree (hc i tree ht), ?_⟩
        intro key
        rw [lookupRoot_some, lookup_prepend, Nibbles.toList_ofList]
        cases key with
        | nil => rw [stripPrefix_short, lookup_branch_nil]; rfl
        | cons j rest =>
          rw [stripPrefix_cons, lookup_branch_cons]
          by_cases hj : j = i
          · subst j
            rw [ite_eq_left rfl, stripPrefix_nil, ht, lookupRoot_some]; rfl
          · rw [ite_eq_right (Ne.symm hj), hn j hj, lookupRoot_none]; rfl
    | cons j tail =>
      refine ⟨some (.branch cs t), ?_, fun _ ↦ lookupRoot_some _ _⟩
      apply canonical_many
      rw [fullCount_slots, hs]
      simp only [List.length_cons]
      omega
private theorem entries_realized (es : Entries) (hd : Distinct es) :
    ∃ root, CanonicalRoot root ∧ Realizes root es := by
  classical
  have all (n : Nat) : ∀ es : Entries, mass es = n → Distinct es →
      ∃ root, CanonicalRoot root ∧ Realizes root es := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro entries hn distinct
      cases entries with
      | nil => exact ⟨none, True.intro, by simp [Realizes, lookupRoot_none]⟩
      | cons e rest =>
        have childWitness (i : Fin 16) : ∃ root, CanonicalRoot root ∧
            Realizes root (childEntries i (e :: rest)) := by
          apply ih (mass (childEntries i (e :: rest)))
          · rw [← hn]
            exact mass_child_lt i e rest
          · exact rfl
          · exact distinct_child i (e :: rest) distinct
        let children (i : Fin 16) : Option FullTree := Classical.choose (childWitness i)
        have childrenCanonical (i : Fin 16) (tree : FullTree) (hc : children i = some tree) :
            Canonical tree := by
          have hh := (Classical.choose_spec (childWitness i)).1
          change CanonicalRoot (children i) at hh
          rw [hc] at hh
          exact hh
        have childrenRealize (i : Fin 16) :
            Realizes (children i) (childEntries i (e :: rest)) :=
          (Classical.choose_spec (childWitness i)).2
        obtain ⟨root, hc, he⟩ := normalize_branch children (terminal (e :: rest)) childrenCanonical
        refine ⟨root, hc, ?_⟩
        intro key value
        rw [he]
        cases key with
        | nil => rw [lookup_branch_nil]; exact terminal_some _ distinct value
        | cons i tail =>
          rw [lookup_branch_cons]
          exact (childrenRealize i tail value).trans (mem_child i _ tail value)
  exact all (mass es) es rfl hd
/-! ### Actual finite-map and complete-byte observation bridge -/

private def mapEntries (obj : Std.ExtTreeMap Nibbles ByteArray) (values : NonemptyValues obj) :
    Entries := obj.toList.attach.map fun e ↦
      (e.val.1.toList, ⟨e.val.2, values e.val.1 e.val.2
        (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp e.property)⟩)
private theorem mapEntries_keys (obj : Std.ExtTreeMap Nibbles ByteArray)
    (values : NonemptyValues obj) :
    (mapEntries obj values).map Prod.fst = obj.toList.map (fun e ↦ e.1.toList) := by
  unfold mapEntries
  rw [List.map_map]
  change obj.toList.attach.map (fun e ↦ e.val.1.toList) = _
  exact List.attach_map_val (l := obj.toList) (f := fun e : Nibbles × ByteArray ↦ e.1.toList)
private theorem mapEntries_distinct (obj : Std.ExtTreeMap Nibbles ByteArray)
    (values : NonemptyValues obj) : Distinct (mapEntries obj values) := by
  rw [Distinct, mapEntries_keys]
  apply List.pairwise_map.mpr
  exact (Std.ExtTreeMap.distinct_keys_toList (t := obj)).imp fun {a b} hab he ↦
    hab ((Nibbles.compare_eq_eq_iff a.1 b.1).mpr (Nibbles.ext he))
private theorem mem_mapEntries (obj : Std.ExtTreeMap Nibbles ByteArray)
    (values : NonemptyValues obj) (key : Nibbles) (value : PresentValue) :
    (key.toList, value) ∈ mapEntries obj values ↔ obj[key]? = some value.val := by
  constructor
  · intro hm
    obtain ⟨e, _, he⟩ := List.mem_map.mp hm
    have hk := Nibbles.ext (congrArg Prod.fst he)
    have hv := congrArg (fun pair : Entry ↦ pair.2.val) he
    have hl := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp e.property
    change e.val.2 = value.val at hv
    rw [hk, hv] at hl
    exact hl
  · intro hl
    let e : {e // e ∈ obj.toList} :=
      ⟨(key, value.val), Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hl⟩
    apply List.mem_map.mpr
    refine ⟨e, List.mem_attach _ _, ?_⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext; rfl
private theorem observe_projection (root : Option FullTree) (key : Nibbles) :
    observe root key = (lookupRoot root key.toList).map Subtype.val := by
  cases root with
  | none => rw [observe_none, lookupRoot_none]; rfl
  | some tree => rw [observe_some, lookupRoot_some]

/-- Every actual finite map satisfying `NonemptyValues`, including the empty map,
has a canonical optional root with exact full byte observations at every finite key. -/
theorem nonemptyValues_realized (obj : Std.ExtTreeMap Nibbles ByteArray)
    (values : NonemptyValues obj) :
    ∃ root : Option FullTree, CanonicalRoot root ∧
      ∀ key : Nibbles, observe root key = obj[key]? := by
  classical
  obtain ⟨root, hc, hr⟩ :=
    entries_realized (mapEntries obj values) (mapEntries_distinct obj values)
  refine ⟨root, hc, ?_⟩
  intro key
  rw [observe_projection]
  cases hl : lookupRoot root key.toList with
  | none =>
    cases hm : obj[key]? with
    | none => rfl
    | some bytes =>
      let v : PresentValue := ⟨bytes, values key bytes hm⟩
      have he := (hr key.toList v).mpr ((mem_mapEntries obj values key v).mpr hm)
      rw [hl] at he
      cases he
  | some v =>
    have hm := (mem_mapEntries obj values key v).mp ((hr key.toList v).mp hl)
    rw [hm]; rfl

end ToVCVio.Trie
