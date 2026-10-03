/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import ToVCVio.Trie.PatriciaSupport

/-!
# Canonical resolved-tree observational extensionality

Library `ToVCVio` in `STFSpecSecurity`. Exact lookup at every finite key determines
an already canonical resolved tree or root. Full optional byte observation retains
the same conclusion. These laws provide no map construction or reference binding.
Spec guidance: `STFSpec/informal/modules/ToVCVio.md` §§5/7.
-/

namespace ToVCVio.Trie
open STFSpec.Commit

private abbrev Key := List (Fin 16)

private def slots (children : Fin 16 → Option FullTree) : List (Fin 16) :=
  (List.ofFn (fun i : Fin 16 ↦ i)).filter (fun i ↦ (children i).isSome)

private theorem fullCount_eq_slots (children : Fin 16 → Option FullTree) :
    fullCount children = (slots children).length := by
  have hm : (List.ofFn (fun i : Fin 16 ↦ i)).map children = List.ofFn children := by
    simpa only [Function.comp_def] using
      (List.map_ofFn (f := fun i : Fin 16 ↦ i) (g := children))
  rw [fullCount, ← hm, List.filter_map, List.length_map]
  rfl

private theorem slots_nodup (children : Fin 16 → Option FullTree) :
    (slots children).Nodup := by
  have hn : (List.ofFn (fun i : Fin 16 ↦ i)).Nodup := by
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

private theorem fullCount_exists_pair (children : Fin 16 → Option FullTree)
    (h : 2 ≤ fullCount children) : ∃ (i j : Fin 16) (child other : FullTree),
      i ≠ j ∧ children i = some child ∧ children j = some other := by
  rw [fullCount_eq_slots] at h
  obtain ⟨i, hi, j, hj, hij⟩ := list_two_distinct (slots children) (slots_nodup children) h
  obtain ⟨child, hc⟩ := slot_some children i hi
  obtain ⟨other, ho⟩ := slot_some children j hj
  exact ⟨i, j, child, other, hij, hc, ho⟩

/-- A finite prefix means exact list concatenation with a residual path. -/
private def KeyPrefix (p key : Key) : Prop := ∃ rest, key = p ++ rest

/-- Universal quantification ranges over every complete present lookup key and value. -/
private def SharedPrefix (tree : FullTree) (p : Key) : Prop :=
  ∀ key value, lookup tree key = some value → KeyPrefix p key

private theorem canonical_branch_avoids_digit (children : Fin 16 → Option FullTree)
    (terminal : Terminal) (h : Canonical (.branch children terminal)) (digit : Fin 16) :
    ∃ key value, lookup (.branch children terminal) key = some value ∧
      ∀ rest, key ≠ digit :: rest := by
  cases h with
  | branch children terminal childCanonical occupancy =>
    cases terminal with
    | some value => exact ⟨[], value, lookup_branch_nil _ _, by intro rest; simp⟩
    | none =>
      have hc : 2 ≤ fullCount children := by
        simpa only [terminalCount, Option.isSome_none, Bool.false_eq_true, ite_false,
          Nat.add_zero] using occupancy
      obtain ⟨i, j, c, e, hij, hi, hj⟩ := fullCount_exists_pair children hc
      have witness (slot : Fin 16) (child : FullTree) (hs : children slot = some child)
          (hd : slot ≠ digit) :
          ∃ key value, lookup (.branch children none) key = some value ∧
            ∀ rest, key ≠ digit :: rest := by
        obtain ⟨key, value, hk⟩ := canonical_supported child (childCanonical slot child hs)
        refine ⟨slot :: key, value, ?_, ?_⟩
        · rw [lookup_branch_cons, hs, lookupRoot_some]; exact hk
        · intro rest he; exact hd (List.cons.inj he).1
      by_cases hid : i = digit
      · exact witness j e hj (by intro hjd; exact hij (hid.trans hjd.symm))
      · exact witness i c hi hid

/-- A canonical resolved branch has no nonempty universally shared finite prefix. -/
private theorem canonical_branch_sharedPrefix_iff (children : Fin 16 → Option FullTree)
    (terminal : Terminal) (h : Canonical (.branch children terminal)) (p : Key) :
    SharedPrefix (.branch children terminal) p ↔ p = [] := by
  constructor
  · intro hp
    cases p with
    | nil => rfl
    | cons digit tail =>
      obtain ⟨key, value, hk, avoid⟩ := canonical_branch_avoids_digit children terminal h digit
      obtain ⟨rest, he⟩ := hp key value hk
      exact False.elim (avoid (tail ++ rest) he)
  · intro hp
    subst p
    intro key value _
    exact ⟨key, rfl⟩

/-- Common prefixes of a segment joined to all branch keys are exactly its own prefixes. -/
private theorem canonical_branch_appended_shared_iff (children : Fin 16 → Option FullTree)
    (terminal : Terminal) (h : Canonical (.branch children terminal)) (p q : Key) :
    (∀ key value, lookup (.branch children terminal) key = some value →
      KeyPrefix q (p ++ key)) ↔ KeyPrefix q p := by
  induction p generalizing q with
  | nil =>
    simp only [List.nil_append]
    change SharedPrefix (.branch children terminal) q ↔ KeyPrefix q []
    rw [canonical_branch_sharedPrefix_iff children terminal h]
    cases q <;> simp [KeyPrefix]
  | cons a p ih =>
    cases q with
    | nil => simp [KeyPrefix]
    | cons b q =>
      constructor
      · intro hall
        obtain ⟨key, value, hk⟩ := canonical_supported _ h
        obtain ⟨rest, he⟩ := hall key value hk
        have hba : b = a := (List.cons.inj he).1.symm
        subst b
        have htail : ∀ key value, lookup (.branch children terminal) key = some value →
            KeyPrefix q (p ++ key) := by
          intro key value hk
          obtain ⟨rest, he⟩ := hall key value hk
          exact ⟨rest, (List.cons.inj he).2⟩
        obtain ⟨rest, he⟩ := (ih q).mp htail
        exact ⟨rest, congrArg (List.cons a) he⟩
      · rintro ⟨rest, he⟩ key value _
        exact ⟨rest ++ key, by rw [he, List.append_assoc]⟩

/-- Every present extension key has exactly the extension segment removed. -/
private theorem extension_support_iff (p : Nibbles) (child : FullTree) (key : Key)
    (value : PresentValue) :
    lookup (.extension p child) key = some value ↔
      ∃ rest, key = p.toList ++ rest ∧ lookup child rest = some value := by
  rw [lookup_extension]
  cases hs : stripPrefix p.toList key with
  | none =>
    simp only [Option.bind_none, reduceCtorEq, false_iff]
    rintro ⟨rest, he, _⟩
    have hh := (stripPrefix_some_iff p.toList key rest).mpr he
    rw [hs] at hh
    cases hh
  | some rest =>
    simp only [Option.bind_some]
    constructor
    · intro hv
      exact ⟨rest, (stripPrefix_some_iff _ _ _).mp hs, hv⟩
    · rintro ⟨other, he, hv⟩
      have hh := (stripPrefix_some_iff p.toList key other).mpr he
      rw [hs] at hh
      cases hh
      exact hv

/-- Finite universal maximal-prefix characterization for an extension over a canonical branch.
The proof also covers a zero segment; canonical extensions retain their positive-size premise. -/
private theorem extension_sharedPrefix_iff (p : Nibbles) (children : Fin 16 → Option FullTree)
    (terminal : Terminal) (h : Canonical (.branch children terminal)) (q : Key) :
    SharedPrefix (.extension p (.branch children terminal)) q ↔ KeyPrefix q p.toList := by
  rw [← canonical_branch_appended_shared_iff children terminal h p.toList q]
  constructor
  · intro hall key value hk
    exact hall (p.toList ++ key) value ((lookup_extension_append p _ key).trans hk)
  · intro hall key value hk
    obtain ⟨rest, he, hr⟩ := (extension_support_iff p _ key value).mp hk
    rw [he]
    exact hall rest value hr

private theorem lookup_leaf_arbitrary_iff (path : Nibbles) (value returned : PresentValue)
    (key : Key) : lookup (.leaf path value) key = some returned ↔
      key = path.toList ∧ value = returned := by
  rw [lookup_leaf]
  split <;> simp_all

private theorem canonical_nonleaf_two_keys (tree : FullTree) (h : Canonical tree)
    (hn : ∀ p v, tree ≠ .leaf p v) :
    ∃ k l v w, k ≠ l ∧ lookup tree k = some v ∧ lookup tree l = some w := by
  cases h with
  | leaf p v => exact False.elim (hn p v rfl)
  | branch cs t hc ho => exact canonical_branch_two_keys cs t (.branch cs t hc ho)
  | extension p cs t hp hc =>
    obtain ⟨k, l, v, w, hkl, hk, hl⟩ := canonical_branch_two_keys cs t hc
    refine ⟨p.toList ++ k, p.toList ++ l, v, w, ?_, ?_, ?_⟩
    · intro he; exact hkl (List.append_cancel_left he)
    · exact (lookup_extension_append _ _ _).trans hk
    · exact (lookup_extension_append _ _ _).trans hl

private theorem keyPrefix_antisymm (p q : Key) (hp : KeyPrefix p q) (hq : KeyPrefix q p) :
    p = q := by
  obtain ⟨r, hr⟩ := hp
  obtain ⟨s, hs⟩ := hq
  have hlen := congrArg List.length hr
  have hlen' := congrArg List.length hs
  simp only [List.length_append] at hlen hlen'
  have hz : r.length = 0 := by omega
  have he : r = [] := List.eq_nil_iff_length_eq_zero.mpr hz
  simpa only [he, List.append_nil] using hr.symm

private theorem sharedPrefix_transport (a b : FullTree)
    (he : ∀ key, lookup a key = lookup b key) (p : Key) :
    SharedPrefix a p ↔ SharedPrefix b p := by
  constructor
  · intro ha key value hk; exact ha key value ((he key).trans hk)
  · intro hb key value hk; exact hb key value ((he key).symm.trans hk)


private theorem leaf_lookup_ext (p : Nibbles) (v : PresentValue)
    (b : FullTree) (hb : Canonical b)
    (he : ∀ key, lookup (.leaf p v) key = lookup b key) : .leaf p v = b := by
  cases hb with
  | leaf q w =>
    have hh := (lookup_leaf_arbitrary_iff q w v p.toList).mp
      ((he p.toList).symm.trans (lookup_leaf_exact p v))
    have hp : p = q := Nibbles.ext hh.1
    cases hp
    cases hh.2
    rfl
  | branch cs t hc ho =>
    obtain ⟨k, l, x, y, hkl, hk, hl⟩ := canonical_branch_two_keys cs t (.branch cs t hc ho)
    have hkp := ((lookup_leaf_arbitrary_iff p v x k).mp ((he k).trans hk)).1
    have hlp := ((lookup_leaf_arbitrary_iff p v y l).mp ((he l).trans hl)).1
    exact False.elim (hkl (hkp.trans hlp.symm))
  | extension q cs t hp hc =>
    have hn : ∀ path value, FullTree.extension q (.branch cs t) ≠ .leaf path value := by
      intro path value he; cases he
    obtain ⟨k, l, x, y, hkl, hk, hl⟩ := canonical_nonleaf_two_keys _
      (.extension q cs t hp hc) hn
    have hkp := ((lookup_leaf_arbitrary_iff p v x k).mp ((he k).trans hk)).1
    have hlp := ((lookup_leaf_arbitrary_iff p v y l).mp ((he l).trans hl)).1
    exact False.elim (hkl (hkp.trans hlp.symm))

private theorem positive_extension_branch_lookup_ne (p : Nibbles)
    (cs ds : Fin 16 → Option FullTree) (t u : Terminal) (hp : 0 < p.size)
    (hc : Canonical (.branch cs t)) (hd : Canonical (.branch ds u)) :
    ¬ (∀ key, lookup (.extension p (.branch cs t)) key = lookup (.branch ds u) key) := by
  intro he
  have hprefix : SharedPrefix (.extension p (.branch cs t)) p.toList :=
    (extension_sharedPrefix_iff p cs t hc p.toList).mpr ⟨[], by simp⟩
  have hz := (canonical_branch_sharedPrefix_iff ds u hd p.toList).mp
    ((sharedPrefix_transport _ _ he p.toList).mp hprefix)
  have hl := congrArg List.length hz
  rw [Nibbles.length_toList] at hl
  simp only [List.length_nil] at hl
  omega

/-- Equality at every finite key determines the entire actual canonical tree. -/
theorem canonical_lookup_ext (a b : FullTree) (ha : Canonical a) (hb : Canonical b)
    (he : ∀ key : List (Fin 16), lookup a key = lookup b key) : a = b := by
  induction ha generalizing b with
  | leaf p v => exact leaf_lookup_ext p v b hb he
  | extension p cs t hp hc ih =>
    cases hb with
    | leaf q w => exact (leaf_lookup_ext q w _ (.extension p cs t hp hc)
        (fun key ↦ (he key).symm)).symm
    | branch ds u hd ho =>
      exact False.elim (positive_extension_branch_lookup_ne p cs ds t u hp hc
        (.branch ds u hd ho) he)
    | extension q ds u hq hd =>
      have hpp : SharedPrefix (.extension p (.branch cs t)) p.toList :=
        (extension_sharedPrefix_iff p cs t hc p.toList).mpr ⟨[], by simp⟩
      have hqq : SharedPrefix (.extension q (.branch ds u)) q.toList :=
        (extension_sharedPrefix_iff q ds u hd q.toList).mpr ⟨[], by simp⟩
      have hpq : KeyPrefix p.toList q.toList :=
        (extension_sharedPrefix_iff q ds u hd p.toList).mp
          ((sharedPrefix_transport _ _ he p.toList).mp hpp)
      have hqp : KeyPrefix q.toList p.toList :=
        (extension_sharedPrefix_iff p cs t hc q.toList).mp
          ((sharedPrefix_transport _ _ he q.toList).mpr hqq)
      have hpq' : p = q := Nibbles.ext (keyPrefix_antisymm _ _ hpq hqp)
      subst q
      have hchild : FullTree.branch cs t = .branch ds u := ih _ hd (by
        intro key
        have hh := he (p.toList ++ key)
        simpa only [lookup_extension_append] using hh)
      exact congrArg (FullTree.extension p) hchild
  | branch cs t hc ho ih =>
    cases hb with
    | leaf q w => exact (leaf_lookup_ext q w _ (.branch cs t hc ho)
        (fun key ↦ (he key).symm)).symm
    | extension q ds u hq hd =>
      exact False.elim (positive_extension_branch_lookup_ne q ds cs u t hq hd
        (.branch cs t hc ho) (fun key ↦ (he key).symm))
    | branch ds u hd hu =>
      have hterminal : t = u := by
        simpa only [lookup_branch_nil] using he []
      have hchildren : cs = ds := by
        funext i
        have hslot : ∀ key, lookupRoot (cs i) key = lookupRoot (ds i) key := by
          intro key
          simpa only [lookup_branch_cons] using he (i :: key)
        cases hs : cs i with
        | none =>
          cases ht : ds i with
          | none => rfl
          | some other =>
            obtain ⟨key, value, hkey⟩ := canonical_supported other (hd i other ht)
            have hh := hslot key
            rw [hs, ht, lookupRoot_none, lookupRoot_some, hkey] at hh
            cases hh
        | some child =>
          cases ht : ds i with
          | none =>
            obtain ⟨key, value, hkey⟩ := canonical_supported child (hc i child hs)
            have hh := hslot key
            rw [hs, ht, lookupRoot_none, lookupRoot_some, hkey] at hh
            cases hh
          | some other =>
            exact congrArg some (ih i child hs other (hd i other ht) (by
              intro key
              have hh := hslot key
              simpa only [hs, ht, lookupRoot_some] using hh))
      cases hchildren
      cases hterminal
      rfl

/-- Optional-root extensionality requires actual canonicality on both roots. -/
theorem canonicalRoot_lookup_ext (a b : Option FullTree)
    (ha : CanonicalRoot a) (hb : CanonicalRoot b)
    (he : ∀ key : List (Fin 16), lookupRoot a key = lookupRoot b key) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some tree =>
      obtain ⟨key, value, hkey⟩ := canonical_supported tree hb
      have hh := he key
      rw [lookupRoot_none, lookupRoot_some, hkey] at hh
      cases hh
  | some tree =>
    cases b with
    | none =>
      obtain ⟨key, value, hkey⟩ := canonical_supported tree ha
      have hh := he key
      rw [lookupRoot_none, lookupRoot_some, hkey] at hh
      cases hh
    | some other =>
      apply congrArg some
      apply canonical_lookup_ext tree other ha hb
      intro key
      simpa only [lookupRoot_some] using he key

private theorem present_projection_injective (a b : Terminal)
    (he : a.map Subtype.val = b.map Subtype.val) : a = b := by
  cases a with
  | none => cases b with
    | none => rfl
    | some value => cases he
  | some value => cases b with
    | none => cases he
    | some other => exact congrArg some (Subtype.ext (Option.some.inj he))

private theorem observe_lookupRoot (root : Option FullTree) (key : Nibbles) :
    observe root key = (lookupRoot root key.toList).map Subtype.val := by
  cases root with
  | none => rw [observe_none, lookupRoot_none]; rfl
  | some tree => rw [observe_some, lookupRoot_some]

/-- Full optional byte observation at every packed key determines a canonical root. -/
theorem canonicalRoot_observe_ext (a b : Option FullTree)
    (ha : CanonicalRoot a) (hb : CanonicalRoot b)
    (he : ∀ key : Nibbles, observe a key = observe b key) : a = b := by
  apply canonicalRoot_lookup_ext a b ha hb
  intro key
  apply present_projection_injective
  have hh := he (Nibbles.ofList key)
  simpa only [observe_lookupRoot, Nibbles.toList_ofList] using hh


end ToVCVio.Trie
