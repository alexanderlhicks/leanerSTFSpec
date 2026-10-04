/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import ToVCVio.Trie.PatriciaRealization

/-!
# Public clients for finite-map observational realization

Library `ToVCVio` in `STFSpecSecurity`. Symbolic clients retain the actual map and
nonempty-value domain. Complete byte fixtures distinguish absent values, empty
bytes and repeated equal values without selecting an existential proof witness.
Spec guidance: `STFSpec/informal/modules/ToVCVio.md` §§4/7.
-/

open STFSpec.Commit ToVCVio.Trie
namespace ToVCVio.Test.Realization
/-- Arbitrary actual maps consume only the complete nonempty-value premise. -/
theorem arbitrary (obj : Std.ExtTreeMap Nibbles ByteArray) (values : NonemptyValues obj) :
    ∃ root : Option FullTree, CanonicalRoot root ∧
      ∀ key : Nibbles, observe root key = obj[key]? := nonemptyValues_realized obj values
private theorem insert_nonempty (obj : Std.ExtTreeMap Nibbles ByteArray)
    (values : NonemptyValues obj) (key : Nibbles) (bytes : ByteArray)
    (nonempty : bytes ≠ ByteArray.empty) : NonemptyValues (obj.insert key bytes) := by
  intro q b hb
  rw [Std.ExtTreeMap.getElem?_insert] at hb
  split at hb
  · cases hb; exact nonempty
  · exact values q b hb
private theorem empty_values : NonemptyValues (∅ : Std.ExtTreeMap Nibbles ByteArray) := by
  intro key bytes h
  simp only [Std.ExtTreeMap.getElem?_empty] at h
  cases h
/-- Arbitrary insertion, including empty or prefix keys and repeated values, retains the domain. -/
theorem arbitrary_insert (obj : Std.ExtTreeMap Nibbles ByteArray) (values : NonemptyValues obj)
    (key : Nibbles) (bytes : ByteArray) (nonempty : bytes ≠ ByteArray.empty) :
    ∃ root : Option FullTree, CanonicalRoot root ∧
      ∀ q : Nibbles, observe root q = (obj.insert key bytes)[q]? :=
  arbitrary _ (insert_nonempty obj values key bytes nonempty)
/-- The empty actual map has the all-finite realization witness without a present tree. -/
theorem empty_realized : ∃ root : Option FullTree, CanonicalRoot root ∧
    ∀ key : Nibbles, observe root key = (∅ : Std.ExtTreeMap Nibbles ByteArray)[key]? :=
  arbitrary _ empty_values
/-- No present canonical tree realizes the empty map; support uses a complete finite key. -/
theorem empty_present_impossible (tree : FullTree) (hc : Canonical tree)
    (he : ∀ key : Nibbles,
      observe (some tree) key = (∅ : Std.ExtTreeMap Nibbles ByteArray)[key]?) : False := by
  obtain ⟨key, value, hv⟩ := canonical_supported tree hc
  have hh := he (Nibbles.ofList key)
  rw [observe_some, Nibbles.toList_ofList, hv, Std.ExtTreeMap.getElem?_empty] at hh
  cases hh
/-- Any stored empty bytes contradict the full observation law, even without canonicality. -/
theorem empty_bytes_impossible (obj : Std.ExtTreeMap Nibbles ByteArray) (key : Nibbles)
    (stored : obj[key]? = some ByteArray.empty) (root : Option FullTree)
    (he : ∀ q, observe root q = obj[q]?) : False := by
  have hh := (he key).trans stored
  cases root with
  | none => rw [observe_none] at hh; cases hh
  | some tree =>
    rw [observe_some] at hh
    cases hl : lookup tree key.toList with
    | none => rw [hl] at hh; cases hh
    | some value =>
      rw [hl] at hh
      exact value.property (Option.some.inj hh)
/-- Two distinct complete values at the same raw list key cannot both be realized. -/
theorem duplicate_values_impossible (root : Option FullTree) (key : List (Fin 16))
    (v w : PresentValue) (different : v ≠ w)
    (hv : lookupRoot root key = some v) (hw : lookupRoot root key = some w) : False :=
  different (Option.some.inj (hv.symm.trans hw))
private def a : ByteArray := [0, 255, 0].toByteArray
private def b : ByteArray := [0, 255, 0, 0].toByteArray
private def prefixMap : Std.ExtTreeMap Nibbles ByteArray :=
  (∅ : Std.ExtTreeMap Nibbles ByteArray).insert (Nibbles.ofList []) a
    |>.insert (Nibbles.ofList [0, 15]) a
    |>.insert (Nibbles.ofList [0, 15, 0]) b
/-- Prefix terminals and longer keys coexist; identical shorter values remain separate keys. -/
theorem prefix_terminals : ∃ root : Option FullTree, CanonicalRoot root ∧
    ∀ key : Nibbles, observe root key = prefixMap[key]? := by
  apply arbitrary
  apply insert_nonempty
  · apply insert_nonempty
    · exact insert_nonempty _ empty_values _ _ (by decide)
    · decide
  · decide
/-- All arbitrary finite path lengths, including odd lengths, retain the complete value. -/
theorem arbitrary_length (n : Nat) (bytes : ByteArray) (nonempty : bytes ≠ ByteArray.empty) :
    ∃ root : Option FullTree, CanonicalRoot root ∧ ∀ key : Nibbles,
      observe root key = ((∅ : Std.ExtTreeMap Nibbles ByteArray).insert
        (Nibbles.ofList (List.replicate n 15)) bytes)[key]? :=
  arbitrary_insert _ empty_values _ bytes nonempty
/-- The 129-digit and 137-digit cases instantiate the same universal proof. -/
theorem long_paths :
    (∃ root, CanonicalRoot root ∧ ∀ key : Nibbles,
      observe root key = ((∅ : Std.ExtTreeMap Nibbles ByteArray).insert
        (Nibbles.ofList (List.replicate 129 15)) a)[key]?) ∧
    (∃ root, CanonicalRoot root ∧ ∀ key : Nibbles,
      observe root key = ((∅ : Std.ExtTreeMap Nibbles ByteArray).insert
        (Nibbles.ofList (List.replicate 137 15)) b)[key]?) :=
  ⟨arbitrary_length 129 a (by decide), arbitrary_length 137 b (by decide)⟩
/-- An actually stored empty value violates NonemptyValues rather than silently disappearing. -/
theorem empty_value_domain_omission (key : Nibbles) :
    ¬ NonemptyValues ((∅ : Std.ExtTreeMap Nibbles ByteArray).insert key ByteArray.empty) := by
  intro values
  apply values key ByteArray.empty
  · rw [Std.ExtTreeMap.getElem?_insert,
      ite_eq_left ((Nibbles.compare_eq_eq_iff key key).mpr rfl)]
  · rfl
private theorem fold_nonempty (keys : List Nibbles) (obj : Std.ExtTreeMap Nibbles ByteArray)
    (values : NonemptyValues obj) (bytes : ByteArray) (nonempty : bytes ≠ ByteArray.empty) :
    NonemptyValues (keys.foldl (fun m k ↦ m.insert k bytes) obj) := by
  induction keys generalizing obj with
  | nil => exact values
  | cons key rest ih => exact ih _ (insert_nonempty obj values key bytes nonempty)
/-- Arbitrary finite insertion histories permit repetitions and equal complete values. -/
theorem repeated_values (keys : List Nibbles) (bytes : ByteArray)
    (nonempty : bytes ≠ ByteArray.empty) :
    ∃ root : Option FullTree, CanonicalRoot root ∧ ∀ key : Nibbles,
      observe root key = (keys.foldl (fun m k ↦ m.insert k bytes)
        (∅ : Std.ExtTreeMap Nibbles ByteArray))[key]? :=
  arbitrary _ (fold_nonempty keys _ empty_values bytes nonempty)
/-- All sixteen positions with identical values include the optional empty-key terminal. -/
theorem all_positions_equal_values (withTerminal : Bool) :
    ∃ root : Option FullTree, CanonicalRoot root ∧ ∀ key : Nibbles,
      observe root key = (((if withTerminal then [Nibbles.ofList []] else []) ++
        List.ofFn (fun i : Fin 16 ↦ Nibbles.ofList [i])).foldl
          (fun m k ↦ m.insert k a) (∅ : Std.ExtTreeMap Nibbles ByteArray))[key]? := by
  exact repeated_values _ a (by decide)
/-- Equal complete map histories induce equal complete root observations. -/
theorem histories_observe (a b : Std.ExtTreeMap Nibbles ByteArray)
    (ha : NonemptyValues a) (hb : NonemptyValues b) (he : ∀ key : Nibbles, a[key]? = b[key]?) :
    ∃ r s : Option FullTree, CanonicalRoot r ∧ CanonicalRoot s ∧
      ∀ key : Nibbles, observe r key = observe s key := by
  obtain ⟨r, hr, ho⟩ := arbitrary a ha
  obtain ⟨s, hs, hp⟩ := arbitrary b hb
  exact ⟨r, s, hr, hs, fun key ↦ (ho key).trans ((he key).trans (hp key).symm)⟩


/-- Safe pure model preparation supplies exactly the public nonempty-value premise. -/
theorem prepared_model {K V : Type} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
    [TrieValue V] [KeyBytes K] (t : STFSpec.Commit.Trie K V) (safe : t.PrepareSafe) :
    ∃ root : Option FullTree, CanonicalRoot root ∧
      ∀ key : Nibbles, observe root key = (prepareTrieModel t)[key]? :=
  nonemptyValues_realized _ (prepareTrieModel_nonemptyValues t safe)

/-- Empty, odd and even finite paths instantiate the same actual-map law. -/
theorem short_paths :
    (∃ root, CanonicalRoot root ∧ ∀ key : Nibbles,
      observe root key = ((∅ : Std.ExtTreeMap Nibbles ByteArray).insert
        (Nibbles.ofList []) a)[key]?) ∧
    (∃ root, CanonicalRoot root ∧ ∀ key : Nibbles,
      observe root key = ((∅ : Std.ExtTreeMap Nibbles ByteArray).insert
        (Nibbles.ofList [15]) b)[key]?) ∧
    (∃ root, CanonicalRoot root ∧ ∀ key : Nibbles,
      observe root key = ((∅ : Std.ExtTreeMap Nibbles ByteArray).insert
        (Nibbles.ofList [15, 15]) a)[key]?) :=
  ⟨arbitrary_length 0 a (by decide), arbitrary_length 1 b (by decide),
    arbitrary_length 2 a (by decide)⟩

/-- Equal support does not identify the complete value observations. -/
theorem support_only_insufficient (p : Nibbles) (v w : PresentValue)
    (different : v.val ≠ w.val) :
    (∀ key, (lookup (.leaf p v) key).isSome = (lookup (.leaf p w) key).isSome) ∧
    observe (some (.leaf p v)) p ≠ observe (some (.leaf p w)) p := by
  constructor
  · intro key
    rw [lookup_leaf, lookup_leaf]
    split <;> rfl
  · intro equal
    rw [observe_some, observe_some, lookup_leaf_exact, lookup_leaf_exact] at equal
    exact different (Option.some.inj equal)

private def present : PresentValue := ⟨a, by decide⟩
private def other : PresentValue := ⟨b, by decide⟩
private def oneChildren (digit : Fin 16) : Fin 16 → Option FullTree :=
  fun i ↦ if i = digit then some (.leaf (Nibbles.ofList []) present) else none
private def twoChildren : Fin 16 → Option FullTree :=
  fun i ↦ if i = 0 ∨ i = 15 then some (.leaf (Nibbles.ofList []) present) else none
private def allChildren : Fin 16 → Option FullTree :=
  fun _ ↦ some (.leaf (Nibbles.ofList []) present)

/-- A terminal and one child remain a branch in the actual canonical grammar. -/
theorem terminal_one (digit : Fin 16) :
    Canonical (.branch (oneChildren digit) (some other)) := by
  apply canonical_one_child_terminal _ _ _
    ((by decide : ∀ i : Fin 16, fullCount (oneChildren i) = 1) digit)
  intro i tree h
  unfold oneChildren at h
  split at h
  · cases h
    exact .leaf _ _
  · cases h

/-- Two identical present children count separately at their numeric positions. -/
theorem two_identical : Canonical (.branch twoChildren none) := by
  apply Canonical.branch
  · intro i tree h
    unfold twoChildren at h
    split at h
    · cases h
      exact .leaf _ _
    · cases h
  · decide

/-- All sixteen identical children allow either a terminal or no terminal. -/
theorem all_identical (terminal : Terminal) : Canonical (.branch allChildren terminal) := by
  apply Canonical.branch
  · intro i tree h
    cases h
    exact .leaf _ _
  · have count : fullCount allChildren = 16 := by decide
    rw [count]
    omega

/-- Independently specified fixtures retain complete Option tags and byte arrays.
No tree is chosen from the existential theorem and no runtime normalizer is used. -/
def observations : List (Option ByteArray × Option ByteArray) :=
  let emptyMap : Std.ExtTreeMap Nibbles ByteArray := ∅
  let singleton := emptyMap.insert (Nibbles.ofList []) a
  let oneMap := singleton.insert (Nibbles.ofList [15]) b
  let twoMap := (emptyMap.insert (Nibbles.ofList [0]) a).insert (Nibbles.ofList [15]) a
  let allMap := (List.ofFn (fun i : Fin 16 ↦ Nibbles.ofList [i])).foldl
    (fun m key ↦ m.insert key a) emptyMap
  let longKey := Nibbles.ofList (List.replicate 137 15 ++ [0])
  let longMap := emptyMap.insert longKey b
  let prefixTree := FullTree.branch
    (fun i ↦ if i = 0 then
      some (.extension (Nibbles.ofList [15])
        (.branch (fun j ↦ if j = 0 then some (.leaf (Nibbles.ofList []) other) else none)
          (some present))) else none) (some present)
  let cases : List (Option FullTree × Std.ExtTreeMap Nibbles ByteArray) :=
    [(none, emptyMap), (some (.leaf (Nibbles.ofList []) present), singleton),
      (some (.branch (fun i ↦ if i = 15 then
        some (.leaf (Nibbles.ofList []) other) else none) (some present)), oneMap),
      (some (.branch twoChildren none), twoMap),
      (some (.branch allChildren none), allMap),
      (some (.branch allChildren (some present)), singleton.union allMap),
      (some (.leaf longKey other), longMap), (some prefixTree, prefixMap)]
  let queries := [Nibbles.ofList [], Nibbles.ofList [0, 15],
    Nibbles.ofList [0, 15, 0], Nibbles.ofList [0, 15, 0, 15], longKey,
    Nibbles.ofList (List.replicate 137 15), Nibbles.ofList (List.replicate 137 15 ++ [1])] ++
    List.ofFn (fun i : Fin 16 ↦ Nibbles.ofList [i])
  cases.flatMap fun (root, map) ↦ queries.map fun key ↦ (observe root key, map[key]?)

end ToVCVio.Test.Realization
