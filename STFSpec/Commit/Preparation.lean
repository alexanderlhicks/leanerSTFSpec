/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.Trie
import STFSpec.Commit.Nibbles

/-!
# Pure unsecured typed-trie preparation

Library `EthCommit`. Pinned EELS `src/ethereum/merkle_patricia_trie.py:407–475`.
Preparation visits the complete stored map once, encodes each binding once and
inserts its injectively interpreted byte-key path. No default or validity filter
is executed. Safety and the unsecured domain are separate erased proof arguments.
The mapped-list reference is proof support, beside the executable packed-key fold.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/5/7.0.3; Q53.
-/

namespace STFSpec.Commit

/-- Injective byte-key interpretation agreeing with the lawful key comparator.
The byte-list comparison is a proof contract, not an executable key conversion.
No concrete Bytes/ByteArray adapter is selected here (Q53). -/
class KeyBytes (K : Type) [Ord K] where
  /-- Complete finite bytes of the key, including empty keys and leading zeros. -/
  toBytes : K → ByteArray
  /-- Distinct typed keys cannot represent equal byte contents. -/
  toBytes_injective : Function.Injective toBytes
  /-- Key order agrees exactly with byte-content lexicographic order. -/
  compare_toBytes : ∀ a b,
    compare a b = compare (toBytes a).toList (toBytes b).toList

variable {K V : Type} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

-- Injectivity uses only the public splitter model and byte reconstruction.
private theorem splitModel_injective : Function.Injective bytesToNibbleListModel := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons b ys => simp [bytesToNibbleListModel] at h
  | cons a xs ih =>
    intro ys h
    cases ys with
    | nil => simp [bytesToNibbleListModel] at h
    | cons b ys =>
      simp only [bytesToNibbleListModel, List.flatMap_cons, List.cons_append,
        List.nil_append, List.cons.injEq] at h
      rcases h with ⟨hh, hl, ht⟩
      have ha := highNibble_mul_add_lowNibble a
      have hb := highNibble_mul_add_lowNibble b
      have hab : a = b := UInt8.toNat_inj.mp (by rw [← ha, ← hb, hh, hl])
      have htail : xs = ys := ih ht
      rw [hab, htail]

private theorem split_injective : Function.Injective bytesToNibbleList := by
  intro a b h
  have hmodel := congrArg Nibbles.toList h
  rw [toList_bytesToNibbleList, toList_bytesToNibbleList] at hmodel
  exact ByteArray.ext (Array.toList_inj.mp (splitModel_injective hmodel))

variable [TrieValue V] [KeyBytes K]

local notation "keyPath" => (fun k : K ↦ bytesToNibbleList (KeyBytes.toBytes k))

omit [Std.TransOrd K] [Std.LawfulEqOrd K] in
/-- The interpreted packed nibble path is injective, using public splitter laws. -/
theorem keyBytes_path_injective : Function.Injective (fun k : K ↦ keyPath k) := by
  intro a b h
  exact KeyBytes.toBytes_injective (split_injective h)

/-- EELS `src/ethereum/merkle_patricia_trie.py:407–475` at the pin:
fold directly over stored bindings, encoding each once with no filtering or hashing. -/
def prepareTrieModel (t : Trie K V) : Std.ExtTreeMap Nibbles ByteArray :=
  t.data.foldl (fun out k v =>
    let encoded := TrieValue.encode v
    out.insert (keyPath k) encoded) ∅

-- This list is a proof model only; executable preparation uses the packed/map fold.
private def preparedEntries (t : Trie K V) : List (Nibbles × ByteArray) :=
  t.data.toList.map (fun (k, v) => (keyPath k, TrieValue.encode v))

/-- Legible mapped-entry reference. It is a proof model; execution uses the map fold. -/
def prepareTrieReference (t : Trie K V) : Std.ExtTreeMap Nibbles ByteArray :=
  Std.ExtTreeMap.ofList (preparedEntries t) compare

omit [Std.LawfulEqOrd K] in
/-- The executable fold equals the mapped-list reference on every stored map. -/
theorem prepareTrieModel_eq_reference (t : Trie K V) :
    prepareTrieModel t = prepareTrieReference t := by
  unfold prepareTrieReference
  rw [prepareTrieModel, Std.ExtTreeMap.foldl_eq_foldl_toList,
    Std.ExtTreeMap.ofList_eq_foldl, preparedEntries, List.foldl_map]

private theorem preparedEntries_distinct (t : Trie K V) :
    (preparedEntries t).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
  rw [preparedEntries, List.pairwise_map]
  apply (Std.ExtTreeMap.distinct_keys_toList (t := t.data)).imp
  intro a b h hab
  have he : keyPath a.1 = keyPath b.1 := Std.LawfulEqCmp.eq_of_compare hab
  have hk : a.1 = b.1 := keyBytes_path_injective he
  apply h
  rw [hk]
  exact Std.ReflCmp.compare_self

omit [Std.LawfulEqOrd K] in
private theorem preparedEntries_length (t : Trie K V) :
    (preparedEntries t).length = t.data.size := by
  rw [preparedEntries, List.length_map, Std.ExtTreeMap.length_toList]

/-- Injective key interpretation preserves the complete stored-map cardinality. -/
theorem prepareTrieModel_size (t : Trie K V) : (prepareTrieModel t).size = t.data.size := by
  rw [prepareTrieModel_eq_reference, prepareTrieReference,
    Std.ExtTreeMap.size_ofList (preparedEntries_distinct t), preparedEntries_length]

omit [Std.LawfulEqOrd K] in
/-- Prepared emptiness is exactly stored-map emptiness, without safety premises. -/
theorem prepareTrieModel_empty_iff (t : Trie K V) : prepareTrieModel t = ∅ ↔ t.data = ∅ := by
  rw [prepareTrieModel_eq_reference, prepareTrieReference, Std.ExtTreeMap.ofList_eq_empty_iff,
    preparedEntries, List.map_eq_nil_iff, Std.ExtTreeMap.toList_eq_nil_iff]

/-- Each stored binding appears at its full interpreted byte-key path. -/
theorem prepareTrieModel_lookup_of_some (t : Trie K V) (k : K) (v : V)
    (h : t.data[k]? = some v) :
    (prepareTrieModel t)[keyPath k]? = some (TrieValue.encode v) := by
  rw [prepareTrieModel_eq_reference, prepareTrieReference]
  apply Std.ExtTreeMap.getElem?_ofList_of_mem (Std.ReflCmp.compare_self)
    (preparedEntries_distinct t)
  apply List.mem_map.mpr
  exact ⟨(k, v), Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr h, rfl⟩

/-- The complete prepared image contains exactly interpreted stored bindings.
Encoding injectivity is not required. -/
theorem prepareTrieModel_lookup_some_iff (t : Trie K V) (q : Nibbles) (b : ByteArray) :
    (prepareTrieModel t)[q]? = some b ↔
      ∃ (k : K) (v : V), t.data[k]? = some v ∧ q = keyPath k ∧ b = TrieValue.encode v := by
  constructor
  · intro h
    have hm : q ∈ prepareTrieModel t := by
      rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, h]
      rfl
    rw [prepareTrieModel_eq_reference, prepareTrieReference, Std.ExtTreeMap.mem_ofList] at hm
    have hl : q ∈ (preparedEntries t).map Prod.fst := List.contains_iff_mem.mp hm
    rcases List.mem_map.mp hl with ⟨p, hp, hq⟩
    rcases List.mem_map.mp hp with ⟨⟨k, v⟩, hkv, he⟩
    subst p
    have hk : t.data[k]? = some v := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hkv
    have henc := prepareTrieModel_lookup_of_some t k v hk
    have hq' : q = keyPath k := hq.symm
    rw [hq'] at h
    have hb : b = TrieValue.encode v := Option.some.inj (h.symm.trans henc)
    exact ⟨k, v, hk, hq', hb⟩
  · rintro ⟨k, v, hk, rfl, rfl⟩
    exact prepareTrieModel_lookup_of_some t k v hk

/-- Optional prepared lookup at a typed key is the encoding of its stored lookup.
An absent key never encodes the supplied default. -/
theorem prepareTrieModel_lookup (t : Trie K V) (k : K) :
    (prepareTrieModel t)[keyPath k]? = (t.data[k]?).map TrieValue.encode := by
  cases h : t.data[k]? with
  | some v => simpa only [Option.map_some] using prepareTrieModel_lookup_of_some t k v h
  | none =>
    cases hp : (prepareTrieModel t)[keyPath k]? with
    | none => rfl
    | some b =>
      rcases (prepareTrieModel_lookup_some_iff t _ b).mp hp with ⟨k', v, hk, he, _⟩
      have he' : k = k' := keyBytes_path_injective he
      rw [← he', h] at hk
      cases hk

/-- Preparation safety gives nonempty bytes for every prepared binding. -/
theorem prepareTrieModel_image_nonempty (t : Trie K V) (safe : t.PrepareSafe)
    (q : Nibbles) (b : ByteArray) (h : (prepareTrieModel t)[q]? = some b) :
    b ≠ ByteArray.empty := by
  rcases (prepareTrieModel_lookup_some_iff t q b).mp h with ⟨k, v, hk, _, rfl⟩
  exact TrieValue.encode_ne_empty v (safe k v hk)

omit [Std.LawfulEqOrd K] in
/-- Preparation depends only on the complete stored map, not the other fields. -/
theorem prepareTrieModel_congr (t t' : Trie K V) (h : t.data = t'.data) :
    prepareTrieModel t = prepareTrieModel t' := by
  simp only [prepareTrieModel, h]

/-- Raw map insertion commutes with interpretation and encoding.
This is separate from the default-deleting typed setter. -/
theorem prepareTrieModel_insert (t : Trie K V) (k : K) (v : V) :
    prepareTrieModel { t with data := t.data.insert k v } =
      (prepareTrieModel t).insert (keyPath k) (TrieValue.encode v) := by
  apply Std.ExtTreeMap.ext_getElem?
  intro q
  by_cases hq : q = keyPath k
  · subst q
    rw [Std.ExtTreeMap.getElem?_insert_self]
    exact prepareTrieModel_lookup_of_some _ k v Std.ExtTreeMap.getElem?_insert_self
  · have hcmp : compare (keyPath k) q ≠ .eq := by
      intro he
      exact hq (Std.LawfulEqCmp.eq_of_compare he).symm
    rw [Std.ExtTreeMap.getElem?_insert, ite_eq_right hcmp]
    apply Option.ext
    intro b
    rw [prepareTrieModel_lookup_some_iff, prepareTrieModel_lookup_some_iff]
    constructor
    · rintro ⟨k', v', hk, he, hb⟩
      have hne : compare k k' ≠ .eq := by
        intro hc
        have hkk : k = k' := Std.LawfulEqCmp.eq_of_compare hc
        exact hq (he.trans (congrArg keyPath hkk.symm))
      have hold : t.data[k']? = some v' := by
        simpa only [Std.ExtTreeMap.getElem?_insert, ite_eq_right hne] using hk
      exact ⟨k', v', hold, he, hb⟩
    · rintro ⟨k', v', hk, he, hb⟩
      have hne : compare k k' ≠ .eq := by
        intro hc
        have hkk : k = k' := Std.LawfulEqCmp.eq_of_compare hc
        exact hq (he.trans (congrArg keyPath hkk.symm))
      refine ⟨k', v', ?_, he, hb⟩
      simpa only [Std.ExtTreeMap.getElem?_insert, ite_eq_right hne] using hk

/-- EELS `src/ethereum/merkle_patricia_trie.py:451–475` at the pin, on the
unsecured, valid supported-value domain. Pure preparation introduces no queries,
local failures or default encoding. `NoDefault` is not a premise. -/
def prepareTrie {m : Type → Type} [Monad m] [Std.LawfulEqOrd K] (t : Trie K V)
    (_unsecured : t.secured = false) (_safe : t.PrepareSafe) :
    m (Std.ExtTreeMap Nibbles ByteArray) := pure (prepareTrieModel t)

/-- The complete monadic action is exactly the pure prepared map; Monad suffices. -/
theorem prepareTrie_eq {m : Type → Type} [Monad m] (t : Trie K V)
    (unsecured : t.secured = false) (safe : t.PrepareSafe) :
    prepareTrie (m := m) t unsecured safe = pure (prepareTrieModel t) := rfl

/-- Empty stored data produces the pure empty map for any supplied default. -/
theorem prepareTrie_empty {m : Type → Type} [Monad m] (t : Trie K V)
    (unsecured : t.secured = false) (safe : t.PrepareSafe) (h : t.data = ∅) :
    prepareTrie (m := m) t unsecured safe = pure ∅ := by
  rw [prepareTrie_eq, (prepareTrieModel_empty_iff t).mpr h]

/-- Domain proofs do not change the executable pure action. -/
theorem prepareTrie_proof_irrel {m : Type → Type} [Monad m] (t : Trie K V)
    (unsecured unsecured' : t.secured = false) (safe safe' : t.PrepareSafe) :
    prepareTrie (m := m) t unsecured safe = prepareTrie t unsecured' safe' := rfl

end STFSpec.Commit
