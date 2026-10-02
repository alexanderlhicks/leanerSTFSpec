/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit

/-!
# Imported preparation clients

Library `EthConformance`. Public owner/model/provider contracts only. Clients do
not unfold preparation, Nibbles or Std map representations.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/7.0.3; Q53.
-/

namespace STFSpec.Conformance.Commit.PreparationCallerProofs
open STFSpec.Commit

variable {K V : Type} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
variable [TrieValue V] [KeyBytes K]

/-- Equal complete optional source observations suffice for equal preparation. -/
theorem equal_observations (t u : Trie K V)
    (h : ∀ k : K, t.data[k]? = u.data[k]?) : prepareTrieModel t = prepareTrieModel u :=
  prepareTrieModel_congr t u (Std.ExtTreeMap.ext_getElem? h)

omit [Std.LawfulEqOrd K] in
/-- Copying retains every prepared binding. -/
theorem copied_preparation (t : Trie K V) :
    prepareTrieModel (copyTrie t) = prepareTrieModel t :=
  prepareTrieModel_congr (copyTrie t) t (copyTrie_data t)

/-- A prepared value is nonempty because its original stored value is valid. -/
theorem consumer_nonempty (t : Trie K V) (safe : t.PrepareSafe)
    (q : Nibbles) (b : ByteArray) (h : (prepareTrieModel t)[q]? = some b) :
    b ≠ ByteArray.empty := prepareTrieModel_image_nonempty t safe q b h

omit [Std.TransOrd K] [Std.LawfulEqOrd K] in
/-- Every prepared path identifies a unique original key, even if values alias. -/
theorem unique_source_key (a b : K)
    (h : bytesToNibbleList (KeyBytes.toBytes a) =
      bytesToNibbleList (KeyBytes.toBytes b)) : a = b := keyBytes_path_injective h

/-- Public pure equation is sufficient for State forwarding and no local effect. -/
theorem state_unchanged (t : Trie K V) (unsecured : t.secured = false)
    (safe : t.PrepareSafe) (state : Nat) :
    (prepareTrie (m := StateM Nat) t unsecured safe).run state =
      (prepareTrieModel t, state) := by
  rw [prepareTrie_eq]
  rfl

/-- Public pure equation supplies success in Except with no oracle requirement. -/
theorem except_success (t : Trie K V) (unsecured : t.secured = false)
    (safe : t.PrepareSafe) :
    prepareTrie (m := Except String) t unsecured safe = .ok (prepareTrieModel t) := by
  rw [prepareTrie_eq]
  rfl

/-- Cardinality and empty-image contracts compose without any encoding injection. -/
theorem cardinality_and_empty (t : Trie K V) :
    (prepareTrieModel t).size = t.data.size ∧
      (prepareTrieModel t = ∅ ↔ t.data = ∅) :=
  ⟨prepareTrieModel_size t, prepareTrieModel_empty_iff t⟩

end STFSpec.Conformance.Commit.PreparationCallerProofs
