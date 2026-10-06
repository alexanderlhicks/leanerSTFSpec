/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit

/-!
# Imported preparation clients

Library `EthConformance`. Public owner/model/provider contracts only. Clients do
not unfold preparation, Nibbles or Std map representations. Existing Bytes clients
consume the exact packed-export adapter law and Q54 provider contracts.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/7.0.3; Q53/Q54.
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

section BytesKeys

open STFSpec.Base STFSpec.Hash

-- No local Bytes instance: these clients resolve the production public import.
private theorem bytes_key_instance :
    (inferInstance : KeyBytes Bytes) = instKeyBytesBytes := rfl

private theorem bytes_key_export (k : Bytes) :
    KeyBytes.toBytes k = k.toByteArray := toBytes_bytes k

private theorem bytes_key_exact_path (k : Bytes) :
    bytesToNibbleList (KeyBytes.toBytes k) = bytesToNibbleList k.toByteArray :=
  congrArg bytesToNibbleList (toBytes_bytes k)

private theorem bytes_key_injective (a b : Bytes)
    (h : KeyBytes.toBytes a = KeyBytes.toBytes b) : a = b :=
  KeyBytes.toBytes_injective h

private theorem bytes_key_order (a b : Bytes) :
    compare a b = compare (KeyBytes.toBytes a).toList (KeyBytes.toBytes b).toList :=
  KeyBytes.compare_toBytes a b

private theorem bytes_key_compare_eq_iff (a b : Bytes) :
    compare (KeyBytes.toBytes a).toList (KeyBytes.toBytes b).toList = .eq ↔ a = b := by
  rw [← bytes_key_order]
  exact Bytes.compare_eq_eq_iff a b

private theorem bytes_key_path_eq (a b : Bytes)
    (h : bytesToNibbleList (KeyBytes.toBytes a) =
      bytesToNibbleList (KeyBytes.toBytes b)) : a = b := keyBytes_path_injective h

-- Caller-supplied value encoding is retained for each complete generic map.
private theorem bytes_prepared_lookup (t : Trie Bytes V) (k : Bytes) :
    (prepareTrieModel t)[bytesToNibbleList k.toByteArray]? =
      (t.data[k]?).map TrieValue.encode := prepareTrieModel_lookup t k

private theorem bytes_prepared_full_image (t : Trie Bytes V) (q : Nibbles)
    (b : ByteArray) :
    (prepareTrieModel t)[q]? = some b ↔
      ∃ (k : Bytes) (v : V), t.data[k]? = some v ∧
        q = bytesToNibbleList k.toByteArray ∧ b = TrieValue.encode v :=
  prepareTrieModel_lookup_some_iff t q b

private theorem bytes_prepared_cardinality (t : Trie Bytes V) :
    (prepareTrieModel t).size = t.data.size := prepareTrieModel_size t

private theorem bytes_prepared_empty (t : Trie Bytes V) :
    prepareTrieModel t = ∅ ↔ t.data = ∅ := prepareTrieModel_empty_iff t

private theorem bytes_prepared_insert (t : Trie Bytes V) (k : Bytes) (v : V) :
    prepareTrieModel { t with data := t.data.insert k v } =
      (prepareTrieModel t).insert (bytesToNibbleList k.toByteArray) (TrieValue.encode v) :=
  prepareTrieModel_insert t k v

private theorem bytes_prepared_overwrite (t : Trie Bytes V) (k : Bytes) (old new : V) :
    prepareTrieModel { t with data := (t.data.insert k old).insert k new } =
      (prepareTrieModel t).insert (bytesToNibbleList k.toByteArray)
        (TrieValue.encode new) := by
  have storage : (t.data.insert k old).insert k new = t.data.insert k new := by
    apply Std.ExtTreeMap.ext_getElem?
    intro q
    simp only [Std.ExtTreeMap.getElem?_insert]
    split <;> rfl
  rw [storage]
  exact bytes_prepared_insert t k new

private theorem bytes_preparation_action {m : Type → Type} [Monad m]
    (t : Trie Bytes V) (unsecured : t.secured = false) (safe : t.PrepareSafe) :
    prepareTrie (m := m) t unsecured safe = pure (prepareTrieModel t) :=
  prepareTrie_eq t unsecured safe

private theorem bytes_preparation_empty_action {m : Type → Type} [Monad m]
    (t : Trie Bytes V) (unsecured : t.secured = false) (safe : t.PrepareSafe)
    (empty : t.data = ∅) : prepareTrie (m := m) t unsecured safe = pure ∅ :=
  prepareTrie_empty t unsecured safe empty

private theorem bytes_root_action {m : Type → Type} [Monad m] [KeccakQuery m]
    (emptyRoot : Hash32) (t : Trie Bytes V) (unsecured : t.secured = false)
    (safe : t.PrepareSafe) :
    root (m := m) emptyRoot t unsecured safe = mathRoot emptyRoot (prepareTrieModel t) :=
  root_eq_mathRoot emptyRoot t unsecured safe

private theorem bytes_root_empty {m : Type → Type} [Monad m] [KeccakQuery m]
    (emptyRoot : Hash32) (t : Trie Bytes V) (unsecured : t.secured = false)
    (safe : t.PrepareSafe) (empty : t.data = ∅) :
    root (m := m) emptyRoot t unsecured safe = pure emptyRoot :=
  root_empty emptyRoot t unsecured safe empty

private theorem bytes_root_sequenced {m : Type → Type} [Monad m] [KeccakQuery m]
    [LawfulMonad m] (emptyRoot : Hash32) (t : Trie Bytes V)
    (unsecured : t.secured = false) (safe : t.PrepareSafe) :
    root (m := m) emptyRoot t unsecured safe = (do
      let prepared ← prepareTrie (m := m) t unsecured safe
      mathRoot emptyRoot prepared) := root_eq_reference emptyRoot t unsecured safe

end BytesKeys

end STFSpec.Conformance.Commit.PreparationCallerProofs
