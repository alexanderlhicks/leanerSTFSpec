/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit

/-!
# Imported typed-trie clients

Library `EthConformance`. Public-only clients for EthCommit C11/Q53; no owner,
map implementation or provider representation is unfolded.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/7.0.3.
-/

namespace STFSpec.Conformance.Commit.TrieCallerProofs

open STFSpec.Base STFSpec.Commit

variable {K V : Type} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
variable [BEq V] [LawfulBEq V]

/-- A copied trie can be updated without changing a distinct-key observation. -/
theorem copy_then_set_other (t : Trie K V) (k a : K) (v : V) (hne : a ≠ k) :
    trieGet (trieSet (copyTrie t) k v) a = trieGet t a := by
  rw [trieGet_set_of_ne (copyTrie t) k a v hne, copyTrie_get]

/-- A nondefault replacement is safe exactly when the new value is valid. -/
theorem safe_nondefault_replacement [TrieValue V] (t : Trie K V) (k : K) (v : V)
    (hsafe : t.PrepareSafe) (hv : v ≠ t.default) :
    (trieSet t k v).PrepareSafe ↔ TrieValue.Valid v := by
  rw [trieSet_prepareSafe_iff t k v hsafe]
  exact ⟨fun h ↦ h.resolve_left hv, Or.inr⟩

/-- A valid write to a safe copy retains preparation safety. -/
theorem persistent_safe_copy [TrieValue V] (t : Trie K V) (k : K) (v : V)
    (hsafe : t.PrepareSafe) (hv : TrieValue.Valid v) :
    (trieSet (copyTrie t) k v).PrepareSafe := by
  apply (trieSet_prepareSafe_iff (copyTrie t) k v ((copyTrie_prepareSafe t).mpr hsafe)).mpr
  exact Or.inr hv

/-- Deleting one key repairs safety when every retained old binding is valid. -/
theorem delete_repair [TrieValue V] (t : Trie K V) (k : K)
    (retained : ∀ a w, a ≠ k → t.data[a]? = some w → TrieValue.Valid w) :
    (trieSet t k t.default).PrepareSafe :=
  (trieSet_delete_prepareSafe_iff t k).mpr retained

/-- A final same-key write supersedes every earlier value. -/
theorem final_write (t : Trie K V) (k : K) (v w : V) :
    trieGet (trieSet (trieSet t k v) k w) k = w := by
  rw [trieSet_overwrite, trieGet_set_same]

/-- The public setter laws compose both independent proof predicates. -/
theorem combined_invariants [TrieValue V] (t : Trie K V) (k : K) (v : V)
    (hdefault : t.NoDefault) (hsafe : t.PrepareSafe)
    (admissible : v = t.default ∨ TrieValue.Valid v) :
    (trieSet t k v).NoDefault ∧ (trieSet t k v).PrepareSafe :=
  ⟨trieSet_noDefault t k v hdefault, (trieSet_prepareSafe_iff t k v hsafe).mpr admissible⟩

end STFSpec.Conformance.Commit.TrieCallerProofs

namespace STFSpec.Conformance.Commit.TrieProviderClients

open STFSpec.Base STFSpec.Commit

/-- Existing fixed-byte key ordering and word equality require no encoding instance. -/
theorem address_word (t : Trie Address U256) (k : Address) (v : U256) :
    trieGet (trieSet t k v) k = v := trieGet_set_same t k v

/-- Existing Hash32 order and Bytes equality support exact default deletion. -/
theorem hash_bytes (t : Trie Hash32 Bytes) (k : Hash32) (v : Bytes) :
    (trieSet t k v).data[k]? = none ↔ v = t.default := trieSet_erases_iff t k v

/-- Existing word keys support all-value natural storage without any encoding instance. -/
theorem word_nat (t : Trie U256 Nat) (k : U256) (v : Nat) :
    trieGet (trieSet t k v) k = v := trieGet_set_same t k v

/-- Existing Nibbles keys support optional Bytes storage without key adaptation. -/
theorem path_bytes (t : Trie Nibbles (Option Bytes)) (k : Nibbles) (v : Option Bytes) :
    trieGet (trieSet t k v) k = v := trieGet_set_same t k v

end STFSpec.Conformance.Commit.TrieProviderClients
