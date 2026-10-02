/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import Std.Data.ExtTreeMap.Lemmas

/-!
# Generic typed-trie storage

Library `EthCommit`. EELS `src/ethereum/merkle_patricia_trie.py:274–347` at the pin.
Storage keeps an arbitrary supplied default and the secured flag, without preparing
values or hashing keys. Both proof predicates are separate from the stored record.
`TrieValue` specifies only total encoding and preparation validity (Q53);
concrete encodings, byte-key interpretation and preparation/root remain consumers'
obligations or remain unimplemented (EthCommit §3).
Spec guidance: `STFSpec/informal/modules/EthCommit.md`.
-/

namespace STFSpec.Commit

/-- Total value encoding with a separate preparation-valid domain (Q53).
No particular default is designated, and invalid encodings make no source-success claim. -/
class TrieValue (V : Type) where
  /-- Total encoding for the chosen value interpretation. -/
  encode : V → ByteArray
  /-- Preparation validity, independent of any trie default. -/
  Valid : V → Prop
  /-- Valid values have nonempty encodings. -/
  encode_ne_empty : ∀ v, Valid v → encode v ≠ ByteArray.empty

/-- EELS `src/ethereum/merkle_patricia_trie.py:274–312` (`Trie`) at the pin:
persistent storage, supplied absence value and deferred secured flag.
EELS `_data` is spelled `data`; no intrinsic default or preparation invariant is imposed. -/
structure Trie (K V : Type) [Ord K] where
  /-- Keys will be hashed only by a later secured preparation operation. -/
  secured : Bool
  /-- The supplied value returned for absence and erased by setters. -/
  default : V
  /-- Persistent stored bindings, with proof predicates kept separately. -/
  data : Std.ExtTreeMap K V

variable {K V : Type} [Ord K]

/-- Field equality determines the complete storage record. -/
theorem Trie.ext {t u : Trie K V} (hs : t.secured = u.secured)
    (hd : t.default = u.default) (hm : t.data = u.data) : t = u := by
  cases t
  cases u
  cases hs
  cases hd
  cases hm
  rfl

/-- EELS `src/ethereum/merkle_patricia_trie.py:315–322` (`copy_trie`) at the pin:
identity because subsequent changes use persistent map operations. -/
def copyTrie (t : Trie K V) : Trie K V := t

/-- Persistent copying is the identity on the complete record. -/
theorem copyTrie_eq (t : Trie K V) : copyTrie t = t := rfl
/-- Copying preserves the complete stored map. -/
theorem copyTrie_data (t : Trie K V) : (copyTrie t).data = t.data := rfl
/-- Copying preserves the supplied absence value. -/
theorem copyTrie_default (t : Trie K V) : (copyTrie t).default = t.default := rfl
/-- Copying preserves the deferred secured flag. -/
theorem copyTrie_secured (t : Trie K V) : (copyTrie t).secured = t.secured := rfl

section Storage
variable [Std.TransOrd K]

/-- Every stored value differs from this trie's supplied default. -/
def Trie.NoDefault (t : Trie K V) : Prop :=
  ∀ (k : K) (v : V), t.data[k]? = some v → v ≠ t.default

/-- Every stored value is valid for its chosen preparation interpretation.
This predicate does not depend on the default or secured flag. -/
def Trie.PrepareSafe [TrieValue V] (t : Trie K V) : Prop :=
  ∀ (k : K) (v : V), t.data[k]? = some v → TrieValue.Valid v

/-- EELS `src/ethereum/merkle_patricia_trie.py:341–347` (`trie_get`) at the pin:
absent keys return exactly the supplied default. -/
def trieGet (t : Trie K V) (k : K) : V := t.data[k]?.getD t.default

/-- Lookup observes the optional stored binding with the supplied default. -/
theorem trieGet_eq (t : Trie K V) (k : K) :
    trieGet t k = t.data[k]?.getD t.default := rfl

/-- A present binding is returned unchanged. -/
theorem trieGet_of_present (t : Trie K V) (k : K) (v : V)
    (h : t.data[k]? = some v) : trieGet t k = v := by
  simp only [trieGet, h, Option.getD_some]

/-- An absent binding returns the supplied default. -/
theorem trieGet_of_absent (t : Trie K V) (k : K)
    (h : t.data[k]? = none) : trieGet t k = t.default := by
  simp only [trieGet, h, Option.getD_none]

/-- Empty construction excludes stored defaults for any supplied absence value. -/
theorem Trie.noDefault_empty (secured : Bool) (default : V) :
    (Trie.mk secured default (∅ : Std.ExtTreeMap K V)).NoDefault := by
  intro k v h
  simp only [Std.ExtTreeMap.getElem?_empty, reduceCtorEq] at h

/-- Empty construction is safe for any default and either secured flag. -/
theorem Trie.prepareSafe_empty [TrieValue V] (secured : Bool) (default : V) :
    (Trie.mk secured default (∅ : Std.ExtTreeMap K V)).PrepareSafe := by
  intro k v h
  simp only [Std.ExtTreeMap.getElem?_empty, reduceCtorEq] at h

/-- An empty trie returns its supplied default at every key. -/
theorem trieGet_empty (secured : Bool) (default : V) (k : K) :
    trieGet (Trie.mk secured default ∅) k = default := by
  simp only [trieGet, Std.ExtTreeMap.getElem?_empty, Option.getD_none]

/-- Changing only the default cannot change stored-value preparation safety. -/
theorem Trie.prepareSafe_default_update [TrieValue V] (t : Trie K V) (default : V) :
    ({ t with default := default } : Trie K V).PrepareSafe ↔ t.PrepareSafe := Iff.rfl

/-- Changing only the secured flag cannot change stored-value preparation safety. -/
theorem Trie.prepareSafe_secured_update [TrieValue V] (t : Trie K V) (secured : Bool) :
    ({ t with secured := secured } : Trie K V).PrepareSafe ↔ t.PrepareSafe := Iff.rfl

/-- Copying preserves every getter observation. -/
theorem copyTrie_get (t : Trie K V) (k : K) : trieGet (copyTrie t) k = trieGet t k := rfl
/-- Copying preserves absence of stored defaults. -/
theorem copyTrie_noDefault (t : Trie K V) :
    (copyTrie t).NoDefault ↔ t.NoDefault := Iff.rfl
/-- Copying preserves stored-value preparation safety. -/
theorem copyTrie_prepareSafe [TrieValue V] (t : Trie K V) :
    (copyTrie t).PrepareSafe ↔ t.PrepareSafe := Iff.rfl

section Extensionality
variable [Std.LawfulEqOrd K]

/-- Public complete-map extensionality, with fields retained explicitly. -/
theorem Trie.ext_lookup {t u : Trie K V} (hs : t.secured = u.secured)
    (hd : t.default = u.default) (hm : ∀ (k : K), t.data[k]? = u.data[k]?) : t = u :=
  Trie.ext hs hd (Std.ExtTreeMap.ext_getElem? hm)

end Extensionality

section Setter
variable [BEq V] [LawfulBEq V]

/-- EELS `src/ethereum/merkle_patricia_trie.py:325–338` (`trie_set`) at the pin:
erase on equality with the supplied default, otherwise insert.
All values are accepted. Neither validity nor encoding is consulted. -/
def trieSet [LawfulBEq V] (t : Trie K V) (k : K) (v : V) : Trie K V :=
  { t with data := if v == t.default then t.data.erase k else t.data.insert k v }

/-- The setter changes only the map, using actual default equality to erase or insert. -/
theorem trieSet_data (t : Trie K V) (k : K) (v : V) :
    (trieSet t k v).data =
      if v == t.default then t.data.erase k else t.data.insert k v := rfl

/-- The setter retains the supplied absence value. -/
theorem trieSet_default (t : Trie K V) (k : K) (v : V) :
    (trieSet t k v).default = t.default := rfl

/-- The setter retains the deferred secured flag. -/
theorem trieSet_secured (t : Trie K V) (k : K) (v : V) :
    (trieSet t k v).secured = t.secured := rfl

/-- Complete optional-map observation, including the actual default-equality branch. -/
theorem trieSet_lookup (t : Trie K V) (k a : K) (v : V) :
    (trieSet t k v).data[a]? =
      if compare k a = .eq then
        (if v == t.default then none else some v) else t.data[a]? := by
  unfold trieSet
  by_cases hv : v = t.default
  · simp only [hv, beq_self_eq_true, ite_true, Std.ExtTreeMap.getElem?_erase]
  · simp only [beq_iff_eq, hv, ite_false, Std.ExtTreeMap.getElem?_insert]

/-- The changed key is absent exactly when the supplied value equals the default. -/
theorem trieSet_erases_iff (t : Trie K V) (k : K) (v : V) :
    (trieSet t k v).data[k]? = none ↔ v = t.default := by
  by_cases hv : v = t.default <;> simp [trieSet, hv]

/-- The changed key reads the supplied value, including default deletion. -/
theorem trieGet_set_same (t : Trie K V) (k : K) (v : V) :
    trieGet (trieSet t k v) k = v := by
  by_cases hv : v = t.default <;> simp [trieGet, trieSet, hv]

section LawfulKeys
variable [Std.LawfulEqOrd K]

/-- A write preserves every distinct-key getter observation. -/
theorem trieGet_set_of_ne (t : Trie K V) (k a : K) (v : V) (hne : a ≠ k) :
    trieGet (trieSet t k v) a = trieGet t a := by
  by_cases hv : v = t.default <;>
    simp [trieGet, trieSet, hv, Std.ExtTreeMap.getElem?_insert,
      Std.ExtTreeMap.getElem?_erase, Ne.symm hne]

/-- Every write preserves absence of stored defaults when it held before. -/
theorem trieSet_noDefault (t : Trie K V) (k : K) (v : V)
    (h : t.NoDefault) : (trieSet t k v).NoDefault := by
  intro a w hw
  rw [trieSet_lookup] at hw
  rw [trieSet_default]
  by_cases hk : k = a
  · by_cases hv : v = t.default
    · simp [hk, hv] at hw
    · simp [hk, hv] at hw
      exact hw ▸ hv
  · simp [hk] at hw
    exact h a w hw

/-- Exact safety condition from an old-safe trie, for arbitrary supplied defaults. -/
theorem trieSet_prepareSafe_iff [TrieValue V] (t : Trie K V) (k : K) (v : V)
    (h : t.PrepareSafe) :
    (trieSet t k v).PrepareSafe ↔ v = t.default ∨ TrieValue.Valid v := by
  constructor
  · intro hset
    by_cases hv : v = t.default
    · exact Or.inl hv
    · apply Or.inr
      apply hset k v
      rw [trieSet_lookup]
      simp [hv]
  · intro hval a w hw
    rw [trieSet_lookup] at hw
    by_cases hk : k = a
    · rcases hval with hv | hv
      · simp [hk, hv] at hw
      · by_cases heq : v = t.default
        · simp [hk, heq] at hw
        · simp [hk, heq] at hw
          exact hw ▸ hv
    · simp [hk] at hw
      exact h a w hw

/-- Deletion may repair an unsafe trie; safety is exactly validity of retained bindings. -/
theorem trieSet_delete_prepareSafe_iff [TrieValue V] (t : Trie K V) (k : K) :
    (trieSet t k t.default).PrepareSafe ↔
      ∀ a w, a ≠ k → t.data[a]? = some w → TrieValue.Valid w := by
  constructor
  · intro h a w hne hw
    apply h a w
    rw [trieSet_lookup]
    simp [Ne.symm hne, hw]
  · intro h a w hw
    rw [trieSet_lookup] at hw
    by_cases hk : k = a
    · simp [hk] at hw
    · simp [hk] at hw
      exact h a w (Ne.symm hk) hw

/-- Any same-key write is superseded by the final write, including default deletion. -/
theorem trieSet_overwrite (t : Trie K V) (k : K) (v w : V) :
    trieSet (trieSet t k v) k w = trieSet t k w := by
  apply Trie.ext_lookup (t := trieSet (trieSet t k v) k w) (u := trieSet t k w) rfl rfl
  intro a
  by_cases hk : k = a <;> by_cases hv : v = t.default <;>
    by_cases hw : w = t.default <;> simp [trieSet_lookup, trieSet_default, hk, hv, hw]

end LawfulKeys

/-- The old copied observation remains available alongside any derived write result. -/
theorem copyTrie_old_observation (t : Trie K V) (k a : K) (v : V) :
    (trieGet (copyTrie t) a, trieGet (trieSet t k v) k) = (trieGet t a, v) := by
  rw [copyTrie_get, trieGet_set_same]

end Setter
end Storage
end STFSpec.Commit
