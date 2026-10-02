/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit

/-!
# Typed-trie storage regressions

Library `EthConformance`. C11/Q53 all-value storage and independent predicates.
The local validity interpretation is test instrumentation only; no production
value/key instance or source preparation API is supplied.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/4/7.0.3.
-/

namespace STFSpec.Conformance.Commit.TrieGuards

open STFSpec.Base STFSpec.Commit

local instance : TrieValue (Option Bytes) where
  encode v := match v with
    | none => ByteArray.empty
    | some b => b.toByteArray
  Valid v := ∃ b, v = some b ∧ b ≠ Bytes.empty
  encode_ne_empty v h := by
    obtain ⟨b, rfl, hb⟩ := h
    intro heq
    change b.toByteArray = ByteArray.empty at heq
    apply hb
    apply Bytes.ext
    rw [Bytes.toList_empty, ← Bytes.toList_toByteArray b, heq]
    rfl

/-- Test value with an exact empty encoding, distinct from the default `none`. -/
def emptyBytes : Option Bytes := some Bytes.empty
/-- Test value whose raw byte encoding is nonempty. -/
def nonemptyBytes : Option Bytes := some (Bytes.ofList [7, 0, 255])
/-- The local total encoding retains validity as a separate proof premise. -/
def encodingObservations : List (List UInt8) :=
  [(TrieValue.encode (none : Option Bytes)).toList,
    (TrieValue.encode emptyBytes).toList, (TrieValue.encode nonemptyBytes).toList]

#guard encodingObservations == [[], [], [7, 0, 255]]

/-- A bounded path supplied through the public Nibbles constructor. -/
def key : Nibbles := Nibbles.ofList [0, 1, 2]
/-- A distinct bounded path with the same first two digits. -/
def otherKey : Nibbles := Nibbles.ofList [0, 1, 3]
/-- Empty optional-byte storage with an invalid but arbitrary supplied default. -/
def base : Trie Nibbles (Option Bytes) := ⟨false, none, ∅⟩
/-- An all-value insertion that retains an invalid nondefault. -/
def invalidInsert : Trie Nibbles (Option Bytes) := trieSet base key emptyBytes
/-- A directly stored valid default, outside setter-reachable `NoDefault`. -/
def validDirectDefault : Trie Nibbles (Option Bytes) :=
  ⟨true, nonemptyBytes, (∅ : Std.ExtTreeMap Nibbles (Option Bytes)).insert key nonemptyBytes⟩

/-- The chosen nonempty test value satisfies the local validity interpretation. -/
theorem nonempty_valid : TrieValue.Valid nonemptyBytes := by
  refine ⟨Bytes.ofList [7, 0, 255], rfl, ?_⟩
  intro h
  have hlist := congrArg Bytes.toList h
  simp only [Bytes.toList_ofList, Bytes.toList_empty, reduceCtorEq] at hlist

/-- An empty byte encoding is excluded by the local validity interpretation. -/
theorem emptyBytes_invalid : ¬ TrieValue.Valid emptyBytes := by
  intro h
  obtain ⟨b, hb, hne⟩ := h
  exact hne (Option.some.inj hb).symm

/-- The `none` interpretation is invalid independently of a supplied default. -/
theorem none_invalid : ¬ TrieValue.Valid (none : Option Bytes) := by
  intro h
  obtain ⟨b, hb, _⟩ := h
  cases hb

/-- An invalid nondefault is still present after the all-value setter. -/
theorem invalid_insert_stores : invalidInsert.data[key]? = some emptyBytes := by
  simp [invalidInsert, trieSet, base, emptyBytes]

/-- Excluding stored defaults does not exclude invalid stored nondefaults. -/
theorem invalid_insert_noDefault : invalidInsert.NoDefault :=
  trieSet_noDefault base key emptyBytes (Trie.noDefault_empty false none)

/-- The retained invalid binding prevents preparation safety. -/
theorem invalid_insert_not_safe : ¬ invalidInsert.PrepareSafe := by
  intro h
  exact emptyBytes_invalid (h key emptyBytes invalid_insert_stores)

/-- Deleting the sole invalid binding repairs preparation safety. -/
theorem deleting_invalid_is_safe : (trieSet invalidInsert key none).PrepareSafe := by
  rw [show trieSet invalidInsert key none = trieSet base key none from
    trieSet_overwrite base key emptyBytes none]
  exact (trieSet_prepareSafe_iff base key none (Trie.prepareSafe_empty false none)).mpr
    (Or.inl rfl)

/-- Deleting a distinct key cannot repair an invalid retained binding. -/
theorem deleting_other_does_not_repair :
    ¬ (trieSet invalidInsert otherKey none).PrepareSafe := by
  intro h
  apply emptyBytes_invalid
  apply h key emptyBytes
  rw [trieSet_lookup]
  have hne : otherKey ≠ key := by
    intro heq
    have := congrArg Nibbles.toList heq
    exact (by decide : ([0, 1, 3] : List (Fin 16)) ≠ [0, 1, 2])
      (by simpa only [otherKey, key, Nibbles.toList_ofList] using this)
  simp [hne, invalid_insert_stores]

/-- A valid directly stored default satisfies preparation safety. -/
theorem direct_default_is_safe : validDirectDefault.PrepareSafe := by
  intro k v hv
  simp only [validDirectDefault, Std.ExtTreeMap.getElem?_insert,
    Std.ExtTreeMap.getElem?_empty] at hv
  split at hv
  · exact (Option.some.inj hv) ▸ nonempty_valid
  · cases hv

/-- A directly stored default violates the independent `NoDefault` predicate. -/
theorem direct_default_is_not_noDefault : ¬ validDirectDefault.NoDefault := by
  intro h
  apply h key nonemptyBytes
  · simp only [validDirectDefault, Std.ExtTreeMap.getElem?_insert_self]
  · rfl

/-- Secured storage with a supplied nonempty optional-byte default. -/
def nonemptyDefault : Trie U256 (Option Bytes) := ⟨true, nonemptyBytes, ∅⟩

/-- With a nonempty default, `none` is retained as a nondefault value. -/
theorem nonempty_default_none_stored :
    (trieSet nonemptyDefault U256.zero none).data[U256.zero]? = some none := by
  simp [trieSet, nonemptyDefault, nonemptyBytes]

/-- With a nonempty default, empty bytes are retained as a nondefault value. -/
theorem nonempty_default_empty_stored :
    (trieSet nonemptyDefault U256.one emptyBytes).data[U256.one]? = some emptyBytes := by
  have hne : emptyBytes ≠ nonemptyBytes := by
    intro h
    exact emptyBytes_invalid (h ▸ nonempty_valid)
  simp [trieSet, nonemptyDefault, hne]

/-- Retained `none` makes the nonempty-default trie unsafe. -/
theorem nonempty_default_none_unsafe :
    ¬ (trieSet nonemptyDefault U256.zero none).PrepareSafe := by
  intro h
  exact none_invalid (h U256.zero none nonempty_default_none_stored)

/-- Retained empty bytes make the nonempty-default trie unsafe. -/
theorem nonempty_default_empty_unsafe :
    ¬ (trieSet nonemptyDefault U256.one emptyBytes).PrepareSafe := by
  intro h
  exact emptyBytes_invalid (h U256.one emptyBytes nonempty_default_empty_stored)

/-- Complete numeric fields, map and getter results for source/native comparison. -/
def numericSnapshot (t : Trie U256 Nat) (queries : List U256) :
    Bool × Nat × List (Nat × Nat) × List Nat :=
  (t.secured, t.default, t.data.toList.map (fun (k, v) => (k.toNat, v)),
    queries.map (trieGet t))

/-- Complete optional-byte fields, map and getter results; public observations only. -/
def bytesSnapshot (t : Trie Nibbles (Option Bytes)) (queries : List Nibbles) :
    Bool × Option (List UInt8) × List (List Nat × Option (List UInt8)) ×
      List (Option (List UInt8)) :=
  (t.secured, t.default.map Bytes.toList,
    t.data.toList.map (fun (k, v) => (k.toList.map Fin.val, v.map Bytes.toList)),
    queries.map (fun k => (trieGet t k).map Bytes.toList))

#guard trieGet (Trie.mk true (99 : Nat) (∅ : Std.ExtTreeMap U256 Nat)) U256.zero == 99
#guard let t := Trie.mk false (99 : Nat) (∅ : Std.ExtTreeMap U256 Nat)
  numericSnapshot (trieSet t U256.zero 0) [U256.zero, U256.one] ==
    (false, 99, [(0, 0)], [0, 99])
#guard let t := trieSet (Trie.mk true (99 : Nat) ∅) U256.zero 0
  numericSnapshot (trieSet t U256.zero 99) [U256.zero, U256.one] ==
    (true, 99, [], [99, 99])
#guard bytesSnapshot invalidInsert [key, otherKey] ==
  (false, none, [([0, 1, 2], some [])], [some [], none])
#guard bytesSnapshot validDirectDefault [key, otherKey] ==
  (true, some [7, 0, 255], [([0, 1, 2], some [7, 0, 255])],
    [some [7, 0, 255], some [7, 0, 255]])
#guard let saved := copyTrie invalidInsert
  let deleted := trieSet invalidInsert key none
  (bytesSnapshot saved [key], bytesSnapshot deleted [key]) ==
    ((false, none, [([0, 1, 2], some [])], [some []]), (false, none, [], [none]))
#guard let saved := copyTrie base
  let inserted := trieSet saved key nonemptyBytes
  (bytesSnapshot saved [key], bytesSnapshot inserted [key]) ==
    ((false, none, [], [none]),
      (false, none, [([0, 1, 2], some [7, 0, 255])], [some [7, 0, 255]]))
#guard let t := trieSet (trieSet (Trie.mk true (99 : Nat) ∅) U256.zero 0) U256.one 7
  numericSnapshot (trieSet t U256.zero 5) [U256.zero, U256.one, U256.ofNat 2] ==
    (true, 99, [(0, 5), (1, 7)], [5, 7, 99])

end STFSpec.Conformance.Commit.TrieGuards
