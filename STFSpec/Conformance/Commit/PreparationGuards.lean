/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit
import STFSpec.Codec

/-!
# Pure preparation regressions

Library `EthConformance`. List-byte and production Bytes keys with sample values are
test instrumentation only. Tests call the production preparation fold/frontend.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/4/7.0.3; Q53.
-/

namespace STFSpec.Conformance.Commit.PreparationGuards
open STFSpec.Base STFSpec.Commit STFSpec.Codec

-- Ordinary core byte observation bridge; no STFspec container internals are unfolded.
private theorem core_toList_loop (b : ByteArray) (n i : Nat) (r : List UInt8)
    (h : n + i = b.size) :
    ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i := by
  induction n generalizing i r with
  | zero =>
    have hi : ¬ i < b.size := by omega
    rw [ByteArray.toList.loop, ite_eq_right hi]
    rw [List.drop_of_length_le
      (by simp only [Array.length_toList, ByteArray.size] at *; omega), List.append_nil]
  | succ n ih =>
    have hi : i < b.size := by omega
    rw [ByteArray.toList.loop, ite_eq_left hi, ih (i + 1) _ (by omega)]
    rw [List.reverse_cons, List.append_assoc]
    congr 1
    rw (occs := [2]) [← List.getElem_cons_drop
      (by simpa only [Array.length_toList, ByteArray.size] using hi)]
    simp only [List.singleton_append, ByteArray.get!, Array.getElem!_eq_getD,
      Array.getD_eq_getD_getElem?, getElem?_pos b.data i hi, Option.getD_some,
      Array.getElem_toList]

private theorem core_toList (b : ByteArray) : b.toList = b.data.toList :=
  core_toList_loop b b.size 0 [] (Nat.add_zero _)

-- A test-local adapter for the existing core List model only.
local instance listKeyBytes : KeyBytes (List UInt8) where
  toBytes := List.toByteArray
  toBytes_injective := by
    intro a b h
    have hl := congrArg (fun x : ByteArray => x.data.toList) h
    simpa only [List.data_toByteArray, List.toList_toArray] using hl
  compare_toBytes a b := by
    simp only [core_toList, List.data_toByteArray, List.toList_toArray]

/-- Finite supported-value instrumentation, with no production encoding instance. -/
inductive SampleValue
  | none
  | raw (bytes : ByteArray)
  | integer (number : Nat)
  | collection (items : List RlpItem)

/-- Exact raw-byte identity or actual public RLP encoding for the sample value. -/
def sampleEncode : SampleValue → ByteArray
  | .none => ByteArray.empty
  | .raw b => b
  | .integer n => Rlp.encode (Rlp.ofNat n)
  | .collection xs => Rlp.encode (.list xs)

/-- Sample preparation domain: exclude None and exact empty encodings. -/
def sampleValid : SampleValue → Prop
  | .none => False
  | .raw b => b ≠ ByteArray.empty
  | .integer n => Rlp.encode (Rlp.ofNat n) ≠ ByteArray.empty
  | .collection xs => Rlp.encode (.list xs) ≠ ByteArray.empty

local instance sampleTrieValue : TrieValue SampleValue where
  encode := sampleEncode
  Valid := sampleValid
  encode_ne_empty v h := by
    cases v with
    | none => cases h
    | raw _ => exact h
    | integer _ => exact h
    | collection _ => exact h

-- Build observations using the exact generic model, not a replacement preparation path.
/-- Build test storage through public lawful map construction. -/
def sampleTrie (default : SampleValue) (rows : List (List UInt8 × SampleValue)) :
    Trie (List UInt8) SampleValue := ⟨false, default, Std.ExtTreeMap.ofList rows compare⟩

/-- Observe every path and byte of the actual production prepared map. -/
def observePrepared (default : SampleValue) (rows : List (List UInt8 × SampleValue)) :
    List (List Nat × List UInt8) :=
  (prepareTrieModel (sampleTrie default rows)).toList.map
    (fun (k, v) => (k.toList.map Fin.val, v.data.toList))

-- The valid directly stored default survives preparation, despite NoDefault failing.
/-- Directly stored valid default, retained by pure preparation. -/
def storedDefault : Trie (List UInt8) SampleValue :=
  ⟨false, .raw [7].toByteArray,
    (∅ : Std.ExtTreeMap (List UInt8) SampleValue).insert [0] (.raw [7].toByteArray)⟩

/-- The directly stored valid default satisfies preparation safety. -/
theorem storedDefault_safe : storedDefault.PrepareSafe := by
  intro k v h
  change ((∅ : Std.ExtTreeMap (List UInt8) SampleValue).insert [0] (.raw [7].toByteArray))[k]? = some v at h
  rw [Std.ExtTreeMap.getElem?_insert] at h
  split at h
  · have he : SampleValue.raw [7].toByteArray = v := Option.some.inj h
    subst v
    change [7].toByteArray ≠ ByteArray.empty
    decide
  · rw [Std.ExtTreeMap.getElem?_empty] at h
    cases h

/-- The independent NoDefault condition fails for a valid stored default. -/
theorem storedDefault_has_default : ¬ storedDefault.NoDefault := by
  intro h
  exact h [0] (.raw [7].toByteArray) Std.ExtTreeMap.getElem?_insert_self rfl

#guard (prepareTrieModel storedDefault).size = 1
#guard (prepareTrieModel storedDefault)[bytesToNibbleList [0].toByteArray]? = some [7].toByteArray

-- Monadic call uses safe+unsecured proofs; no NoDefault premise can be supplied.
#guard (prepareTrie (m := Id) storedDefault rfl storedDefault_safe).size = 1

-- Different source values may encode identically; map-value recovery needs its hypothesis.
#guard observePrepared .none [([0], .raw [128].toByteArray)] =
  observePrepared .none [([0], .integer 0)]

/-- A stored None interpretation is outside the safe frontend domain. -/
theorem stored_none_unsafe (t : Trie (List UInt8) SampleValue) (k : List UInt8)
    (h : t.data[k]? = some .none) : ¬ t.PrepareSafe := by
  intro safe
  exact safe k .none h

/-- A stored empty raw byte value is outside the safe frontend domain. -/
theorem stored_empty_bytes_unsafe (t : Trie (List UInt8) SampleValue) (k : List UInt8)
    (h : t.data[k]? = some (.raw ByteArray.empty)) : ¬ t.PrepareSafe := by
  intro safe
  exact safe k (.raw ByteArray.empty) h rfl


/-- Whole empty-key, prefix, leading-zero and unequal-length observations. -/
def prefixObservation : List (List Nat × List UInt8) :=
  observePrepared .none [([255], .raw [9].toByteArray), ([], .raw [1].toByteArray),
    ([0, 1], .raw [3].toByteArray), ([0], .raw [2].toByteArray),
    ([1], .raw [4].toByteArray), ([1, 255], .raw [5].toByteArray)]

#guard prefixObservation ==
  [([], [1]), ([0, 0], [2]), ([0, 0, 0, 1], [3]), ([0, 1], [4]),
    ([0, 1, 15, 15], [5]), ([15, 15], [9])]
#guard observePrepared (.raw [99].toByteArray) [] == []
#guard observePrepared .none [([0], .integer 0), ([1], .collection []),
  ([2], .raw [2, 192].toByteArray), ([0], .raw [7].toByteArray)] ==
  [([0, 0], [7]), ([0, 1], [192]), ([0, 2], [2, 192])]
#guard compare ([0] : List UInt8) [0, 0] == Ordering.lt
#guard bytesToNibbleList [0].toByteArray ≠ bytesToNibbleList [0, 0].toByteArray
#guard bytesToNibbleList [].toByteArray ≠ bytesToNibbleList [0].toByteArray

/-- Preparation leaves arbitrary carried State unchanged, with no query instance. -/
def stateObservation : List (List Nat × List UInt8) × Nat :=
  let (prepared, state) :=
    (prepareTrie (m := StateM Nat) storedDefault rfl storedDefault_safe).run 713
  (prepared.toList.map (fun (k, v) ↦ (k.toList.map Fin.val, v.data.toList)), state)

#guard stateObservation == ([([0, 0], [7])], 713)

/-- Pure preparation succeeds in Except even though no oracle instance is supplied. -/
def exceptObservation : Except String Nat :=
  (prepareTrie (m := Except String) storedDefault rfl storedDefault_safe).map
    Std.ExtTreeMap.size

#guard match exceptObservation with
  | .ok n => n == 1
  | .error _ => false

/-- Print complete fixed regression values, without a checksum. -/
def printComplete : IO Unit := do
  IO.println (repr prefixObservation)
  IO.println (repr stateObservation)
  IO.println (repr exceptObservation)
  IO.println (repr (observePrepared (.raw [99].toByteArray) []))

/-! ### Existing packed Bytes key controls -/

-- Bytes controls synthesize the production adapter; no local key instance is added.
private def bytesTrie (default : SampleValue) (rows : List (Bytes × SampleValue)) :
    Trie Bytes SampleValue := ⟨false, default, Std.ExtTreeMap.ofList rows compare⟩

private def observeBytesTrie (t : Trie Bytes SampleValue) :
    List (List Nat × List UInt8) :=
  (prepareTrieModel t).toList.map
    (fun (k, v) ↦ (k.toList.map Fin.val, v.data.toList))

private def observeBytes (default : SampleValue) (rows : List (Bytes × SampleValue)) :
    List (List Nat × List UInt8) := observeBytesTrie (bytesTrie default rows)

private def bytesPrefixRows : List (Bytes × SampleValue) :=
  [(Bytes.ofList [255], .raw [9].toByteArray), (Bytes.ofList [], .raw [1].toByteArray),
    (Bytes.ofList [0, 1], .raw [3].toByteArray), (Bytes.ofList [0], .raw [2].toByteArray),
    (Bytes.ofList [1], .raw [4].toByteArray), (Bytes.ofList [1, 255], .raw [5].toByteArray),
    (Bytes.ofList [0, 0], .raw [6].toByteArray)]

#guard observeBytes .none bytesPrefixRows =
  [([], [1]), ([0, 0], [2]), ([0, 0, 0, 0], [6]), ([0, 0, 0, 1], [3]),
    ([0, 1], [4]), ([0, 1, 15, 15], [5]), ([15, 15], [9])]
#guard observeBytes (.raw [99].toByteArray) [] = []
#guard observeBytes .none bytesPrefixRows.reverse = observeBytes .none bytesPrefixRows
#guard (bytesTrie .none bytesPrefixRows).data.size = 7
#guard (prepareTrieModel (bytesTrie .none bytesPrefixRows)).size = 7

-- Complete maps distinguish early and late mismatches and unsigned high bytes.
#guard observeBytes .none
  [(Bytes.ofList [255, 0, 0], .raw [4].toByteArray),
    (Bytes.ofList [1, 0, 1], .raw [2].toByteArray),
    (Bytes.ofList [0, 255, 255], .raw [1].toByteArray),
    (Bytes.ofList [1, 0, 2], .raw [3].toByteArray)] =
  [([0, 0, 15, 15, 15, 15], [1]), ([0, 1, 0, 0, 0, 1], [2]),
    ([0, 1, 0, 0, 0, 2], [3]), ([15, 15, 0, 0, 0, 0], [4])]

-- Different public constructions have actual equal content and overwrite one key.
#guard Bytes.ofByteArray [0, 1].toByteArray = Bytes.ofList [0, 1]
#guard compare (Bytes.ofByteArray [0, 1].toByteArray) (Bytes.ofList [0, 1]) = Ordering.eq
#guard observeBytes .none
  [(Bytes.ofList [0, 1], .integer 0), (Bytes.ofList [0], .collection []),
    (Bytes.ofByteArray [0, 1].toByteArray, .raw [7].toByteArray),
    (Bytes.ofList [1], .raw [2, 192].toByteArray)] =
  [([0, 0], [192]), ([0, 0, 0, 1], [7]), ([0, 1], [2, 192])]

-- Equal encoded values do not collapse distinct keys; encoding need not be injective.
#guard observeBytes .none
  [(Bytes.ofList [0], .raw [128].toByteArray), (Bytes.ofList [0, 0], .integer 0)] =
  [([0, 0], [128]), ([0, 0, 0, 0], [128])]
#guard observeBytes .none [(Bytes.ofList [0], .raw [128].toByteArray)] =
  observeBytes .none [(Bytes.ofList [0], .integer 0)]

-- These are raw ordinal byte keys, with no Python alias or consumer encoder selected.
#guard compare (Bytes.ofList [128]) (Bytes.ofList [1]) = Ordering.gt
#guard observeBytes .none
  [(Bytes.ofList [128], .raw [9].toByteArray), (Bytes.ofList [1], .raw [8].toByteArray)] =
  [([0, 1], [8]), ([8, 0], [9])]
#guard KeyBytes.toBytes (Bytes.ofList []) = [].toByteArray
#guard KeyBytes.toBytes (Bytes.ofList [0, 0, 1]) = [0, 0, 1].toByteArray

private def bytesStoredDefault : Trie Bytes SampleValue :=
  ⟨false, .raw [7].toByteArray,
    (∅ : Std.ExtTreeMap Bytes SampleValue).insert (Bytes.ofList []) (.raw [7].toByteArray)⟩

private theorem bytesStoredDefault_safe : bytesStoredDefault.PrepareSafe := by
  intro k v h
  change ((∅ : Std.ExtTreeMap Bytes SampleValue).insert
    (Bytes.ofList []) (.raw [7].toByteArray))[k]? = some v at h
  rw [Std.ExtTreeMap.getElem?_insert] at h
  split at h
  · have he : SampleValue.raw [7].toByteArray = v := Option.some.inj h
    subst v
    change [7].toByteArray ≠ ByteArray.empty
    decide
  · rw [Std.ExtTreeMap.getElem?_empty] at h
    cases h

private theorem bytesStoredDefault_has_default : ¬ bytesStoredDefault.NoDefault := by
  intro h
  exact h (Bytes.ofList []) (.raw [7].toByteArray) Std.ExtTreeMap.getElem?_insert_self rfl

#guard observeBytesTrie bytesStoredDefault = [([], [7])]
#guard (prepareTrieModel bytesStoredDefault)[bytesToNibbleList [].toByteArray]? =
  some [7].toByteArray
#guard observeBytesTrie
  { bytesStoredDefault with data :=
      bytesStoredDefault.data.insert (Bytes.ofList [0]) (.raw [8].toByteArray) } =
  [([], [7]), ([0, 0], [8])]
#guard observeBytesTrie
  { bytesStoredDefault with data :=
      bytesStoredDefault.data.insert (Bytes.ofByteArray [].toByteArray) (.raw [8].toByteArray) } =
  [([], [8])]

-- Whole pure frontend observations retain safety and unsecured proofs, without a query.
private def bytesStateObservation : List (List Nat × List UInt8) × Nat :=
  let (prepared, state) :=
    (prepareTrie (m := StateM Nat) bytesStoredDefault rfl bytesStoredDefault_safe).run 713
  (prepared.toList.map (fun (k, v) ↦ (k.toList.map Fin.val, v.data.toList)), state)

#guard bytesStateObservation = ([([], [7])], 713)
#guard (prepareTrie (m := Id) bytesStoredDefault rfl bytesStoredDefault_safe).toList.map
  (fun (k, v) ↦ (k.toList.map Fin.val, v.data.toList)) = [([], [7])]

private def bytesExceptObservation : Except String (List (List Nat × List UInt8)) :=
  (prepareTrie (m := Except String) bytesStoredDefault rfl bytesStoredDefault_safe).map
    (fun prepared ↦ prepared.toList.map
      (fun (k, v) ↦ (k.toList.map Fin.val, v.data.toList)))

#guard match bytesExceptObservation with
  | .ok observed => observed == [([], [7])]
  | .error _ => false

end STFSpec.Conformance.Commit.PreparationGuards
