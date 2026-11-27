/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block
import STFSpec.Commit

/-!
# Withdrawal trie byte interpretation clients

Library `EthConformance`. Private clients check the named withdrawal dictionary,
local activation, exact stored bytes and the existing preparation domain.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–5.
-/

namespace STFSpec.Conformance.Block.WithdrawalTrieValueControls

open STFSpec.Base STFSpec.Commit

private theorem no_dictionary_on_import : True := by
  fail_if_success
    let _ : TrieValue (Option Bytes) := inferInstance
  trivial

section

open STFSpec.Block STFSpec.Block.Withdrawal

private theorem no_dictionary_on_open : True := by
  fail_if_success
    let _ : TrieValue (Option Bytes) := inferInstance
  trivial

end

open STFSpec.Block

private abbrev dictionary : TrieValue (Option Bytes) := Withdrawal.encodedTrieValue

private theorem exact_encode_law (value : Option Bytes) :
    dictionary.encode value =
      (match value with
       | none => ByteArray.empty
       | some bytes => bytes.toByteArray) := Withdrawal.encodedTrieValue_encode value

private theorem exact_valid_law (value : Option Bytes) :
    dictionary.Valid value ↔
      (match value with
       | none => False
       | some bytes => bytes ≠ Bytes.empty) := Withdrawal.encodedTrieValue_valid value

private theorem invalid_none : ¬ dictionary.Valid none :=
  (Withdrawal.encodedTrieValue_valid none).mp

private theorem invalid_empty : ¬ dictionary.Valid (some Bytes.empty) :=
  fun valid ↦ (Withdrawal.encodedTrieValue_valid (some Bytes.empty)).mp valid rfl

private theorem locally_selects_dictionary :
    letI : TrieValue (Option Bytes) := dictionary
    inferInstanceAs (TrieValue (Option Bytes)) = dictionary := rfl

private def encodedBytes (value : Option Bytes) : List UInt8 :=
  (Bytes.ofByteArray (dictionary.encode value)).toList

private def payload : Bytes := Bytes.ofList [0, 128, 0, 255]

private def longPayload : Bytes :=
  Bytes.ofList ((List.range 64).map UInt8.ofNat)

#guard encodedBytes none == []
#guard encodedBytes (some Bytes.empty) == []
#guard encodedBytes (some payload) == [0, 128, 0, 255]
#guard encodedBytes (some longPayload) ==
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
    48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]

section

local instance : TrieValue (Option Bytes) := dictionary

private def fresh : Trie Bytes (Option Bytes) := ⟨false, none, ∅⟩
private def key : Bytes := Bytes.ofList [128]
private def storedEmpty : Trie Bytes (Option Bytes) := trieSet fresh key (some Bytes.empty)
private def storedPayload : Trie Bytes (Option Bytes) := trieSet fresh key (some payload)

private theorem empty_is_unsafe : ¬ storedEmpty.PrepareSafe := by
  intro safe
  have changedKey : storedEmpty.data[key]? = some (some Bytes.empty) := by
    simp [storedEmpty, trieSet_lookup, fresh]
  exact invalid_empty (safe key (some Bytes.empty) changedKey)

private theorem payload_is_safe : storedPayload.PrepareSafe := by
  refine (trieSet_prepareSafe_iff fresh key (some payload)
    (Trie.prepareSafe_empty false none)).mpr (.inr ?_)
  exact (Withdrawal.encodedTrieValue_valid (some payload)).mpr (by decide)

private def prepared : Std.ExtTreeMap Nibbles ByteArray :=
  prepareTrie (m := Id) storedPayload rfl payload_is_safe

#guard storedEmpty.data[key]? == some (some Bytes.empty)
#guard (trieSet storedPayload key none).data[key]? == none
#guard prepared.toList.map
  (fun (path, bytes) ↦ (path.toList, (Bytes.ofByteArray bytes).toList)) ==
    [([8, 0], [0, 128, 0, 255])]

end

end STFSpec.Conformance.Block.WithdrawalTrieValueControls
