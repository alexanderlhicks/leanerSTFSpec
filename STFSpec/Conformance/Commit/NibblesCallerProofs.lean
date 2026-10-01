/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit

/-!
# Public path caller proofs

Library `EthConformance`. Uses stable observers and public laws, without unfolding
packed storage, generators or scans. Spec guidance: EthCommit §§3/7/8.
-/

namespace STFSpec.Conformance.Commit.NibblesCallerProofs

open STFSpec.Commit

example (x : Nibbles) : x.toList.length = x.size := Nibbles.length_toList x
example (x : Nibbles) (i : Fin x.size) : (x.get i).val < 16 := Nibbles.get_lt x i
example (x : Nibbles) (i : Nat) (h : i < x.size) :
    x.toList[i]'(by rw [Nibbles.length_toList]; exact h) = x.get ⟨i, h⟩ :=
  Nibbles.getElem_toList x i h
example (xs : List (Fin 16)) : (Nibbles.ofList xs).toList = xs := Nibbles.toList_ofList xs
example (x : Nibbles) : Nibbles.ofList x.toList = x := Nibbles.ofList_toList x
example (a b : Nibbles) (h : a.toList = b.toList) : a = b := Nibbles.ext h

example (b : ByteArray) : (bytesToNibbleList b).toList = bytesToNibbleListModel b.data.toList :=
  toList_bytesToNibbleList b
example (b : ByteArray) : (bytesToNibbleList b).size = 2 * b.size := size_bytesToNibbleList b
example (b : ByteArray) (i : Nat) (h : i < b.size) :
    (bytesToNibbleList b).get ⟨2 * i, by rw [size_bytesToNibbleList]; omega⟩ = highNibble b[i] :=
  get_bytesToNibbleList_high b i h
example (b : ByteArray) (i : Nat) (h : i < b.size) :
    (bytesToNibbleList b).get ⟨2 * i + 1, by rw [size_bytesToNibbleList]; omega⟩ = lowNibble b[i] :=
  get_bytesToNibbleList_low b i h
example (b : UInt8) : 16 * (highNibble b).val + (lowNibble b).val = b.toNat := high_low_decomposition b

example (x : Nibbles) (leaf : Bool) :
    (nibbleListToCompact x leaf).data.toList = nibbleListToCompactModel x.toList leaf :=
  nibbleListToCompact_eq_model x leaf
example (x : Nibbles) (leaf : Bool) : (nibbleListToCompact x leaf).size = x.size / 2 + 1 :=
  size_nibbleListToCompact x leaf
example (x : Nibbles) (leaf : Bool) : 0 < (nibbleListToCompact x leaf).size :=
  nibbleListToCompact_nonempty x leaf
example (x : Nibbles) (leaf : Bool) :
    ((nibbleListToCompact x leaf)[0]'(nibbleListToCompact_nonempty x leaf)).toNat / 16 =
      2 * (if leaf then 1 else 0) + x.size % 2 := nibbleListToCompact_flag x leaf
example (x : Nibbles) (leaf : Bool) :
    ((nibbleListToCompact x leaf)[0]'(nibbleListToCompact_nonempty x leaf)).toNat % 16 =
      if x.size % 2 = 0 then 0 else (x.toList[0]?.getD 0).val := nibbleListToCompact_first x leaf
example (leaf : Bool) : (nibbleListToCompact (Nibbles.ofList []) leaf).data.toList =
    [if leaf then 32 else 0] := nibbleListToCompact_empty leaf

example (a b : Nibbles) : commonPrefixLength a b = commonPrefixLengthModel a.toList b.toList :=
  commonPrefixLength_eq_model a b
example (a b : Nibbles) : commonPrefixLength a b ≤ a.size := commonPrefixLength_le_left a b
example (a b : Nibbles) : commonPrefixLength a b ≤ b.size := commonPrefixLength_le_right a b
example (a b : Nibbles) : commonPrefixLength a b = commonPrefixLength b a := commonPrefixLength_symm a b
example (a : Nibbles) : commonPrefixLength a a = a.size := commonPrefixLength_self a
example (a b : Nibbles) (k : Nat) (ha : k ≤ a.size) (hb : k ≤ b.size) :
    a.toList.take k = b.toList.take k ↔ k ≤ commonPrefixLength a b := commonPrefixLength_take_iff a b k ha hb
example (a b : Nibbles) : a.toList.take (commonPrefixLength a b) = b.toList.take (commonPrefixLength a b) :=
  commonPrefixLength_equal_prefixes a b
example (a b : Nibbles) (ha : commonPrefixLength a b < a.size) (hb : commonPrefixLength a b < b.size) :
    a.get ⟨commonPrefixLength a b, ha⟩ ≠ b.get ⟨commonPrefixLength a b, hb⟩ := commonPrefixLength_maximal a b ha hb

end STFSpec.Conformance.Commit.NibblesCallerProofs
