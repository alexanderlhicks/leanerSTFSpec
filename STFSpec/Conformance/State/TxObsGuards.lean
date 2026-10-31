/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Complete raw transaction observation controls

Library `EthConformance`: complete four-field observations use public byte exports.
A separate finite numeric-list model supplies expected contents, with no iteration-order claim.
Retained parents/siblings are functional controls, not ownership or lifetime evidence.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/7.
-/

namespace STFSpec.Conformance.State.TxObsGuards

open STFSpec.State STFSpec.Base

private def a (n : Nat) : Address := Address.ofNat n
private def k (n : Nat) : Bytes32 := FixedBytes.ofNat n
private def h (n : Nat) : Hash32 := Hash32.ofBytes32 (k n)

private def addresses (xs : List Nat) : Std.HashSet Address :=
  xs.foldl (fun s n ↦ s.insert (a n)) ∅

private def slots (xs : List (Nat × Nat)) : Std.HashSet (Address × Bytes32) :=
  xs.foldl (fun s n ↦ s.insert (a n.1, k n.2)) ∅

private def codes (xs : List (Nat × Nat)) : Std.HashSet (Address × Hash32) :=
  xs.foldl (fun s n ↦ s.insert (a n.1, h n.2)) ∅

private def supplied (ar : List Nat) (sr cr : List (Nat × Nat)) (ca : List Nat) : TxObs :=
  TxObs.mk (addresses ar) (slots sr) (codes cr) (addresses ca)

private def observe (t : TxObs) :=
  (((t.accountReads.toList.mergeSort (fun x y ↦ compare x y != .gt)).map
      (fun x ↦ x.toBytes.toList)),
    ((t.storageReads.toList.mergeSort (fun x y ↦ compare x y != .gt)).map
      (fun x ↦ (x.1.toBytes.toList, x.2.toBytes.toList))),
    ((t.codeReads.toList.mergeSort (fun x y ↦
      (compare x.1 y.1).then (compare x.2 y.2) != .gt)).map
      (fun x ↦ (x.1.toBytes.toList, x.2.toBytes.toList))),
    ((t.createdAccounts.toList.mergeSort (fun x y ↦ compare x y != .gt)).map
      (fun x ↦ x.toBytes.toList)))

-- Independent finite model: mask each complete numeric key, deduplicate, sort,
-- then emit every big-endian byte, including zeros at both ends.
private def digits (width n : Nat) : List UInt8 :=
  (List.range width).map (fun i ↦ UInt8.ofNat (n / 256 ^ (width - 1 - i)))

private def expectAddresses (xs : List Nat) : List (List UInt8) :=
  (((xs.map (fun n ↦ n % 2 ^ 160)).eraseDups).mergeSort
    (fun x y ↦ x ≤ y)).map (digits 20)

private def expectPairs (xs : List (Nat × Nat)) : List (List UInt8 × List UInt8) :=
  (((xs.map (fun x ↦ (x.1 % 2 ^ 160, x.2 % 2 ^ 256))).eraseDups).mergeSort
    (fun x y ↦ (compare x.1 y.1).then (compare x.2 y.2) != .gt)).map
      (fun x ↦ (digits 20 x.1, digits 32 x.2))

private def check (t : TxObs) (ar : List Nat) (sr cr : List (Nat × Nat))
    (ca : List Nat) : Bool :=
  observe t == (expectAddresses ar, expectPairs sr, expectPairs cr, expectAddresses ca)

private def parent : TxObs :=
  supplied [3, 2 ^ 159 + 7] [(3, 5), (3, 2 ^ 255 + 9)]
    [(3, 11), (2 ^ 159 + 7, 11)] [8, 2 ^ 159 + 17]

#guard check (supplied [] [] [] []) [] [] [] []
#guard check parent [3, 2 ^ 159 + 7] [(3, 5), (3, 2 ^ 255 + 9)]
  [(3, 11), (2 ^ 159 + 7, 11)] [8, 2 ^ 159 + 17]
#guard check (supplied [3, 3 + 2 ^ 160] [(3, 5), (3 + 2 ^ 160, 5 + 2 ^ 256)]
  [(3, 11), (3 + 2 ^ 160, 11 + 2 ^ 256)] [8, 8 + 2 ^ 160])
  [3] [(3, 5)] [(3, 11)] [8]

#guard check { parent with accountReads := addresses [99, 0] }
  [99, 0] [(3, 5), (3, 2 ^ 255 + 9)] [(3, 11), (2 ^ 159 + 7, 11)] [8, 2 ^ 159 + 17]
#guard check { parent with storageReads := slots [(99, 5), (3, 99)] }
  [3, 2 ^ 159 + 7] [(99, 5), (3, 99)] [(3, 11), (2 ^ 159 + 7, 11)] [8, 2 ^ 159 + 17]
#guard check { parent with codeReads := codes [(99, 11), (3, 99)] }
  [3, 2 ^ 159 + 7] [(3, 5), (3, 2 ^ 255 + 9)] [(99, 11), (3, 99)] [8, 2 ^ 159 + 17]
#guard check { parent with createdAccounts := addresses [3, 99] }
  [3, 2 ^ 159 + 7] [(3, 5), (3, 2 ^ 255 + 9)] [(3, 11), (2 ^ 159 + 7, 11)] [3, 99]

private def unionChild : TxObs :=
  ⟨parent.accountReads ∪ addresses [3, 99], parent.storageReads ∪ slots [(3, 5), (99, 5)],
    parent.codeReads ∪ codes [(3, 11), (3, 99)], parent.createdAccounts ∪ addresses [8, 99]⟩

#guard check unionChild [3, 2 ^ 159 + 7, 99] [(3, 5), (3, 2 ^ 255 + 9), (99, 5)]
  [(3, 11), (2 ^ 159 + 7, 11), (3, 99)] [8, 2 ^ 159 + 17, 99]
#guard check parent [3, 2 ^ 159 + 7] [(3, 5), (3, 2 ^ 255 + 9)]
  [(3, 11), (2 ^ 159 + 7, 11)] [8, 2 ^ 159 + 17]

private def membershipControls : Bool :=
  parent.accountReads.contains (a 3) && !parent.createdAccounts.contains (a 3) &&
    parent.createdAccounts.contains (a 8) && !parent.accountReads.contains (a 8) &&
    parent.storageReads.contains (a 3, k 5) &&
    !parent.storageReads.contains (a 8, k 5) &&
    !parent.storageReads.contains (a 3, k 8) &&
    parent.codeReads.contains (a 3, h 11) &&
    !parent.codeReads.contains (a 8, h 11) &&
    !parent.codeReads.contains (a 3, h 8) &&
    (parent.accountReads.insert (a (3 + 2 ^ 160))).size == parent.accountReads.size &&
    (parent.storageReads.insert (a (3 + 2 ^ 160), k (5 + 2 ^ 256))).size ==
      parent.storageReads.size &&
    (parent.codeReads.insert (a (3 + 2 ^ 160), h (11 + 2 ^ 256))).size ==
      parent.codeReads.size &&
    (parent.createdAccounts.insert (a (8 + 2 ^ 160))).size == parent.createdAccounts.size

#guard membershipControls
#guard !check parent [8] [(3, 5), (3, 2 ^ 255 + 9)]
  [(3, 11), (2 ^ 159 + 7, 11)] [3]
#guard (List.range 20).all fun i ↦
  let n := 129 * 256 ^ i + 17
  check (supplied [n] [(n, 7)] [(n, 11)] [n + 1]) [n] [(n, 7)] [(n, 11)] [n + 1]
#guard (List.range 32).all fun i ↦
  let n := 129 * 256 ^ i + 17
  check (supplied [3] [(3, n), (8, n)] [(3, n), (8, n)] [8])
    [3] [(3, n), (8, n)] [(3, n), (8, n)] [8]

end STFSpec.Conformance.State.TxObsGuards
