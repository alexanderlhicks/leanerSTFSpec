/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit

/-!
# Deterministic pure trie path guards

Library `EthConformance`. These evaluate public operations and exact observations.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §4.
-/

namespace STFSpec.Conformance.Commit.NibblesGuards

open STFSpec.Commit

/-- Construct deterministic test paths through the public model constructor. -/
def path (xs : List Nat) : Nibbles := Nibbles.ofList (xs.map (fun n ↦ ⟨n % 16, by omega⟩))

/-- Exact Nat observation used only in tests. -/
def digits (x : Nibbles) : List Nat := x.toList.map Fin.val

def bytes (b : ByteArray) : List Nat := b.data.toList.map UInt8.toNat

/-- Every possible byte is checked independently, including 00 and ff. -/
def allByteSplits : Bool := (List.range 256).all fun n ↦
  digits (bytesToNibbleList [UInt8.ofNat n].toByteArray) == [n / 16, n % 16]

/-- All 256 ordered nibble pairs under both flags, plus all 16 odd singletons. -/
def allCompactFlags : Bool := (List.range 16).all fun a ↦
  bytes (nibbleListToCompact (path [a]) false) == [16 + a] &&
  bytes (nibbleListToCompact (path [a]) true) == [48 + a] &&
  (List.range 16).all fun b ↦
    bytes (nibbleListToCompact (path [a, b]) false) == [0, 16 * a + b] &&
    bytes (nibbleListToCompact (path [a, b]) true) == [32, 16 * a + b]

def longPath : Nibbles := path (List.range 4097)

def longCompactExpected (leaf : Bool) : List Nat :=
  (if leaf then 48 else 16) ::
    (List.range 2048).map (fun i ↦ 16 * ((2 * i + 1) % 16) + (2 * i + 2) % 16)

def longChecks : Bool :=
  bytes (nibbleListToCompact longPath false) == longCompactExpected false &&
  bytes (nibbleListToCompact longPath true) == longCompactExpected true &&
  digits (bytesToNibbleList (List.replicate 4096 (255 : UInt8)).toByteArray) ==
    List.replicate 8192 15 &&
  digits (bytesToNibbleList (List.replicate 4096 (0 : UInt8)).toByteArray) ==
    List.replicate 8192 0 &&
  commonPrefixLength longPath longPath == 4097 &&
  commonPrefixLength (path (List.range 4096)) longPath == 4096 &&
  commonPrefixLength longPath (path (List.range 4096)) == 4096 &&
  commonPrefixLength (path (List.range 4096 ++ [0])) (path (List.range 4096 ++ [1])) == 4096 &&
  commonPrefixLength (path (0 :: List.range 4096)) (path (1 :: List.range 4096)) == 0

#guard allByteSplits
#guard allCompactFlags
#guard longChecks
#guard digits (bytesToNibbleList ByteArray.empty) == []
#guard digits (bytesToNibbleList ([0, 15, 16, 255] : List UInt8).toByteArray) == [0, 0, 0, 15, 1, 0, 15, 15]
#guard bytes (nibbleListToCompact (path []) false) == [0]
#guard bytes (nibbleListToCompact (path []) true) == [32]
#guard bytes (nibbleListToCompact (path [1, 2, 3]) false) == [17, 35]
#guard bytes (nibbleListToCompact (path [1, 2, 3]) true) == [49, 35]
#guard bytes (nibbleListToCompact (path [0, 15, 15, 0]) false) == [0, 15, 240]
#guard bytes (nibbleListToCompact (path [0, 15, 15, 0]) true) == [32, 15, 240]
#guard commonPrefixLength (path []) (path [1, 2]) == 0
#guard commonPrefixLength (path [1, 2]) (path []) == 0
#guard commonPrefixLength (path [1, 2, 3]) (path [1, 2, 4]) == 2
#guard commonPrefixLength (path [1, 2]) (path [1, 2, 3]) == 2
#guard commonPrefixLength (path [1, 2, 3]) (path [1, 2]) == 2
#guard commonPrefixLength (path [0, 15]) (path [15, 0]) == 0

end STFSpec.Conformance.Commit.NibblesGuards
