/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit
import STFSpec.Conformance.Commit.NibblesGuards

/-!
# Compact decoder regressions

Library `EthConformance`. Exact diagnostic, ordered digits, flags, canonical
roundtrips and accepted-wire normalization. No node or guest acceptance claim.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Commit.CompactGuards

open STFSpec.Commit NibblesGuards

/-- Compare exact typed diagnostics and full values in conformance observations. -/
local instance {α : Type} [BEq α] : BEq (Except TrieError α) where
  beq
    | .error a, .error b => a == b
    | .ok a, .ok b => a == b
    | _, _ => false

/-- Observe the whole public decoder result, retaining the typed diagnostic. -/
def decodeView (b : ByteArray) : Except TrieError (List Nat × Bool) :=
  (compactToNibbles b).map (fun p ↦ (digits p.1, p.2))

/-- Check the complete canonical roundtrip, including its leaf flag. -/
def roundtrip (p : Nibbles) (leaf : Bool) : Bool :=
  decodeView (nibbleListToCompact p leaf) == .ok (digits p, leaf)

/-- Observe the complete canonical reencoding of an accepted wire. -/
def reencodeView (b : ByteArray) : Except TrieError (List Nat) :=
  (compactToNibbles b).map (fun p ↦ bytes (nibbleListToCompact p.1 p.2))

/-- All leading bytes, with an empty and a four-byte suffix, independently. -/
def allLeadingBytes : Bool := (List.range 256).all fun first ↦
  let leaf := first / 32 % 2 == 1
  let firstDigits := if first / 16 % 2 == 1 then [first % 16] else []
  decodeView [UInt8.ofNat first].toByteArray == .ok (firstDigits, leaf) &&
  decodeView ([UInt8.ofNat first, 35, 255, 0, 126] : List UInt8).toByteArray ==
    .ok (firstDigits ++ [2, 3, 15, 15, 0, 0, 7, 14], leaf)

/-- Empty/odd/even, zero/15 and mixed long paths under both leaf flags. -/
def canonicalCases : Bool :=
  ([[], [0], [15], [1, 2], [1, 2, 3], List.replicate 4096 0,
    List.replicate 4097 15, List.range 4096, List.range 4097] : List (List Nat)).all
      fun xs ↦ roundtrip (path xs) false && roundtrip (path xs) true

#guard allLeadingBytes
#guard canonicalCases
#guard decodeView ByteArray.empty == .error (.malformed .compactEmpty)
#guard decodeView ([0] : List UInt8).toByteArray == .ok ([], false)
#guard decodeView ([15] : List UInt8).toByteArray == .ok ([], false)
#guard decodeView ([32] : List UInt8).toByteArray == .ok ([], true)
#guard decodeView ([47] : List UInt8).toByteArray == .ok ([], true)
#guard decodeView ([241, 35] : List UInt8).toByteArray == .ok ([1, 2, 3], true)
#guard reencodeView ([15] : List UInt8).toByteArray == .ok [0]
#guard reencodeView ([47] : List UInt8).toByteArray == .ok [32]
#guard reencodeView ([241, 35] : List UInt8).toByteArray == .ok [49, 35]
#guard reencodeView ([128, 35] : List UInt8).toByteArray == .ok [0, 35]

end STFSpec.Conformance.Commit.CompactGuards
