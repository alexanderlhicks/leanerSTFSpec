/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit
import STFSpec.Codec.RlpU256

/-!
# Complete storage decoder semantic and first-failure regressions

Library `EthConformance`. Complete numeric values and complete parser results are observed
separately. The typed 32-byte admission and framing thresholds are checked independently.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` §§3–4.
-/

open STFSpec.Base STFSpec.Codec STFSpec.State STFSpec.StateCommit

private def raw (xs : List UInt8) : ByteArray := ⟨xs.toArray⟩
private def observed (leaf : ByteArray) : Option Nat :=
  match decodeStorageLeaf leaf with
  | .ok v => some v.toNat
  | .error _ => none
private def leafError (leaf : ByteArray) : Bool :=
  match decodeStorageLeaf leaf with
  | .error (.malformed .leaf) => true
  | _ => false
private def stringValue (xs : List UInt8) : Option Nat :=
  observed (Rlp.encodeBytes (raw xs))
private def parserBytes (wire payload : List UInt8) : Bool :=
  match Rlp.decode (raw wire) with
  | .ok (.bytes b) => b.data.toList == payload
  | _ => false
private def parserError (wire : List UInt8) (expected : RlpError) : Bool :=
  match Rlp.decode (raw wire) with
  | .error e => e == expected && leafError (raw wire)
  | _ => false

#guard leafError (raw [])
#guard parserBytes [128] [] ∧ observed (raw [128]) = some 0
#guard ([1, 127] : List UInt8).all fun b ↦
  parserBytes [b] [b] && observed (raw [b]) == some b.toNat
#guard parserBytes [129, 128] [128] ∧ observed (raw [129, 128]) = some 128
#guard parserBytes [129, 255] [255] ∧ observed (raw [129, 255]) = some 255
#guard leafError (raw [0])
#guard leafError (raw [130, 0, 1])
#guard leafError (raw [130, 0, 0])
#guard ([[], [0], [128], [192], [0, 129, 128], [193, 192]] : List (List UInt8)).all
  fun body ↦ leafError (Rlp.encode (.list (body.map fun b ↦ .bytes (raw [b]))))
#guard leafError (raw [192])
#guard leafError (raw [193, 0])
#guard leafError (raw [193, 128])

-- Complete payload boundary observations include every significant position.
#guard ([1, 31, 32, 33, 55, 56, 57, 64, 255, 256, 257, 1024] : List Nat).all
  fun k ↦ stringValue (List.replicate k 0) == none &&
    ([1, 127, 128, 255] : List UInt8).all fun b ↦
      stringValue (List.replicate k 0 ++ [b]) == none
#guard ([0, 1, 31, 32, 33, 55, 56, 57, 64, 256, 1024] : List Nat).all fun k ↦
  stringValue (List.replicate k 0 ++ [1] ++ List.replicate 31 0) ==
    (if k = 0 then some (2 ^ 248) else none) &&
  stringValue (List.replicate k 0 ++ List.replicate 32 255) ==
    (if k = 0 then some (2 ^ 256 - 1) else none) &&
  stringValue (List.replicate k 0 ++ [1] ++ List.replicate 32 0) == none
#guard (List.range 32).all fun j ↦
  stringValue (List.replicate j 0 ++ [1] ++ List.replicate (31 - j) 0) ==
    (if j = 0 then some (2 ^ 248) else none)
#guard (List.range 256).all fun j ↦
  observed (encodeStorage (U256.ofNat (2 ^ j))) == some (2 ^ j)
#guard observed (encodeStorage (U256.ofNat (2 ^ 256 - 1))) = some (2 ^ 256 - 1)
#guard stringValue [1, 2, 0, 255] = some 16908543
#guard stringValue [255, 0, 2, 1] = some 4278190593
#guard ([[], [0], [255], [1, 0, 128, 255], List.replicate 1024 0,
    List.replicate 1024 255] : List (List UInt8)).all fun suffix ↦
  stringValue (List.replicate 32 255 ++ [0] ++ suffix) == none &&
  stringValue ([1] ++ List.replicate 32 0 ++ suffix) == none &&
  stringValue (List.replicate 33 128 ++ suffix) == none

-- Numeric-looking list children are parsed fully but never checked as U256.
private def mixedList : RlpItem := .list [.bytes (raw (List.replicate 33 255)),
  .list [.bytes (raw (List.replicate 1024 0 ++ [1])), .list []], .bytes (raw [128])]
#guard leafError (Rlp.encode mixedList)

-- Explicit parser diagnostics and local errors establish failure order.
#guard parserError [] .empty
#guard parserError [129, 0] (.nonCanonical "prefixed single byte")
#guard parserError [129, 1] (.nonCanonical "prefixed single byte")
#guard parserError [184, 1, 1] (.nonCanonical "long form for short payload")
#guard parserError [248, 1, 128] (.nonCanonical "long form for short payload")
#guard parserError [185, 0, 56] (.nonCanonical "leading zero length")
#guard parserError [249, 0, 56] (.nonCanonical "leading zero length")
#guard parserError [130, 1] .truncated
#guard parserError [184, 56, 0] .truncated
#guard parserError [248, 56, 128] .truncated
#guard parserError [0, 0] (.nonCanonical "negative length")
#guard parserError [5, 0] (.nonCanonical "negative length")
#guard parserError [192, 0] .trailing
#guard parserError [193, 129] .truncated
#guard parserError [194, 129, 0] (.nonCanonical "prefixed single byte")
#guard parserError [194, 193, 129] .truncated
private def overflowWire : List UInt8 :=
  (Rlp.encodeBytes (raw ([1] ++ List.replicate 32 0))).data.toList
#guard parserBytes overflowWire ([1] ++ List.replicate 32 0) ∧
  leafError (raw overflowWire)
#guard parserError (overflowWire ++ [0]) .trailing
#guard parserError (163 :: [1] ++ List.replicate 32 0) .truncated
private def malformedList : List UInt8 :=
  228 :: overflowWire ++ [129, 0]
#guard parserError malformedList (.nonCanonical "prefixed single byte")

-- Empty numeric payload is accepted privately, without changing stored-zero policy.
#guard observed (encodeStorage U256.zero) = some 0
#guard parserError [130, 0, 1, 128] .trailing
#guard parserError [193, 0, 128] .trailing
private def leadingWide : ByteArray := raw (0 :: List.replicate 31 0 ++ [1])
private def typedError (leaf : ByteArray) (expected : RlpError) : Bool :=
  match Rlp.decodeTo (α := U256) leaf with
  | .error e => e == expected
  | .ok _ => false
#guard typedError (Rlp.encodeBytes leadingWide) (.nonCanonical "integer leading zero")
#guard typedError (Rlp.encodeBytes (raw (1 :: List.replicate 32 0))) (.shape "integer width")
#guard typedError (raw [192]) (.shape "integer")
#guard typedError (raw [130, 0, 1, 128]) .trailing
#guard typedError (raw [194, 129, 0]) (.nonCanonical "prefixed single byte")
#guard leafError (Rlp.encodeBytes leadingWide)
#guard parserError ((Rlp.encodeBytes leadingWide).data.toList ++ [0]) .trailing
