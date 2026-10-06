/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit.AccountDecode

/-!
# Complete account decoder wire regressions

Library `EthConformance`. Observe complete parser trees separately from complete
nonce, balance, root and code values. Coarse errors do not reveal failed fields.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` §§3–4.
-/

open STFSpec.Base STFSpec.Codec STFSpec.State STFSpec.StateCommit

#check_failure STFSpec.StateCommit.checkedBalance
#check_failure STFSpec.StateCommit.checkedBalanceReference
#check_failure STFSpec.StateCommit.balanceStep
#check_failure STFSpec.StateCommit.nonceField
#check_failure STFSpec.StateCommit.balanceField
#check_failure STFSpec.StateCommit.hashField
#check_failure STFSpec.StateCommit.accountFields

private def raw (xs : List UInt8) : ByteArray := ⟨xs.toArray⟩
private def testHash (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def consts : HashConsts := ⟨testHash 17, testHash 23, testHash 31, testHash 37⟩
private def defaults : Option (Nat × Nat × List UInt8 × List UInt8) :=
  some (0, 0, (testHash 23).toBytes.toList, (testHash 17).toBytes.toList)
private def observed (wire : ByteArray) : Option (Nat × Nat × List UInt8 × List UInt8) :=
  match decodeAccountLeaf consts wire with
  | .ok (acc, root) => some (acc.nonce, acc.balance.toNat, root.toBytes.toList,
      acc.codeHash.toBytes.toList)
  | .error _ => none
private def leafError (wire : ByteArray) : Bool :=
  match decodeAccountLeaf consts wire with
  | .error (.malformed .leaf) => true
  | _ => false
private def tree : RlpItem → String
  | .bytes bs => "bytes" ++ toString (bs.data.toList.map UInt8.toNat)
  | .list xs => "list[" ++ String.intercalate "," (xs.map tree) ++ "]"

private def parsed (wire : ByteArray) (item : RlpItem) : Bool :=
  match Rlp.decode wire with
  | .ok actual => tree actual == tree item
  | .error _ => false
private def parserError (wire : List UInt8) (e : RlpError) : Bool :=
  match Rlp.decode (raw wire) with
  | .error actual => actual == e && leafError (raw wire)
  | _ => false
private def allEmpty : List RlpItem := List.replicate 4 (.bytes ByteArray.empty)
private def fields (items : List RlpItem) : ByteArray := Rlp.encode (.list items)
private def changed (i : Nat) (item : RlpItem) : ByteArray := fields (allEmpty.set i item)
private def bytesField (i : Nat) (xs : List UInt8) : ByteArray := changed i (.bytes (raw xs))

#guard parserError [] .empty
#guard parsed (raw [196, 128, 128, 128, 128]) (.list allEmpty)
#guard observed (raw [196, 128, 128, 128, 128]) = defaults
#guard observed (raw [196, 192, 192, 192, 192]) = defaults
#guard (List.range 16).all fun mask ↦
  let items := (List.range 4).map fun i ↦
    if mask / 2 ^ i % 2 = 0 then RlpItem.bytes ByteArray.empty else .list []
  parsed (fields items) (.list items) && observed (fields items) == defaults
#guard ([[], [.bytes ByteArray.empty], List.replicate 3 (.list []),
    List.replicate 5 (.list [])] : List (List RlpItem)).all fun items ↦
  parsed (fields items) (.list items) && leafError (fields items)
#guard parsed (raw [132, 128, 128, 128, 128]) (.bytes (raw [128, 128, 128, 128])) &&
  leafError (raw [132, 128, 128, 128, 128])
#guard ([0, 1, 127, 128, 255] : List UInt8).all fun b ↦
  leafError (Rlp.encodeBytes (raw [b]))
#guard (List.range 4).all fun i ↦
  ([.list [.bytes ByteArray.empty], .list [.list []],
    .list [.list [.list []]], .list [.bytes (raw [1])]] : List RlpItem).all fun item ↦
    parsed (changed i item) (.list (allEmpty.set i item)) && leafError (changed i item)

-- Complete unbounded nonce and numerically bounded balance, including long zeros.
#guard ([0, 1, 31, 32, 33, 55, 56, 57, 255, 256, 257, 1024] : List Nat).all fun k ↦
  observed (bytesField 0 (List.replicate k 0 ++ [1])) ==
    some (1, 0, (testHash 23).toBytes.toList, (testHash 17).toBytes.toList) &&
  observed (bytesField 1 (List.replicate k 0 ++ [1])) ==
    some (0, 1, (testHash 23).toBytes.toList, (testHash 17).toBytes.toList) &&
  observed (bytesField 1 (List.replicate k 0 ++ List.replicate 32 255)) ==
    some (0, 2 ^ 256 - 1, (testHash 23).toBytes.toList, (testHash 17).toBytes.toList) &&
  leafError (bytesField 1 (List.replicate k 0 ++ [1] ++ List.replicate 32 0))
#guard observed (bytesField 0 ([1] ++ List.replicate 128 0 ++ [17])) =
  some (2 ^ 1032 + 17, 0, (testHash 23).toBytes.toList, (testHash 17).toBytes.toList)
#guard observed (bytesField 0 [0, 0, 1]) =
  some (1, 0, (testHash 23).toBytes.toList, (testHash 17).toBytes.toList)
#guard observed (bytesField 1 [1, 2, 0, 255]) =
  some (0, 16908543, (testHash 23).toBytes.toList, (testHash 17).toBytes.toList)
#guard (List.range 256).all fun j ↦
  observed (changed 1 (Rlp.ofNat (2 ^ j))) ==
    some (0, 2 ^ j, (testHash 23).toBytes.toList, (testHash 17).toBytes.toList)
#guard ([[], [0], [255], [1, 0, 128, 255], List.replicate 1024 0,
    List.replicate 1024 255] : List (List UInt8)).all fun suffix ↦
  leafError (bytesField 1 (List.replicate 32 255 ++ [0] ++ suffix))

-- Empty hash payloads default; explicit length-32 all-zero strings remain zero.
#guard ([2, 3] : List Nat).all fun i ↦
  ([1, 31, 33, 55, 56, 57, 255, 256, 1024] : List Nat).all fun k ↦
    parsed (bytesField i (List.replicate k 0))
      (.list (allEmpty.set i (.bytes (raw (List.replicate k 0))))) &&
    leafError (bytesField i (List.replicate k 0))
#guard observed (bytesField 2 (List.replicate 32 0)) =
  some (0, 0, List.replicate 32 0, (testHash 17).toBytes.toList)
#guard observed (bytesField 3 (List.replicate 32 0)) =
  some (0, 0, (testHash 23).toBytes.toList, List.replicate 32 0)
#guard (List.range 32).all fun i ↦ ([0, 1, 127, 128, 255] : List UInt8).all fun b ↦
  let payload := (List.replicate 32 0).set i b
  observed (bytesField 2 payload) == some (0, 0, payload, (testHash 17).toBytes.toList) &&
  observed (bytesField 3 payload) == some (0, 0, (testHash 23).toBytes.toList, payload)
private def asymmetricRoot : List UInt8 := (List.range 32).map fun i ↦ UInt8.ofNat (i * 7)
private def asymmetricCode : List UInt8 := (List.range 32).map fun i ↦ UInt8.ofNat (255 - i * 3)
#guard observed (fields [.bytes (raw [0, 1]), .bytes (raw [255]),
    .bytes (raw asymmetricRoot), .bytes (raw asymmetricCode)]) =
  some (1, 255, asymmetricRoot, asymmetricCode)
#guard observed (fields [.bytes (raw [0, 1]), .bytes (raw [255]),
    .bytes (raw asymmetricCode), .bytes (raw asymmetricRoot)]) =
  some (1, 255, asymmetricCode, asymmetricRoot)

-- Full raw RLP errors precede all local shape/field failures.
#guard parserError [198, 193, 128, 128, 128, 129, 0]
  (.nonCanonical "prefixed single byte")
#guard parserError [198, 193, 128, 128, 128, 193, 129] .truncated
#guard parserError [198, 128, 128, 128, 129, 0, 128]
  (.nonCanonical "prefixed single byte")
#guard parserError [199, 193, 128, 128, 128, 184, 1, 1]
  (.nonCanonical "long form for short payload")
#guard parserError [196, 128, 128, 128] .truncated
#guard parserError [196, 128, 128, 128, 128, 0] .trailing
#guard parserError [248, 4, 128, 128, 128, 128]
  (.nonCanonical "long form for short payload")
#guard parserError [249, 0, 56] (.nonCanonical "leading zero length")
#guard parserError [0, 0] (.nonCanonical "negative length")
#guard parserError [129, 1] (.nonCanonical "prefixed single byte")
#guard parserError [248, 56, 128] .truncated

-- Canonical encoder/decoder pairs include zero/max balance and huge nonces.
#guard ([0, 1, 127, 128, 255, 256, 2 ^ 256, 2 ^ 1024 + 17] : List Nat).all fun n ↦
  ([U256.zero, U256.one, U256.max] : List U256).all fun b ↦
    ([testHash 0, testHash 17, testHash 23] : List Hash32).all fun r ↦
      observed (encodeAccount (Account.mk n b (testHash 0)) r) ==
        some (n, b.toNat, r.toBytes.toList, List.replicate 32 0)
