/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block
import Lean

/-!
# Complete raw header observations

Library `EthConformance`. The runtime catalogue contains inputs only.
Observations read actual record fields and each common parent getter.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–7.
-/

open STFSpec.Base STFSpec.Block Lean

private def emit (j : Json) : IO Unit := do
  (← IO.getStdout).putStrLn j.compress

private def natural (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw (IO.userError "invalid natural input")

private def digit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

private def parseHexChars : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let high ← digit a
    let low ← digit b
    let tail ← parseHexChars rest
    pure (UInt8.ofNat (16 * high + low) :: tail)
  | _ => none

private def bytes (s : String) : IO Bytes :=
  match parseHexChars s.toList with
  | some bs => pure (Bytes.ofList bs)
  | none => throw (IO.userError "invalid hexadecimal input")

private def fixed {n : Nat} (s : String) : IO (FixedBytes n) := do
  match FixedBytes.ofBytes? (← bytes s) with
  | some value => pure value
  | none => throw (IO.userError "fixed byte width differs")

private def hash32 (s : String) : IO Hash32 := do
  match Hash32.ofBytes? (← bytes s) with
  | some value => pure value
  | none => throw (IO.userError "hash width differs")

private def address (s : String) : IO Address := do
  match Address.ofBytes? (← bytes s) with
  | some value => pure value
  | none => throw (IO.userError "address width differs")

private def word (s : String) : IO U256 := do
  match U256.ofNat? (← natural s) with
  | some value => pure value
  | none => throw (IO.userError "word overflow")

private def u64 (s : String) : IO U64 := do
  match U64.ofNat? (← natural s) with
  | some value => pure value
  | none => throw (IO.userError "U64 overflow")

private def item (values : Array String) (i : Nat) : IO String :=
  match values[i]? with
  | some value => pure value
  | none => throw (IO.userError "missing input field")

private def constructHeader (values : Array String) : IO Header := do
  if values.size != 23 then throw (IO.userError "field count differs")
  return Header.mk
    (← hash32 (← item values 0))
    (← hash32 (← item values 1))
    (← address (← item values 2))
    (← hash32 (← item values 3))
    (← hash32 (← item values 4))
    (← hash32 (← item values 5))
    (← fixed (← item values 6))
    (← natural (← item values 7))
    (← natural (← item values 8))
    (← natural (← item values 9))
    (← natural (← item values 10))
    (← word (← item values 11))
    (← bytes (← item values 12))
    (← fixed (← item values 13))
    (← fixed (← item values 14))
    (← natural (← item values 15))
    (← hash32 (← item values 16))
    (← u64 (← item values 17))
    (← u64 (← item values 18))
    (← hash32 (← item values 19))
    (← hash32 (← item values 20))
    (← hash32 (← item values 21))
    (← u64 (← item values 22))

private def constructPrevHeader (values : Array String) : IO PrevHeader := do
  if values.size != 21 then throw (IO.userError "field count differs")
  return PrevHeader.mk
    (← hash32 (← item values 0))
    (← hash32 (← item values 1))
    (← address (← item values 2))
    (← hash32 (← item values 3))
    (← hash32 (← item values 4))
    (← hash32 (← item values 5))
    (← fixed (← item values 6))
    (← natural (← item values 7))
    (← natural (← item values 8))
    (← natural (← item values 9))
    (← natural (← item values 10))
    (← word (← item values 11))
    (← bytes (← item values 12))
    (← fixed (← item values 13))
    (← fixed (← item values 14))
    (← natural (← item values 15))
    (← hash32 (← item values 16))
    (← u64 (← item values 17))
    (← u64 (← item values 18))
    (← hash32 (← item values 19))
    (← hash32 (← item values 20))

private def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then '0'.toNat + n else 'a'.toNat + n - 10)

private def hex (bs : Bytes) : String :=
  String.ofList (bs.toList.flatMap fun byte ↦
    [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)])

private def field (position : Nat) (name nominal : String) (value : Json) : Json :=
  Json.mkObj [("position", toJson position), ("name", toJson name),
    ("type", toJson nominal), ("value", value)]

private def accessor (name nominal : String) (value : Json) : Json :=
  Json.mkObj [("name", toJson name), ("type", toJson nominal), ("value", value)]

private def observeHeader (h : Header) : List Json :=
  [field 0 "parentHash" "Hash32" (toJson (hex (h.parentHash).toBytes)),
   field 1 "ommersHash" "Hash32" (toJson (hex (h.ommersHash).toBytes)),
   field 2 "coinbase" "Address" (toJson (hex (h.coinbase).toBytes)),
   field 3 "stateRoot" "Root" (toJson (hex (h.stateRoot).toBytes)),
   field 4 "transactionsRoot" "Root" (toJson (hex (h.transactionsRoot).toBytes)),
   field 5 "receiptRoot" "Root" (toJson (hex (h.receiptRoot).toBytes)),
   field 6 "bloom" "Bloom" (toJson (hex (h.bloom).toBytes)),
   field 7 "difficulty" "Nat" (toJson (h.difficulty)),
   field 8 "number" "Nat" (toJson (h.number)),
   field 9 "gasLimit" "Nat" (toJson (h.gasLimit)),
   field 10 "gasUsed" "Nat" (toJson (h.gasUsed)),
   field 11 "timestamp" "U256" (toJson (h.timestamp).toNat),
   field 12 "extraData" "Bytes" (toJson (hex (h.extraData))),
   field 13 "prevRandao" "Bytes32" (toJson (hex (h.prevRandao).toBytes)),
   field 14 "nonce" "Bytes8" (toJson (hex (h.nonce).toBytes)),
   field 15 "baseFeePerGas" "Nat" (toJson (h.baseFeePerGas)),
   field 16 "withdrawalsRoot" "Root" (toJson (hex (h.withdrawalsRoot).toBytes)),
   field 17 "blobGasUsed" "U64" (toJson (h.blobGasUsed).toNat),
   field 18 "excessBlobGas" "U64" (toJson (h.excessBlobGas).toNat),
   field 19 "parentBeaconBlockRoot" "Root" (toJson (hex (h.parentBeaconBlockRoot).toBytes)),
   field 20 "requestsHash" "Hash32" (toJson (hex (h.requestsHash).toBytes)),
   field 21 "blockAccessListHash" "Hash32" (toJson (hex (h.blockAccessListHash).toBytes)),
   field 22 "slotNumber" "U64" (toJson (h.slotNumber).toNat)]

private def observePrevHeader (h : PrevHeader) : List Json :=
  [field 0 "parentHash" "Hash32" (toJson (hex (h.parentHash).toBytes)),
   field 1 "ommersHash" "Hash32" (toJson (hex (h.ommersHash).toBytes)),
   field 2 "coinbase" "Address" (toJson (hex (h.coinbase).toBytes)),
   field 3 "stateRoot" "Root" (toJson (hex (h.stateRoot).toBytes)),
   field 4 "transactionsRoot" "Root" (toJson (hex (h.transactionsRoot).toBytes)),
   field 5 "receiptRoot" "Root" (toJson (hex (h.receiptRoot).toBytes)),
   field 6 "bloom" "Bloom" (toJson (hex (h.bloom).toBytes)),
   field 7 "difficulty" "Nat" (toJson (h.difficulty)),
   field 8 "number" "Nat" (toJson (h.number)),
   field 9 "gasLimit" "Nat" (toJson (h.gasLimit)),
   field 10 "gasUsed" "Nat" (toJson (h.gasUsed)),
   field 11 "timestamp" "U256" (toJson (h.timestamp).toNat),
   field 12 "extraData" "Bytes" (toJson (hex (h.extraData))),
   field 13 "prevRandao" "Bytes32" (toJson (hex (h.prevRandao).toBytes)),
   field 14 "nonce" "Bytes8" (toJson (hex (h.nonce).toBytes)),
   field 15 "baseFeePerGas" "Nat" (toJson (h.baseFeePerGas)),
   field 16 "withdrawalsRoot" "Root" (toJson (hex (h.withdrawalsRoot).toBytes)),
   field 17 "blobGasUsed" "U64" (toJson (h.blobGasUsed).toNat),
   field 18 "excessBlobGas" "U64" (toJson (h.excessBlobGas).toNat),
   field 19 "parentBeaconBlockRoot" "Root" (toJson (hex (h.parentBeaconBlockRoot).toBytes)),
   field 20 "requestsHash" "Hash32" (toJson (hex (h.requestsHash).toBytes))]

private def observeParent (h : ParentHeader) : List Json :=
  [accessor "gasLimit" "Nat" (toJson (h.gasLimit)),
   accessor "gasUsed" "Nat" (toJson (h.gasUsed)),
   accessor "baseFeePerGas" "Nat" (toJson (h.baseFeePerGas)),
   accessor "timestamp" "U256" (toJson (h.timestamp).toNat),
   accessor "number" "Nat" (toJson (h.number)),
   accessor "stateRoot" "Root" (toJson (hex (h.stateRoot).toBytes)),
   accessor "excessBlobGas" "U64" (toJson (h.excessBlobGas).toNat),
   accessor "blobGasUsed" "U64" (toJson (h.blobGasUsed).toNat),
   accessor "parentHash" "Hash32" (toJson (hex (h.parentHash).toBytes))]

private def observe (id family variant : String) (values : Array String) : IO Unit := do
  let (fields, accessors, actualVariant) ← match family, variant with
    | "Header", "amsterdam" => do
      let h ← constructHeader values
      pure (observeHeader h, [], "amsterdam")
    | "PrevHeader", "bpo5" => do
      let h ← constructPrevHeader values
      pure (observePrevHeader h, [], "bpo5")
    | "ParentHeader", "amsterdam" => do
      let parent := ParentHeader.amsterdam (← constructHeader values)
      match parent with
      | .amsterdam h => pure (observeHeader h, observeParent parent, "amsterdam")
      | .bpo5 h => pure (observePrevHeader h, observeParent parent, "bpo5")
    | "ParentHeader", "bpo5" => do
      let parent := ParentHeader.bpo5 (← constructPrevHeader values)
      match parent with
      | .amsterdam h => pure (observeHeader h, observeParent parent, "amsterdam")
      | .bpo5 h => pure (observePrevHeader h, observeParent parent, "bpo5")
    | _, _ => throw (IO.userError "input family or variant differs")
  emit <| Json.mkObj [("caseId", toJson id), ("family", toJson family),
    ("variant", toJson actualVariant), ("fields", toJson fields),
    ("commonAccessors", toJson accessors)]

/-- Emit complete actual observations from the input-only catalogue. -/
def main (args : List String) : IO UInt32 := do
  try
    let path ← match args with
      | [path] => pure path
      | _ => throw (IO.userError "expected one input path")
    let rows := (← IO.FS.readFile path).splitOn "\n" |>.filter (· != "")
    emit <| Json.mkObj [("schema", toJson "header-carriers-v1"),
      ("catalog", toJson "4639932a31950e19686713ce32266d01ba172dc64417b66d0c922a3cb2152d63"),
      ("count", toJson rows.length)]
    for row in rows do
      match row.splitOn "\t" with
      | id :: family :: variant :: values => observe id family variant values.toArray
      | _ => throw (IO.userError "input row shape differs")
    emit <| Json.mkObj [("complete", toJson true), ("count", toJson rows.length)]
    pure 0
  catch error =>
    (← IO.getStderr).putStrLn error.toString
    pure 1
