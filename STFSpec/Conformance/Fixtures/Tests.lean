/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Conformance.Fixtures.Extract
import STFSpec.Conformance.Fixtures.Index

/-!
# Fixture extraction guards

Lean-only deterministic cases for the `EthConformance` helpers, including
failure precedence and independence from fixture validity labels. No guest is executed.
Spec guidance: `STFSpec/informal/modules/EthConformance.md`.
-/

namespace STFSpec.Conformance.Internal.Tests

private def hashText : String := "0x" ++ String.ofList (List.replicate 64 '0')
private def outputText : String := "0x" ++ String.ofList (List.replicate 86 '0')
private def guestBlock (input := "0x1501") (output := outputText) : Lean.Json :=
  Lean.Json.mkObj [("statelessInputBytes", .str input), ("statelessOutputBytes", .str output)]
private def test (blocks : Array Lean.Json) (engine := false) : Lean.Json :=
  Lean.Json.mkObj [("_info", Lean.Json.mkObj [("hash", .str hashText),
    ("fixture-format", .str (if engine then "blockchain_test_engine" else "blockchain_test"))]),
    (if engine then "engineNewPayloads" else "blocks", .arr blocks)]
private def withField (value : Lean.Json) (name : String) (field : Lean.Json) : Lean.Json :=
  match value with
  | .obj fields => .obj (fields.insert name field)
  | _ => value
private def fixture (blocks : Array Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [("test", test blocks)]
private def ids (result : Except FixtureError (Array GuestRecord)) : Array FixtureId :=
  match result with
  | .ok records => records.map (·.id)
  | .error _ => #[]
private def isError {α : Type} (result : Except FixtureError α) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false
private def file : String := "blockchain_tests/area/file.json"
private def id (testId : String) (index : Nat := 0) (file := file) : FixtureId :=
  { file, testId, blockIndex := index, infoHash := hashText }

#guard (decodeHex "x" "0x00aAfF").toOption.map (·.data) == some #[0, 170, 255]
#guard (decodeHex "x" "0x").toOption.map (·.size) == some 0
#guard isError (decodeHex "x" "0X00")
#guard isError (decodeHex "x" "0")
#guard (decodeHex "x" "0x0").toOption == none
#guard isError (decodeHex "x" "0xgg")
#guard isError (decodeHex "x" "0x00 0")
#guard isError (decodeHex "x" "0xé")
#guard decodeHex "x" "0xg" matches .error (.oddHexLength "x")
#guard decodeHex "x" "0x0g" matches .error (.nonHex "x" 1)

#guard (extractGuestRecords file (fixture #[guestBlock])).toOption.map (·.size) == some 1
#guard ((extractGuestRecords file (fixture #[guestBlock])).toOption.bind (·[0]?)
  |>.map (fun r ↦ r.input.data == #[21, 1] && r.expected.size == 43 && r.id == id "test"))
  == some true
#guard (extractGuestRecords file (fixture #[Lean.Json.mkObj []])).toOption.map (·.size) == some 0
#guard isError (extractGuestRecords file (fixture #[Lean.Json.mkObj
  [("statelessInputBytes", .str "0x")]]))
#guard isError (extractGuestRecords file (fixture #[Lean.Json.mkObj
  [("statelessOutputBytes", .str outputText)]]))
#guard isError (extractGuestRecords file (fixture #[guestBlock "0x0"]))
#guard isError (extractGuestRecords file (fixture #[guestBlock "0xgg"]))
#guard isError (extractGuestRecords file (fixture #[guestBlock "0x" "0x00"]))
#guard isError (extractGuestRecords file (fixture #[Lean.Json.mkObj
  [("statelessInputBytes", .null), ("statelessOutputBytes", .str outputText)]]))
#guard isError (extractGuestRecords file (fixture #[.null]))
#guard isError (extractGuestRecords file (.arr #[]))
#guard isError (extractGuestRecords file (Lean.Json.mkObj [("test", .null)]))
#guard isError (extractGuestRecords file (Lean.Json.mkObj [("test", Lean.Json.mkObj [])]))
#guard isError (extractGuestRecords file (Lean.Json.mkObj [("test",
  withField (test #[]) "engineNewPayloads" (.arr #[]))]))
#guard (extractGuestRecords "blockchain_tests_engine/area/file.json"
  (Lean.Json.mkObj [("test", test #[] true)])).toOption.map (·.size) == some 0
#guard isError (extractGuestRecords "blockchain_tests_engine/area/file.json" (fixture #[]))
#guard isError (parseGuestRecords file "{")
#guard isError (parseGuestRecords file "{} trailing")
#guard isError (extractGuestRecords "../blockchain_tests/file.json" (fixture #[]))

-- Constructor-specific failures, with later fields malformed to lock failure order.
private def info (hash : Lean.Json := .str hashText)
    (format : Lean.Json := .str "blockchain_test") : Lean.Json :=
  Lean.Json.mkObj [("hash", hash), ("fixture-format", format)]
private def badTest (metadata : Lean.Json) (blocks : Lean.Json := .null) : Lean.Json :=
  Lean.Json.mkObj [("test", Lean.Json.mkObj [("_info", metadata), ("blocks", blocks)])]
private def failure {α : Type} (result : Except FixtureError α) : Option FixtureError :=
  match result with
  | .error error => some error
  | .ok _ => none
private def location : String := file ++ ":test"
private def blockLocation : String := location ++ ":blocks[0]"
private def engineFile : String := "blockchain_tests_engine/area/file.json"

#guard extractGuestRecords "unsupported" .null matches .error (.unsupportedFile _)
#guard extractGuestRecords file .null matches .error (.expectedObject _)
#guard extractGuestRecords file (Lean.Json.mkObj [("test", .null)])
  matches .error (.expectedObject _)
#guard extractGuestRecords file (Lean.Json.mkObj [("test", Lean.Json.mkObj [])])
  matches .error (.missingField _ "_info")
#guard extractGuestRecords file (badTest .null) matches .error (.expectedObject _)
#guard extractGuestRecords file (badTest (Lean.Json.mkObj []))
  matches .error (.missingField _ "hash")
#guard extractGuestRecords file (badTest (info .null .null))
  matches .error (.expectedString _)
#guard extractGuestRecords file (badTest (info (.str "00") .null))
  matches .error (.hexPrefix _)
#guard extractGuestRecords file (badTest (info (.str "0xg") .null))
  matches .error (.oddHexLength _)
#guard extractGuestRecords file (badTest (info (.str "0xgg") .null))
  matches .error (.nonHex _ 0)
#guard extractGuestRecords file (badTest (info (.str "0x00") .null))
  matches .error (.infoHashLength _ 1)
#guard extractGuestRecords file (badTest (Lean.Json.mkObj [("hash", .str hashText)]))
  matches .error (.missingField _ "fixture-format")
#guard extractGuestRecords file (badTest (info (.str hashText) .null))
  matches .error (.expectedString _)
#guard extractGuestRecords file (badTest (info (.str hashText) (.str "wrong")))
  matches .error (.fixtureFormat _ "blockchain_test" "wrong")
#guard extractGuestRecords file (Lean.Json.mkObj [("test",
  withField (test #[]) "engineNewPayloads" .null)])
  matches .error (.conflictingShape _)
#guard extractGuestRecords engineFile (Lean.Json.mkObj [("test",
  withField (test #[] true) "blocks" .null)]) matches .error (.conflictingShape _)
-- Conflicting shapes take precedence even when the selected container is invalid.
#guard extractGuestRecords file (Lean.Json.mkObj [("test",
  withField (withField (test #[]) "blocks" .null) "engineNewPayloads" .null)])
  matches .error (.conflictingShape _)
#guard extractGuestRecords engineFile (Lean.Json.mkObj [("test",
  withField (withField (test #[] true) "engineNewPayloads" .null) "blocks" .null)])
  matches .error (.conflictingShape _)
#guard extractGuestRecords engineFile (Lean.Json.mkObj [("test",
  withField (test #[] true) "engineNewPayloads" .null)])
  matches .error (.expectedArray _)
#guard extractGuestRecords file (badTest info) matches .error (.expectedArray _)
#guard extractGuestRecords file (fixture #[.null]) matches .error (.expectedObject _)
#guard extractGuestRecords file (fixture #[Lean.Json.mkObj [("statelessInputBytes", .null)]])
  matches .error (.unpairedGuestFields _)
#guard extractGuestRecords file (fixture #[withField (guestBlock "0xg" "bad")
  "statelessInputBytes" .null]) matches .error (.expectedString _)
#guard extractGuestRecords file (fixture #[guestBlock "bad" "bad"])
  matches .error (.hexPrefix _)
#guard extractGuestRecords file (fixture #[guestBlock "0xg" "bad"])
  matches .error (.oddHexLength _)
#guard extractGuestRecords file (fixture #[guestBlock "0xgg" "bad"])
  matches .error (.nonHex _ 0)
#guard extractGuestRecords file (fixture #[withField guestBlock "statelessOutputBytes" .null])
  matches .error (.expectedString _)
#guard extractGuestRecords file (fixture #[guestBlock "0x" "bad"])
  matches .error (.hexPrefix _)
#guard extractGuestRecords file (fixture #[guestBlock "0x" "0xg"])
  matches .error (.oddHexLength _)
#guard extractGuestRecords file (fixture #[guestBlock "0x" "0xgg"])
  matches .error (.nonHex _ 0)
#guard extractGuestRecords file (fixture #[guestBlock "0x" "0x00"])
  matches .error (.outputLength _ 1)
-- Locations retain the owning object or failing field, including missing metadata fields.
#guard failure (extractGuestRecords file (badTest (Lean.Json.mkObj []))) ==
  some (.missingField (location ++ "._info") "hash")
#guard failure (extractGuestRecords file (badTest (info (.str "0x00")))) ==
  some (.infoHashLength (location ++ "._info.hash") 1)
#guard failure (extractGuestRecords file (fixture #[guestBlock "0x" "0x00"])) ==
  some (.outputLength (blockLocation ++ ".statelessOutputBytes") 1)

-- Same exact bytes despite mutually contradictory fixture validity labels and debug data.
#guard (extractGuestRecords file (fixture #[guestBlock])).toOption ==
  (extractGuestRecords file (fixture #[withField
    (withField guestBlock "expectException" (.str "INVALID"))
    "executionWitness" (.str "irrelevant")])).toOption
#guard ids (extractGuestRecords file (Lean.Json.mkObj
  [("z", test #[guestBlock]), ("a", test #[Lean.Json.mkObj [], guestBlock, guestBlock])])) ==
  #[id "a" 1, id "a" 2, id "z"]
#guard (sortedIndex #[id "z", id "a" 2, id "a"]).toOption == some #[id "a", id "a" 2, id "z"]
#guard isError (sortedIndex #[id "a", id "a"])
#guard (boundedIndex 1 #[id "z", id "a" 2, id "a"]).toOption == some #[id "a"]
#guard (boundedIndex 0 #[id "z", id "x" 0
  "blockchain_tests/for_amsterdam/eip8025_optional_proofs/case/file.json"]).toOption ==
  some #[id "x" 0 "blockchain_tests/for_amsterdam/eip8025_optional_proofs/case/file.json"]
#guard (boundedIndex 1 #[id "z", id "a" 2, id "a"]).toOption ==
  (boundedIndex 1 #[id "a", id "z", id "a" 2]).toOption

end STFSpec.Conformance.Internal.Tests
