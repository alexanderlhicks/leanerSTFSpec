/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import Lean.Data.Json.Parser
import STFSpec.Conformance.Fixtures.Hex

/-!
# Guest record extraction

Internal projections for `EthConformance`, independent of the unimplemented full fixture
and guest types. Validity labels and debug witnesses are never used to compute bytes.
Spec guidance: `STFSpec/informal/modules/EthConformance.md`.
-/

namespace STFSpec.Conformance.Internal

private def object (location : String) (value : Lean.Json) :=
  value.getObj?.mapError fun _ ↦ FixtureError.expectedObject location

private def field (location : String) (value : Lean.Json) (name : String) :=
  value.getObjVal? name |>.mapError fun _ ↦ FixtureError.missingField location name

private def string (location : String) (value : Lean.Json) :=
  value.getStr?.mapError fun _ ↦ FixtureError.expectedString location

private def array (location : String) (value : Lean.Json) :=
  value.getArr?.mapError fun _ ↦ FixtureError.expectedArray location

private def blockRecord (id : FixtureId) (value : Lean.Json) :
    Except FixtureError (Option GuestRecord) := do
  let location := s!"{id.file}:{id.testId}:blocks[{id.blockIndex}]"
  let fields ← object location value
  match fields.get? "statelessInputBytes", fields.get? "statelessOutputBytes" with
  | none, none => return none
  | some input, some expected =>
    let input ← decodeHex (location ++ ".statelessInputBytes")
      (← string (location ++ ".statelessInputBytes") input)
    let expected ← decodeHex (location ++ ".statelessOutputBytes")
      (← string (location ++ ".statelessOutputBytes") expected)
    if expected.size != 43 then
      throw (.outputLength (location ++ ".statelessOutputBytes") expected.size)
    return some { id, input, expected }
  | _, _ => throw (.unpairedGuestFields location)

/-- Project paired guest fields in test-id/block-index order. Engine fixtures produce
no guest records. This is not the future `parseBlockchainFile`/`parseEngineFile` API;
only the format, metadata and relevant container shapes are validated here. -/
def extractGuestRecords (file : String) (value : Lean.Json) :
    Except FixtureError (Array GuestRecord) := do
  let engine ← if file.startsWith "blockchain_tests/" then pure false
    else if file.startsWith "blockchain_tests_engine/" then pure true
    else throw (.unsupportedFile file)
  let tests ← object file value
  let mut records := #[]
  for (testId, test) in tests.toArray do
    let location := file ++ ":" ++ testId
    let fields ← object location test
    let info ← field location test "_info"
    let _ ← object (location ++ "._info") info
    let infoHash ← string (location ++ "._info.hash")
      (← field (location ++ "._info") info "hash")
    let hashBytes ← decodeHex (location ++ "._info.hash") infoHash
    if hashBytes.size != 32 then
      throw (.infoHashLength (location ++ "._info.hash") hashBytes.size)
    let format ← string (location ++ "._info.fixture-format")
      (← field (location ++ "._info") info "fixture-format")
    let expectedFormat := if engine then "blockchain_test_engine" else "blockchain_test"
    if format != expectedFormat then throw (.fixtureFormat location expectedFormat format)
    if engine then
      if (fields.get? "blocks").isSome then throw (.conflictingShape location)
      let _ ← array (location ++ ".engineNewPayloads")
        (← field location test "engineNewPayloads")
    else
      if (fields.get? "engineNewPayloads").isSome then throw (.conflictingShape location)
      let blocks ← array (location ++ ".blocks") (← field location test "blocks")
      for h : index in [:blocks.size] do
        let id : FixtureId := { file, testId, blockIndex := index, infoHash }
        if let some record ← blockRecord id blocks[index] then
          records := records.push record
  return records

/-- Parse a JSON document with Lean's standard parser, then project its guest fields.
Archive authentication and duplicate JSON key rejection belong to the host tool. -/
def parseGuestRecords (file text : String) : Except FixtureError (Array GuestRecord) := do
  let value ← Lean.Json.parse text |>.mapError FixtureError.jsonSyntax
  extractGuestRecords file value

end STFSpec.Conformance.Internal
