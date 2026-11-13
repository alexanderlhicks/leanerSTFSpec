/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit.StorageDecode
import Lean

/-!
# Complete strict storage-leaf observations

Library `EthConformance`. Reads only independently frozen raw inputs; observations
contain every raw byte and full local result, preserving row order and duplicates.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` §§3–7.
-/

open STFSpec.Base STFSpec.State STFSpec.StateCommit Lean

private def hexByte (s : String) : Option UInt8 := do
  let digits ← s.toList.mapM fun c ↦
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
    else none
  match digits with
  | [a, b] => some (UInt8.ofNat (16 * a + b))
  | _ => none

private def rawBytes (s : String) : Option ByteArray := do
  let chars := s.toList
  if chars.length % 2 != 0 then none
  else
    let bytes ← (List.range (chars.length / 2)).mapM fun i ↦
      hexByte (String.ofList ((chars.drop (2 * i)).take 2))
    pure ⟨bytes.toArray⟩

/-- Observe each complete raw wire through the public decoder. -/
def main (args : List String) : IO UInt32 := do
  try
    let path ← match args with
      | [] => pure "STFSpec/Conformance/StateCommit/storage_decode_inputs.jsonl"
      | [path] => pure path
      | _ => throw (IO.userError "expected at most one input path")
    let source ← IO.FS.readFile path
    for line in source.splitOn "\n" do
      if !line.isEmpty then
        let row ← IO.ofExcept (Json.parse line)
        let id ← IO.ofExcept (row.getObjValAs? String "id")
        let hex ← IO.ofExcept (row.getObjValAs? String "raw_hex")
        let some raw := rawBytes hex | throw (IO.userError "invalid raw hex")
        let result ← match decodeStorageLeaf raw with
          | .ok v => pure (Json.mkObj [("ok", toJson v.toNat)])
          | .error (.malformed .leaf) =>
            pure (Json.mkObj [("error", toJson "WitnessError.malformed.leaf")])
          | .error _ => throw (IO.userError "unexpected witness error")
        (← IO.getStdout).putStrLn <| "{\"id\":" ++ (toJson id).compress ++
          ",\"raw_hex\":" ++ (toJson hex).compress ++ ",\"result\":" ++ result.compress ++ "}"
    pure 0
  catch e =>
    (← IO.getStderr).putStrLn e.toString
    pure 1
