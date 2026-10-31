/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Precompiles
import Lean

/-!
# Complete interpreted and compiled KZG helper observations

Library `EthConformance`. Read the single canonical frozen input catalog and emit
every input/result byte. The external strict reader binds exact IDs and all bytes.
Spec guidance: `STFSpec/informal/modules/EthPrecompiles.md` §§3/4/7.
-/

open STFSpec.Precompiles.Kzg Lean

private def digit (n : Nat) : Char := Char.ofNat (if n < 10 then 48 + n else 87 + n)
private def hex (data : ByteArray) : String :=
  String.ofList (data.data.toList.flatMap fun b ↦ [digit (b.toNat / 16), digit (b.toNat % 16)])
private def nibble (c : Char) : Except String Nat :=
  if '0' ≤ c ∧ c ≤ '9' then .ok (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then .ok (c.toNat - 87)
  else .error "noncanonical input hex"
private def unhex : List Char → Except String (List UInt8)
  | [] => .ok []
  | a :: b :: rest => do
    let x ← nibble a
    let y ← nibble b
    return UInt8.ofNat (16 * x + y) :: (← unhex rest)
  | [_] => .error "odd input hex"
private def emit (value : Json) : IO Unit := do (← IO.getStdout).putStrLn value.compress

/-- Emit all frozen raw commitments and every actual versioned-hash byte. -/
def main : IO Unit := do
  let text ← IO.FS.readFile
    "STFSpec/Conformance/Precompiles/kzg-versioned-hash-cases.json"
  let catalog ← IO.ofExcept (Json.parse text)
  let cases ← IO.ofExcept ((← IO.ofExcept (catalog.getObjVal? "cases")).getArr?)
  if cases.size != 926 then throw (IO.userError "frozen case count")
  emit (Json.mkObj [("schema", toJson "kzg-versioned-hash-v1"),
    ("count", toJson cases.size)])
  for row in cases do
    let id ← IO.ofExcept (row.getObjValAs? String "id")
    let text ← IO.ofExcept (row.getObjValAs? String "hex")
    let data := (← IO.ofExcept (unhex text.toList)).toByteArray
    emit (Json.mkObj [("id", toJson id), ("input_hex", toJson (hex data)),
      ("length", toJson data.size),
      ("actual_hex", toJson (hex (commitmentToVersionedHash data).toBytes.toByteArray))])
  emit (Json.mkObj [("end", toJson true), ("count", toJson cases.size)])
