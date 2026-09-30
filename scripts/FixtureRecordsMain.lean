/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Conformance.Fixtures.Extract
import Lean.Data.Json.Printer

/-!
# Fixture extraction driver

Internal `fixture-records` driver: read `[archiveRelativeName, localPath]` commands from
stdin, or append `"content"` for exact identity/byte replies. Each reply is one line:
`ok N`, `{"count": N, "records": [...]}`, or diagnostic `error ...`. Diagnostic text
is escaped into one physical line and has no stable schema. EOF ends the batch;
any error makes the exit status nonzero.
Authentication is the host tool's responsibility. No guest is executed.
Spec guidance: `STFSpec/informal/modules/EthConformance.md`.
-/

private def hexString (bytes : ByteArray) : String := Id.run do
  let mut text := "0x"
  for byte in bytes do
    for n in [byte.toNat / 16, byte.toNat % 16] do
      text := text.push (Char.ofNat (if n < 10 then 48 + n else 87 + n))
  return text

private def recordJson (record : STFSpec.Conformance.GuestRecord) : Lean.Json :=
  Lean.Json.mkObj [("id", Lean.Json.mkObj [("file", .str record.id.file),
    ("testId", .str record.id.testId),
    ("blockIndex", .num (Lean.JsonNumber.fromNat record.id.blockIndex)),
    ("infoHash", .str record.id.infoHash)]), ("input", .str (hexString record.input)),
    ("expected", .str (hexString record.expected))]

private def runCommand (line : String) : IO String := do
  match Lean.Json.parse line >>= Lean.Json.getArr? with
  | .error message => return "error command: " ++ reprStr message
  | .ok command =>
    match command[0]?.bind (fun x ↦ x.getStr?.toOption),
        command[1]?.bind (fun x ↦ x.getStr?.toOption) with
    | some file, some path =>
      let content := command.size == 3 &&
        command[2]?.bind (fun x ↦ x.getStr?.toOption) == some "content"
      if command.size != 2 && !content then return "error command arity"
      let text ← IO.FS.readFile path
      match STFSpec.Conformance.Internal.parseGuestRecords file text with
      | .error error => return "error " ++ reprStr (reprStr error)
      | .ok records =>
        if content then
          return (Lean.Json.mkObj [("count", .num (Lean.JsonNumber.fromNat records.size)),
            ("records", .arr (records.map recordJson))]).compress
        return s!"ok {records.size}"
    | _, _ => return "error command strings"

/-- Internal batch entry point, used after host-side archive authentication. -/
def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut failed := false
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let result ← try runCommand line catch error => pure ("error IO: " ++ reprStr error.toString)
    if result.startsWith "error" then failed := true
    stdout.putStrLn result
    stdout.flush
  return if failed then 1 else 0
