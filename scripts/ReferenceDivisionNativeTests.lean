/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Field
import Lean

/-!
# Complete natural-reference division observations

Library `EthConformance`. The runtime TSV contains inputs only. Every input is
observed under three metadata choices using both the named operation and notation.
Spec guidance: `STFSpec/informal/modules/EthField.md` §§3–7.
-/

open STFSpec.Field Lean

private def emit (j : Json) : IO Unit := do
  (← IO.getStdout).putStrLn j.compress

private def natural (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw (IO.userError "invalid natural input")

private def observe (id context : String) (p rawA rawB : Nat) : IO Unit := do
  if hp : 1 < p then
    for metadata in [none, some 0, some (2 ^ 4096 + 17)] do
      letI : FieldModulus p := ⟨hp, metadata⟩
      let a : PrimeFieldRef p := PrimeFieldRef.ofNat rawA
      let b : PrimeFieldRef p := PrimeFieldRef.ofNat rawB
      let inverse := PrimeFieldRef.inv0 b
      let named := PrimeFieldRef.div a b
      let operator := a / b
      emit <| Json.mkObj [("id", toJson id), ("context", toJson context),
        ("p", toJson p), ("raw_a", toJson rawA), ("raw_b", toJson rawB),
        ("metadata", toJson metadata), ("canonical_a", toJson a.toNat),
        ("canonical_b", toJson b.toNat), ("inverse", toJson inverse.toNat),
        ("named", toJson named.toNat), ("operator", toJson operator.toNat),
        ("in_range", toJson (decide (named.toNat < p) && decide (operator.toNat < p)))]
  else throw (IO.userError "modulus must exceed one")

/-- Emit all actual observations from the input-only runtime catalogue. -/
def main (args : List String) : IO UInt32 := do
  try
    let path : String := match args with
      | [] => "STFSpec/Conformance/Field/reference_division_inputs.tsv"
      | [path] => path
      | _ => ""
    if path.isEmpty then throw (IO.userError "expected at most one input path")
    let lines := (← IO.FS.readFile path).splitOn "\n"
    let rows := lines.filter (fun line ↦ !line.isEmpty)
    -- Opaque fixed catalogue label shared with the differential; not a digest of any
    -- committed file. The differential pins the committed inputs and baseline by SHA-256.
    emit <| Json.mkObj [("schema", toJson "reference-division-v1"),
      ("catalog", toJson "19119c6a0f1960ee3fae319250af7ba1e399ceec40afe14bb0b48df29a5be9d2"),
      ("count", toJson (rows.length * 3))]
    for row in rows do
      match row.splitOn "\t" with
      | [id, context, p, a, b] => observe id context (← natural p) (← natural a) (← natural b)
      | _ => throw (IO.userError "invalid input row")
    emit <| Json.mkObj [("complete", toJson true), ("count", toJson (rows.length * 3))]
    pure 0
  catch e =>
    (← IO.getStderr).putStrLn e.toString
    pure 1
