/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Conformance.Vm.Runner.BudgetGuards
import Lean

/-! Input-only complete raw-meter producer. Expected arithmetic lives in the independent
Python model, never in this executable. Guidance: `EthVmRunner` §§3/4/7. -/

open STFSpec.Vm.Core STFSpec.Vm.Runner Lean

private def nat (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw (IO.userError "invalid Nat input")

private def integer (s : String) : IO Int :=
  match s.toInt? with
  | some n => pure n
  | none => throw (IO.userError "invalid Int input")

private def meterJson (m : GasMeter) : Json := Json.mkObj [
  ("gasLeft", toJson m.gasLeft), ("stateGasLeft", toJson m.stateGasLeft),
  ("stateGasBaseline", toJson m.stateGasBaseline), ("refundCounter", toJson m.refundCounter),
  ("stateGasSpilled", toJson m.stateGasSpilled),
  ("stateGasCommittedSpill", toJson m.stateGasCommittedSpill)]

private def emit (line : String) : IO Unit := do
  match line.splitOn "\t" with
  | [id, e, r, b, q, s, c, n] =>
    let meter := GasMeter.mk (← nat e) (← nat r) (← nat b) (← integer q) (← nat s) (← nat c)
    let constant ← nat n
    let policy : BudgetPolicy := constBudget constant
    (← IO.getStdout).putStrLn (Json.mkObj [
      ("id", toJson id), ("meter", meterJson meter), ("constant", toJson constant),
      ("phi", toJson meter.phi), ("phiBudget", toJson (phiBudget meter)),
      ("constBudget", toJson (policy meter))]).compress
  | _ => throw (IO.userError "input row must contain eight TSV fields")

/-- Emit complete observations for a bounded input-only control file. -/
def main (args : List String) : IO UInt32 := do
  try
    match args with
    | [path] =>
      let raw ← IO.FS.readFile path
      if raw.utf8ByteSize > 4000000 then throw (IO.userError "control file too large")
      let rows := (raw.splitOn "\n").filter (fun row ↦ !row.isEmpty)
      if rows.length > 512 then throw (IO.userError "too many control rows")
      let out ← IO.getStdout
      out.putStrLn (Json.mkObj [("schema", toJson "budget-policy-v1"),
        ("count", toJson rows.length)]).compress
      for row in rows do emit row
      out.putStrLn (Json.mkObj [("end", toJson true), ("count", toJson rows.length)]).compress
      return 0
    | _ => throw (IO.userError "usage: budget-policy-native-tests INPUT.tsv")
  catch error =>
    (← IO.getStderr).putStrLn s!"FAIL {error}"
    return 1
