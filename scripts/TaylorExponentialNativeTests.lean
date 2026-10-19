/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.TaylorExponential
import Lean

/-!
# Complete Taylor exponential observations

One frozen positive-denominator input schedule, emitted by the same source in
interpreted and compiled modes. Only the public operation computes results.
No expected-value model, source helper, checksum or hidden price is used.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §3.
-/

open STFSpec.Base Lean

private def cases : List (String × Nat × Nat × Nat) := [
  ("T01", 0, 7, 3),
  ("T02", 5, 0, 3),
  ("T03", 1, 0, 1),
  ("T04", 1, 1, 1),
  ("T05", 1, 2, 1),
  ("T06", 2, 1, 2),
  ("T07", 1, 3, 2),
  ("T08", 3, 2, 3),
  ("T09", 0, 0, 1),
  ("T10", 0, 1, 11684671),
  ("T11", 1, 1, 2),
  ("T12", 1, 2, 3),
  ("T13", 7, 1, 3),
  ("T14", 9, 4, 3),
  ("T15", 1, 3, 1),
  ("T16", 2, 5, 2),
  ("T17", 1, 8, 3),
  ("T18", 18446744073709551615, 0, 1),
  ("T19", 18446744073709551616, 1, 18446744073709551617),
  ("T20", 340282366920938463463374607431768211456, 1, 340282366920938463463374607431768211457),
  ("T21",
    115792089237316195423570985008687907853269984665640564039457584007913129639935,
    1,
    115792089237316195423570985008687907853269984665640564039457584007913129639936),
  ("T22", 1, 0, 11684671),
  ("T23", 1, 1, 11684671),
  ("T24", 1, 11684670, 11684671),
  ("T25", 1, 11684671, 11684671),
  ("T26", 1, 11684672, 11684671),
  ("T27", 1, 23369342, 11684671),
  ("T28", 7, 23369343, 11684671)]

private def inputJson (factor numerator denominator : Nat) : Json :=
  Json.mkObj [("factor", toJson factor), ("numerator", toJson numerator),
    ("denominator", toJson denominator)]

private def inputClasses : Json :=
  Json.mkObj [("factor", toJson "Lean.Nat"), ("numerator", toJson "Lean.Nat"),
    ("denominator", toJson "Lean.Nat")]

private def emit (id : String) (factor numerator denominator : Nat)
    (h : 0 < denominator) : IO Unit := do
  let input := inputJson factor numerator denominator
  let result := taylorExponential factor numerator denominator h
  let frame := Json.mkObj [
    ("schema", toJson "taylor-target-v1"), ("id", toJson id),
    ("domain", toJson "typed-target"), ("operation", toJson "taylor_exponential"),
    ("input", input),
    ("output", Json.mkObj [("kind", toJson "success"), ("result", toJson result),
      ("after", input)]),
    ("classes", Json.mkObj [("input", inputClasses), ("output", toJson "Lean.Nat"),
      ("after", inputClasses)])]
  (← IO.getStdout).putStrLn frame.compress

/-- Isolated whole-frame producer, outside the public library API. -/
def main : IO UInt32 := do
  try
    for (id, factor, numerator, denominator) in cases do
      if h : 0 < denominator then
        emit id factor numerator denominator h
      else
        throw (IO.userError s!"nonpositive denominator in {id}")
    return 0
  catch error =>
    (← IO.getStderr).putStrLn s!"FAIL {error}"
    return 1
