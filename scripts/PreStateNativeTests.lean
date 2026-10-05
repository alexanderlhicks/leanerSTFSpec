/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Conformance.State.PreStateGuards

/-!
# Native complete pre-state callback values

Library `EthConformance`: compare every complete callback input/result with an
independent expected value. These are raw carrier tests, not backend or Protocol execution.
Run `lake exe pre-state-native-tests`; add `--dump` to emit every complete checked record.
Interpret with `lake env lean --run scripts/PreStateNativeTests.lean --dump`.
Spec guidance: `STFSpec/informal/modules/EthState.md`.
-/

open STFSpec.Conformance.State.PreStateGuards

/-- Validate every complete callback family; optionally emit the actual and expected values. -/
def main (args : List String) : IO Unit := do
  let dump ← match args with
    | [] => pure false
    | ["--dump"] => pure true
    | _ => throw (IO.userError "usage: pre-state-native-tests [--dump]")
  unless nominal do throw (IO.userError "nominal payload mismatch")
  unless cases.length == 126 do throw (IO.userError "expected 126 complete callback families")
  for (label, actual, expected) in cases do
    unless equal actual expected do throw (IO.userError s!"{label}: complete callback mismatch")
    if dump then
      IO.println s!"{label}:{render actual}"
      IO.println s!"{label}:expected:{render expected}"
  unless dump do IO.println "complete pre-state callback observations PASS"
