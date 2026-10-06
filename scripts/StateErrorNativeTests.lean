/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Conformance.State.StateErrorGuards

/-!
# Native complete nominal state-error values

Library `EthConformance`: shared observers compare all tags and complete supplied bytes
against independent expectations. No production equality instance or error adapter is installed.
Run `lake exe state-error-native-tests`; add `--dump` to emit every complete checked record.
Interpret with `lake env lean --run scripts/StateErrorNativeTests.lean --dump`.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/5.
-/

open STFSpec.Conformance.State.StateErrorGuards

/-- Validate every complete nominal observation; optionally emit actual and expected values. -/
def main (args : List String) : IO Unit := do
  let dump ← match args with
    | [] => pure false
    | ["--dump"] => pure true
    | _ => throw (IO.userError "usage: state-error-native-tests [--dump]")
  unless cases.length == 340 do throw (IO.userError "state-error case count mismatch")
  for (label, error, expected) in cases do
    let actual := observe witnessValue error
    unless actual == expected do throw (IO.userError s!"{label}: complete state-error mismatch")
    if dump then
      IO.println s!"{label}:actual:{repr actual}"
      IO.println s!"{label}:expected:{repr expected}"
  unless dump do IO.println "complete nominal state-error observations PASS"
