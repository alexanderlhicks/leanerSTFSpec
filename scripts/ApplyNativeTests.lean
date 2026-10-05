/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Conformance.State.ApplyGuards

/-!
# Complete mathematical apply native observations

Library `EthConformance`: compare every complete raw/model/getter/retained-parent observation.
Run `lake exe apply-native-tests`; add `--dump` to emit every complete checked record.
Interpret with `lake env lean --run scripts/ApplyNativeTests.lean --dump`.
Spec guidance: `STFSpec/informal/modules/EthState.md`.
-/

/-- Validate complete observations; optionally emit them for interpreted/native equality. -/
def main (args : List String) : IO Unit := do
  let dump ← match args with
    | [] => pure false
    | ["--dump"] => pure true
    | _ => throw (IO.userError "usage: apply-native-tests [--dump]")
  for (pass, observation) in STFSpec.Conformance.ApplyGuards.rows do
    unless pass do
      throw (IO.userError "complete raw apply model mismatch")
    if dump then IO.println observation
  IO.println "complete mathematical apply observations PASS"
