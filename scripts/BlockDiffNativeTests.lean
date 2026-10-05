/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Conformance.State.BlockDiffGuards

/-!
# Native complete raw BlockDiff values

Compiled finite association-list oracle, seven-field sensitivity and retained
parent/sibling observations. Every emitted value is complete, including bytes,
unbounded numbers, optional deletion tags and every metadata occurrence.
Library `EthConformance`: complete-value regression checks for EthState.
Spec guidance: `STFSpec/informal/modules/EthState.md`.
Run `lake exe block-diff-native-tests`; add `--dump` to retain complete observations.
Interpret with `lake env lean --run scripts/BlockDiffNativeTests.lean --dump`.
-/

open STFSpec.Base STFSpec.State STFSpec.Conformance.State.BlockDiffGuards

/-- Check complete parent/sibling values; optionally print every checked field. -/
def checkModel (dump : Bool) (label : String) (m : Model) : IO Unit := do
  let parent := build m
  let left := {parent with accountOrder := parent.accountOrder.reverse}
  let right := {parent with storageSlotOrder :=
    (parent.storageSlotOrder.insert (Address.ofNat 123)
      [FixedBytes.ofNat 123, FixedBytes.ofNat 123])}
  let leftWant := expected {m with accountOrder := m.accountOrder.reverse}
  let rightWant := expected {m with slotOrder := m.slotOrder ++
    [(Address.ofNat 123, [FixedBytes.ofNat 123, FixedBytes.ofNat 123])]}
  let want := expected m
  let actual := observe parent
  unless actual == want do throw (IO.userError s!"{label}: complete oracle mismatch")
  unless observe (build (permuted m)) == want do
    throw (IO.userError s!"{label}: insertion-order mismatch")
  unless observe left == leftWant && observe right == rightWant do
    throw (IO.userError s!"{label}: retained value mismatch")
  if dump then
    IO.println s!"{label}:parent:{reprStr actual}"
    IO.println s!"{label}:left:{reprStr (observe left)}"
    IO.println s!"{label}:right:{reprStr (observe right)}"

/-- Native complete-observation runner, with independently varied raw fields. -/
def main (args : List String) : IO Unit := do
  let dump ← match args with
    | [] => pure false
    | ["--dump"] => pure true
    | _ => throw (IO.userError "usage: block-diff-native-tests [--dump]")
  unless guards do throw (IO.userError "seven-field guards failed")
  for (m, i) in variations.zipIdx do checkModel dump s!"variation-{i}" m
  for i in List.range 4 do checkModel dump s!"indexed-{i}" (indexedModel i)
  let count := variations.length + 4
  IO.println s!"BlockDiff complete oracle and retained values PASS ({count} models)"
