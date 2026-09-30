/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Conformance.Fixtures.Types
import Std.Data.TreeMap

/-!
# Internal fixture identity indexing

Deterministic order and explicit bounds for `EthConformance` tooling. This does
not implement the `core`/`ci` tier policies, whose membership/bound inputs remain open.
Spec guidance: `STFSpec/informal/modules/EthConformance.md`.
-/

namespace STFSpec.Conformance.Internal

private def identityCompare (a b : FixtureId) : Ordering :=
  (compare a.file b.file).then ((compare a.testId b.testId).then
    ((compare a.blockIndex b.blockIndex).then (compare a.infoHash b.infoHash)))

/-- Sort a fixture identity index and reject duplicate complete identities. -/
def sortedIndex (index : Array FixtureId) : Except FixtureError (Array FixtureId) := do
  let result := index.toList.mergeSort (fun a b => identityCompare a b != .gt) |>.toArray
  let mut previous : Option FixtureId := none
  for id in result do
    if previous == some id then throw (.duplicateIdentity id)
    previous := some id
  return result

private def directory (file : String) : String :=
  String.intercalate "/" (file.splitOn "/" |>.dropLast)

/-- Internal bounded index: include guest-specific EIP-8025 identities and the first
`bound` identities in each file's containing directory, after sorting. The caller supplies
`bound`; this helper does not choose a CI time budget or implement `selectSlice`. -/
def boundedIndex (bound : Nat) (index : Array FixtureId) :
    Except FixtureError (Array FixtureId) := do
  let index ← sortedIndex index
  let mut counts : Std.TreeMap String Nat := {}
  let mut selected := #[]
  for id in index do
    let dir := directory id.file
    let count := counts.getD dir 0
    counts := counts.insert dir (count + 1)
    if (id.file.splitOn "/").contains "eip8025_optional_proofs" || count < bound then
      selected := selected.push id
  return selected

end STFSpec.Conformance.Internal
