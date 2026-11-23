/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Ancestor access controls

Library `EthConformance`. Check the maximum offset, absence versus zero,
retained transaction sentinels and provider isolation through the State facade.
Spec guidance: `STFSpec/informal/modules/EthState.md` R27 and §§3/4/7.
-/

namespace STFSpec.Conformance.State.AncestorAccessChecks

open STFSpec.Base STFSpec.State

private abbrev Trace := StateT (List Nat) Id

private def providerCalled {α : Type} : Trace (Except WitnessError α) := do
  modify (1 :: ·)
  let hash := Hash32.ofBytes32 (FixedBytes.ofNat 17)
  pure (.error (.missing (.node hash)))

private structure Recipe where
  initial : Option Nat
  offsets : List Nat

private def recipes : List Recipe :=
  [⟨none, [0, 1, 1, 0, 256, 255, 257]⟩,
   ⟨none, []⟩,
   ⟨some 0, [0, 0, 1]⟩,
   ⟨some 256, [1, 256, 255, 511, 256]⟩,
   ⟨some (2 ^ 180), [2 ^ 180 - 1, 0, 2 ^ 180, 2 ^ 256, 2 ^ 256 - 1]⟩]

private def initial (oldest : Option Nat) : TxState Trace :=
  let provider : PreState Trace := ⟨fun _ ↦ providerCalled, fun _ _ ↦ providerCalled,
    fun _ ↦ providerCalled, fun _ ↦ providerCalled⟩
  let hash := Hash32.ofBytes32 (FixedBytes.ofNat 17)
  let a := Address.ofNat 17
  let k : Bytes32 := FixedBytes.ofNat 23
  let rev : TxRevertible := ⟨∅, WriteOrder.empty, ∅, WriteOrder.empty, ∅, ∅, ∅,
    (∅ : Std.ExtTreeMap (Address × Bytes32) U256).insert (a, k) (U256.ofNat 31)⟩
  let obs : TxObs := ⟨(∅ : Std.HashSet Address).insert a, ∅, ∅, ∅⟩
  let block := BlockState.new provider ⟨hash, hash, hash, hash⟩
  let reads := (∅ : Std.HashSet Address).insert (Address.ofNat 37)
  let ready := { block with oldestAncestorOffset := oldest, accountReads := reads }
  ⟨ready, rev, obs⟩

private def observe (recipe : Recipe) : Option (List (Option Nat)) := do
  let mut t := initial recipe.initial
  let mut observations := [t.block.oldestAncestorOffset]
  for offset in recipe.offsets do
    let (result, calls) := (((trackAncestorAccess offset).run t).run).run []
    let .ok ((), updated) := result | none
    if !calls.isEmpty ||
        updated.block.accountReads.toList != t.block.accountReads.toList ||
        updated.rev.transient.toList != t.rev.transient.toList ||
        updated.obs.accountReads.toList != t.obs.accountReads.toList then
      none
    else
      t := updated
      observations := t.block.oldestAncestorOffset :: observations
  return observations.reverse


#guard recipes.map observe ==
  [some [none, some 0, some 1, some 1, some 1, some 256, some 256, some 257],
   some [none],
   some [some 0, some 0, some 0, some 1],
   some [some 256, some 256, some 256, some 256, some 511, some 511],
   some [some (2 ^ 180), some (2 ^ 180), some (2 ^ 180), some (2 ^ 180),
     some (2 ^ 256), some (2 ^ 256)]]

end STFSpec.Conformance.State.AncestorAccessChecks
