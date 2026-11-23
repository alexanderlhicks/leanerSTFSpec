/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Account creation marker controls

Library `EthConformance`. Use the public State facade to check complete marker sets
and the raw transaction frame. Spec guidance: `STFSpec/informal/modules/EthState.md` R22.
-/

namespace STFSpec.Conformance.State.MarkAccountCreatedGuards

open STFSpec.State STFSpec.Base

private def exactType : {m : Type → Type} → [Monad m] →
    Address → STFSpec.State.StateM m Unit := @markAccountCreated

private theorem run_and_retain {m : Type → Type} [Monad m] (t : TxState m) (a : Address) :
    ((markAccountCreated a).run t).run =
      pure (.ok ((), { t with obs.createdAccounts := t.obs.createdAccounts.insert a })) := rfl

private abbrev Effects := StateT (List String) Id

private def recordEffect (name : String) (α : Type) : Effects (Except WitnessError α) := do
  modify (· ++ [name])
  pure (.error (.missing .leaf))

private def provider : PreState Effects where
  getAccount? := fun _ ↦ recordEffect "account" _
  getStorage := fun _ _ ↦ recordEffect "storage" _
  getCode := fun _ ↦ recordEffect "code" _
  stateRoot := fun _ ↦ recordEffect "root" _

private def seed (initial : List Nat) : TxState Effects :=
  let addr := Address.ofNat 17
  let slot : Bytes32 := FixedBytes.ofNat (2 ^ 255 + 3)
  let hash := Hash32.ofBytes32 slot
  let block := { BlockState.new provider HashConsts.literals with
    accountWrites := (∅ : Std.ExtTreeMap Address (Option Account)).insert addr none
    oldestAncestorOffset := some (2 ^ 180) }
  let rev : TxRevertible :=
    ⟨∅, WriteOrder.empty.record addr, ∅, WriteOrder.empty, ∅, ∅, ∅,
      (∅ : Std.ExtTreeMap (Address × Bytes32) U256).insert (addr, slot) (U256.ofNat 19)⟩
  let obs : TxObs :=
    ⟨{addr}, {(addr, slot)}, {hash}, initial.foldl (fun s n ↦ s.insert (Address.ofNat n)) ∅⟩
  ⟨block, rev, obs⟩

private def observeMarks (initial targets : List Nat) : Option (List (List Nat)) := do
  let mut t := seed initial
  let mut observations := []
  for target in targets do
    match (((markAccountCreated (Address.ofNat target)).run t).run).run ["prior"] with
    | (.ok ((), next), ["prior"]) =>
      let members := next.obs.createdAccounts.toList.map (·.toNat)
      observations := observations ++ [members.mergeSort (· ≤ ·)]
      t := next
    | _ => none
  return observations

private def high : Nat := 2 ^ 159 + 5
private def maximum : Nat := 2 ^ 160 - 1

#guard observeMarks [] [0] == some [[0]]
#guard observeMarks [5] [5, 5, 5] == some [[5], [5], [5]]
#guard observeMarks [5] [high, 5, high] == some [[5, high], [5, high], [5, high]]
#guard observeMarks [3, high] [0, maximum, 3, 17] ==
  some [[0, 3, high], [0, 3, high, maximum], [0, 3, high, maximum], [0, 3, 17, high, maximum]]

end STFSpec.Conformance.State.MarkAccountCreatedGuards
