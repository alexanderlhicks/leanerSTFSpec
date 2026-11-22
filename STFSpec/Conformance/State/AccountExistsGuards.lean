/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Current account existence controls

Library `EthConformance`. Check both overlays, presence and failure at the
provider, repeated reads, and provider call addresses.
Spec guidance: `STFSpec/informal/modules/EthState.md` §4.
-/

namespace STFSpec.Conformance.State.AccountExistsGuards

open STFSpec.Base STFSpec.State

private def exact_type : {m : Type → Type} → [Monad m] →
    Address → STFSpec.State.StateM m Bool := @accountExists

private def queried : Address := Address.ofNat (2 ^ 159 + 0x42)
private def other : Address := Address.ofNat 0x42
private def slot : Bytes32 :=
  FixedBytes.ofNat 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f
private def empty : Account := emptyAccount HashConsts.literals
private def nonempty : Account := ⟨3, U256.ofNat 17, empty.codeHash⟩
private def missingNode : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat (2 ^ 255 + 0x42))

private inductive Outcome where
  | exists
  | absent
  | failure
  deriving DecidableEq

private structure Case where
  label : String
  txAccount : Option (Option Account)
  blockAccount : Option (Option Account)
  supplied : Except WitnessError (Option Account)
  expected : Outcome
  calls : Nat

private def failed : Except WitnessError (Option Account) := .error (.missing (.node missingNode))

private def cases : List Case :=
  [⟨"tx-tombstone", some none, some (some nonempty), failed, .absent, 0⟩,
   ⟨"tx-empty", some (some empty), some none, failed, .exists, 0⟩,
   ⟨"tx-nonempty", some (some nonempty), none, failed, .exists, 0⟩,
   ⟨"block-tombstone", none, some none, failed, .absent, 0⟩,
   ⟨"block-empty", none, some (some empty), failed, .exists, 0⟩,
   ⟨"block-nonempty", none, some (some nonempty), failed, .exists, 0⟩,
   ⟨"provider-missing", none, none, .ok none, .absent, 1⟩,
   ⟨"provider-empty", none, none, .ok (some empty), .exists, 1⟩,
   ⟨"provider-nonempty", none, none, .ok (some nonempty), .exists, 1⟩,
   ⟨"provider-error", none, none, failed, .failure, 1⟩]

private abbrev Trace := _root_.StateM (List Address)

private def provider (supplied : Except WitnessError (Option Account)) : PreState Trace where
  getAccount? a := do
    modify (· ++ [a])
    pure supplied
  getStorage _ _ := pure (.error (.malformed .leaf))
  getCode _ := pure (.error (.malformed .leaf))
  stateRoot _ := pure (.error (.malformed .leaf))

private def writes (entry : Option (Option Account)) (nearby : Account) :
    Std.ExtTreeMap Address (Option Account) :=
  let initial := (∅ : Std.ExtTreeMap Address (Option Account)).insert other (some nearby)
  match entry with
  | none => initial
  | some account => initial.insert queried account

private def initial (test : Case) : TxState Trace :=
  let block := BlockState.new (provider test.supplied) HashConsts.literals
  { block := { block with
      accountWrites := writes test.blockAccount empty
      storageClears := block.storageClears.insert queried }
    rev := ⟨writes test.txAccount nonempty, WriteOrder.empty, ∅, WriteOrder.empty, ∅, ∅, ∅,
      (∅ : Std.ExtTreeMap (Address × Bytes32) U256).insert (queried, slot) (U256.ofNat 9)⟩
    obs := ⟨(∅ : Std.HashSet Address).insert other,
      (∅ : Std.HashSet (Address × Bytes32)).insert (other, slot), ∅, ∅⟩ }

private def observe (before : TxState Trace) :
    Except StateError (Bool × TxState Trace) → Option Outcome × TxState Trace
  | .ok (present, next) =>
    let expectedReads := next.obs.accountReads.size == 2 &&
      next.obs.accountReads.contains queried && next.obs.accountReads.contains other
    let retained := decide (next.obs.storageReads.toList = before.obs.storageReads.toList ∧
      next.rev.accountWrites.toList = before.rev.accountWrites.toList ∧
      next.rev.transient.toList = before.rev.transient.toList ∧
      next.block.accountWrites.toList = before.block.accountWrites.toList ∧
      next.block.storageClears.toList = before.block.storageClears.toList)
    if expectedReads && retained then (some (if present then .exists else .absent), next)
    else (none, next)
  | .error (.witness (.missing (.node h))) =>
    (if h == missingNode then some .failure else none, before)
  | .error _ => (none, before)

private def observations (test : Case) : Option Outcome × Option Outcome × List Address × List Address :=
  let before := initial test
  let (first, firstCalls) := (((accountExists queried).run before).run).run []
  let (firstOutcome, next) := observe before first
  let (second, secondCalls) := (((accountExists queried).run next).run).run []
  (firstOutcome, (observe before second).1, firstCalls, secondCalls)

private def passes (test : Case) : Bool :=
  let calls := List.replicate test.calls queried
  decide (observations test = (some test.expected, some test.expected, calls, calls))

#guard cases.all passes

end STFSpec.Conformance.State.AccountExistsGuards
