/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Current account emptiness and liveness controls

Library `EthConformance`. Check the literal actions, exact returned state and
error, and agreement with the mathematical transaction view.
Spec guidance is in `STFSpec/informal/modules/EthState.md` §§3/4/7.1.
-/

namespace STFSpec.Conformance.State.AccountEmptinessControls

open STFSpec.State STFSpec.Base

private def emptyResult (consts : HashConsts) : Option Account → Bool
  | none => false
  | some account => decide (account = emptyAccount consts)

private def aliveResult (consts : HashConsts) : Option Account → Bool
  | none => false
  | some account => decide (account ≠ emptyAccount consts)

private theorem empty_action {m : Type → Type} [Monad m] (a : Address) (t : TxState m) :
    ((accountExistsAndIsEmpty a).run t).run = (do
      match ← ((getAccountOptional a).run t).run with
      | .error error => pure (.error error)
      | .ok (none, next) => pure (.ok (false, next))
      | .ok (some account, next) =>
        pure (.ok (decide (account = emptyAccount next.block.consts), next))) :=
  rfl

private theorem alive_action {m : Type → Type} [Monad m] (a : Address) (t : TxState m) :
    ((isAccountAlive a).run t).run = (do
      match ← ((getAccountOptional a).run t).run with
      | .error error => pure (.error error)
      | .ok (none, next) => pure (.ok (false, next))
      | .ok (some account, next) =>
        pure (.ok (decide (account ≠ emptyAccount next.block.consts), next))) :=
  rfl

private theorem exact_error (a : Address) (t : TxState Id) (error : StateError)
    (h : ((getAccountOptional a).run t).run = .error error) :
    ((accountExistsAndIsEmpty a).run t).run = .error error ∧
      ((isAccountAlive a).run t).run = .error error := by
  rw [empty_action, alive_action, h]
  exact ⟨rfl, rfl⟩

private theorem exact_success (a : Address) (t next : TxState Id) (account : Option Account)
    (h : ((getAccountOptional a).run t).run = .ok (account, next)) :
    ((accountExistsAndIsEmpty a).run t).run = .ok (emptyResult t.block.consts account, next) ∧
      ((isAccountAlive a).run t).run = .ok (aliveResult t.block.consts account, next) := by
  have blockFrame := (getAccountOptional_frames t a account next h).1
  rw [empty_action, alive_action, h]
  cases account with
  | none => exact ⟨rfl, rfl⟩
  | some value =>
    change Except.ok (decide (value = emptyAccount next.block.consts), next) = _ ∧
      Except.ok (decide (value ≠ emptyAccount next.block.consts), next) = _
    rw [blockFrame]
    exact ⟨rfl, rfl⟩

private theorem partition_presence (consts : HashConsts) (account : Option Account) :
    (emptyResult consts account || aliveResult consts account) = account.isSome ∧
      (emptyResult consts account && aliveResult consts account) = false := by
  cases account with
  | none => exact ⟨rfl, rfl⟩
  | some value =>
    by_cases h : value = emptyAccount consts <;> simp [emptyResult, aliveResult, h]

private theorem model (a : Address) (t next : TxState Id) (initial : MathState)
    (account : Option Account) (wf : MathState.WF initial)
    (models : ModelsLookups t.block.consts t.block.preState initial)
    (h : ((getAccountOptional a).run t).run = .ok (account, next)) :
    ((accountExistsAndIsEmpty a).run t).run =
      .ok (emptyResult t.block.consts ((t.view initial).account? a), next) ∧
    ((isAccountAlive a).run t).run =
      .ok (aliveResult t.block.consts ((t.view initial).account? a), next) := by
  rw [← getAccountOptional_model t initial wf models a account next h]
  exact exact_success a t next account h

private def hash (value : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat value)

private def outcomes (consts : HashConsts) (account : Option Account) : Option (Bool × Bool) := do
  let a := Address.ofNat 19
  let provider : PreState Id :=
    ⟨fun _ ↦ .error (.missing .leaf), fun _ _ ↦ .error (.missing .leaf),
      fun _ ↦ .error (.missing .leaf), fun _ ↦ .error (.missing .leaf)⟩
  let block := BlockState.new provider consts
  let writes := (∅ : Std.ExtTreeMap Address (Option Account)).insert a account
  let rev : TxRevertible := ⟨writes, WriteOrder.empty, ∅, WriteOrder.empty, ∅, ∅, ∅, ∅⟩
  let t : TxState Id := ⟨block, rev, ⟨∅, ∅, ∅, ∅⟩⟩
  let (empty, _) ← (((accountExistsAndIsEmpty a).run t).run : Except StateError _).toOption
  let (alive, _) ← (((isAccountAlive a).run t).run : Except StateError _).toOption
  return (empty, alive)

#guard
  let consts : HashConsts := ⟨hash 30, hash 31, hash 32, hash 33⟩
  let account : Account := ⟨0, U256.zero, hash 30⟩
  [none, some account,
    some { account with nonce := 2 ^ 143 + 9 },
    some { account with balance := U256.ofNat (2 ^ 256 - 1) },
    some { account with codeHash := hash (2 ^ 255 + 30) },
    some { account with codeHash := hash 31 }].map (outcomes consts) ==
  [some (false, false), some (true, false), some (false, true),
    some (false, true), some (false, true), some (false, true)]

end STFSpec.Conformance.State.AccountEmptinessControls
