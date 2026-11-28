/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Block access list pre-transaction read controls

Library `EthConformance`. The State facade clients check block overlay
precedence, the exact retained provider actions, and transaction independence.
Spec guidance: `STFSpec/informal/modules/EthState.md` §4.
-/

namespace STFSpec.Conformance.State.PreTxReadControls

open STFSpec.Base STFSpec.State

private theorem account_ignores_transaction {m : Type → Type} [Monad m] (t : TxState m)
    (a : Address) (r : TxRevertible) (o : TxObs) :
    preTxAccount { t with rev := r, obs := o } a = preTxAccount t a := rfl

private theorem storage_ignores_transaction {m : Type → Type} [Monad m] (t : TxState m)
    (a : Address) (k : Bytes32) (r : TxRevertible) (o : TxObs) :
    preTxStorage { t with rev := r, obs := o } a k = preTxStorage t a k := rfl

private def target := Address.ofNat 41
private def sibling := Address.ofNat 43
private def slot : Bytes32 := FixedBytes.ofNat 173
private def otherSlot : Bytes32 := FixedBytes.ofNat 89
private def emptyHash := Hash32.ofBytes32 (FixedBytes.ofNat 47)
private def accessHash := Hash32.ofBytes32 (FixedBytes.ofNat 53)
private def faultHash := Hash32.ofBytes32 (FixedBytes.ofNat (2 ^ 255 + 61))
private def consts : HashConsts := ⟨emptyHash, accessHash, emptyHash, accessHash⟩
private def maxWord := U256.ofNat (2 ^ 256 - 1)
private def coveredAccount : Account := ⟨2 ^ 80 + 67, maxWord, accessHash⟩
private def txAccount : Account := ⟨71, U256.ofNat 73, emptyHash⟩
private def accountError : WitnessError := .malformed (.node faultHash)
private def storageError : WitnessError := .unresolved faultHash

private inductive Event where
  | account (a : Address)
  | storage (a : Address) (k : Bytes32)
  | code
  | root
  deriving BEq

private abbrev Observing := StateT (List Event) Id

private def observe {α : Type} (event : Event) (value : α) : Observing α :=
  fun prior ↦ pure (value, prior ++ [event])

private def provider (account : Except WitnessError (Option Account))
    (word : Except WitnessError U256) : PreState Observing :=
  ⟨fun a ↦ observe (.account a) account, fun a k ↦ observe (.storage a k) word,
    fun _ ↦ observe .code (.error accountError), fun _ ↦ observe .root (.error storageError)⟩

private abbrev Slots := Std.ExtTreeMap Bytes32 U256

private def siblingSlot : Slots := (∅ : Slots).insert otherSlot (U256.ofNat 79)

private def entry (account : Except WitnessError (Option Account))
    (word : Except WitnessError U256) (blockAccount : Option (Option Account))
    (blockSlots : Option Slots) (blockClear : Bool) : TxState Observing :=
  let b := BlockState.new (provider account word) consts
  let b := { b with
    accountWrites := blockAccount.elim b.accountWrites (b.accountWrites.insert target)
    storageWrites := blockSlots.elim b.storageWrites (b.storageWrites.insert target)
    storageClears := if blockClear then b.storageClears.insert target else b.storageClears
    oldestAncestorOffset := some 83
    accountReads := b.accountReads.insert sibling
    storageReads := b.storageReads.insert (sibling, otherSlot) }
  let t := TxState.new b
  { t with
    rev := { t.rev with
      accountWrites := t.rev.accountWrites.insert target (some txAccount)
      storageWrites := t.rev.storageWrites.insert target (siblingSlot.insert slot (U256.ofNat 97))
      storageClears := t.rev.storageClears.insert target
      codeWrites := t.rev.codeWrites.insert accessHash (ByteArray.mk #[96, 0, 255])
      transient := t.rev.transient.insert (target, slot) (U256.ofNat 101) }
    obs := { t.obs with
      createdAccounts := t.obs.createdAccounts.insert target
      accountReads := t.obs.accountReads.insert sibling
      storageReads := t.obs.storageReads.insert (sibling, otherSlot)
      codeReads := t.obs.codeReads.insert accessHash } }

private def accountRun (t : TxState Observing) (events : List Event) :=
  Id.run <| (preTxAccount t target).run events

private def storageRun (t : TxState Observing) (events : List Event) :=
  Id.run <| (preTxStorage t target slot).run events

private def accountFields (a : Account) := (a.nonce, a.balance, a.codeHash)

private def accountMatches (run : Except StateError (Option Account) × List Event)
    (answer : Option Account) (events : List Event) : Bool :=
  match run with
  | (.ok account, observed) =>
    account.map accountFields == answer.map accountFields && observed == events
  | (.error _, _) => false

private def wordMatches (run : Except StateError U256 × List Event)
    (word : U256) (events : List Event) : Bool :=
  match run with
  | (.ok answer, observed) => answer == word && observed == events
  | (.error _, _) => false

#guard
  let t := entry (.error accountError) (.error storageError) (some none) none false
  accountMatches (accountRun t [.root]) none [.root]

#guard
  let input := entry (.error accountError) (.error storageError)
    (some (some coveredAccount)) none false
  let t := { input with rev.accountWrites := input.rev.accountWrites.insert target none }
  accountMatches (accountRun t [.code]) (some coveredAccount) [.code]

#guard
  let t := entry (.ok none) (.error storageError) none none false
  accountMatches (accountRun t [.storage sibling otherSlot]) none
    [.storage sibling otherSlot, .account target]

#guard
  let t := entry (.ok (some coveredAccount)) (.error storageError) none none false
  accountMatches (accountRun t []) (some coveredAccount) [.account target]

#guard
  let t := entry (.error accountError) (.error storageError) none none false
  match accountRun t [.code] with
  | (.error (.witness (.malformed (.node h))), events) =>
    h == faultHash && events == [.code, .account target]
  | _ => false

#guard
  let t := entry (.error accountError) (.error storageError) none
    (some (siblingSlot.insert slot U256.zero)) true
  wordMatches (storageRun t [.root]) U256.zero [.root]

#guard
  let t := entry (.error accountError) (.error storageError) none
    (some (siblingSlot.insert slot maxWord)) false
  wordMatches (storageRun t []) maxWord []

#guard
  let t := entry (.error accountError) (.error storageError) none (some siblingSlot) true
  wordMatches (storageRun t [.account sibling]) U256.zero [.account sibling]

#guard
  let t := entry (.error accountError) (.ok maxWord) none (some siblingSlot) false
  wordMatches (storageRun t [.root]) maxWord [.root, .storage target slot]

#guard
  let t := entry (.error accountError) (.ok U256.zero) none none false
  wordMatches (storageRun t []) U256.zero [.storage target slot]

#guard
  let t := entry (.error accountError) (.error storageError) none (some ∅) false
  match storageRun t [.account sibling] with
  | (.error (.witness (.unresolved h)), events) =>
    h == faultHash && events == [.account sibling, .storage target slot]
  | _ => false

#guard
  let t := entry (.ok none) (.ok maxWord) none none false
  let reads : Observing (Except StateError U256) := do
    let _ ← preTxAccount t target
    let _ ← preTxStorage t target slot
    let _ ← preTxAccount t target
    preTxStorage t target slot
  wordMatches (Id.run (reads.run [])) maxWord
    [.account target, .storage target slot, .account target, .storage target slot]

end STFSpec.Conformance.State.PreTxReadControls
