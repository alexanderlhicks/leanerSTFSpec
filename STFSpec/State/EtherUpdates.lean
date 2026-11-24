/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.U256Arithmetic
import STFSpec.State.ModifyState

/-!
# Ether transfers and credits

Library `EthState`. Spec guidance `STFSpec/informal/modules/EthState.md` R19.
-/

namespace STFSpec.State
open Base

private def debit (amount : U256) (account : Account) : Except StateError Account :=
  match account.balance.checkedSub amount with
  | some balance => .ok { account with balance }
  | none => .error .balanceUnderflow

private def credit (amount : U256) (account : Account) : Except StateError Account :=
  match account.balance.checkedAdd amount with
  | some balance => .ok { account with balance }
  | none => .error .balanceOverflow

/-- Debit the sender through `modifyState`, then credit the recipient through
the same operation. Implements EELS
`src/ethereum/forks/amsterdam/state_tracker.py:616–647`. -/
def moveEther {m : Type → Type} [Monad m] (sender recipient : Address)
    (amount : U256) : StateM m Unit := do
  modifyState sender (debit amount)
  modifyState recipient (credit amount)

/-- Credit newly created Ether through `modifyState`. Implements EELS
`src/ethereum/forks/amsterdam/state_tracker.py:650–670`. -/
def createEther {m : Type → Type} [Monad m] (recipient : Address)
    (amount : U256) : StateM m Unit :=
  modifyState recipient (credit amount)

private theorem debit_short (account : Account) (amount : U256)
    (short : account.balance.toNat < amount.toNat) :
    debit amount account = .error .balanceUnderflow := by
  rw [debit, (U256.checkedSub_eq_none_iff _ _).2 short]

private theorem debit_exact (account : Account) (amount balance : U256)
    (enough : amount.toNat ≤ account.balance.toNat)
    (exactBalance : account.balance.toNat - amount.toNat = balance.toNat) :
    debit amount account = .ok { account with balance } := by
  rw [debit, (U256.checkedSub_eq_some_iff _ _ _).2 ⟨enough, exactBalance.symm⟩]

private theorem credit_overflow (account : Account) (amount : U256)
    (overflows : 2^256 ≤ account.balance.toNat + amount.toNat) :
    credit amount account = .error .balanceOverflow := by
  rw [credit, (U256.checkedAdd_eq_none_iff _ _).2 overflows]

private theorem credit_exact (account : Account) (amount balance : U256)
    (exactBalance : account.balance.toNat + amount.toNat = balance.toNat) :
    credit amount account = .ok { account with balance } := by
  have fits : account.balance.toNat + amount.toNat < 2^256 := by
    rw [exactBalance]
    exact U256.toNat_lt balance
  rw [credit, (U256.checkedAdd_eq_some_iff _ _ _).2 ⟨fits, exactBalance.symm⟩]

private theorem move_run {m : Type → Type} [Monad m] (t : TxState m)
    (sender recipient : Address) (amount : U256) :
    ((moveEther sender recipient amount).run t).run =
      (((modifyState sender (debit amount)).run t).run >>= ExceptT.bindCont
        (fun pair : Unit × TxState m ↦
          match pair with
          | (_, afterDebit) => (modifyState recipient (credit amount)).run afterDebit)) :=
  rfl

private theorem move_debit_error (t : TxState Id) (sender recipient : Address)
    (amount : U256) (error : StateError)
    (failed : ((modifyState sender (debit amount)).run t).run = .error error) :
    ((moveEther sender recipient amount).run t).run = .error error := by
  rw [move_run, failed]
  rfl

private theorem move_after_debit (t afterDebit : TxState Id) (sender recipient : Address)
    (amount : U256) (paid : ((modifyState sender (debit amount)).run t).run = .ok ((), afterDebit)) :
    ((moveEther sender recipient amount).run t).run =
      ((modifyState recipient (credit amount)).run afterDebit).run := by
  rw [move_run, paid]
  rfl

private theorem create_run {m : Type → Type} [Monad m] (t : TxState m)
    (recipient : Address) (amount : U256) :
    ((createEther recipient amount).run t).run =
      ((modifyState recipient (credit amount)).run t).run :=
  rfl

end STFSpec.State
