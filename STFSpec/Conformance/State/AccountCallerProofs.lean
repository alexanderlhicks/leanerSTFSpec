/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.Account

/-!
# Account public-law clients

Library `EthConformance`: symbolic clients of the public Account value laws.
Spec guidance: `STFSpec/informal/modules/EthState.md`.
-/

namespace STFSpec.Conformance.State.AccountCallerProofs

open STFSpec.Base STFSpec.State

/-- Arbitrary constructor fields are retained, including all nonce and hash bits. -/
theorem constructor_fields (nonce : Nat) (balance : U256) (codeHash : Hash32) :
    (State.Account.mk nonce balance codeHash).nonce = nonce ∧
    (State.Account.mk nonce balance codeHash).balance = balance ∧
    (State.Account.mk nonce balance codeHash).codeHash = codeHash :=
  ⟨State.Account.nonce_mk nonce balance codeHash,
    State.Account.balance_mk nonce balance codeHash,
    State.Account.codeHash_mk nonce balance codeHash⟩

/-- Public fields support reconstruction without any provider representation unfolding. -/
theorem reconstruct (x : State.Account) :
    State.Account.mk x.nonce x.balance x.codeHash = x := State.Account.eta x

/-- Public account extensionality consumes all three field equalities. -/
theorem fields_determine (x y : State.Account) (hn : x.nonce = y.nonce)
    (hb : x.balance = y.balance) (hc : x.codeHash = y.codeHash) : x = y :=
  State.Account.ext hn hb hc

/-- Every supplied constants record gives the specified three empty-account fields. -/
theorem empty_fields (consts : HashConsts) :
    (emptyAccount consts).nonce = 0 ∧
    (emptyAccount consts).balance = U256.zero ∧
    (emptyAccount consts).codeHash = consts.emptyCodeHash :=
  ⟨emptyAccount_nonce consts, emptyAccount_balance consts, emptyAccount_codeHash consts⟩

/-- A present empty account is distinct from absence for every constants record. -/
theorem absent_ne_present_empty (consts : HashConsts) :
    (none : Option State.Account) ≠ some (emptyAccount consts) := by
  intro h
  cases h

end STFSpec.Conformance.State.AccountCallerProofs
