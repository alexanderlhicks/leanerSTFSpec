/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.ValueRecords

/-!
# Account values and the supplied empty account

Library `EthState`: the account record is its own model. Nonces are unbounded naturals;
the empty account uses the caller's `HashConsts.emptyCodeHash` without hashing.
Absence remains a separate `Option Account` value.

Spec guidance: `STFSpec/informal/modules/EthState.md`.
-/

namespace STFSpec.State

open Base

/-- Account value with exactly the pinned EELS `src/ethereum/state.py:42–49` fields. -/
structure Account where
  /-- Unbounded EELS `Uint` nonce; transaction admission owns nonce limits. -/
  nonce : Nat
  /-- Unsigned 256-bit balance. -/
  balance : U256
  /-- Complete code hash value. -/
  codeHash : Hash32

namespace Account

/-- Construction preserves the unbounded nonce. -/
theorem nonce_mk (nonce : Nat) (balance : U256) (codeHash : Hash32) :
    (Account.mk nonce balance codeHash).nonce = nonce := rfl

/-- Construction preserves the balance. -/
theorem balance_mk (nonce : Nat) (balance : U256) (codeHash : Hash32) :
    (Account.mk nonce balance codeHash).balance = balance := rfl

/-- Construction preserves all code hash bytes. -/
theorem codeHash_mk (nonce : Nat) (balance : U256) (codeHash : Hash32) :
    (Account.mk nonce balance codeHash).codeHash = codeHash := rfl

/-- Equality of the three public fields determines the complete account. -/
theorem ext {x y : Account} (hn : x.nonce = y.nonce) (hb : x.balance = y.balance)
    (hc : x.codeHash = y.codeHash) : x = y := by
  cases x
  cases y
  cases hn
  cases hb
  cases hc
  rfl

/-- Reconstructing the public fields returns the original account. -/
theorem eta (x : Account) : Account.mk x.nonce x.balance x.codeHash = x := by
  cases x
  rfl

/-- Account equality uses ordinary equality of its public Nat, U256 and Hash32 fields. -/
instance : DecidableEq Account := fun x y ↦
  if hn : x.nonce = y.nonce then
    if hb : x.balance = y.balance then
      if hc : x.codeHash = y.codeHash then
        isTrue (ext hn hb hc)
      else isFalse (fun h ↦ hc (congrArg Account.codeHash h))
    else isFalse (fun h ↦ hb (congrArg Account.balance h))
  else isFalse (fun h ↦ hn (congrArg Account.nonce h))

end Account

section

variable (consts : HashConsts)
local notation "EMPTY_CODE_HASH" => consts.emptyCodeHash

/-- Empty account; EELS `src/ethereum/state.py:52–56`, with caller-supplied F20 constants. -/
def emptyAccount : Account := ⟨0, U256.zero, EMPTY_CODE_HASH⟩

/-- The empty account nonce is zero. -/
theorem emptyAccount_nonce : (emptyAccount consts).nonce = 0 := rfl

/-- The empty account balance is the word zero. -/
theorem emptyAccount_balance : (emptyAccount consts).balance = U256.zero := rfl

/-- The empty account retains exactly the supplied empty-code hash. -/
theorem emptyAccount_codeHash : (emptyAccount consts).codeHash = consts.emptyCodeHash := rfl

end

end STFSpec.State
