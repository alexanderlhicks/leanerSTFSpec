/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit
import STFSpec.Conformance.StateCommit.AccountDomain

/-!
# Contextual account encoder public-law clients

Library `EthConformance`. Arbitrary inputs consume the complete assembled Q47 premises.
Each field can vary independently, including a nonce above any fixed-width bound.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` §§3–7.
-/

namespace STFSpec.Conformance.StateCommit.AccountCallerProofs
open STFSpec.Base STFSpec.Codec STFSpec.State STFSpec.StateCommit

private def domain (acc : Account) (root : Hash32) : Prop :=
  Rlp.Encodable (.list [Rlp.ofNat acc.nonce, Rlp.ofNat acc.balance.toNat,
    .bytes root.toBytes.toByteArray, .bytes acc.codeHash.toBytes.toByteArray])

private theorem wire_nonempty (acc : Account) (root : Hash32) :
    encodeAccount acc root ≠ ByteArray.empty := encodeAccount_ne_empty acc root

private theorem recover_pair (a b : Account) (r s : Hash32)
    (ha : domain a r) (hb : domain b s) (h : encodeAccount a r = encodeAccount b s) :
    a = b ∧ r = s := (encodeAccount_inj a b r s ha hb).mp h

private theorem equal_pairs_equal_wires (a b : Account) (r s : Hash32)
    (ha : domain a r) (hb : domain b s) (h : a = b ∧ r = s) :
    encodeAccount a r = encodeAccount b s := (encodeAccount_inj a b r s ha hb).mpr h

private theorem nonce_varies (n m : Nat) (balance : U256) (code root : Hash32)
    (hn : n ≠ m) (ha : domain ⟨n, balance, code⟩ root)
    (hb : domain ⟨m, balance, code⟩ root) :
    encodeAccount ⟨n, balance, code⟩ root ≠ encodeAccount ⟨m, balance, code⟩ root := by
  intro h
  have he := (recover_pair _ _ _ _ ha hb h).1
  exact hn (congrArg Account.nonce he)

private theorem balance_varies (nonce : Nat) (a b : U256) (code root : Hash32)
    (hab : a ≠ b) (ha : domain ⟨nonce, a, code⟩ root)
    (hb : domain ⟨nonce, b, code⟩ root) :
    encodeAccount ⟨nonce, a, code⟩ root ≠ encodeAccount ⟨nonce, b, code⟩ root := by
  intro h
  exact hab (congrArg Account.balance (recover_pair _ _ _ _ ha hb h).1)

private theorem code_varies (nonce : Nat) (balance : U256) (a b root : Hash32)
    (hab : a ≠ b) (ha : domain ⟨nonce, balance, a⟩ root)
    (hb : domain ⟨nonce, balance, b⟩ root) :
    encodeAccount ⟨nonce, balance, a⟩ root ≠ encodeAccount ⟨nonce, balance, b⟩ root := by
  intro h
  exact hab (congrArg Account.codeHash (recover_pair _ _ _ _ ha hb h).1)

private theorem root_varies (acc : Account) (r s : Hash32) (hrs : r ≠ s)
    (ha : domain acc r) (hb : domain acc s) :
    encodeAccount acc r ≠ encodeAccount acc s := by
  intro h
  exact hrs (recover_pair _ _ _ _ ha hb h).2

private theorem empty_account_binding (c d : HashConsts) (r s : Hash32) :
    encodeAccount (emptyAccount c) r = encodeAccount (emptyAccount d) s ↔
      emptyAccount c = emptyAccount d ∧ r = s :=
  encodeAccount_inj _ _ _ _ (AccountDomain.empty_domain c r) (AccountDomain.empty_domain d s)

end STFSpec.Conformance.StateCommit.AccountCallerProofs
