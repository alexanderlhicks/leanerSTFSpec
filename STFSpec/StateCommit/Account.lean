/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.Account
import STFSpec.Codec.RlpTyped
import STFSpec.Codec.RlpCanonical

/-!
# Contextual account-leaf encoding

Library `EthStateCommit`. A supplied storage root completes the three-field Account.
Integers use minimal unsigned bytes; both hashes retain all 32 bytes. The existing
Q47 RLP completion applies to every unbounded nonce; binding requires the complete
assembled standard domain. No hashing or trie traversal occurs here (Q53).
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` §§3–7.
-/

namespace STFSpec.StateCommit
open Base Codec State

/-- RLP list of nonce, balance, supplied storage root and code hash, in that order.
Integers use minimal unsigned payloads; both hashes retain all 32 bytes (SC1).
EELS `src/ethereum/merkle_patricia_trie.py:193–210` and
`src/ethereum/forks/amsterdam/fork_types.py:67–81` at the pin. -/
def encodeAccount (acc : Account) (storageRoot : Hash32) : ByteArray :=
  Rlp.encode (.list [Rlp.ofNat acc.nonce, Rlp.ofNat acc.balance.toNat,
    .bytes storageRoot.toBytes.toByteArray, .bytes acc.codeHash.toBytes.toByteArray])

/-- The complete account-list wire is nonempty on every account and supplied root. -/
theorem encodeAccount_ne_empty (acc : Account) (storageRoot : Hash32) :
    encodeAccount acc storageRoot ≠ ByteArray.empty := by
  intro h
  have hs := Rlp.size_encode_list [Rlp.ofNat acc.nonce, Rlp.ofNat acc.balance.toNat,
    .bytes storageRoot.toBytes.toByteArray, .bytes acc.codeHash.toBytes.toByteArray]
  change (encodeAccount acc storageRoot).size = _ at hs
  rw [h] at hs
  simp only [ByteArray.size_empty] at hs
  split at hs <;> omega

private theorem hash_eq_of_bytes_eq (a b : Hash32)
    (h : a.toBytes.toByteArray = b.toBytes.toByteArray) : a = b := by
  apply Hash32.toBytes_inj.mp
  simpa only [Bytes.ofByteArray_toByteArray] using congrArg Bytes.ofByteArray h

/-- Equal complete wires bind both Account and root on the two complete Q47 domains.
The premises include every child and the total encoded child-payload length. -/
theorem encodeAccount_inj (acc₁ acc₂ : Account) (root₁ root₂ : Hash32)
    (h₁ : Rlp.Encodable (.list [Rlp.ofNat acc₁.nonce, Rlp.ofNat acc₁.balance.toNat,
      .bytes root₁.toBytes.toByteArray, .bytes acc₁.codeHash.toBytes.toByteArray]))
    (h₂ : Rlp.Encodable (.list [Rlp.ofNat acc₂.nonce, Rlp.ofNat acc₂.balance.toNat,
      .bytes root₂.toBytes.toByteArray, .bytes acc₂.codeHash.toBytes.toByteArray])) :
    encodeAccount acc₁ root₁ = encodeAccount acc₂ root₂ ↔ acc₁ = acc₂ ∧ root₁ = root₂ := by
  constructor
  · intro h
    have he := Rlp.eq_of_encode_eq _ _ h₁ h₂ h
    have hl := RlpItem.list.inj he
    simp only [List.cons.injEq, RlpItem.bytes.injEq, and_true] at hl
    have hn := congrArg Rlp.toNat hl.1
    have hb := congrArg Rlp.toNat hl.2.1
    simp only [Rlp.toNat_ofNat, Except.ok.injEq] at hn hb
    exact ⟨Account.ext hn (U256.toNat_inj.mp hb)
      (hash_eq_of_bytes_eq _ _ hl.2.2.2), hash_eq_of_bytes_eq _ _ hl.2.2.1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end STFSpec.StateCommit
