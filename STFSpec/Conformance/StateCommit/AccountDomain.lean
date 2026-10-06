/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit.Account

/-!
# Shared empty-account encoding domain

Library `EthConformance`. The encoder and decoder public-law clients share this
ordinary proof of the complete assembled Q47 domain. This conformance helper adds
no production Account API or broader domain claim.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` §3.
-/

namespace STFSpec.Conformance.StateCommit.AccountDomain
open STFSpec.Base STFSpec.Codec STFSpec.State

/-- The complete domain is inhabited for every supplied empty account and root. -/
theorem empty_domain (c : HashConsts) (r : Hash32) :
    Rlp.Encodable (.list [Rlp.ofNat (emptyAccount c).nonce,
      Rlp.ofNat (emptyAccount c).balance.toNat, .bytes r.toBytes.toByteArray,
      .bytes (emptyAccount c).codeHash.toBytes.toByteArray]) := by
  have hz : ((Uint.toBeBytes 0).toByteArray).size = 0 := by
    rw [Uint.toBeBytes_zero, Bytes.size_toByteArray, Bytes.size_empty]
  have hr : r.toBytes.toByteArray.size = 32 := by
    rw [Bytes.size_toByteArray, Hash32.size_toBytes]
  have hc : c.emptyCodeHash.toBytes.toByteArray.size = 32 := by
    rw [Bytes.size_toByteArray, Hash32.size_toBytes]
  have eb (b : ByteArray) (h : b.size = 0 ∨ b.size = 32) :
      Rlp.Encodable (.bytes b) := by
    apply (Rlp.encodable_bytes_iff _).mpr
    rcases h with h | h <;> rw [h] <;> decide
  apply (Rlp.encodable_list_iff _).mpr
  constructor
  · intro x hx
    simp only [emptyAccount_nonce, emptyAccount_balance, emptyAccount_codeHash,
      U256.toNat_zero, Rlp.ofNat, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact eb _ (.inl hz)
    · exact eb _ (.inl hz)
    · exact eb _ (.inr hr)
    · exact eb _ (.inr hc)
  · rw [Rlp.length_encodePayloadModel]
    simp only [emptyAccount_nonce, emptyAccount_balance, emptyAccount_codeHash,
      U256.toNat_zero, Rlp.ofNat, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, ← Rlp.size_encode, Rlp.encode_bytes, Rlp.size_encodeBytes, hz, hr, hc]
    simp

end STFSpec.Conformance.StateCommit.AccountDomain
