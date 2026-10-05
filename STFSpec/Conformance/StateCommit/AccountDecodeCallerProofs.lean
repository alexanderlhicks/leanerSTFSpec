/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit.AccountDecode

/-!
# Account decoder public-contract clients

Library `EthConformance`. Ordinary arbitrary-input clients consume every public
law and provider models, with complete supplied constants and Q47 domains.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` §§3–7.
-/

namespace STFSpec.Conformance.StateCommit.AccountDecodeCallerProofs
open STFSpec.Base STFSpec.Codec STFSpec.State STFSpec.StateCommit

private theorem complete_success_values (consts : HashConsts) (leaf : ByteArray)
    (acc : Account) (root : Hash32) (h : decodeAccountLeaf consts leaf = .ok (acc, root)) :
    ∃ n b r c : RlpItem, Rlp.decode leaf = .ok (.list [n, b, r, c]) := by
  obtain ⟨n, b, r, c, hp, _⟩ := (decodeAccountLeaf_eq_ok_iff _ _ _ _).mp h
  exact ⟨n, b, r, c, hp⟩

private theorem parsed_falsy_lists (consts : HashConsts) (leaf : ByteArray)
    (h : Rlp.decode leaf = .ok (.list [.list [], .list [], .list [], .list []])) :
    decodeAccountLeaf consts leaf = .ok (emptyAccount consts, consts.emptyTrieRoot) := by
  apply (decodeAccountLeaf_eq_ok_iff _ _ _ _).mpr
  refine ⟨_, _, _, _, h, Or.inr ?_, Or.inr ?_, Or.inl ?_, Or.inl ?_⟩
  · exact ⟨rfl, emptyAccount_nonce consts⟩
  · exact ⟨rfl, emptyAccount_balance consts⟩
  · exact ⟨Or.inr rfl, rfl⟩
  · exact ⟨Or.inr rfl, emptyAccount_codeHash consts⟩

private theorem all_falsy_mixtures (consts : HashConsts) (leaf : ByteArray)
    (n b r c : RlpItem)
    (hp : Rlp.decode leaf = .ok (.list [n, b, r, c]))
    (hn : n = .bytes ByteArray.empty ∨ n = .list [])
    (hb : b = .bytes ByteArray.empty ∨ b = .list [])
    (hr : r = .bytes ByteArray.empty ∨ r = .list [])
    (hc : c = .bytes ByteArray.empty ∨ c = .list []) :
    decodeAccountLeaf consts leaf = .ok (emptyAccount consts, consts.emptyTrieRoot) := by
  have hz : Uint.ofBeBytes (Bytes.ofByteArray ByteArray.empty) = 0 := by
    have h := Uint.ofBeBytes_lt (Bytes.ofByteArray ByteArray.empty)
    rw [Bytes.size_ofByteArray, ByteArray.size_empty] at h
    simp only [Nat.mul_zero, Nat.pow_zero] at h
    omega
  apply (decodeAccountLeaf_eq_ok_iff _ _ _ _).mpr
  refine ⟨n, b, r, c, hp, ?_, ?_, Or.inl ⟨hr, rfl⟩,
    Or.inl ⟨hc, emptyAccount_codeHash consts⟩⟩
  · rcases hn with hn | hn
    · exact Or.inl ⟨_, hn, hz.trans (emptyAccount_nonce consts).symm⟩
    · exact Or.inr ⟨hn, emptyAccount_nonce consts⟩
  · rcases hb with hb | hb
    · refine Or.inl ⟨_, hb, ?_⟩
      rw [emptyAccount_balance, U256.toNat_zero]
      exact hz
    · exact Or.inr ⟨hb, emptyAccount_balance consts⟩

private theorem arbitrary_unsigned_nonce (consts : HashConsts) (leaf bs : ByteArray)
    (balance : U256) (root code : Hash32)
    (h : Rlp.decode leaf = .ok (.list [.bytes bs, Rlp.ofNat balance.toNat,
      .bytes root.toBytes.toByteArray, .bytes code.toBytes.toByteArray])) :
    decodeAccountLeaf consts leaf =
      .ok (Account.mk (Uint.ofBeBytes (Bytes.ofByteArray bs)) balance code, root) := by
  apply (decodeAccountLeaf_eq_ok_iff _ _ _ _).mpr
  refine ⟨_, _, _, _, h, Or.inl ⟨bs, rfl, rfl⟩, Or.inl ?_, Or.inr rfl, Or.inr rfl⟩
  exact ⟨_, rfl, by rw [Bytes.ofByteArray_toByteArray, Uint.ofBeBytes_toBeBytes]⟩

private theorem rejection_of_no_values (consts : HashConsts) (leaf : ByteArray)
    (h : ∀ acc root, decodeAccountLeaf consts leaf ≠ .ok (acc, root)) :
    decodeAccountLeaf consts leaf = .error (.malformed .leaf) := by
  apply (decodeAccountLeaf_eq_error_iff _ _).mpr
  rintro ⟨acc, root, hs⟩
  exact h acc root hs

private theorem raw_empty_rejection (consts : HashConsts) :
    decodeAccountLeaf consts ByteArray.empty = .error (.malformed .leaf) :=
  decodeAccountLeaf_empty consts

private theorem complete_domain_roundtrip (consts : HashConsts) (acc : Account) (root : Hash32)
    (h : Rlp.Encodable (.list [Rlp.ofNat acc.nonce, Rlp.ofNat acc.balance.toNat,
      .bytes root.toBytes.toByteArray, .bytes acc.codeHash.toBytes.toByteArray])) :
    decodeAccountLeaf consts (encodeAccount acc root) = .ok (acc, root) :=
  decodeAccountLeaf_encodeAccount consts acc root h

private theorem huge_nonce_roundtrip (consts : HashConsts) (balance : U256)
    (code root : Hash32)
    (h : Rlp.Encodable (.list [Rlp.ofNat (2 ^ 1024 + 17), Rlp.ofNat balance.toNat,
      .bytes root.toBytes.toByteArray, .bytes code.toBytes.toByteArray])) :
    decodeAccountLeaf consts (encodeAccount (Account.mk (2 ^ 1024 + 17) balance code) root) =
      .ok (Account.mk (2 ^ 1024 + 17) balance code, root) :=
  decodeAccountLeaf_encodeAccount consts _ root h

private theorem irrelevant_constants (consts : HashConsts) (leaf : ByteArray)
    (ommer topic : Hash32) :
    decodeAccountLeaf { consts with emptyOmmerHash := ommer, transferTopic := topic } leaf =
      decodeAccountLeaf consts leaf :=
  decodeAccountLeaf_congr_consts _ _ leaf rfl rfl

/-- The complete domain is inhabited for every supplied empty account and root. -/
private theorem empty_domain (c : HashConsts) (r : Hash32) :
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

private theorem empty_account_roundtrip (consts c : HashConsts) (root : Hash32) :
    decodeAccountLeaf consts (encodeAccount (emptyAccount c) root) =
      .ok (emptyAccount c, root) :=
  decodeAccountLeaf_encodeAccount consts _ root (empty_domain c root)

end STFSpec.Conformance.StateCommit.AccountDecodeCallerProofs
