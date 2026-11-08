/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit

/-!
# Storage decoder public-contract clients

Library `EthConformance`. Arbitrary-input proofs use the decoder laws in the
spec guidance and public Base/Codec contracts without access to private numeric representation.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` §§3–7.
-/

namespace STFSpec.Conformance.StateCommit.StorageDecodeCallerProofs
open STFSpec.Base STFSpec.Codec STFSpec.State STFSpec.StateCommit

private theorem parser_error (leaf : ByteArray) (e : RlpError)
    (h : Rlp.decode leaf = .error e) :
    decodeStorageLeaf leaf = .error (.malformed .leaf) :=
  decodeStorageLeaf_of_rlp_error leaf e h

private theorem parsed_list (leaf : ByteArray) (items : List RlpItem)
    (h : Rlp.decode leaf = .ok (.list items)) :
    decodeStorageLeaf leaf = .error (.malformed .leaf) :=
  decodeStorageLeaf_of_rlp_list leaf items h

private theorem parsed_bytes (leaf payload : ByteArray)
    (h : Rlp.decode leaf = .ok (.bytes payload)) :
    decodeStorageLeaf leaf =
      if payload[0]? = some 0 then .error (.malformed .leaf)
      else if payload.size ≤ 32 then
        .ok (U256.ofNat (Uint.ofBeBytes (Bytes.ofByteArray payload)))
      else .error (.malformed .leaf) :=
  decodeStorageLeaf_of_rlp_bytes leaf payload h

private theorem admitted_value_lt (payload : ByteArray) (hw : payload.size ≤ 32) :
    Uint.ofBeBytes (Bytes.ofByteArray payload) < 2 ^ 256 := by
  have hn := Uint.ofBeBytes_lt (Bytes.ofByteArray payload)
  rw [Bytes.size_ofByteArray] at hn
  exact Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (by omega))

private theorem numeric_success_iff (leaf payload : ByteArray) (v : U256)
    (h : Rlp.decode leaf = .ok (.bytes payload)) :
    decodeStorageLeaf leaf = .ok v ↔
      payload[0]? ≠ some 0 ∧ payload.size ≤ 32 ∧
      v.toNat = Uint.ofBeBytes (Bytes.ofByteArray payload) := by
  rw [decodeStorageLeaf_of_rlp_bytes leaf payload h]
  by_cases hz : payload[0]? = some 0
  · simp only [hz, ↓reduceIte, reduceCtorEq, ne_eq, not_true_eq_false, false_and]
  · by_cases hw : payload.size ≤ 32
    · simp only [ite_eq_right hz, ite_eq_left hw, Except.ok.injEq]
      constructor
      · intro he
        exact ⟨hz, hw, by rw [← he,
          U256.toNat_ofNat_of_lt (admitted_value_lt payload hw)]⟩
      · intro he
        rw [← he.2.2, U256.ofNat_toNat]
    · simp only [hz, hw, ↓reduceIte, reduceCtorEq, false_and, and_false]

private theorem numeric_error_iff (leaf payload : ByteArray)
    (h : Rlp.decode leaf = .ok (.bytes payload)) :
    decodeStorageLeaf leaf = .error (.malformed .leaf) ↔
      payload[0]? = some 0 ∨ 32 < payload.size := by
  rw [decodeStorageLeaf_of_rlp_bytes leaf payload h]
  by_cases hz : payload[0]? = some 0 <;>
    by_cases hw : payload.size ≤ 32 <;> simp [hz, hw] <;> omega

private theorem complete_numeric_success (leaf payload : ByteArray)
    (h : Rlp.decode leaf = .ok (.bytes payload))
    (hz : payload[0]? ≠ some 0) (hw : payload.size ≤ 32) :
    ∃ v, decodeStorageLeaf leaf = .ok v ∧
      v.toNat = Uint.ofBeBytes (Bytes.ofByteArray payload) := by
  have hn := U256.toNat_ofNat_of_lt (admitted_value_lt payload hw)
  exact ⟨_, (numeric_success_iff leaf payload _ h).mpr ⟨hz, hw, hn⟩, hn⟩

private theorem all_word_roundtrip (v : U256) :
    decodeStorageLeaf (encodeStorage v) = .ok v := by
  by_cases hz : v = U256.zero
  · subst v
    have hd : Rlp.decode (encodeStorage U256.zero) = .ok (.bytes ByteArray.empty) := by
      rw [encodeStorage_eq, U256.toNat_zero]
      exact Rlp.decode_encode _ ((Rlp.encodable_bytes_iff _).mpr (by decide))
    rw [decodeStorageLeaf_of_rlp_bytes _ _ hd]
    rfl
  · exact decodeStorageLeaf_encodeStorage v hz

private theorem whole_wire_success_iff (leaf : ByteArray) (v : U256) :
    decodeStorageLeaf leaf = .ok v ↔ leaf = encodeStorage v := by
  constructor
  · intro hs
    cases hd : Rlp.decode leaf with
    | error e => rw [decodeStorageLeaf_of_rlp_error _ _ hd] at hs; cases hs
    | ok item =>
      cases item with
      | list items => rw [decodeStorageLeaf_of_rlp_list _ _ hd] at hs; cases hs
      | bytes payload =>
        obtain ⟨hz, _, hv⟩ := (numeric_success_iff leaf payload v hd).mp hs
        have hn := (Rlp.toNat_eq_ok_bytes_iff payload v.toNat).mpr ⟨hz, hv.symm⟩
        have hb := (Rlp.toNat_canonical_iff payload v.toNat).mp hn
        rw [← Rlp.encode_eq_of_decode_eq_ok _ _ hd, hb, encodeStorage_eq]
        rfl
  · intro he
    rw [he]
    exact all_word_roundtrip v

private theorem canonical_nonzero_roundtrip (v : U256) (h : v ≠ U256.zero) :
    decodeStorageLeaf (encodeStorage v) = .ok v := decodeStorageLeaf_encodeStorage v h

end STFSpec.Conformance.StateCommit.StorageDecodeCallerProofs
