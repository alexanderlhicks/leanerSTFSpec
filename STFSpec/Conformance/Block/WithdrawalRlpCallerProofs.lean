/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block
import STFSpec.Codec.RlpDecode

/-!
# Withdrawal RLP model clients

Library `EthConformance`. Private clients use the public reference model and
Base/Codec laws. Single-withdrawal bounds imply no arbitrary outer-list bound.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–7.
-/

namespace STFSpec.Conformance.Block.WithdrawalRlpCallerProofs

open STFSpec.Base STFSpec.Block STFSpec.Codec

private theorem instance_identity :
    (inferInstance : RlpEncode Withdrawal) = Withdrawal.instRlpEncode := rfl

private theorem complete_model (w : Withdrawal) :
    RlpEncode.toRlp w = .list [Rlp.ofNat w.index.toNat, Rlp.ofNat w.validatorIndex.toNat,
      .bytes w.address.toBytes.toByteArray, Rlp.ofNat w.amount.toNat] := rfl

private theorem arbitrary_fields (i v a : U64) (address : Address) :
    RlpEncode.toRlp (Withdrawal.mk i v address a) =
      .list [Rlp.ofNat i.toNat, Rlp.ofNat v.toNat, .bytes address.toBytes.toByteArray,
        Rlp.ofNat a.toNat] := rfl

private def wordWire (x : U64) : List UInt8 :=
  (Rlp.encodeBytes (Uint.toBeBytes x.toNat).toByteArray).data.toList

private def payload (w : Withdrawal) : List UInt8 :=
  wordWire w.index ++ wordWire w.validatorIndex ++
    (148 :: w.address.toBytes.toList) ++ wordWire w.amount

private theorem word_digits (x : U64) :
    (Uint.toBeBytes x.toNat).size ≤ 8 ∧
      Uint.ofBeBytes (Uint.toBeBytes x.toNat) = x.toNat ∧
      (Uint.toBeBytes x.toNat = Bytes.empty ↔ x.toNat = 0) ∧
      (x.toNat ≠ 0 → (Uint.toBeBytes x.toNat).toList.head? ≠ some 0) :=
  ⟨(Uint.size_toBeBytes_le_iff _ 8).mpr (U64.toNat_lt x),
    Uint.ofBeBytes_toBeBytes _, Uint.toBeBytes_eq_empty_iff _,
    Uint.toList_toBeBytes_head_ne_zero _⟩

private theorem word_width (x : U64) : 1 ≤ (wordWire x).length ∧
    (wordWire x).length ≤ 9 := by
  let b := (Uint.toBeBytes x.toNat).toByteArray
  have hb : b.size ≤ 8 := by
    rw [Bytes.size_toByteArray]
    exact (word_digits x).1
  have he := Rlp.size_encodeBytes b
  have hs : b.size < 56 := by omega
  by_cases hsingle : b.size = 1 ∧ (b[0]?.getD 128).toNat < 128
  · rw [ite_eq_left hsingle] at he
    have := hsingle.1
    change 1 ≤ (Rlp.encodeBytes b).data.toList.length ∧
      (Rlp.encodeBytes b).data.toList.length ≤ 9
    rw [Array.length_toList]
    change 1 ≤ (Rlp.encodeBytes b).size ∧ (Rlp.encodeBytes b).size ≤ 9
    omega
  · rw [ite_eq_right hsingle, ite_eq_left hs] at he
    change 1 ≤ (Rlp.encodeBytes b).data.toList.length ∧
      (Rlp.encodeBytes b).data.toList.length ≤ 9
    rw [Array.length_toList]
    change 1 ≤ (Rlp.encodeBytes b).size ∧ (Rlp.encodeBytes b).size ≤ 9
    omega

private theorem address_wire (a : Address) :
    (Rlp.encodeBytes a.toBytes.toByteArray).data.toList = 148 :: a.toBytes.toList := by
  have hs : a.toBytes.toByteArray.size = 20 := by
    rw [Bytes.size_toByteArray, Address.size_toBytes]
  rw [Rlp.encodeBytes_short _ (by omega) (by simp [hs]), hs, Bytes.toList_toByteArray]
  rfl

private theorem complete_payload (w : Withdrawal) :
    Rlp.encodePayloadModel [Rlp.ofNat w.index.toNat, Rlp.ofNat w.validatorIndex.toNat,
      .bytes w.address.toBytes.toByteArray, Rlp.ofNat w.amount.toNat] = payload w := by
  rw [Rlp.encodePayloadModel_eq_flatMap]
  simp only [List.flatMap_cons, List.flatMap_nil, Rlp.ofNat, Rlp.encode_bytes,
    address_wire, List.append_nil, payload, wordWire, List.append_assoc]

private theorem payload_bounds (w : Withdrawal) :
    24 ≤ (payload w).length ∧ (payload w).length ≤ 48 := by
  have hi := word_width w.index
  have hv := word_width w.validatorIndex
  have ha := word_width w.amount
  have hs := Address.size_toBytes w.address
  simp only [payload, List.length_append, List.length_cons, Bytes.length_toList]
  omega

private theorem word_encodable (x : U64) : Rlp.Encodable (Rlp.ofNat x.toNat) := by
  apply (Rlp.encodable_bytes_iff _).mpr
  rw [Bytes.size_toByteArray]
  exact Nat.lt_of_le_of_lt (word_digits x).1 (by decide)

private theorem address_encodable (a : Address) :
    Rlp.Encodable (.bytes a.toBytes.toByteArray) := by
  rw [Rlp.encodable_bytes_iff, Bytes.size_toByteArray, Address.size_toBytes]
  decide

private theorem actual_encodable (w : Withdrawal) : Rlp.Encodable (RlpEncode.toRlp w) := by
  rw [complete_model, Rlp.encodable_list_iff]
  constructor
  · simp only [List.mem_cons, List.not_mem_nil, forall_eq_or_imp]
    exact ⟨word_encodable w.index, word_encodable w.validatorIndex,
      address_encodable w.address, word_encodable w.amount, by simp⟩
  · rw [complete_payload]
    exact Nat.lt_of_le_of_lt (payload_bounds w).2 (by decide)

private theorem complete_wire (w : Withdrawal) :
    (Rlp.encodeOf w).data.toList = UInt8.ofNat (192 + (payload w).length) :: payload w := by
  unfold Rlp.encodeOf
  rw [complete_model, Rlp.encode_list_short, complete_payload]
  rw [complete_payload]
  have := payload_bounds w
  omega

private theorem wire_bounds (w : Withdrawal) :
    25 ≤ (Rlp.encodeOf w).size ∧ (Rlp.encodeOf w).size ≤ 49 := by
  have := payload_bounds w
  have he := congrArg List.length (complete_wire w)
  simp only [Array.length_toList, List.length_cons] at he
  change 25 ≤ (Rlp.encodeOf w).data.size ∧ (Rlp.encodeOf w).data.size ≤ 49
  omega

private theorem tag_bounds (w : Withdrawal) :
    216 ≤ (UInt8.ofNat (192 + (payload w).length)).toNat ∧
      (UInt8.ofNat (192 + (payload w).length)).toNat ≤ 240 := by
  have := payload_bounds w
  rw [UInt8.toNat_ofNat_of_lt' (by omega : 192 + (payload w).length < 256)]
  omega

private theorem raw_decode (w : Withdrawal) :
    Rlp.decode (Rlp.encodeOf w) = .ok (RlpEncode.toRlp w) :=
  Rlp.decode_encode _ (actual_encodable w)

private theorem word_boundaries :
    wordWire (U64.ofNat 0) = [128] ∧ wordWire (U64.ofNat 1) = [1] ∧
    wordWire (U64.ofNat 127) = [127] ∧ wordWire (U64.ofNat 128) = [129, 128] ∧
    wordWire (U64.ofNat 255) = [129, 255] ∧ wordWire (U64.ofNat 256) = [130, 1, 0] ∧
    wordWire (U64.ofNat (2 ^ 63)) = [136, 128, 0, 0, 0, 0, 0, 0, 0] ∧
    wordWire (U64.ofNat (2 ^ 64 - 1)) = [136, 255, 255, 255, 255, 255, 255, 255, 255] := by
  decide

private theorem lower_attained :
    (Rlp.encodeOf (Withdrawal.mk (U64.ofNat 0) (U64.ofNat 0)
      (Address.ofNat 0) (U64.ofNat 0))).size = 25 := by
  decide

private theorem upper_attained :
    (Rlp.encodeOf (Withdrawal.mk (U64.ofNat (2 ^ 64 - 1)) (U64.ofNat (2 ^ 64 - 1))
      (Address.ofNat 0) (U64.ofNat (2 ^ 64 - 1)))).size = 49 := by
  decide

end STFSpec.Conformance.Block.WithdrawalRlpCallerProofs
