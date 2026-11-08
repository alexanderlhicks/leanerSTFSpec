/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block
import STFSpec.Codec

/-!
# Header RLP public-model clients

Library `EthConformance`. All supplementary declarations are private. Clients use
the actual public dictionaries and Base/Codec model laws, with the complete
assembled Encodable premise retained for the raw wire inverse.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–7.
-/

namespace STFSpec.Conformance.Block.HeaderRlpCallerProofs

open STFSpec.Base STFSpec.Block STFSpec.Codec STFSpec.Codec.Rlp

private theorem header_dictionary :
    (inferInstance : RlpEncode Header) = Header.instRlpEncode := rfl

private def headerFields (h : Header) : List RlpItem := [
  .bytes h.parentHash.toBytes.toByteArray,
  .bytes h.ommersHash.toBytes.toByteArray,
  .bytes h.coinbase.toBytes.toByteArray,
  .bytes h.stateRoot.toBytes.toByteArray,
  .bytes h.transactionsRoot.toBytes.toByteArray,
  .bytes h.receiptRoot.toBytes.toByteArray,
  .bytes h.bloom.toBytes.toByteArray,
  Rlp.ofNat h.difficulty,
  Rlp.ofNat h.number,
  Rlp.ofNat h.gasLimit,
  Rlp.ofNat h.gasUsed,
  Rlp.ofNat h.timestamp.toNat,
  .bytes h.extraData.toByteArray,
  .bytes h.prevRandao.toBytes.toByteArray,
  .bytes h.nonce.toBytes.toByteArray,
  Rlp.ofNat h.baseFeePerGas,
  .bytes h.withdrawalsRoot.toBytes.toByteArray,
  Rlp.ofNat h.blobGasUsed.toNat,
  Rlp.ofNat h.excessBlobGas.toNat,
  .bytes h.parentBeaconBlockRoot.toBytes.toByteArray,
  .bytes h.requestsHash.toBytes.toByteArray,
  .bytes h.blockAccessListHash.toBytes.toByteArray,
  Rlp.ofNat h.slotNumber.toNat]

private theorem header_model (h : Header) :
    RlpEncode.toRlp h = .list (headerFields h) := rfl

private theorem header_arity (h : Header) :
    (headerFields h).length = 23 := rfl

private theorem header_wire (h : Header) :
    (encodeOf h).data.toList =
      lengthPrefixModel 192 247 (encodePayloadModel (headerFields h)).length ++
        encodePayloadModel (headerFields h) := by
  rw [encodeOf, header_model]
  exact toList_encode_list (headerFields h)

private theorem header_size (h : Header) :
    (encodeOf h).size =
      (if (encodePayloadModel (headerFields h)).length < 56 then 1 else
        1 + (Uint.toBeBytes (encodePayloadModel (headerFields h)).length).size) +
      (encodePayloadModel (headerFields h)).length := by
  rw [encodeOf, header_model]
  exact size_encode_list (headerFields h)

private theorem header_domain (h : Header) :
    Encodable (RlpEncode.toRlp h) ↔
      (∀ x ∈ headerFields h, Encodable x) ∧
        (encodePayloadModel (headerFields h)).length < 2 ^ 64 := by
  rw [header_model]
  exact encodable_list_iff (headerFields h)

private theorem header_raw_inverse (h : Header)
    (domain : Encodable (RlpEncode.toRlp h)) :
    decode (encodeOf h) = .ok (RlpEncode.toRlp h) := decode_encode _ domain

private theorem prevHeader_dictionary :
    (inferInstance : RlpEncode PrevHeader) = PrevHeader.instRlpEncode := rfl

private def prevHeaderFields (h : PrevHeader) : List RlpItem := [
  .bytes h.parentHash.toBytes.toByteArray,
  .bytes h.ommersHash.toBytes.toByteArray,
  .bytes h.coinbase.toBytes.toByteArray,
  .bytes h.stateRoot.toBytes.toByteArray,
  .bytes h.transactionsRoot.toBytes.toByteArray,
  .bytes h.receiptRoot.toBytes.toByteArray,
  .bytes h.bloom.toBytes.toByteArray,
  Rlp.ofNat h.difficulty,
  Rlp.ofNat h.number,
  Rlp.ofNat h.gasLimit,
  Rlp.ofNat h.gasUsed,
  Rlp.ofNat h.timestamp.toNat,
  .bytes h.extraData.toByteArray,
  .bytes h.prevRandao.toBytes.toByteArray,
  .bytes h.nonce.toBytes.toByteArray,
  Rlp.ofNat h.baseFeePerGas,
  .bytes h.withdrawalsRoot.toBytes.toByteArray,
  Rlp.ofNat h.blobGasUsed.toNat,
  Rlp.ofNat h.excessBlobGas.toNat,
  .bytes h.parentBeaconBlockRoot.toBytes.toByteArray,
  .bytes h.requestsHash.toBytes.toByteArray]

private theorem prevHeader_model (h : PrevHeader) :
    RlpEncode.toRlp h = .list (prevHeaderFields h) := rfl

private theorem prevHeader_arity (h : PrevHeader) :
    (prevHeaderFields h).length = 21 := rfl

private theorem prevHeader_wire (h : PrevHeader) :
    (encodeOf h).data.toList =
      lengthPrefixModel 192 247 (encodePayloadModel (prevHeaderFields h)).length ++
        encodePayloadModel (prevHeaderFields h) := by
  rw [encodeOf, prevHeader_model]
  exact toList_encode_list (prevHeaderFields h)

private theorem prevHeader_size (h : PrevHeader) :
    (encodeOf h).size =
      (if (encodePayloadModel (prevHeaderFields h)).length < 56 then 1 else
        1 + (Uint.toBeBytes (encodePayloadModel (prevHeaderFields h)).length).size) +
      (encodePayloadModel (prevHeaderFields h)).length := by
  rw [encodeOf, prevHeader_model]
  exact size_encode_list (prevHeaderFields h)

private theorem prevHeader_domain (h : PrevHeader) :
    Encodable (RlpEncode.toRlp h) ↔
      (∀ x ∈ prevHeaderFields h, Encodable x) ∧
        (encodePayloadModel (prevHeaderFields h)).length < 2 ^ 64 := by
  rw [prevHeader_model]
  exact encodable_list_iff (prevHeaderFields h)

private theorem prevHeader_raw_inverse (h : PrevHeader)
    (domain : Encodable (RlpEncode.toRlp h)) :
    decode (encodeOf h) = .ok (RlpEncode.toRlp h) := decode_encode _ domain

private theorem parent_dictionary :
    (inferInstance : RlpEncode ParentHeader) = ParentHeader.instRlpEncode := rfl

private theorem parent_amsterdam (h : Header) :
    RlpEncode.toRlp (ParentHeader.amsterdam h) = RlpEncode.toRlp h ∧
      encodeOf (ParentHeader.amsterdam h) = encodeOf h := ⟨rfl, rfl⟩

private theorem parent_bpo5 (h : PrevHeader) :
    RlpEncode.toRlp (ParentHeader.bpo5 h) = RlpEncode.toRlp h ∧
      encodeOf (ParentHeader.bpo5 h) = encodeOf h := ⟨rfl, rfl⟩

private theorem parent_raw_inverse (h : ParentHeader)
    (domain : Encodable (RlpEncode.toRlp h)) :
    decode (encodeOf h) = .ok (RlpEncode.toRlp h) := decode_encode _ domain

private theorem bytes_size (b : ByteArray) :
    encodedSize (.bytes b) =
      if b.size = 1 ∧ (b[0]?.getD 128).toNat < 128 then b.size else
        (if b.size < 56 then 1 else 1 + (Uint.toBeBytes b.size).size) + b.size := by
  rw [← size_encode, encode_bytes, size_encodeBytes]

private theorem bytes_nonempty_wire (b : ByteArray) : 1 ≤ encodedSize (.bytes b) := by
  rw [bytes_size]
  split
  · omega
  · split <;> omega

private theorem fixed_size (b : ByteArray) (n : Nat) (hb : b.size = n) (hn : 2 ≤ n) :
    encodedSize (.bytes b) =
      (if n < 56 then 1 else 1 + (Uint.toBeBytes n).size) + n := by
  rw [bytes_size, hb, ite_eq_right (by omega)]

private theorem numeric_nonempty_wire (n : Nat) : 1 ≤ encodedSize (ofNat n) :=
  bytes_nonempty_wire _

private theorem numeric_domain (n : Nat) (bound : n < 2 ^ 256) :
    Encodable (ofNat n) := by
  rw [ofNat, encodable_bytes_iff, Bytes.size_toByteArray]
  have width := (Uint.size_toBeBytes_le_iff n 32).mpr bound
  omega

private theorem parent_variants_distinct (h : Header) (p : PrevHeader) :
    RlpEncode.toRlp (ParentHeader.amsterdam h) ≠
      RlpEncode.toRlp (ParentHeader.bpo5 p) := by
  intro equal
  change RlpItem.list (headerFields h) = .list (prevHeaderFields p) at equal
  have arity := congrArg List.length (RlpItem.list.inj equal)
  rw [header_arity, prevHeader_arity] at arity
  contradiction

private theorem parent_wires_distinct (h : Header) (p : PrevHeader)
    (hd : Encodable (RlpEncode.toRlp h)) (pd : Encodable (RlpEncode.toRlp p)) :
    encodeOf (ParentHeader.amsterdam h) ≠ encodeOf (ParentHeader.bpo5 p) := by
  intro equal
  exact parent_variants_distinct h p (eq_of_encode_eq _ _ hd pd equal)

private theorem hash_width (x : Hash32) :
    encodedSize (.bytes x.toBytes.toByteArray) = 33 := by
  rw [fixed_size _ 32 (by rw [Bytes.size_toByteArray, Hash32.size_toBytes]) (by decide)]
  rfl

private theorem address_width (x : Address) :
    encodedSize (.bytes x.toBytes.toByteArray) = 21 := by
  rw [fixed_size _ 20 (by rw [Bytes.size_toByteArray, Address.size_toBytes]) (by decide)]
  rfl

private theorem fixed32_width (x : Bytes32) :
    encodedSize (.bytes x.toBytes.toByteArray) = 33 := by
  rw [fixed_size _ 32 (by rw [Bytes.size_toByteArray, FixedBytes.size_toBytes]) (by decide)]
  rfl

private theorem nonce_width (x : Bytes8) :
    encodedSize (.bytes x.toBytes.toByteArray) = 9 := by
  rw [fixed_size _ 8 (by rw [Bytes.size_toByteArray, FixedBytes.size_toBytes]) (by decide)]
  rfl

private theorem bloom_width (x : Bloom) :
    encodedSize (.bytes x.toBytes.toByteArray) = 259 := by
  have upper : (Uint.toBeBytes 256).size ≤ 2 :=
    (Uint.size_toBeBytes_le_iff 256 2).mpr (by decide)
  have lower : ¬(Uint.toBeBytes 256).size ≤ 1 := by
    intro bound
    have := (Uint.size_toBeBytes_le_iff 256 1).mp bound
    omega
  have width : (Uint.toBeBytes 256).size = 2 := by omega
  rw [fixed_size _ 256 (by rw [Bytes.size_toByteArray, FixedBytes.size_toBytes])
    (by decide), ite_eq_right (by decide), width]

private theorem header_payload (h : Header) :
    (encodePayloadModel (headerFields h)).length =
      619 + encodedSize (ofNat h.difficulty) +
      encodedSize (ofNat h.number) +
      encodedSize (ofNat h.gasLimit) +
      encodedSize (ofNat h.gasUsed) +
      encodedSize (ofNat h.baseFeePerGas) +
      encodedSize (ofNat h.timestamp.toNat) +
      encodedSize (ofNat h.blobGasUsed.toNat) +
      encodedSize (ofNat h.excessBlobGas.toNat) +
      encodedSize (ofNat h.slotNumber.toNat) +
      encodedSize (.bytes h.extraData.toByteArray) := by
  simp only [length_encodePayloadModel, headerFields, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, hash_width, address_width, fixed32_width,
    nonce_width, bloom_width]
  omega

private theorem header_minimum (h : Header) :
    629 ≤ (encodePayloadModel (headerFields h)).length := by
  rw [header_payload]
  have := numeric_nonempty_wire h.difficulty
  have := numeric_nonempty_wire h.number
  have := numeric_nonempty_wire h.gasLimit
  have := numeric_nonempty_wire h.gasUsed
  have := numeric_nonempty_wire h.baseFeePerGas
  have := numeric_nonempty_wire h.timestamp.toNat
  have := numeric_nonempty_wire h.blobGasUsed.toNat
  have := numeric_nonempty_wire h.excessBlobGas.toNat
  have := numeric_nonempty_wire h.slotNumber.toNat
  have := bytes_nonempty_wire h.extraData.toByteArray
  omega

private theorem header_long_wire (h : Header) :
    (encodeOf h).data.toList =
      UInt8.ofNat (247 + (Uint.toBeBytes (encodePayloadModel (headerFields h)).length).size) ::
        (Uint.toBeBytes (encodePayloadModel (headerFields h)).length).toList ++
          encodePayloadModel (headerFields h) := by
  rw [encodeOf, header_model]
  exact encode_list_long _ (by have := header_minimum h; omega)

private theorem prevHeader_payload (h : PrevHeader) :
    (encodePayloadModel (prevHeaderFields h)).length =
      586 + encodedSize (ofNat h.difficulty) +
      encodedSize (ofNat h.number) +
      encodedSize (ofNat h.gasLimit) +
      encodedSize (ofNat h.gasUsed) +
      encodedSize (ofNat h.baseFeePerGas) +
      encodedSize (ofNat h.timestamp.toNat) +
      encodedSize (ofNat h.blobGasUsed.toNat) +
      encodedSize (ofNat h.excessBlobGas.toNat) +
      encodedSize (.bytes h.extraData.toByteArray) := by
  simp only [length_encodePayloadModel, prevHeaderFields, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, hash_width, address_width, fixed32_width,
    nonce_width, bloom_width]
  omega

private theorem prevHeader_minimum (h : PrevHeader) :
    595 ≤ (encodePayloadModel (prevHeaderFields h)).length := by
  rw [prevHeader_payload]
  have := numeric_nonempty_wire h.difficulty
  have := numeric_nonempty_wire h.number
  have := numeric_nonempty_wire h.gasLimit
  have := numeric_nonempty_wire h.gasUsed
  have := numeric_nonempty_wire h.baseFeePerGas
  have := numeric_nonempty_wire h.timestamp.toNat
  have := numeric_nonempty_wire h.blobGasUsed.toNat
  have := numeric_nonempty_wire h.excessBlobGas.toNat
  have := bytes_nonempty_wire h.extraData.toByteArray
  omega

private theorem prevHeader_long_wire (h : PrevHeader) :
    (encodeOf h).data.toList =
      UInt8.ofNat (247 + (Uint.toBeBytes (encodePayloadModel (prevHeaderFields h)).length).size) ::
        (Uint.toBeBytes (encodePayloadModel (prevHeaderFields h)).length).toList ++
          encodePayloadModel (prevHeaderFields h) := by
  rw [encodeOf, prevHeader_model]
  exact encode_list_long _ (by have := prevHeader_minimum h; omega)

private theorem header_wire_minimum (h : Header) :
    632 ≤ (encodeOf h).size := by
  have minimum := header_minimum h
  have digits : 2 ≤ (Uint.toBeBytes (encodePayloadModel (headerFields h)).length).size := by
    have notSmall : ¬(Uint.toBeBytes (encodePayloadModel (headerFields h)).length).size ≤ 1 := by
      intro width
      have := (Uint.size_toBeBytes_le_iff _ 1).mp width
      omega
    omega
  rw [header_size, ite_eq_right (by omega)]
  omega

private theorem prevHeader_wire_minimum (h : PrevHeader) :
    598 ≤ (encodeOf h).size := by
  have minimum := prevHeader_minimum h
  have digits : 2 ≤ (Uint.toBeBytes (encodePayloadModel (prevHeaderFields h)).length).size := by
    have notSmall :
        ¬(Uint.toBeBytes (encodePayloadModel (prevHeaderFields h)).length).size ≤ 1 := by
      intro width
      have := (Uint.size_toBeBytes_le_iff _ 1).mp width
      omega
    omega
  rw [prevHeader_size, ite_eq_right (by omega)]
  omega

private theorem hash_domain (x : Hash32) : Encodable (.bytes x.toBytes.toByteArray) := by
  rw [encodable_bytes_iff, Bytes.size_toByteArray, Hash32.size_toBytes]
  decide

private theorem address_domain (x : Address) : Encodable (.bytes x.toBytes.toByteArray) := by
  rw [encodable_bytes_iff, Bytes.size_toByteArray, Address.size_toBytes]
  decide

private theorem fixed_domain {n : Nat} (x : FixedBytes n) (bound : n < 2 ^ 64) :
    Encodable (.bytes x.toBytes.toByteArray) := by
  rw [encodable_bytes_iff, Bytes.size_toByteArray, FixedBytes.size_toBytes]
  exact bound

private theorem word_domain (x : U64) : Encodable (ofNat x.toNat) := by
  apply numeric_domain
  have := U64.toNat_lt x
  omega

private theorem timestamp_domain (x : U256) : Encodable (ofNat x.toNat) :=
  numeric_domain _ (U256.toNat_lt x)

private theorem extra_domain (x : Bytes) (bound : x.size < 2 ^ 64) :
    Encodable (.bytes x.toByteArray) := by
  rw [encodable_bytes_iff, Bytes.size_toByteArray]
  exact bound

private theorem header_assembled_domain (h : Header)
    (difficulty : h.difficulty < 2 ^ 256) (number : h.number < 2 ^ 256)
    (gasLimit : h.gasLimit < 2 ^ 256) (gasUsed : h.gasUsed < 2 ^ 256)
    (baseFee : h.baseFeePerGas < 2 ^ 256) (extra : h.extraData.size < 2 ^ 64)
    (payload : (encodePayloadModel (headerFields h)).length < 2 ^ 64) :
    Encodable (RlpEncode.toRlp h) := by
  rw [header_domain]
  refine ⟨?_, payload⟩
  simp only [headerFields, List.mem_cons, List.not_mem_nil, forall_eq_or_imp]
  exact ⟨hash_domain h.parentHash, hash_domain h.ommersHash, address_domain h.coinbase,
    hash_domain h.stateRoot, hash_domain h.transactionsRoot, hash_domain h.receiptRoot,
    fixed_domain h.bloom (by decide), numeric_domain _ difficulty, numeric_domain _ number,
    numeric_domain _ gasLimit, numeric_domain _ gasUsed, timestamp_domain h.timestamp,
    extra_domain _ extra, fixed_domain h.prevRandao (by decide),
    fixed_domain h.nonce (by decide), numeric_domain _ baseFee, hash_domain h.withdrawalsRoot,
    word_domain h.blobGasUsed, word_domain h.excessBlobGas, hash_domain h.parentBeaconBlockRoot,
    hash_domain h.requestsHash, hash_domain h.blockAccessListHash, word_domain h.slotNumber,
    by simp⟩

private theorem prevHeader_assembled_domain (h : PrevHeader)
    (difficulty : h.difficulty < 2 ^ 256) (number : h.number < 2 ^ 256)
    (gasLimit : h.gasLimit < 2 ^ 256) (gasUsed : h.gasUsed < 2 ^ 256)
    (baseFee : h.baseFeePerGas < 2 ^ 256) (extra : h.extraData.size < 2 ^ 64)
    (payload : (encodePayloadModel (prevHeaderFields h)).length < 2 ^ 64) :
    Encodable (RlpEncode.toRlp h) := by
  rw [prevHeader_domain]
  refine ⟨?_, payload⟩
  simp only [prevHeaderFields, List.mem_cons, List.not_mem_nil, forall_eq_or_imp]
  exact ⟨hash_domain h.parentHash, hash_domain h.ommersHash, address_domain h.coinbase,
    hash_domain h.stateRoot, hash_domain h.transactionsRoot, hash_domain h.receiptRoot,
    fixed_domain h.bloom (by decide), numeric_domain _ difficulty, numeric_domain _ number,
    numeric_domain _ gasLimit, numeric_domain _ gasUsed, timestamp_domain h.timestamp,
    extra_domain _ extra, fixed_domain h.prevRandao (by decide),
    fixed_domain h.nonce (by decide), numeric_domain _ baseFee, hash_domain h.withdrawalsRoot,
    word_domain h.blobGasUsed, word_domain h.excessBlobGas, hash_domain h.parentBeaconBlockRoot,
    hash_domain h.requestsHash, by simp⟩

end STFSpec.Conformance.Block.HeaderRlpCallerProofs
