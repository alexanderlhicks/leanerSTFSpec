/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Public RLP encoder caller proofs

Library `EthConformance`. Uses public byte/model/size/domain contracts only;
no temporary writer or replaceable Base storage is unfolded.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3/7/8.
-/

namespace STFSpec.Conformance.Codec.RlpEncodeCallerProofs

open STFSpec.Base STFSpec.Codec STFSpec.Codec.Rlp

example (x : RlpItem) : (encode x).data.toList = encodeModel x := toList_encode x
example (x : RlpItem) : (encode x).size = (encodeModel x).length := by
  rw [size_encode, encodedSize_eq_model_length]
example (x : RlpItem) : (encode x).size = encodedSize x := size_encode x
example (b : ByteArray) : encode (.bytes b) = encodeBytes b := encode_bytes b
example (b : ByteArray) (value : UInt8) (hs : b.size = 1)
    (hv : b[0]? = some value) (h : value.toNat < 128) :
    encodeBytes b = b := encodeBytes_single b value hs hv h
example (b : ByteArray) (h : 56 ≤ b.size) :
    (encodeBytes b).data.toList =
      UInt8.ofNat (183 + (Uint.toBeBytes b.size).size) ::
        (Uint.toBeBytes b.size).toList ++ b.data.toList := encodeBytes_long b h
example (short long : UInt8) (len : Nat) :
    (encodeLengthPrefix short long len).data.toList = lengthPrefixModel short long len :=
  toList_encodeLengthPrefix short long len
example (short long : UInt8) (len : Nat) :
    (encodeLengthPrefix short long len).size =
      if len < 56 then 1 else 1 + (Uint.toBeBytes len).size :=
  size_encodeLengthPrefix short long len
example (len : Nat) :
    (Uint.toBeBytes len).toList.foldl (fun a b ↦ 256 * a + b.toNat) 0 = len :=
  length_digits_value len
example (len k : Nat) : (Uint.toBeBytes len).size ≤ k ↔ len < 256 ^ k :=
  length_digits_width len k
example (b : ByteArray) : Encodable (.bytes b) ↔ b.size < 2 ^ 64 := encodable_bytes_iff b
example (xs : List RlpItem) :
    Encodable (.list xs) ↔ (∀ x ∈ xs, Encodable x) ∧
      (encodePayloadModel xs).length < 2 ^ 64 := encodable_list_iff xs
example (xs : List RlpItem) :
    (encodePayloadModel xs).length = (xs.map encodedSize).sum := length_encodePayloadModel xs
example (xs ys : List RlpItem) :
    encodePayloadModel (xs ++ ys) = encodePayloadModel xs ++ encodePayloadModel ys :=
  encodePayloadModel_append xs ys
example (xs : List RlpItem) :
    encodePayloadModel xs = xs.flatMap (fun child ↦ (encode child).data.toList) :=
  encodePayloadModel_eq_flatMap xs
example (x y : RlpItem) :
    (encode (.list [x, y])).data.toList =
      lengthPrefixModel 192 247 ((encode x).size + (encode y).size) ++
        (encode x).data.toList ++ (encode y).data.toList := by
  rw [toList_encode_list, encodePayloadModel_cons, encodePayloadModel_cons,
    encodePayloadModel_nil, List.append_nil, List.length_append,
    ← toList_encode x, ← toList_encode y, Array.length_toList, Array.length_toList]
  rw [List.append_assoc]
  rfl
example (xs : List RlpItem) :
    (encode (.list xs)).data.toList =
      lengthPrefixModel 192 247 (encodePayloadModel xs).length ++ encodePayloadModel xs :=
  toList_encode_list xs
example (xs : List RlpItem) (h : Encodable (.list xs)) :
    (UInt8.ofNat (247 + (Uint.toBeBytes (encodePayloadModel xs).length).size)).toNat =
      247 + (Uint.toBeBytes (encodePayloadModel xs).length).size := encodable_list_tag xs h
example (b : ByteArray) (h : Encodable (.bytes b)) :
    (UInt8.ofNat (183 + (Uint.toBeBytes b.size).size)).toNat =
      183 + (Uint.toBeBytes b.size).size := encodable_bytes_tag b h
-- Empty child and empty nested list both remain separate ordered payload components.
example (x : RlpItem) :
    encodePayloadModel [.bytes ByteArray.empty, .list [], x] =
      [128, 192] ++ (encode x).data.toList := by
  rw [encodePayloadModel_cons, encodePayloadModel_cons, encodePayloadModel_cons,
    encodePayloadModel_nil, List.append_nil, ← toList_encode x]
  have hb : encodeModel (.bytes ByteArray.empty) = [128] := by decide
  have hl : encodeModel (.list []) = [192] := by decide
  rw [hb, hl]
  rfl

end STFSpec.Conformance.Codec.RlpEncodeCallerProofs
