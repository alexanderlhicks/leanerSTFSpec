/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.FixedBytes
import STFSpec.Base.U64
import STFSpec.Codec.SszEncode

/-!
# Stateless result serialization

Library `EthStateless`. The concrete four-field SSZ output container and zero sentinel.
This serializer accepts every value of its field types; it makes no guest outcome claim.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3–7.
-/

namespace STFSpec.Stateless

open Base Codec

/-- The fixed-width output record; EELS
`src/ethereum/forks/amsterdam/stateless.py:181–216` at the pin. -/
structure StatelessValidationResult where
  newPayloadRequestRoot : Hash32
  successfulValidation : Bool
  chainId : U64
  schemaId : UInt16

private def outputSchema : SszType := .container [.byteVector 32, .bool, .uint 8, .uint 2]

private def outputValue (r : StatelessValidationResult) : SszValue :=
  .container [.bytes r.newPayloadRequestRoot.toBytes.toByteArray,
    .bool r.successfulValidation, .uint r.chainId.toNat, .uint r.schemaId.toNat]

private theorem root_supported (r : StatelessValidationResult) :
    Ssz.Serializable (.byteVector 32) (.bytes r.newPayloadRequestRoot.toBytes.toByteArray) :=
  (Ssz.serializable_iff _ _).mpr (by
    change r.newPayloadRequestRoot.toBytes.toByteArray.size = 32
    rw [Bytes.size_toByteArray, Hash32.size_toBytes])

private theorem bool_supported (b : Bool) : Ssz.Serializable .bool (.bool b) :=
  (Ssz.serializable_iff _ _).mpr True.intro

private theorem uint_supported (w n : Nat)
    (hw : w = 2 ∨ w = 8) (hn : n < 2^(8*w)) :
    Ssz.Serializable (.uint w) (.uint n) :=
  (Ssz.serializable_iff _ _).mpr ⟨by omega, hn⟩

private theorem fixed_vector (n : Nat) : SszType.fixedSize? (.byteVector n) = some n :=
  SszType.fixedSize?_eq _

private theorem fixed_bool : SszType.fixedSize? .bool = some 1 := SszType.fixedSize?_eq _

private theorem fixed_uint (n : Nat) : SszType.fixedSize? (.uint n) = some n :=
  SszType.fixedSize?_eq _

private theorem output_supported (r : StatelessValidationResult) :
    Ssz.Serializable outputSchema (outputValue r) := by
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  · intro p hp
    change p ∈ [(.byteVector 32, .bytes r.newPayloadRequestRoot.toBytes.toByteArray),
      (.bool, .bool r.successfulValidation), (.uint 8, .uint r.chainId.toNat),
      (.uint 2, .uint r.schemaId.toNat)] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact root_supported r
    · exact bool_supported _
    · exact uint_supported 8 _ (Or.inr rfl) (U64.toNat_lt _)
    · exact uint_supported 2 _ (Or.inl rfl) (UInt16.toNat_lt _)
  · simp only [List.zip_cons_cons, List.zip_nil_right,
      List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
      fixed_vector, fixed_bool, fixed_uint, List.not_mem_nil]
    exact fun _ h ↦ h.elim

/-- Serialize the result with its concrete SSZ schema; EELS
`src/ethereum/forks/amsterdam/stateless_guest.py:19–23` at the pin. -/
def serializeStatelessOutput (r : StatelessValidationResult) : ByteArray :=
  Ssz.encode outputSchema (outputValue r) (output_supported r)

private def digits (w n : Nat) : List UInt8 :=
  (List.range w).map (fun i ↦ UInt8.ofNat ((n / 256^i) % 256))

private theorem bytes_ext {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b :=
  ByteArray.ext (Array.toList_inj.mp h)

private theorem uint_bytes (w n : Nat) (h : Ssz.Serializable (.uint w) (.uint n)) :
    Ssz.encode (.uint w) (.uint n) h = (digits w n).toByteArray := by
  apply bytes_ext
  simpa only [List.toList_data_toByteArray, digits] using Ssz.encode_eq (.uint w) (.uint n) h

/-- Complete output layout: every root byte, a 00/01 boolean, eight little-endian
chain-ID digits and two little-endian schema-ID digits, in that order. -/
theorem serializeStatelessOutput_eq (r : StatelessValidationResult) :
    (serializeStatelessOutput r).data.toList =
      r.newPayloadRequestRoot.toBytes.toList ++ [if r.successfulValidation then 1 else 0] ++
      (List.range 8).map (fun i ↦ UInt8.ofNat ((r.chainId.toNat / 256^i) % 256)) ++
      (List.range 2).map (fun i ↦ UInt8.ofNat ((r.schemaId.toNat / 256^i) % 256)) := by
  have hc := Ssz.encode_eq outputSchema (outputValue r) (output_supported r)
  let bs := [r.newPayloadRequestRoot.toBytes.toByteArray,
    ([if r.successfulValidation then 1 else 0] : List UInt8).toByteArray,
    (digits 8 r.chainId.toNat).toByteArray, (digits 2 r.schemaId.toNat).toByteArray]
  have hb : ∀ q ∈ ([.byteVector 32, .bool, .uint 8, .uint 2] : List SszType).zip
      [(.bytes r.newPayloadRequestRoot.toBytes.toByteArray : SszValue),
        .bool r.successfulValidation, .uint r.chainId.toNat, .uint r.schemaId.toNat] |>.zip bs,
      ∀ h : Ssz.Serializable q.1.1 q.1.2, Ssz.encode q.1.1 q.1.2 h = q.2 := by
    intro q hq h
    simp only [bs, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact bytes_ext (Ssz.encode_eq _ _ h)
    · apply bytes_ext
      simpa only [List.toList_data_toByteArray] using Ssz.encode_eq _ _ h
    · exact uint_bytes _ _ h
    · exact uint_bytes _ _ h
  have he := hc bs ⟨rfl, hb⟩
  simpa only [serializeStatelessOutput, outputSchema, outputValue, bs,
    List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fixed_vector, fixed_bool,
    fixed_uint, digits,
    Option.getD_some, List.toList_data_toByteArray, Bytes.toList_toByteArray,
    List.nil_append, List.append_nil] using he

/-- Every result serializes to exactly 43 bytes. -/
theorem serializeStatelessOutput_size (r : StatelessValidationResult) :
    (serializeStatelessOutput r).size = 43 := by
  change (serializeStatelessOutput r).data.size = 43
  have h := congrArg List.length (serializeStatelessOutput_eq r)
  simpa only [Array.length_toList, List.length_append, List.length_cons,
    List.length_nil, List.length_map, List.length_range, Bytes.length_toList,
    Hash32.size_toBytes, Nat.reduceAdd] using h

private theorem digits_eq_fixed (w n : Nat) :
    digits w n = (FixedBytes.ofLeNat (n := w) n).toBytes.toList := by
  rw [FixedBytes.toBytes_ofLeNat, Bytes.toList_generate]
  apply List.map_eq_map_iff.mpr
  intro i _
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_mul]
  apply UInt8.toNat_inj.mp
  change (n / 256^i) % 256 % 256 = (n / 256^i) % 256
  exact Nat.mod_mod _ _

private theorem digits_inj (w a b : Nat) (ha : a < 2^(8*w)) (hb : b < 2^(8*w))
    (h : digits w a = digits w b) : a = b := by
  rw [digits_eq_fixed, digits_eq_fixed, FixedBytes.toBytes_ofLeNat_eq_reverse,
    FixedBytes.toBytes_ofLeNat_eq_reverse, Bytes.toList_ofList, Bytes.toList_ofList] at h
  have he := List.reverse_inj.mp h
  have hf := FixedBytes.toBytes_inj.mp (Bytes.ext he)
  have hn := congrArg FixedBytes.toNat hf
  simpa only [FixedBytes.toNat_ofNat_of_lt _ ha, FixedBytes.toNat_ofNat_of_lt _ hb] using hn

/-- Equal serialized outputs preserve all four fields (serialization direction of
L-output-codec); no decoder premise or restricted schema-ID domain is required. -/
theorem serializeStatelessOutput_inj {a b : StatelessValidationResult} :
    serializeStatelessOutput a = serializeStatelessOutput b ↔ a = b := by
  constructor
  · intro h
    have he := congrArg (fun x : ByteArray ↦ x.data.toList) h
    rw [serializeStatelessOutput_eq, serializeStatelessOutput_eq] at he
    simp only [List.append_assoc] at he
    obtain ⟨hr, ht⟩ := List.append_inj he (by
      rw [Bytes.length_toList, Bytes.length_toList, Hash32.size_toBytes, Hash32.size_toBytes])
    have hr' := Hash32.toBytes_inj.mp (Bytes.ext hr)
    have hc := List.cons.inj ht
    have hv : a.successfulValidation = b.successfulValidation := by
      cases ha : a.successfulValidation <;> cases hb : b.successfulValidation <;>
        simp_all
    have htail : digits 8 a.chainId.toNat ++ digits 2 a.schemaId.toNat =
        digits 8 b.chainId.toNat ++ digits 2 b.schemaId.toNat := hc.2
    obtain ⟨hchain, hschema⟩ := List.append_inj htail (by
      simp only [digits, List.length_map, List.length_range])
    have hchain' := U64.toNat_inj.mp (digits_inj 8 _ _
      (U64.toNat_lt _) (U64.toNat_lt _) hchain)
    have hschema' := UInt16.toNat_inj.mp (digits_inj 2 _ _
      (UInt16.toNat_lt _) (UInt16.toNat_lt _) hschema)
    cases a
    cases b
    simp_all
  · exact congrArg serializeStatelessOutput

/-- Default failed output; EELS
`src/ethereum/forks/amsterdam/stateless_guest.py:41–50` at the pin. -/
def zeroSentinel : StatelessValidationResult :=
  ⟨Hash32.ofBytes32 (FixedBytes.ofNat 0), false, U64.zero, 0⟩

/-- Complete field equation for the zero sentinel. -/
theorem zeroSentinel_fields :
    zeroSentinel.newPayloadRequestRoot = Hash32.ofBytes32 (FixedBytes.ofNat 0) ∧
    zeroSentinel.successfulValidation = false ∧ zeroSentinel.chainId = U64.zero ∧
    zeroSentinel.schemaId = 0 := ⟨rfl, rfl, rfl, rfl⟩

/-- The complete serialized sentinel consists of exactly 43 zero bytes. -/
theorem serializeStatelessOutput_zeroSentinel :
    (serializeStatelessOutput zeroSentinel).data.toList = List.replicate 43 0 := by
  rw [serializeStatelessOutput_eq]
  rcases zeroSentinel_fields with ⟨hr, hv, hc, hs⟩
  rw [hr, hv, hc, hs, Hash32.toBytes_ofBytes32, FixedBytes.toBytes_ofNat,
    Bytes.toList_generate, U64.toNat_zero]
  decide

end STFSpec.Stateless
