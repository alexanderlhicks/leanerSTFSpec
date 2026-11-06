/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block
import STFSpec.Codec.SszCountRecoverable

/-!
# Withdrawal schema clients and complete controls

Library `EthConformance`. Private clients use the public Block facade and Codec
laws. Complete literal controls check the local adapter and forward bytes, without
a source execution or a decoder claim.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–7.
-/

namespace STFSpec.Conformance.Block.WithdrawalSszControls

open STFSpec.Base STFSpec.Block STFSpec.Codec

private abbrev schema : SszSchema Withdrawal := Withdrawal.instSszSchema

private theorem metadata :
    (inferInstance : SszSchema Withdrawal) = Withdrawal.instSszSchema ∧
    schema.type = .container [.uint 8, .uint 8, .byteVector 20, .uint 8] ∧
    schema.fieldNames = ["index", "validator_index", "address", "amount"] ∧
    schema.valid = (fun _ ↦ True) := ⟨rfl, rfl, rfl, rfl⟩

private theorem complete_forward_value (a : Withdrawal) :
    schema.toValue a = .container [.uint a.index.toNat, .uint a.validatorIndex.toNat,
      .bytes a.address.toBytes.toByteArray, .uint a.amount.toNat] := rfl

private def inverse_signature : SszValue → Option Withdrawal := schema.ofValue?

private theorem word_bounds (a : Withdrawal) :
    a.index.toNat < 2 ^ 64 ∧ a.validatorIndex.toNat < 2 ^ 64 ∧ a.amount.toNat < 2 ^ 64 :=
  ⟨U64.toNat_lt a.index, U64.toNat_lt a.validatorIndex, U64.toNat_lt a.amount⟩

private theorem wf_signature : Withdrawal.instSszSchema.type.WellFormed :=
  Withdrawal.ssz_type_wellFormed

private theorem forward_signature : ∀ a, Withdrawal.instSszSchema.valid a →
    Withdrawal.instSszSchema.ofValue? (Withdrawal.instSszSchema.toValue a) = some a ∧
      SszValue.WellTyped Withdrawal.instSszSchema.type (Withdrawal.instSszSchema.toValue a) :=
  Withdrawal.ssz_ofValue_toValue

private theorem reverse_signature : ∀ v a,
    SszValue.WellTyped Withdrawal.instSszSchema.type v ∧
      Withdrawal.instSszSchema.ofValue? v = some a →
    Withdrawal.instSszSchema.valid a ∧ Withdrawal.instSszSchema.toValue a = v :=
  Withdrawal.ssz_toValue_ofValue

private theorem complete_roundtrip (a : Withdrawal) :
    schema.ofValue? (schema.toValue a) = some a ∧
      SszValue.WellTyped schema.type (schema.toValue a) :=
  Withdrawal.ssz_ofValue_toValue a True.intro

private theorem word_serializable (x : U64) :
    Ssz.Serializable (.uint 8) (.uint x.toNat) :=
  (Ssz.serializable_iff _ _).mpr ⟨by decide, U64.toNat_lt x⟩

private theorem address_serializable (x : Address) :
    Ssz.Serializable (.byteVector 20) (.bytes x.toBytes.toByteArray) :=
  (Ssz.serializable_iff _ _).mpr
    (by change x.toBytes.toByteArray.size = 20
        rw [Bytes.size_toByteArray, Address.size_toBytes])

private theorem actual_serializable (a : Withdrawal) :
    Ssz.Serializable schema.type (schema.toValue a) := by
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  · simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
      forall_eq_or_imp]
    exact ⟨word_serializable a.index, word_serializable a.validatorIndex,
      address_serializable a.address, word_serializable a.amount, by simp⟩
  · simp [SszType.fixedSize?_eq (.uint _), SszType.fixedSize?_eq (.byteVector _)]

private theorem actual_count_recoverable (a : Withdrawal) :
    Ssz.CountRecoverable schema.type (schema.toValue a) := by
  change Ssz.CountRecoverable (.container [.uint 8, .uint 8, .byteVector 20, .uint 8])
    (.container [.uint a.index.toNat, .uint a.validatorIndex.toNat,
      .bytes a.address.toBytes.toByteArray, .uint a.amount.toNat])
  simp [Ssz.countRecoverable_iff (.container _) (.container _),
    Ssz.countRecoverable_iff (.uint _) (.uint _),
    Ssz.countRecoverable_iff (.byteVector _) (.bytes _)]

private theorem fixed_width : schema.type.fixedSize? = some 44 := by
  change (SszType.container [.uint 8, .uint 8, .byteVector 20, .uint 8]).fixedSize? = _
  simp [SszType.fixedSize?_eq (.container _), SszType.fixedSize?_eq (.uint _),
    SszType.fixedSize?_eq (.byteVector _)]

private def digits (n : Nat) : List UInt8 :=
  (List.range 8).map (fun i ↦ UInt8.ofNat ((n / 256 ^ i) % 256))

private theorem word_bytes (x : U64) (h : Ssz.Serializable (.uint 8) (.uint x.toNat)) :
    Ssz.encode (.uint 8) (.uint x.toNat) h = (digits x.toNat).toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa [digits] using Ssz.encode_eq (.uint 8) (.uint x.toNat) h

private theorem address_bytes (x : Address)
    (h : Ssz.Serializable (.byteVector 20) (.bytes x.toBytes.toByteArray)) :
    Ssz.encode (.byteVector 20) (.bytes x.toBytes.toByteArray) h = x.toBytes.toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  exact Ssz.encode_eq (.byteVector 20) (.bytes x.toBytes.toByteArray) h

private theorem complete_layout (a : Withdrawal) :
    (SszSchema.encodeBytes a (actual_serializable a)).data.toList =
      digits a.index.toNat ++ digits a.validatorIndex.toNat ++
        a.address.toBytes.toByteArray.data.toList ++ digits a.amount.toNat := by
  rw [SszSchema.encodeBytes_eq]
  have layout := Ssz.encode_eq schema.type (schema.toValue a) (actual_serializable a)
  specialize layout [(digits a.index.toNat).toByteArray,
    (digits a.validatorIndex.toNat).toByteArray, a.address.toBytes.toByteArray,
    (digits a.amount.toNat).toByteArray]
  have certificates : ∀ q ∈
      [((SszType.uint 8, SszValue.uint a.index.toNat), (digits a.index.toNat).toByteArray),
       ((.uint 8, .uint a.validatorIndex.toNat), (digits a.validatorIndex.toNat).toByteArray),
       ((.byteVector 20, .bytes a.address.toBytes.toByteArray), a.address.toBytes.toByteArray),
       ((.uint 8, .uint a.amount.toNat), (digits a.amount.toNat).toByteArray)],
      ∀ hc : Ssz.Serializable q.1.1 q.1.2, Ssz.encode q.1.1 q.1.2 hc = q.2 := by
    simp only [List.mem_cons, List.not_mem_nil, forall_eq_or_imp]
    exact ⟨word_bytes a.index, word_bytes a.validatorIndex,
      address_bytes a.address, word_bytes a.amount, by simp⟩
  have result := layout ⟨rfl, certificates⟩
  simpa [schema, SszSchema.type, SszSchema.toValue, Withdrawal.instSszSchema,
    SszType.fixedSize?_eq (.uint _), SszType.fixedSize?_eq (.byteVector _),
    List.append_assoc] using result

private def observe (a : Withdrawal) : Nat × Nat × List Nat × Nat :=
  (a.index.toNat, a.validatorIndex.toNat, a.address.toBytes.toList.map UInt8.toNat,
    a.amount.toNat)

private def rawObserve : SszValue → Option (Nat × Nat × List Nat × Nat)
  | .container [.uint i, .uint j, .bytes b, .uint n] =>
      some (i, j, b.data.toList.map UInt8.toNat, n)
  | _ => none

private def control (i j : Nat) (address : List UInt8) (n : Nat)
    (expected : List Nat) : Bool :=
  let raw := SszValue.container [.uint i, .uint j, .bytes address.toByteArray, .uint n]
  let whole := (i, j, address.map UInt8.toNat, n)
  match schema.ofValue? raw with
  | none => false
  | some a =>
      observe a == whole && rawObserve (schema.toValue a) == some whole &&
      (schema.ofValue? (schema.toValue a)).map observe == some whole &&
      (SszSchema.encodeBytes a (actual_serializable a)).data.toList.map UInt8.toNat == expected

/- Whole inputs and outputs were independently calculated before the target implementation.
The tests retain all four fields and every byte, including the amount in Gwei. -/

-- zero
#guard control 0 0
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

-- max
#guard control 18446744073709551615 18446744073709551615
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
  255, 255] 18446744073709551615
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
  255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
  255, 255, 255, 255, 255, 255, 255, 255]

-- distinct-ascending
#guard control 81985529216486895 18364758544493064720
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] 9833440827789222417
  [239, 205, 171, 137, 103, 69, 35, 1, 16, 50, 84, 118, 152, 186, 220, 254, 0, 1, 2, 3, 4, 5,
  6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 17, 34, 51, 68, 85, 102, 119, 136]

-- distinct-reversed
#guard control 81985529216486895 18364758544493064720
  [19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] 9833440827789222417
  [239, 205, 171, 137, 103, 69, 35, 1, 16, 50, 84, 118, 152, 186, 220, 254, 19, 18, 17, 16,
  15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 17, 34, 51, 68, 85, 102, 119, 136]

-- index-0
#guard control 0 9833440827789222417
  [11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202]
  17357102489901502592
  [0, 0, 0, 0, 0, 0, 0, 0, 17, 34, 51, 68, 85, 102, 119, 136, 11, 48, 85, 122, 159, 196, 233,
  14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 128, 144, 160, 176, 192, 208,
  224, 240]

-- index-1
#guard control 1 9833440827789222417
  [11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202]
  17357102489901502592
  [1, 0, 0, 0, 0, 0, 0, 0, 17, 34, 51, 68, 85, 102, 119, 136, 11, 48, 85, 122, 159, 196, 233,
  14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 128, 144, 160, 176, 192, 208,
  224, 240]

-- index-255
#guard control 255 9833440827789222417
  [11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202]
  17357102489901502592
  [255, 0, 0, 0, 0, 0, 0, 0, 17, 34, 51, 68, 85, 102, 119, 136, 11, 48, 85, 122, 159, 196,
  233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 128, 144, 160, 176, 192,
  208, 224, 240]

-- index-256
#guard control 256 9833440827789222417
  [11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202]
  17357102489901502592
  [0, 1, 0, 0, 0, 0, 0, 0, 17, 34, 51, 68, 85, 102, 119, 136, 11, 48, 85, 122, 159, 196, 233,
  14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 128, 144, 160, 176, 192, 208,
  224, 240]

-- index-2p63
#guard control 9223372036854775808 9833440827789222417
  [11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202]
  17357102489901502592
  [0, 0, 0, 0, 0, 0, 0, 128, 17, 34, 51, 68, 85, 102, 119, 136, 11, 48, 85, 122, 159, 196,
  233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 128, 144, 160, 176, 192,
  208, 224, 240]

-- index-max
#guard control 18446744073709551615 9833440827789222417
  [11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202]
  17357102489901502592
  [255, 255, 255, 255, 255, 255, 255, 255, 17, 34, 51, 68, 85, 102, 119, 136, 11, 48, 85, 122,
  159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 128, 144, 160,
  176, 192, 208, 224, 240]

-- validatorIndex-0
#guard control 1161981756646125696 0
  [11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202]
  17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 0, 0, 0, 0, 0, 0, 0, 0, 11, 48, 85, 122, 159, 196, 233,
  14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 128, 144, 160, 176, 192, 208,
  224, 240]

-- validatorIndex-1
#guard control 1161981756646125696 1
  [11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202]
  17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 1, 0, 0, 0, 0, 0, 0, 0, 11, 48, 85, 122, 159, 196, 233,
  14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 128, 144, 160, 176, 192, 208,
  224, 240]

-- validatorIndex-255
#guard control 1161981756646125696 255
  [11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202]
  17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 255, 0, 0, 0, 0, 0, 0, 0, 11, 48, 85, 122, 159, 196, 233,
  14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 128, 144, 160, 176, 192, 208,
  224, 240]

-- validatorIndex-256
#guard control 1161981756646125696 256
  [11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202]
  17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 0, 1, 0, 0, 0, 0, 0, 0, 11, 48, 85, 122, 159, 196, 233,
  14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 128, 144, 160, 176, 192, 208,
  224, 240]

-- validatorIndex-2p63
#guard control 1161981756646125696 9223372036854775808
  [11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202]
  17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 0, 0, 0, 0, 0, 0, 0, 128, 11, 48, 85, 122, 159, 196, 233,
  14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 128, 144, 160, 176, 192, 208,
  224, 240]

-- validatorIndex-max
#guard control 1161981756646125696 18446744073709551615
  [11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202]
  17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 255, 255, 255, 255, 255, 255, 255, 255, 11, 48, 85, 122,
  159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 128, 144, 160,
  176, 192, 208, 224, 240]

-- amount-0
#guard control 1161981756646125696 9833440827789222417
  [11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202] 0
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 11, 48, 85, 122, 159,
  196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 0, 0, 0, 0, 0, 0, 0, 0]

-- amount-1
#guard control 1161981756646125696 9833440827789222417
  [11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202] 1
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 11, 48, 85, 122, 159,
  196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 1, 0, 0, 0, 0, 0, 0, 0]

-- amount-255
#guard control 1161981756646125696 9833440827789222417
  [11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202] 255
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 11, 48, 85, 122, 159,
  196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 255, 0, 0, 0, 0, 0, 0,
  0]

-- amount-256
#guard control 1161981756646125696 9833440827789222417
  [11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202] 256
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 11, 48, 85, 122, 159,
  196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 0, 1, 0, 0, 0, 0, 0, 0]

-- amount-2p63
#guard control 1161981756646125696 9833440827789222417
  [11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202]
  9223372036854775808
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 11, 48, 85, 122, 159,
  196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 0, 0, 0, 0, 0, 0, 0,
  128]

-- amount-max
#guard control 1161981756646125696 9833440827789222417
  [11, 48, 85, 122, 159, 196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202]
  18446744073709551615
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 11, 48, 85, 122, 159,
  196, 233, 14, 51, 88, 125, 162, 199, 236, 17, 54, 91, 128, 165, 202, 255, 255, 255, 255,
  255, 255, 255, 255]

-- address-leading-zero
#guard control 1161981756646125696 9833440827789222417
  [0, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]
  17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 0, 17, 18, 19, 20, 21,
  22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 128, 144, 160, 176, 192, 208, 224,
  240]

-- address-trailing-zero
#guard control 1161981756646125696 9833440827789222417
  [81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 0]
  17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 81, 82, 83, 84, 85,
  86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 0, 128, 144, 160, 176, 192, 208,
  224, 240]

-- address-marker-00
#guard control 1161981756646125696 9833440827789222417
  [128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 128, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 144, 160, 176, 192, 208, 224, 240]

-- address-marker-01
#guard control 1161981756646125696 9833440827789222417
  [0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 0, 128, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 144, 160, 176, 192, 208, 224, 240]

-- address-marker-02
#guard control 1161981756646125696 9833440827789222417
  [0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 0, 0, 128, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 144, 160, 176, 192, 208, 224, 240]

-- address-marker-03
#guard control 1161981756646125696 9833440827789222417
  [0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 0, 0, 0, 128, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 144, 160, 176, 192, 208, 224, 240]

-- address-marker-04
#guard control 1161981756646125696 9833440827789222417
  [0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 0, 0, 0, 0, 128, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 144, 160, 176, 192, 208, 224, 240]

-- address-marker-05
#guard control 1161981756646125696 9833440827789222417
  [0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 0, 0, 0, 0, 0, 128, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 144, 160, 176, 192, 208, 224, 240]

-- address-marker-06
#guard control 1161981756646125696 9833440827789222417
  [0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 0, 0, 0, 0, 0, 0, 128,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 144, 160, 176, 192, 208, 224, 240]

-- address-marker-07
#guard control 1161981756646125696 9833440827789222417
  [0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 0, 0, 0, 0, 0, 0, 0,
  128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 144, 160, 176, 192, 208, 224, 240]

-- address-marker-08
#guard control 1161981756646125696 9833440827789222417
  [0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 0, 0, 0, 0, 0, 0, 0,
  0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 144, 160, 176, 192, 208, 224, 240]

-- address-marker-09
#guard control 1161981756646125696 9833440827789222417
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 144, 160, 176, 192, 208, 224, 240]

-- address-marker-10
#guard control 1161981756646125696 9833440827789222417
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0] 17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 144, 160, 176, 192, 208, 224, 240]

-- address-marker-11
#guard control 1161981756646125696 9833440827789222417
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0] 17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 128, 144, 160, 176, 192, 208, 224, 240]

-- address-marker-12
#guard control 1161981756646125696 9833440827789222417
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0] 17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 128, 144, 160, 176, 192, 208, 224, 240]

-- address-marker-13
#guard control 1161981756646125696 9833440827789222417
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0] 17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 128, 144, 160, 176, 192, 208, 224, 240]

-- address-marker-14
#guard control 1161981756646125696 9833440827789222417
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0] 17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 128, 144, 160, 176, 192, 208, 224, 240]

-- address-marker-15
#guard control 1161981756646125696 9833440827789222417
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0] 17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 128, 144, 160, 176, 192, 208, 224, 240]

-- address-marker-16
#guard control 1161981756646125696 9833440827789222417
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0] 17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 128, 144, 160, 176, 192, 208, 224, 240]

-- address-marker-17
#guard control 1161981756646125696 9833440827789222417
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0] 17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 128, 144, 160, 176, 192, 208, 224, 240]

-- address-marker-18
#guard control 1161981756646125696 9833440827789222417
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0] 17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 128, 144, 160, 176, 192, 208, 224, 240]

-- address-marker-19
#guard control 1161981756646125696 9833440827789222417
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128] 17357102489901502592
  [128, 112, 96, 80, 64, 48, 32, 16, 17, 34, 51, 68, 85, 102, 119, 136, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 128, 144, 160, 176, 192, 208, 224, 240]

private def fails (v : SszValue) : Bool := (schema.ofValue? v).isNone

#guard fails (.uint 0)
#guard fails (.bool false)
#guard fails (.bytes ByteArray.empty)
#guard fails (.list [])
#guard fails (.container [])
#guard fails (.container [.uint 0])
#guard fails (.container [.uint 0, .uint 0, .bytes ByteArray.empty])
#guard fails (.container
  [.uint 0, .uint 0, .bytes ((List.replicate 20 0).toByteArray), .uint 0, .uint 0])
#guard fails (.container
  [.bytes ByteArray.empty, .uint 29,
    .bytes ((List.range 20).map UInt8.ofNat).toByteArray, .uint 43])
#guard fails (.container
  [.bool false, .uint 29, .bytes ((List.range 20).map UInt8.ofNat).toByteArray, .uint 43])
#guard fails (.container
  [.list [], .uint 29, .bytes ((List.range 20).map UInt8.ofNat).toByteArray, .uint 43])
#guard fails (.container
  [.container [], .uint 29, .bytes ((List.range 20).map UInt8.ofNat).toByteArray, .uint 43])
#guard fails (.container
  [.uint 17, .bytes ByteArray.empty,
    .bytes ((List.range 20).map UInt8.ofNat).toByteArray, .uint 43])
#guard fails (.container
  [.uint 17, .bool false, .bytes ((List.range 20).map UInt8.ofNat).toByteArray, .uint 43])
#guard fails (.container
  [.uint 17, .list [], .bytes ((List.range 20).map UInt8.ofNat).toByteArray, .uint 43])
#guard fails (.container
  [.uint 17, .container [], .bytes ((List.range 20).map UInt8.ofNat).toByteArray, .uint 43])
#guard fails (.container [.uint 17, .uint 29, .uint 20, .uint 43])
#guard fails (.container [.uint 17, .uint 29, .bool false, .uint 43])
#guard fails (.container [.uint 17, .uint 29, .list [], .uint 43])
#guard fails (.container [.uint 17, .uint 29, .container [], .uint 43])
#guard fails (.container
  [.uint 17, .uint 29,
    .bytes ((List.range 20).map UInt8.ofNat).toByteArray, .bytes ByteArray.empty])
#guard fails (.container
  [.uint 17, .uint 29, .bytes ((List.range 20).map UInt8.ofNat).toByteArray, .bool false])
#guard fails (.container
  [.uint 17, .uint 29, .bytes ((List.range 20).map UInt8.ofNat).toByteArray, .list []])
#guard fails (.container
  [.uint 17, .uint 29, .bytes ((List.range 20).map UInt8.ofNat).toByteArray, .container []])
#guard fails (.container
  [.uint (2 ^ 64), .uint 29, .bytes ((List.range 20).map UInt8.ofNat).toByteArray, .uint 43])
#guard fails (.container
  [.uint (2 ^ 64 + 1), .uint 29, .bytes ((List.range 20).map UInt8.ofNat).toByteArray, .uint 43])
#guard fails (.container
  [.uint 17, .uint (2 ^ 64), .bytes ((List.range 20).map UInt8.ofNat).toByteArray, .uint 43])
#guard fails (.container
  [.uint 17, .uint (2 ^ 64 + 1), .bytes ((List.range 20).map UInt8.ofNat).toByteArray, .uint 43])
#guard fails (.container
  [.uint 17, .uint 29, .bytes ((List.range 20).map UInt8.ofNat).toByteArray, .uint (2 ^ 64)])
#guard fails (.container
  [.uint 17, .uint 29, .bytes ((List.range 20).map UInt8.ofNat).toByteArray, .uint (2 ^ 64 + 1)])
#guard fails (.container [.uint 17, .uint 29, .bytes ((List.replicate 0 0).toByteArray), .uint 43])
#guard fails (.container
  [.uint 17, .uint 29, .bytes ((List.replicate 19 0).toByteArray), .uint 43])
#guard fails (.container
  [.uint 17, .uint 29, .bytes ((List.replicate 21 0).toByteArray), .uint 43])
#guard fails (.container [.uint (2 ^ 64), .uint 0, .bytes ByteArray.empty, .uint 0])

end STFSpec.Conformance.Block.WithdrawalSszControls
