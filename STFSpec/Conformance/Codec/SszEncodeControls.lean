/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Complete SSZ forward serialization controls

Library `EthConformance`. Sixty-one independent literal byte cases cover supported
scalars, bytes, lists, nested mixed containers, equal offsets, fixed-zero fields,
sparse masks and intentional mathematical extensions. The original-source test
matrix independently fixes every expected byte; source class/backing/host
admission and general refinement remain separate.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

open STFSpec.Codec

-- u1_zero: eels_dataclass; 1 zero little-endian bytes.
private theorem support_u1_zero : Ssz.Serializable (.uint 1) (.uint 0) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_u1_zero : ByteArray :=
  Ssz.encode (.uint 1) (.uint 0) support_u1_zero
private def expected_u1_zero : ByteArray := (⟨#[0]⟩ : ByteArray)

-- u1_max: eels_dataclass; 1 maximal little-endian bytes.
private theorem support_u1_max : Ssz.Serializable (.uint 1) (.uint 255) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_u1_max : ByteArray :=
  Ssz.encode (.uint 1) (.uint 255) support_u1_max
private def expected_u1_max : ByteArray := (⟨#[255]⟩ : ByteArray)

-- u1_pattern: eels_dataclass; low-to-high bytes 01 through 01.
private theorem support_u1_pattern : Ssz.Serializable (.uint 1) (.uint 1) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_u1_pattern : ByteArray :=
  Ssz.encode (.uint 1) (.uint 1) support_u1_pattern
private def expected_u1_pattern : ByteArray := (⟨#[1]⟩ : ByteArray)

-- u2_zero: eels_dataclass; 2 zero little-endian bytes.
private theorem support_u2_zero : Ssz.Serializable (.uint 2) (.uint 0) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_u2_zero : ByteArray :=
  Ssz.encode (.uint 2) (.uint 0) support_u2_zero
private def expected_u2_zero : ByteArray := (⟨#[0, 0]⟩ : ByteArray)

-- u2_max: eels_dataclass; 2 maximal little-endian bytes.
private theorem support_u2_max : Ssz.Serializable (.uint 2) (.uint 65535) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_u2_max : ByteArray :=
  Ssz.encode (.uint 2) (.uint 65535) support_u2_max
private def expected_u2_max : ByteArray := (⟨#[255, 255]⟩ : ByteArray)

-- u2_pattern: eels_dataclass; low-to-high bytes 01 through 02.
private theorem support_u2_pattern : Ssz.Serializable (.uint 2) (.uint 513) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_u2_pattern : ByteArray :=
  Ssz.encode (.uint 2) (.uint 513) support_u2_pattern
private def expected_u2_pattern : ByteArray := (⟨#[1, 2]⟩ : ByteArray)

-- u4_zero: eels_dataclass; 4 zero little-endian bytes.
private theorem support_u4_zero : Ssz.Serializable (.uint 4) (.uint 0) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_u4_zero : ByteArray :=
  Ssz.encode (.uint 4) (.uint 0) support_u4_zero
private def expected_u4_zero : ByteArray := (⟨#[0, 0, 0, 0]⟩ : ByteArray)

-- u4_max: eels_dataclass; 4 maximal little-endian bytes.
private theorem support_u4_max : Ssz.Serializable (.uint 4) (.uint 4294967295) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_u4_max : ByteArray :=
  Ssz.encode (.uint 4) (.uint 4294967295) support_u4_max
private def expected_u4_max : ByteArray := (⟨#[255, 255, 255, 255]⟩ : ByteArray)

-- u4_pattern: eels_dataclass; low-to-high bytes 01 through 04.
private theorem support_u4_pattern : Ssz.Serializable (.uint 4) (.uint 67305985) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_u4_pattern : ByteArray :=
  Ssz.encode (.uint 4) (.uint 67305985) support_u4_pattern
private def expected_u4_pattern : ByteArray := (⟨#[1, 2, 3, 4]⟩ : ByteArray)

-- u8_zero: eels_dataclass; 8 zero little-endian bytes.
private theorem support_u8_zero : Ssz.Serializable (.uint 8) (.uint 0) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_u8_zero : ByteArray :=
  Ssz.encode (.uint 8) (.uint 0) support_u8_zero
private def expected_u8_zero : ByteArray := (⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩ : ByteArray)

-- u8_max: eels_dataclass; 8 maximal little-endian bytes.
private theorem support_u8_max : Ssz.Serializable (.uint 8) (.uint 18446744073709551615) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_u8_max : ByteArray :=
  Ssz.encode (.uint 8) (.uint 18446744073709551615) support_u8_max
private def expected_u8_max : ByteArray := (⟨#[255, 255, 255, 255, 255, 255, 255, 255]⟩ : ByteArray)

-- u8_pattern: eels_dataclass; low-to-high bytes 01 through 08.
private theorem support_u8_pattern : Ssz.Serializable (.uint 8) (.uint 578437695752307201) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_u8_pattern : ByteArray :=
  Ssz.encode (.uint 8) (.uint 578437695752307201) support_u8_pattern
private def expected_u8_pattern : ByteArray := (⟨#[1, 2, 3, 4, 5, 6, 7, 8]⟩ : ByteArray)

-- u16_zero: eels_dataclass; 16 zero little-endian bytes.
private theorem support_u16_zero : Ssz.Serializable (.uint 16) (.uint 0) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_u16_zero : ByteArray :=
  Ssz.encode (.uint 16) (.uint 0) support_u16_zero
private def expected_u16_zero : ByteArray := (⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩
  : ByteArray)

-- u16_max: eels_dataclass; 16 maximal little-endian bytes.
private theorem support_u16_max : Ssz.Serializable (.uint 16) (.uint
  340282366920938463463374607431768211455) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_u16_max : ByteArray :=
  Ssz.encode (.uint 16) (.uint 340282366920938463463374607431768211455) support_u16_max
private def expected_u16_max : ByteArray := (⟨#[255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
  255, 255, 255, 255, 255, 255]⟩ : ByteArray)

-- u16_pattern: eels_dataclass; low-to-high bytes 01 through 10.
private theorem support_u16_pattern : Ssz.Serializable (.uint 16) (.uint
  21345817372864405881847059188222722561) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_u16_pattern : ByteArray :=
  Ssz.encode (.uint 16) (.uint 21345817372864405881847059188222722561) support_u16_pattern
private def expected_u16_pattern : ByteArray := (⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
  15, 16]⟩ : ByteArray)

-- u32_zero: eels_dataclass; 32 zero little-endian bytes.
private theorem support_u32_zero : Ssz.Serializable (.uint 32) (.uint 0) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_u32_zero : ByteArray :=
  Ssz.encode (.uint 32) (.uint 0) support_u32_zero
private def expected_u32_zero : ByteArray := (⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ : ByteArray)

-- u32_max: eels_dataclass; 32 maximal little-endian bytes.
private theorem support_u32_max : Ssz.Serializable (.uint 32) (.uint
  115792089237316195423570985008687907853269984665640564039457584007913129639935) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_u32_max : ByteArray :=
  Ssz.encode (.uint 32) (.uint
    115792089237316195423570985008687907853269984665640564039457584007913129639935)
    support_u32_max
private def expected_u32_max : ByteArray := (⟨#[255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
  255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
  255, 255, 255]⟩ : ByteArray)

-- u32_pattern: eels_dataclass; low-to-high bytes 01 through 20.
private theorem support_u32_pattern : Ssz.Serializable (.uint 32) (.uint
  14528991250861404666834535435384615765856667510756806797353855100662256435713) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_u32_pattern : ByteArray :=
  Ssz.encode (.uint 32) (.uint
    14528991250861404666834535435384615765856667510756806797353855100662256435713)
    support_u32_pattern
private def expected_u32_pattern : ByteArray := (⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
  15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]⟩ : ByteArray)

-- bool_false: eels_dataclass; false byte.
private theorem support_bool_false : Ssz.Serializable .bool (.bool false) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_bool_false : ByteArray :=
  Ssz.encode .bool (.bool false) support_bool_false
private def expected_bool_false : ByteArray := (⟨#[0]⟩ : ByteArray)

-- bool_true: eels_dataclass; true byte.
private theorem support_bool_true : Ssz.Serializable .bool (.bool true) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_bool_true : ByteArray :=
  Ssz.encode .bool (.bool true) support_bool_true
private def expected_bool_true : ByteArray := (⟨#[1]⟩ : ByteArray)

-- vector0: eels_dataclass; exact raw bytes, no header or padding.
private theorem support_vector0 : Ssz.Serializable (.byteVector 0) (.bytes (⟨#[]⟩ : ByteArray)) :=
  by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_vector0 : ByteArray :=
  Ssz.encode (.byteVector 0) (.bytes (⟨#[]⟩ : ByteArray)) support_vector0
private def expected_vector0 : ByteArray := (⟨#[]⟩ : ByteArray)

-- vector1: eels_dataclass; exact raw bytes, no header or padding.
private theorem support_vector1 : Ssz.Serializable (.byteVector 1) (.bytes (⟨#[165]⟩ : ByteArray))
  := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_vector1 : ByteArray :=
  Ssz.encode (.byteVector 1) (.bytes (⟨#[165]⟩ : ByteArray)) support_vector1
private def expected_vector1 : ByteArray := (⟨#[165]⟩ : ByteArray)

-- vector3: eels_dataclass; exact raw bytes, no header or padding.
private theorem support_vector3 : Ssz.Serializable (.byteVector 3) (.bytes (⟨#[0, 165, 255]⟩ :
  ByteArray)) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_vector3 : ByteArray :=
  Ssz.encode (.byteVector 3) (.bytes (⟨#[0, 165, 255]⟩ : ByteArray)) support_vector3
private def expected_vector3 : ByteArray := (⟨#[0, 165, 255]⟩ : ByteArray)

-- vector32: eels_dataclass; exact raw bytes, no header or padding.
private theorem support_vector32 : Ssz.Serializable (.byteVector 32) (.bytes (⟨#[1, 35, 69, 103,
  137, 171, 205, 239, 1, 35, 69, 103, 137, 171, 205, 239, 1, 35, 69, 103, 137, 171, 205, 239, 1,
  35, 69, 103, 137, 171, 205, 239]⟩ : ByteArray)) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_vector32 : ByteArray :=
  Ssz.encode (.byteVector 32) (.bytes (⟨#[1, 35, 69, 103, 137, 171, 205, 239, 1, 35, 69, 103, 137,
    171, 205, 239, 1, 35, 69, 103, 137, 171, 205, 239, 1, 35, 69, 103, 137, 171, 205, 239]⟩ :
    ByteArray)) support_vector32
private def expected_vector32 : ByteArray := (⟨#[1, 35, 69, 103, 137, 171, 205, 239, 1, 35, 69,
  103, 137, 171, 205, 239, 1, 35, 69, 103, 137, 171, 205, 239, 1, 35, 69, 103, 137, 171, 205,
  239]⟩ : ByteArray)

-- bl0: eels_dataclass; raw byte-list payload, no length prefix.
private theorem support_bl0 : Ssz.Serializable (.byteList 0) (.bytes (⟨#[]⟩ : ByteArray)) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_bl0 : ByteArray :=
  Ssz.encode (.byteList 0) (.bytes (⟨#[]⟩ : ByteArray)) support_bl0
private def expected_bl0 : ByteArray := (⟨#[]⟩ : ByteArray)

-- bl4_empty: eels_dataclass; raw byte-list payload, no length prefix.
private theorem support_bl4_empty : Ssz.Serializable (.byteList 4) (.bytes (⟨#[]⟩ : ByteArray)) :=
  by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_bl4_empty : ByteArray :=
  Ssz.encode (.byteList 4) (.bytes (⟨#[]⟩ : ByteArray)) support_bl4_empty
private def expected_bl4_empty : ByteArray := (⟨#[]⟩ : ByteArray)

-- bl4_full: eels_dataclass; raw byte-list payload, no length prefix.
private theorem support_bl4_full : Ssz.Serializable (.byteList 4) (.bytes (⟨#[0, 165, 255, 126]⟩ :
  ByteArray)) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_bl4_full : ByteArray :=
  Ssz.encode (.byteList 4) (.bytes (⟨#[0, 165, 255, 126]⟩ : ByteArray)) support_bl4_full
private def expected_bl4_full : ByteArray := (⟨#[0, 165, 255, 126]⟩ : ByteArray)

-- pbytes_empty: eels_dataclass; raw byte-list payload, no length prefix.
private theorem support_pbytes_empty : Ssz.Serializable .progressiveByteList (.bytes (⟨#[]⟩ :
  ByteArray)) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_pbytes_empty : ByteArray :=
  Ssz.encode .progressiveByteList (.bytes (⟨#[]⟩ : ByteArray)) support_pbytes_empty
private def expected_pbytes_empty : ByteArray := (⟨#[]⟩ : ByteArray)

-- pbytes: eels_dataclass; raw byte-list payload, no length prefix.
private theorem support_pbytes : Ssz.Serializable .progressiveByteList (.bytes (⟨#[0, 165, 255,
  126]⟩ : ByteArray)) := by
  apply (Ssz.serializable_iff _ _).mpr
  decide
private def output_pbytes : ByteArray :=
  Ssz.encode .progressiveByteList (.bytes (⟨#[0, 165, 255, 126]⟩ : ByteArray)) support_pbytes
private def expected_pbytes : ByteArray := (⟨#[0, 165, 255, 126]⟩ : ByteArray)

-- list_u16_empty: eels_dataclass; fixed children concatenate; dynamic children use listed
-- four-byte starts and ordered payloads.
private theorem support_list_u16_empty : Ssz.Serializable (.list (.uint 2) 4) (.list []) := by
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simp
private def output_list_u16_empty : ByteArray :=
  Ssz.encode (.list (.uint 2) 4) (.list []) support_list_u16_empty
private def expected_list_u16_empty : ByteArray := (⟨#[]⟩ : ByteArray)

-- list_u16: eels_dataclass; fixed children concatenate; dynamic children use listed four-byte
-- starts and ordered payloads.
private theorem support_list_u16 : Ssz.Serializable (.list (.uint 2) 4) (.list [(.uint 0), (.uint
  513), (.uint 65535)]) := by
  have h0 : Ssz.Serializable (.uint 2) (.uint 0) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h1 : Ssz.Serializable (.uint 2) (.uint 513) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h2 : Ssz.Serializable (.uint 2) (.uint 65535) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa using (show Ssz.Serializable (.uint 2) (.uint 0) ∧ Ssz.Serializable (.uint 2) (.uint 513)
    ∧ Ssz.Serializable (.uint 2) (.uint 65535) from ⟨h0, ⟨h1, h2⟩⟩)
private def output_list_u16 : ByteArray :=
  Ssz.encode (.list (.uint 2) 4) (.list [(.uint 0), (.uint 513), (.uint 65535)]) support_list_u16
private def expected_list_u16 : ByteArray := (⟨#[0, 0, 1, 2, 255, 255]⟩ : ByteArray)

-- plist_u16: eels_dataclass; fixed children concatenate; dynamic children use listed four-byte
-- starts and ordered payloads.
private theorem support_plist_u16 : Ssz.Serializable (.progressiveList (.uint 2)) (.list [(.uint
  0), (.uint 513), (.uint 65535)]) := by
  have h0 : Ssz.Serializable (.uint 2) (.uint 0) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h1 : Ssz.Serializable (.uint 2) (.uint 513) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h2 : Ssz.Serializable (.uint 2) (.uint 65535) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨?_, by decide⟩
  simpa using (show Ssz.Serializable (.uint 2) (.uint 0) ∧ Ssz.Serializable (.uint 2) (.uint 513)
    ∧ Ssz.Serializable (.uint 2) (.uint 65535) from ⟨h0, ⟨h1, h2⟩⟩)
private def output_plist_u16 : ByteArray :=
  Ssz.encode (.progressiveList (.uint 2)) (.list [(.uint 0), (.uint 513), (.uint 65535)])
    support_plist_u16
private def expected_plist_u16 : ByteArray := (⟨#[0, 0, 1, 2, 255, 255]⟩ : ByteArray)

-- list_bool: eels_dataclass; fixed children concatenate; dynamic children use listed four-byte
-- starts and ordered payloads.
private theorem support_list_bool : Ssz.Serializable (.list .bool 4) (.list [(.bool false), (.bool
  true), (.bool false)]) := by
  have h0 : Ssz.Serializable .bool (.bool false) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h1 : Ssz.Serializable .bool (.bool true) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h2 : Ssz.Serializable .bool (.bool false) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa using (show Ssz.Serializable .bool (.bool false) ∧ Ssz.Serializable .bool (.bool true) ∧
    Ssz.Serializable .bool (.bool false) from ⟨h0, ⟨h1, h2⟩⟩)
private def output_list_bool : ByteArray :=
  Ssz.encode (.list .bool 4) (.list [(.bool false), (.bool true), (.bool false)]) support_list_bool
private def expected_list_bool : ByteArray := (⟨#[0, 1, 0]⟩ : ByteArray)

-- list_vec0_empty: eels_dataclass; fixed children concatenate; dynamic children use listed
-- four-byte starts and ordered payloads.
private theorem support_list_vec0_empty : Ssz.Serializable (.list (.byteVector 0) 4) (.list []) :=
  by
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simp
private def output_list_vec0_empty : ByteArray :=
  Ssz.encode (.list (.byteVector 0) 4) (.list []) support_list_vec0_empty
private def expected_list_vec0_empty : ByteArray := (⟨#[]⟩ : ByteArray)

-- list_vec0_three: eels_dataclass; fixed children concatenate; dynamic children use listed
-- four-byte starts and ordered payloads.
private theorem support_list_vec0_three : Ssz.Serializable (.list (.byteVector 0) 4) (.list
  [(.bytes (⟨#[]⟩ : ByteArray)), (.bytes (⟨#[]⟩ : ByteArray)), (.bytes (⟨#[]⟩ : ByteArray))]) :=
  by
  have h0 : Ssz.Serializable (.byteVector 0) (.bytes (⟨#[]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h1 : Ssz.Serializable (.byteVector 0) (.bytes (⟨#[]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h2 : Ssz.Serializable (.byteVector 0) (.bytes (⟨#[]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa using (show Ssz.Serializable (.byteVector 0) (.bytes (⟨#[]⟩ : ByteArray)) ∧
    Ssz.Serializable (.byteVector 0) (.bytes (⟨#[]⟩ : ByteArray)) ∧ Ssz.Serializable (.byteVector
    0) (.bytes (⟨#[]⟩ : ByteArray)) from ⟨h0, ⟨h1, h2⟩⟩)
private def output_list_vec0_three : ByteArray :=
  Ssz.encode (.list (.byteVector 0) 4) (.list [(.bytes (⟨#[]⟩ : ByteArray)), (.bytes (⟨#[]⟩ :
    ByteArray)), (.bytes (⟨#[]⟩ : ByteArray))]) support_list_vec0_three
private def expected_list_vec0_three : ByteArray := (⟨#[]⟩ : ByteArray)

-- plist_vec0_three: eels_dataclass; fixed children concatenate; dynamic children use listed
-- four-byte starts and ordered payloads.
private theorem support_plist_vec0_three : Ssz.Serializable (.progressiveList (.byteVector 0))
  (.list [(.bytes (⟨#[]⟩ : ByteArray)), (.bytes (⟨#[]⟩ : ByteArray)), (.bytes (⟨#[]⟩ :
  ByteArray))]) := by
  have h0 : Ssz.Serializable (.byteVector 0) (.bytes (⟨#[]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h1 : Ssz.Serializable (.byteVector 0) (.bytes (⟨#[]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h2 : Ssz.Serializable (.byteVector 0) (.bytes (⟨#[]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨?_, by decide⟩
  simpa using (show Ssz.Serializable (.byteVector 0) (.bytes (⟨#[]⟩ : ByteArray)) ∧
    Ssz.Serializable (.byteVector 0) (.bytes (⟨#[]⟩ : ByteArray)) ∧ Ssz.Serializable (.byteVector
    0) (.bytes (⟨#[]⟩ : ByteArray)) from ⟨h0, ⟨h1, h2⟩⟩)
private def output_plist_vec0_three : ByteArray :=
  Ssz.encode (.progressiveList (.byteVector 0)) (.list [(.bytes (⟨#[]⟩ : ByteArray)), (.bytes
    (⟨#[]⟩ : ByteArray)), (.bytes (⟨#[]⟩ : ByteArray))]) support_plist_vec0_three
private def expected_plist_vec0_three : ByteArray := (⟨#[]⟩ : ByteArray)

-- list_vec2: eels_dataclass; fixed children concatenate; dynamic children use listed four-byte
-- starts and ordered payloads.
private theorem support_list_vec2 : Ssz.Serializable (.list (.byteVector 2) 3) (.list [(.bytes
  (⟨#[170, 187]⟩ : ByteArray)), (.bytes (⟨#[0, 255]⟩ : ByteArray))]) := by
  have h0 : Ssz.Serializable (.byteVector 2) (.bytes (⟨#[170, 187]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h1 : Ssz.Serializable (.byteVector 2) (.bytes (⟨#[0, 255]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa using (show Ssz.Serializable (.byteVector 2) (.bytes (⟨#[170, 187]⟩ : ByteArray)) ∧
    Ssz.Serializable (.byteVector 2) (.bytes (⟨#[0, 255]⟩ : ByteArray)) from ⟨h0, h1⟩)
private def output_list_vec2 : ByteArray :=
  Ssz.encode (.list (.byteVector 2) 3) (.list [(.bytes (⟨#[170, 187]⟩ : ByteArray)), (.bytes
    (⟨#[0, 255]⟩ : ByteArray))]) support_list_vec2
private def expected_list_vec2 : ByteArray := (⟨#[170, 187, 0, 255]⟩ : ByteArray)

-- list_bytes_empty: eels_dataclass; fixed children concatenate; dynamic children use listed
-- four-byte starts and ordered payloads.
private theorem support_list_bytes_empty : Ssz.Serializable (.list (.byteList 3) 4) (.list []) := by
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simp
private def output_list_bytes_empty : ByteArray :=
  Ssz.encode (.list (.byteList 3) 4) (.list []) support_list_bytes_empty
private def expected_list_bytes_empty : ByteArray := (⟨#[]⟩ : ByteArray)

-- list_bytes_equal_offsets: eels_dataclass; fixed children concatenate; dynamic children use
-- listed four-byte starts and ordered payloads.
private theorem support_list_bytes_equal_offsets : Ssz.Serializable (.list (.byteList 3) 4) (.list
  [(.bytes (⟨#[]⟩ : ByteArray)), (.bytes (⟨#[170, 187]⟩ : ByteArray)), (.bytes (⟨#[]⟩ :
  ByteArray))]) := by
  have h0 : Ssz.Serializable (.byteList 3) (.bytes (⟨#[]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h1 : Ssz.Serializable (.byteList 3) (.bytes (⟨#[170, 187]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h2 : Ssz.Serializable (.byteList 3) (.bytes (⟨#[]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa using (show Ssz.Serializable (.byteList 3) (.bytes (⟨#[]⟩ : ByteArray)) ∧ Ssz.Serializable
    (.byteList 3) (.bytes (⟨#[170, 187]⟩ : ByteArray)) ∧ Ssz.Serializable (.byteList 3) (.bytes
    (⟨#[]⟩ : ByteArray)) from ⟨h0, ⟨h1, h2⟩⟩)
private def output_list_bytes_equal_offsets : ByteArray :=
  Ssz.encode (.list (.byteList 3) 4) (.list [(.bytes (⟨#[]⟩ : ByteArray)), (.bytes (⟨#[170, 187]⟩
    : ByteArray)), (.bytes (⟨#[]⟩ : ByteArray))]) support_list_bytes_equal_offsets
private def expected_list_bytes_equal_offsets : ByteArray := (⟨#[12, 0, 0, 0, 12, 0, 0, 0, 14, 0,
  0, 0, 170, 187]⟩ : ByteArray)

-- plist_bytes_equal_offsets: eels_dataclass; fixed children concatenate; dynamic children use
-- listed four-byte starts and ordered payloads.
private theorem support_plist_bytes_equal_offsets : Ssz.Serializable (.progressiveList (.byteList
  3)) (.list [(.bytes (⟨#[]⟩ : ByteArray)), (.bytes (⟨#[170, 187]⟩ : ByteArray)), (.bytes (⟨#[]⟩ :
  ByteArray))]) := by
  have h0 : Ssz.Serializable (.byteList 3) (.bytes (⟨#[]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h1 : Ssz.Serializable (.byteList 3) (.bytes (⟨#[170, 187]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h2 : Ssz.Serializable (.byteList 3) (.bytes (⟨#[]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨?_, by decide⟩
  simpa using (show Ssz.Serializable (.byteList 3) (.bytes (⟨#[]⟩ : ByteArray)) ∧ Ssz.Serializable
    (.byteList 3) (.bytes (⟨#[170, 187]⟩ : ByteArray)) ∧ Ssz.Serializable (.byteList 3) (.bytes
    (⟨#[]⟩ : ByteArray)) from ⟨h0, ⟨h1, h2⟩⟩)
private def output_plist_bytes_equal_offsets : ByteArray :=
  Ssz.encode (.progressiveList (.byteList 3)) (.list [(.bytes (⟨#[]⟩ : ByteArray)), (.bytes
    (⟨#[170, 187]⟩ : ByteArray)), (.bytes (⟨#[]⟩ : ByteArray))]) support_plist_bytes_equal_offsets
private def expected_plist_bytes_equal_offsets : ByteArray := (⟨#[12, 0, 0, 0, 12, 0, 0, 0, 14, 0,
  0, 0, 170, 187]⟩ : ByteArray)

-- list_pbytes: eels_dataclass; fixed children concatenate; dynamic children use listed four-byte
-- starts and ordered payloads.
private theorem support_list_pbytes : Ssz.Serializable (.list .progressiveByteList 4) (.list
  [(.bytes (⟨#[170]⟩ : ByteArray)), (.bytes (⟨#[]⟩ : ByteArray)), (.bytes (⟨#[187, 204]⟩ :
  ByteArray))]) := by
  have h0 : Ssz.Serializable .progressiveByteList (.bytes (⟨#[170]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h1 : Ssz.Serializable .progressiveByteList (.bytes (⟨#[]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h2 : Ssz.Serializable .progressiveByteList (.bytes (⟨#[187, 204]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa using (show Ssz.Serializable .progressiveByteList (.bytes (⟨#[170]⟩ : ByteArray)) ∧
    Ssz.Serializable .progressiveByteList (.bytes (⟨#[]⟩ : ByteArray)) ∧ Ssz.Serializable
    .progressiveByteList (.bytes (⟨#[187, 204]⟩ : ByteArray)) from ⟨h0, ⟨h1, h2⟩⟩)
private def output_list_pbytes : ByteArray :=
  Ssz.encode (.list .progressiveByteList 4) (.list [(.bytes (⟨#[170]⟩ : ByteArray)), (.bytes
    (⟨#[]⟩ : ByteArray)), (.bytes (⟨#[187, 204]⟩ : ByteArray))]) support_list_pbytes
private def expected_list_pbytes : ByteArray := (⟨#[12, 0, 0, 0, 13, 0, 0, 0, 13, 0, 0, 0, 170,
  187, 204]⟩ : ByteArray)

-- nested_lists: eels_dataclass; fixed children concatenate; dynamic children use listed four-byte
-- starts and ordered payloads.
private theorem support_nested_lists : Ssz.Serializable (.list (.list (.uint 1) 3) 3) (.list
  [(.list []), (.list [(.uint 1), (.uint 2)]), (.list [(.uint 255)])]) := by
  have h0 : Ssz.Serializable (.list (.uint 1) 3) (.list []) := by
    apply (Ssz.serializable_iff _ _).mpr
    refine ⟨by decide, ?_, by decide⟩
    simp
  have h1 : Ssz.Serializable (.list (.uint 1) 3) (.list [(.uint 1), (.uint 2)]) := by
    have h0 : Ssz.Serializable (.uint 1) (.uint 1) := by
      apply (Ssz.serializable_iff _ _).mpr
      decide
    have h1 : Ssz.Serializable (.uint 1) (.uint 2) := by
      apply (Ssz.serializable_iff _ _).mpr
      decide
    apply (Ssz.serializable_iff _ _).mpr
    refine ⟨by decide, ?_, by decide⟩
    simpa using (show Ssz.Serializable (.uint 1) (.uint 1) ∧ Ssz.Serializable (.uint 1) (.uint 2)
      from ⟨h0, h1⟩)
  have h2 : Ssz.Serializable (.list (.uint 1) 3) (.list [(.uint 255)]) := by
    have h0 : Ssz.Serializable (.uint 1) (.uint 255) := by
      apply (Ssz.serializable_iff _ _).mpr
      decide
    apply (Ssz.serializable_iff _ _).mpr
    refine ⟨by decide, ?_, by decide⟩
    simpa using (show Ssz.Serializable (.uint 1) (.uint 255) from h0)
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa using (show Ssz.Serializable (.list (.uint 1) 3) (.list []) ∧ Ssz.Serializable (.list
    (.uint 1) 3) (.list [(.uint 1), (.uint 2)]) ∧ Ssz.Serializable (.list (.uint 1) 3) (.list
    [(.uint 255)]) from ⟨h0, ⟨h1, h2⟩⟩)
private def output_nested_lists : ByteArray :=
  Ssz.encode (.list (.list (.uint 1) 3) 3) (.list [(.list []), (.list [(.uint 1), (.uint 2)]),
    (.list [(.uint 255)])]) support_nested_lists
private def expected_nested_lists : ByteArray := (⟨#[12, 0, 0, 0, 12, 0, 0, 0, 14, 0, 0, 0, 1, 2,
  255]⟩ : ByteArray)

-- nested_plists: eels_dataclass; fixed children concatenate; dynamic children use listed
-- four-byte starts and ordered payloads.
private theorem support_nested_plists : Ssz.Serializable (.progressiveList (.progressiveList
  (.uint 1))) (.list [(.list []), (.list [(.uint 1), (.uint 2)]), (.list [(.uint 255)])]) := by
  have h0 : Ssz.Serializable (.progressiveList (.uint 1)) (.list []) := by
    apply (Ssz.serializable_iff _ _).mpr
    refine ⟨?_, by decide⟩
    simp
  have h1 : Ssz.Serializable (.progressiveList (.uint 1)) (.list [(.uint 1), (.uint 2)]) := by
    have h0 : Ssz.Serializable (.uint 1) (.uint 1) := by
      apply (Ssz.serializable_iff _ _).mpr
      decide
    have h1 : Ssz.Serializable (.uint 1) (.uint 2) := by
      apply (Ssz.serializable_iff _ _).mpr
      decide
    apply (Ssz.serializable_iff _ _).mpr
    refine ⟨?_, by decide⟩
    simpa using (show Ssz.Serializable (.uint 1) (.uint 1) ∧ Ssz.Serializable (.uint 1) (.uint 2)
      from ⟨h0, h1⟩)
  have h2 : Ssz.Serializable (.progressiveList (.uint 1)) (.list [(.uint 255)]) := by
    have h0 : Ssz.Serializable (.uint 1) (.uint 255) := by
      apply (Ssz.serializable_iff _ _).mpr
      decide
    apply (Ssz.serializable_iff _ _).mpr
    refine ⟨?_, by decide⟩
    simpa using (show Ssz.Serializable (.uint 1) (.uint 255) from h0)
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨?_, by decide⟩
  simpa using (show Ssz.Serializable (.progressiveList (.uint 1)) (.list []) ∧ Ssz.Serializable
    (.progressiveList (.uint 1)) (.list [(.uint 1), (.uint 2)]) ∧ Ssz.Serializable
    (.progressiveList (.uint 1)) (.list [(.uint 255)]) from ⟨h0, ⟨h1, h2⟩⟩)
private def output_nested_plists : ByteArray :=
  Ssz.encode (.progressiveList (.progressiveList (.uint 1))) (.list [(.list []), (.list [(.uint
    1), (.uint 2)]), (.list [(.uint 255)])]) support_nested_plists
private def expected_nested_plists : ByteArray := (⟨#[12, 0, 0, 0, 12, 0, 0, 0, 14, 0, 0, 0, 1, 2,
  255]⟩ : ByteArray)

-- triple_dynamic: eels_dataclass; fixed children concatenate; dynamic children use listed
-- four-byte starts and ordered payloads.
private theorem support_triple_dynamic : Ssz.Serializable (.list (.list (.byteList 2) 3) 3) (.list
  [(.list [(.bytes (⟨#[170]⟩ : ByteArray))]), (.list []), (.list [(.bytes (⟨#[]⟩ : ByteArray)),
  (.bytes (⟨#[187]⟩ : ByteArray))])]) := by
  have h0 : Ssz.Serializable (.list (.byteList 2) 3) (.list [(.bytes (⟨#[170]⟩ : ByteArray))]) := by
    have h0 : Ssz.Serializable (.byteList 2) (.bytes (⟨#[170]⟩ : ByteArray)) := by
      apply (Ssz.serializable_iff _ _).mpr
      decide
    apply (Ssz.serializable_iff _ _).mpr
    refine ⟨by decide, ?_, by decide⟩
    simpa using (show Ssz.Serializable (.byteList 2) (.bytes (⟨#[170]⟩ : ByteArray)) from h0)
  have h1 : Ssz.Serializable (.list (.byteList 2) 3) (.list []) := by
    apply (Ssz.serializable_iff _ _).mpr
    refine ⟨by decide, ?_, by decide⟩
    simp
  have h2 : Ssz.Serializable (.list (.byteList 2) 3) (.list [(.bytes (⟨#[]⟩ : ByteArray)), (.bytes
    (⟨#[187]⟩ : ByteArray))]) := by
    have h0 : Ssz.Serializable (.byteList 2) (.bytes (⟨#[]⟩ : ByteArray)) := by
      apply (Ssz.serializable_iff _ _).mpr
      decide
    have h1 : Ssz.Serializable (.byteList 2) (.bytes (⟨#[187]⟩ : ByteArray)) := by
      apply (Ssz.serializable_iff _ _).mpr
      decide
    apply (Ssz.serializable_iff _ _).mpr
    refine ⟨by decide, ?_, by decide⟩
    simpa using (show Ssz.Serializable (.byteList 2) (.bytes (⟨#[]⟩ : ByteArray)) ∧
      Ssz.Serializable (.byteList 2) (.bytes (⟨#[187]⟩ : ByteArray)) from ⟨h0, h1⟩)
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa using (show Ssz.Serializable (.list (.byteList 2) 3) (.list [(.bytes (⟨#[170]⟩ :
    ByteArray))]) ∧ Ssz.Serializable (.list (.byteList 2) 3) (.list []) ∧ Ssz.Serializable (.list
    (.byteList 2) 3) (.list [(.bytes (⟨#[]⟩ : ByteArray)), (.bytes (⟨#[187]⟩ : ByteArray))]) from
    ⟨h0, ⟨h1, h2⟩⟩)
private def output_triple_dynamic : ByteArray :=
  Ssz.encode (.list (.list (.byteList 2) 3) 3) (.list [(.list [(.bytes (⟨#[170]⟩ : ByteArray))]),
    (.list []), (.list [(.bytes (⟨#[]⟩ : ByteArray)), (.bytes (⟨#[187]⟩ : ByteArray))])])
    support_triple_dynamic
private def expected_triple_dynamic : ByteArray := (⟨#[12, 0, 0, 0, 17, 0, 0, 0, 17, 0, 0, 0, 4,
  0, 0, 0, 170, 8, 0, 0, 0, 8, 0, 0, 0, 187]⟩ : ByteArray)

-- container_fixed: eels_dataclass; fixed fields 0102,01,aabbcc inline.
private theorem support_container_fixed : Ssz.Serializable (.container [(.uint 2), .bool,
  (.byteVector 3)]) (.container [(.uint 513), (.bool true), (.bytes (⟨#[170, 187, 204]⟩ :
  ByteArray))]) := by
  have h0 : Ssz.Serializable (.uint 2) (.uint 513) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h1 : Ssz.Serializable .bool (.bool true) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h2 : Ssz.Serializable (.byteVector 3) (.bytes (⟨#[170, 187, 204]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa using (show Ssz.Serializable (.uint 2) (.uint 513) ∧ Ssz.Serializable .bool (.bool true) ∧
    Ssz.Serializable (.byteVector 3) (.bytes (⟨#[170, 187, 204]⟩ : ByteArray)) from ⟨h0, ⟨h1,
    h2⟩⟩)
private def output_container_fixed : ByteArray :=
  Ssz.encode (.container [(.uint 2), .bool, (.byteVector 3)]) (.container [(.uint 513), (.bool
    true), (.bytes (⟨#[170, 187, 204]⟩ : ByteArray))]) support_container_fixed
private def expected_container_fixed : ByteArray := (⟨#[1, 2, 1, 170, 187, 204]⟩ : ByteArray)

-- container_zero_fixed: eels_dataclass; zero-width field contributes no bytes.
private theorem support_container_zero_fixed : Ssz.Serializable (.container [(.byteVector 0),
  (.uint 1)]) (.container [(.bytes (⟨#[]⟩ : ByteArray)), (.uint 17)]) := by
  have h0 : Ssz.Serializable (.byteVector 0) (.bytes (⟨#[]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h1 : Ssz.Serializable (.uint 1) (.uint 17) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa using (show Ssz.Serializable (.byteVector 0) (.bytes (⟨#[]⟩ : ByteArray)) ∧
    Ssz.Serializable (.uint 1) (.uint 17) from ⟨h0, h1⟩)
private def output_container_zero_fixed : ByteArray :=
  Ssz.encode (.container [(.byteVector 0), (.uint 1)]) (.container [(.bytes (⟨#[]⟩ : ByteArray)),
    (.uint 17)]) support_container_zero_fixed
private def expected_container_zero_fixed : ByteArray := (⟨#[17]⟩ : ByteArray)

-- container_mixed: eels_dataclass; head=2+4+1+4=11; starts11,12; tails aa,bbcc.
private theorem support_container_mixed : Ssz.Serializable (.container [(.uint 2), (.byteList 3),
  .bool, .progressiveByteList]) (.container [(.uint 513), (.bytes (⟨#[170]⟩ : ByteArray)), (.bool
  true), (.bytes (⟨#[187, 204]⟩ : ByteArray))]) := by
  have h0 : Ssz.Serializable (.uint 2) (.uint 513) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h1 : Ssz.Serializable (.byteList 3) (.bytes (⟨#[170]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h2 : Ssz.Serializable .bool (.bool true) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h3 : Ssz.Serializable .progressiveByteList (.bytes (⟨#[187, 204]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa using (show Ssz.Serializable (.uint 2) (.uint 513) ∧ Ssz.Serializable (.byteList 3)
    (.bytes (⟨#[170]⟩ : ByteArray)) ∧ Ssz.Serializable .bool (.bool true) ∧ Ssz.Serializable
    .progressiveByteList (.bytes (⟨#[187, 204]⟩ : ByteArray)) from ⟨h0, ⟨h1, ⟨h2, h3⟩⟩⟩)
private def output_container_mixed : ByteArray :=
  Ssz.encode (.container [(.uint 2), (.byteList 3), .bool, .progressiveByteList]) (.container
    [(.uint 513), (.bytes (⟨#[170]⟩ : ByteArray)), (.bool true), (.bytes (⟨#[187, 204]⟩ :
    ByteArray))]) support_container_mixed
private def expected_container_mixed : ByteArray := (⟨#[1, 2, 11, 0, 0, 0, 1, 12, 0, 0, 0, 170,
  187, 204]⟩ : ByteArray)

-- container_empty_dynamics: eels_dataclass; head12; empty first/last payload; starts12,12,14.
private theorem support_container_empty_dynamics : Ssz.Serializable (.container [(.byteList 0),
  (.byteList 2), (.byteList 0)]) (.container [(.bytes (⟨#[]⟩ : ByteArray)), (.bytes (⟨#[170, 187]⟩
  : ByteArray)), (.bytes (⟨#[]⟩ : ByteArray))]) := by
  have h0 : Ssz.Serializable (.byteList 0) (.bytes (⟨#[]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h1 : Ssz.Serializable (.byteList 2) (.bytes (⟨#[170, 187]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h2 : Ssz.Serializable (.byteList 0) (.bytes (⟨#[]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa using (show Ssz.Serializable (.byteList 0) (.bytes (⟨#[]⟩ : ByteArray)) ∧ Ssz.Serializable
    (.byteList 2) (.bytes (⟨#[170, 187]⟩ : ByteArray)) ∧ Ssz.Serializable (.byteList 0) (.bytes
    (⟨#[]⟩ : ByteArray)) from ⟨h0, ⟨h1, h2⟩⟩)
private def output_container_empty_dynamics : ByteArray :=
  Ssz.encode (.container [(.byteList 0), (.byteList 2), (.byteList 0)]) (.container [(.bytes
    (⟨#[]⟩ : ByteArray)), (.bytes (⟨#[170, 187]⟩ : ByteArray)), (.bytes (⟨#[]⟩ : ByteArray))])
    support_container_empty_dynamics
private def expected_container_empty_dynamics : ByteArray := (⟨#[12, 0, 0, 0, 12, 0, 0, 0, 14, 0,
  0, 0, 170, 187]⟩ : ByteArray)

-- container_nested: eels_dataclass; outer head10; inner bytes0705000000aabb length7; starts10,17.
private theorem support_container_nested : Ssz.Serializable (.container [(.uint 2), (.container
  [(.uint 1), (.byteList 2)]), (.byteVector 0), .progressiveByteList]) (.container [(.uint 513),
  (.container [(.uint 7), (.bytes (⟨#[170, 187]⟩ : ByteArray))]), (.bytes (⟨#[]⟩ : ByteArray)),
  (.bytes (⟨#[204]⟩ : ByteArray))]) := by
  have h0 : Ssz.Serializable (.uint 2) (.uint 513) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h1 : Ssz.Serializable (.container [(.uint 1), (.byteList 2)]) (.container [(.uint 7),
    (.bytes (⟨#[170, 187]⟩ : ByteArray))]) := by
    have h0 : Ssz.Serializable (.uint 1) (.uint 7) := by
      apply (Ssz.serializable_iff _ _).mpr
      decide
    have h1 : Ssz.Serializable (.byteList 2) (.bytes (⟨#[170, 187]⟩ : ByteArray)) := by
      apply (Ssz.serializable_iff _ _).mpr
      decide
    apply (Ssz.serializable_iff _ _).mpr
    refine ⟨by decide, ?_, by decide⟩
    simpa using (show Ssz.Serializable (.uint 1) (.uint 7) ∧ Ssz.Serializable (.byteList 2)
      (.bytes (⟨#[170, 187]⟩ : ByteArray)) from ⟨h0, h1⟩)
  have h2 : Ssz.Serializable (.byteVector 0) (.bytes (⟨#[]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h3 : Ssz.Serializable .progressiveByteList (.bytes (⟨#[204]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa using (show Ssz.Serializable (.uint 2) (.uint 513) ∧ Ssz.Serializable (.container [(.uint
    1), (.byteList 2)]) (.container [(.uint 7), (.bytes (⟨#[170, 187]⟩ : ByteArray))]) ∧
    Ssz.Serializable (.byteVector 0) (.bytes (⟨#[]⟩ : ByteArray)) ∧ Ssz.Serializable
    .progressiveByteList (.bytes (⟨#[204]⟩ : ByteArray)) from ⟨h0, ⟨h1, ⟨h2, h3⟩⟩⟩)
private def output_container_nested : ByteArray :=
  Ssz.encode (.container [(.uint 2), (.container [(.uint 1), (.byteList 2)]), (.byteVector 0),
    .progressiveByteList]) (.container [(.uint 513), (.container [(.uint 7), (.bytes (⟨#[170,
    187]⟩ : ByteArray))]), (.bytes (⟨#[]⟩ : ByteArray)), (.bytes (⟨#[204]⟩ : ByteArray))])
    support_container_nested
private def expected_container_nested : ByteArray := (⟨#[1, 2, 10, 0, 0, 0, 17, 0, 0, 0, 7, 5, 0,
  0, 0, 170, 187, 204]⟩ : ByteArray)

-- list_containers: eels_dataclass; list head8; child sizes6,5; starts8,14; inner heads5.
private theorem support_list_containers : Ssz.Serializable (.list (.container [(.uint 1),
  (.byteList 2)]) 3) (.list [(.container [(.uint 7), (.bytes (⟨#[170]⟩ : ByteArray))]),
  (.container [(.uint 8), (.bytes (⟨#[]⟩ : ByteArray))])]) := by
  have h0 : Ssz.Serializable (.container [(.uint 1), (.byteList 2)]) (.container [(.uint 7),
    (.bytes (⟨#[170]⟩ : ByteArray))]) := by
    have h0 : Ssz.Serializable (.uint 1) (.uint 7) := by
      apply (Ssz.serializable_iff _ _).mpr
      decide
    have h1 : Ssz.Serializable (.byteList 2) (.bytes (⟨#[170]⟩ : ByteArray)) := by
      apply (Ssz.serializable_iff _ _).mpr
      decide
    apply (Ssz.serializable_iff _ _).mpr
    refine ⟨by decide, ?_, by decide⟩
    simpa using (show Ssz.Serializable (.uint 1) (.uint 7) ∧ Ssz.Serializable (.byteList 2)
      (.bytes (⟨#[170]⟩ : ByteArray)) from ⟨h0, h1⟩)
  have h1 : Ssz.Serializable (.container [(.uint 1), (.byteList 2)]) (.container [(.uint 8),
    (.bytes (⟨#[]⟩ : ByteArray))]) := by
    have h0 : Ssz.Serializable (.uint 1) (.uint 8) := by
      apply (Ssz.serializable_iff _ _).mpr
      decide
    have h1 : Ssz.Serializable (.byteList 2) (.bytes (⟨#[]⟩ : ByteArray)) := by
      apply (Ssz.serializable_iff _ _).mpr
      decide
    apply (Ssz.serializable_iff _ _).mpr
    refine ⟨by decide, ?_, by decide⟩
    simpa using (show Ssz.Serializable (.uint 1) (.uint 8) ∧ Ssz.Serializable (.byteList 2)
      (.bytes (⟨#[]⟩ : ByteArray)) from ⟨h0, h1⟩)
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa using (show Ssz.Serializable (.container [(.uint 1), (.byteList 2)]) (.container [(.uint
    7), (.bytes (⟨#[170]⟩ : ByteArray))]) ∧ Ssz.Serializable (.container [(.uint 1), (.byteList
    2)]) (.container [(.uint 8), (.bytes (⟨#[]⟩ : ByteArray))]) from ⟨h0, h1⟩)
private def output_list_containers : ByteArray :=
  Ssz.encode (.list (.container [(.uint 1), (.byteList 2)]) 3) (.list [(.container [(.uint 7),
    (.bytes (⟨#[170]⟩ : ByteArray))]), (.container [(.uint 8), (.bytes (⟨#[]⟩ : ByteArray))])])
    support_list_containers
private def expected_list_containers : ByteArray := (⟨#[8, 0, 0, 0, 14, 0, 0, 0, 7, 5, 0, 0, 0,
  170, 8, 5, 0, 0, 0]⟩ : ByteArray)

-- container_list: eels_dataclass; outer head6; nested list starts8,8.
private theorem support_container_list : Ssz.Serializable (.container [.bool, (.list (.byteList 2)
  3), (.uint 1)]) (.container [(.bool true), (.list [(.bytes (⟨#[]⟩ : ByteArray)), (.bytes
  (⟨#[170, 187]⟩ : ByteArray))]), (.uint 9)]) := by
  have h0 : Ssz.Serializable .bool (.bool true) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h1 : Ssz.Serializable (.list (.byteList 2) 3) (.list [(.bytes (⟨#[]⟩ : ByteArray)), (.bytes
    (⟨#[170, 187]⟩ : ByteArray))]) := by
    have h0 : Ssz.Serializable (.byteList 2) (.bytes (⟨#[]⟩ : ByteArray)) := by
      apply (Ssz.serializable_iff _ _).mpr
      decide
    have h1 : Ssz.Serializable (.byteList 2) (.bytes (⟨#[170, 187]⟩ : ByteArray)) := by
      apply (Ssz.serializable_iff _ _).mpr
      decide
    apply (Ssz.serializable_iff _ _).mpr
    refine ⟨by decide, ?_, by decide⟩
    simpa using (show Ssz.Serializable (.byteList 2) (.bytes (⟨#[]⟩ : ByteArray)) ∧
      Ssz.Serializable (.byteList 2) (.bytes (⟨#[170, 187]⟩ : ByteArray)) from ⟨h0, h1⟩)
  have h2 : Ssz.Serializable (.uint 1) (.uint 9) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa using (show Ssz.Serializable .bool (.bool true) ∧ Ssz.Serializable (.list (.byteList 2) 3)
    (.list [(.bytes (⟨#[]⟩ : ByteArray)), (.bytes (⟨#[170, 187]⟩ : ByteArray))]) ∧
    Ssz.Serializable (.uint 1) (.uint 9) from ⟨h0, ⟨h1, h2⟩⟩)
private def output_container_list : ByteArray :=
  Ssz.encode (.container [.bool, (.list (.byteList 2) 3), (.uint 1)]) (.container [(.bool true),
    (.list [(.bytes (⟨#[]⟩ : ByteArray)), (.bytes (⟨#[170, 187]⟩ : ByteArray))]), (.uint 9)])
    support_container_list
private def expected_container_list : ByteArray := (⟨#[1, 6, 0, 0, 0, 9, 8, 0, 0, 0, 8, 0, 0, 0,
  170, 187]⟩ : ByteArray)

-- progressive_container: eels_dataclass; all-active progressive container head6, payload aa.
private theorem support_progressive_container : Ssz.Serializable (.progressiveContainer [true,
  true] [(.uint 2), (.byteList 3)]) (.container [(.uint 513), (.bytes (⟨#[170]⟩ : ByteArray))]) :=
  by
  have h0 : Ssz.Serializable (.uint 2) (.uint 513) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h1 : Ssz.Serializable (.byteList 3) (.bytes (⟨#[170]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa using (show Ssz.Serializable (.uint 2) (.uint 513) ∧ Ssz.Serializable (.byteList 3)
    (.bytes (⟨#[170]⟩ : ByteArray)) from ⟨h0, h1⟩)
private def output_progressive_container : ByteArray :=
  Ssz.encode (.progressiveContainer [true, true] [(.uint 2), (.byteList 3)]) (.container [(.uint
    513), (.bytes (⟨#[170]⟩ : ByteArray))]) support_progressive_container
private def expected_progressive_container : ByteArray := (⟨#[1, 2, 6, 0, 0, 0, 170]⟩ : ByteArray)

-- sparse_101: dependency_sparse; active mask absent from wire; head6, payload aa.
private theorem support_sparse_101 : Ssz.Serializable (.progressiveContainer [true, false, true]
  [(.uint 2), (.byteList 3)]) (.container [(.uint 513), (.bytes (⟨#[170]⟩ : ByteArray))]) := by
  have h0 : Ssz.Serializable (.uint 2) (.uint 513) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h1 : Ssz.Serializable (.byteList 3) (.bytes (⟨#[170]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa using (show Ssz.Serializable (.uint 2) (.uint 513) ∧ Ssz.Serializable (.byteList 3)
    (.bytes (⟨#[170]⟩ : ByteArray)) from ⟨h0, h1⟩)
private def output_sparse_101 : ByteArray :=
  Ssz.encode (.progressiveContainer [true, false, true] [(.uint 2), (.byteList 3)]) (.container
    [(.uint 513), (.bytes (⟨#[170]⟩ : ByteArray))]) support_sparse_101
private def expected_sparse_101 : ByteArray := (⟨#[1, 2, 6, 0, 0, 0, 170]⟩ : ByteArray)

-- sparse_00101: dependency_sparse; active mask absent from wire; head6, payload aa.
private theorem support_sparse_00101 : Ssz.Serializable (.progressiveContainer [false, false,
  true, false, true] [(.uint 2), (.byteList 3)]) (.container [(.uint 513), (.bytes (⟨#[170]⟩ :
  ByteArray))]) := by
  have h0 : Ssz.Serializable (.uint 2) (.uint 513) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h1 : Ssz.Serializable (.byteList 3) (.bytes (⟨#[170]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa using (show Ssz.Serializable (.uint 2) (.uint 513) ∧ Ssz.Serializable (.byteList 3)
    (.bytes (⟨#[170]⟩ : ByteArray)) from ⟨h0, h1⟩)
private def output_sparse_00101 : ByteArray :=
  Ssz.encode (.progressiveContainer [false, false, true, false, true] [(.uint 2), (.byteList 3)])
    (.container [(.uint 513), (.bytes (⟨#[170]⟩ : ByteArray))]) support_sparse_00101
private def expected_sparse_00101 : ByteArray := (⟨#[1, 2, 6, 0, 0, 0, 170]⟩ : ByteArray)

-- sparse_zero: dependency_sparse; zero fixed first field; one offset4 then aabb.
private theorem support_sparse_zero : Ssz.Serializable (.progressiveContainer [false, true, false,
  true] [(.byteVector 0), (.byteList 2)]) (.container [(.bytes (⟨#[]⟩ : ByteArray)), (.bytes
  (⟨#[170, 187]⟩ : ByteArray))]) := by
  have h0 : Ssz.Serializable (.byteVector 0) (.bytes (⟨#[]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h1 : Ssz.Serializable (.byteList 2) (.bytes (⟨#[170, 187]⟩ : ByteArray)) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa using (show Ssz.Serializable (.byteVector 0) (.bytes (⟨#[]⟩ : ByteArray)) ∧
    Ssz.Serializable (.byteList 2) (.bytes (⟨#[170, 187]⟩ : ByteArray)) from ⟨h0, h1⟩)
private def output_sparse_zero : ByteArray :=
  Ssz.encode (.progressiveContainer [false, true, false, true] [(.byteVector 0), (.byteList 2)])
    (.container [(.bytes (⟨#[]⟩ : ByteArray)), (.bytes (⟨#[170, 187]⟩ : ByteArray))])
    support_sparse_zero
private def expected_sparse_zero : ByteArray := (⟨#[4, 0, 0, 0, 170, 187]⟩ : ByteArray)

-- extra_empty_container: b0_mathematical_extra; approved B0 actual-value recursion; no
-- source-success claim.
private theorem support_extra_empty_container : Ssz.Serializable (.container []) (.container [])
  := by
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simp
private def output_extra_empty_container : ByteArray :=
  Ssz.encode (.container []) (.container []) support_extra_empty_container
private def expected_extra_empty_container : ByteArray := (⟨#[]⟩ : ByteArray)

-- extra_empty_progressive: b0_mathematical_extra; approved B0 actual-value recursion; no
-- source-success claim.
private theorem support_extra_empty_progressive : Ssz.Serializable (.progressiveContainer [] [])
  (.container []) := by
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simp
private def output_extra_empty_progressive : ByteArray :=
  Ssz.encode (.progressiveContainer [] []) (.container []) support_extra_empty_progressive
private def expected_extra_empty_progressive : ByteArray := (⟨#[]⟩ : ByteArray)

-- extra_bad_mask: b0_mathematical_extra; approved B0 actual-value recursion; no source-success
-- claim.
private theorem support_extra_bad_mask : Ssz.Serializable (.progressiveContainer [false] [(.uint
  1)]) (.container [(.uint 17)]) := by
  have h0 : Ssz.Serializable (.uint 1) (.uint 17) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa using (show Ssz.Serializable (.uint 1) (.uint 17) from h0)
private def output_extra_bad_mask : ByteArray :=
  Ssz.encode (.progressiveContainer [false] [(.uint 1)]) (.container [(.uint 17)])
    support_extra_bad_mask
private def expected_extra_bad_mask : ByteArray := (⟨#[17]⟩ : ByteArray)

-- extra_empty_bad_uint_list: b0_mathematical_extra; approved B0 actual-value recursion; no
-- source-success claim.
private theorem support_extra_empty_bad_uint_list : Ssz.Serializable (.list (.uint 3) 0) (.list
  []) := by
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simp
private def output_extra_empty_bad_uint_list : ByteArray :=
  Ssz.encode (.list (.uint 3) 0) (.list []) support_extra_empty_bad_uint_list
private def expected_extra_empty_bad_uint_list : ByteArray := (⟨#[]⟩ : ByteArray)

-- extra_empty_bad_progressive_list: b0_mathematical_extra; approved B0 actual-value recursion; no
-- source-success claim.
private theorem support_extra_empty_bad_progressive_list : Ssz.Serializable (.progressiveList
  (.uint 0)) (.list []) := by
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨?_, by decide⟩
  simp
private def output_extra_empty_bad_progressive_list : ByteArray :=
  Ssz.encode (.progressiveList (.uint 0)) (.list []) support_extra_empty_bad_progressive_list
private def expected_extra_empty_bad_progressive_list : ByteArray := (⟨#[]⟩ : ByteArray)

-- mathematical_fixed43: mathematical_layout_only; 32 ordered vector bytes, true=01, eight
-- low-first digits20..27, two digits28..29.
private theorem support_mathematical_fixed43 : Ssz.Serializable (.container [(.byteVector 32),
  .bool, (.uint 8), (.uint 2)]) (.container [(.bytes (⟨#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12,
  13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]⟩ : ByteArray)),
  (.bool true), (.uint 2820983053732684064), (.uint 10536)]) := by
  have h0 : Ssz.Serializable (.byteVector 32) (.bytes (⟨#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
    12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]⟩ : ByteArray))
    := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h1 : Ssz.Serializable .bool (.bool true) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h2 : Ssz.Serializable (.uint 8) (.uint 2820983053732684064) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  have h3 : Ssz.Serializable (.uint 2) (.uint 10536) := by
    apply (Ssz.serializable_iff _ _).mpr
    decide
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, by decide⟩
  simpa using (show Ssz.Serializable (.byteVector 32) (.bytes (⟨#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
    10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]⟩ :
    ByteArray)) ∧ Ssz.Serializable .bool (.bool true) ∧ Ssz.Serializable (.uint 8) (.uint
    2820983053732684064) ∧ Ssz.Serializable (.uint 2) (.uint 10536) from ⟨h0, ⟨h1, ⟨h2, h3⟩⟩⟩)
private def output_mathematical_fixed43 : ByteArray :=
  Ssz.encode (.container [(.byteVector 32), .bool, (.uint 8), (.uint 2)]) (.container [(.bytes
    (⟨#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
    25, 26, 27, 28, 29, 30, 31]⟩ : ByteArray)), (.bool true), (.uint 2820983053732684064), (.uint
    10536)]) support_mathematical_fixed43
private def expected_mathematical_fixed43 : ByteArray := (⟨#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
  12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 1, 32, 33, 34,
  35, 36, 37, 38, 39, 40, 41]⟩ : ByteArray)
#guard output_u1_zero.data.toList = expected_u1_zero.data.toList
#guard output_u1_max.data.toList = expected_u1_max.data.toList
#guard output_u1_pattern.data.toList = expected_u1_pattern.data.toList
#guard output_u2_zero.data.toList = expected_u2_zero.data.toList
#guard output_u2_max.data.toList = expected_u2_max.data.toList
#guard output_u2_pattern.data.toList = expected_u2_pattern.data.toList
#guard output_u4_zero.data.toList = expected_u4_zero.data.toList
#guard output_u4_max.data.toList = expected_u4_max.data.toList
#guard output_u4_pattern.data.toList = expected_u4_pattern.data.toList
#guard output_u8_zero.data.toList = expected_u8_zero.data.toList
#guard output_u8_max.data.toList = expected_u8_max.data.toList
#guard output_u8_pattern.data.toList = expected_u8_pattern.data.toList
#guard output_u16_zero.data.toList = expected_u16_zero.data.toList
#guard output_u16_max.data.toList = expected_u16_max.data.toList
#guard output_u16_pattern.data.toList = expected_u16_pattern.data.toList
#guard output_u32_zero.data.toList = expected_u32_zero.data.toList
#guard output_u32_max.data.toList = expected_u32_max.data.toList
#guard output_u32_pattern.data.toList = expected_u32_pattern.data.toList
#guard output_bool_false.data.toList = expected_bool_false.data.toList
#guard output_bool_true.data.toList = expected_bool_true.data.toList
#guard output_vector0.data.toList = expected_vector0.data.toList
#guard output_vector1.data.toList = expected_vector1.data.toList
#guard output_vector3.data.toList = expected_vector3.data.toList
#guard output_vector32.data.toList = expected_vector32.data.toList
#guard output_bl0.data.toList = expected_bl0.data.toList
#guard output_bl4_empty.data.toList = expected_bl4_empty.data.toList
#guard output_bl4_full.data.toList = expected_bl4_full.data.toList
#guard output_pbytes_empty.data.toList = expected_pbytes_empty.data.toList
#guard output_pbytes.data.toList = expected_pbytes.data.toList
#guard output_list_u16_empty.data.toList = expected_list_u16_empty.data.toList
#guard output_list_u16.data.toList = expected_list_u16.data.toList
#guard output_plist_u16.data.toList = expected_plist_u16.data.toList
#guard output_list_bool.data.toList = expected_list_bool.data.toList
#guard output_list_vec0_empty.data.toList = expected_list_vec0_empty.data.toList
#guard output_list_vec0_three.data.toList = expected_list_vec0_three.data.toList
#guard output_plist_vec0_three.data.toList = expected_plist_vec0_three.data.toList
#guard output_list_vec2.data.toList = expected_list_vec2.data.toList
#guard output_list_bytes_empty.data.toList = expected_list_bytes_empty.data.toList
#guard output_list_bytes_equal_offsets.data.toList = expected_list_bytes_equal_offsets.data.toList
#guard output_plist_bytes_equal_offsets.data.toList = expected_plist_bytes_equal_offsets.data.toList
#guard output_list_pbytes.data.toList = expected_list_pbytes.data.toList
#guard output_nested_lists.data.toList = expected_nested_lists.data.toList
#guard output_nested_plists.data.toList = expected_nested_plists.data.toList
#guard output_triple_dynamic.data.toList = expected_triple_dynamic.data.toList
#guard output_container_fixed.data.toList = expected_container_fixed.data.toList
#guard output_container_zero_fixed.data.toList = expected_container_zero_fixed.data.toList
#guard output_container_mixed.data.toList = expected_container_mixed.data.toList
#guard output_container_empty_dynamics.data.toList = expected_container_empty_dynamics.data.toList
#guard output_container_nested.data.toList = expected_container_nested.data.toList
#guard output_list_containers.data.toList = expected_list_containers.data.toList
#guard output_container_list.data.toList = expected_container_list.data.toList
#guard output_progressive_container.data.toList = expected_progressive_container.data.toList
#guard output_sparse_101.data.toList = expected_sparse_101.data.toList
#guard output_sparse_00101.data.toList = expected_sparse_00101.data.toList
#guard output_sparse_zero.data.toList = expected_sparse_zero.data.toList
#guard output_extra_empty_container.data.toList = expected_extra_empty_container.data.toList
#guard output_extra_empty_progressive.data.toList = expected_extra_empty_progressive.data.toList
#guard output_extra_bad_mask.data.toList = expected_extra_bad_mask.data.toList
#guard output_extra_empty_bad_uint_list.data.toList = expected_extra_empty_bad_uint_list.data.toList
#guard output_extra_empty_bad_progressive_list.data.toList =
  expected_extra_empty_bad_progressive_list.data.toList
#guard output_mathematical_fixed43.data.toList = expected_mathematical_fixed43.data.toList
