/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Closed structural SSZ payload controls

Library `EthConformance`. 130 complete signed propositions on the public typing,
well-formedness and sizing contracts. No runtime validator or source operation.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–4/§7.
-/

namespace STFSpec.Conformance.Codec

open STFSpec.Codec

private theorem wtM01 :
    SszValue.WellTyped (.uint 1) (.uint 0) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtM02 :
    ¬ SszValue.WellTyped (.uint 1) (.bool true) := by
  simp [SszValue.wellTyped_iff (.uint _) (.bool _)] <;> decide

private theorem wtM03 :
    ¬ SszValue.WellTyped (.uint 1) (.bytes (ByteArray.mk #[0])) := by
  simp [SszValue.wellTyped_iff (.uint _) (.bytes _)] <;> decide

private theorem wtM04 :
    ¬ SszValue.WellTyped (.uint 1) (.list [.bool true]) := by
  simp [SszValue.wellTyped_iff (.uint _) (.list _)] <;> decide

private theorem wtM05 :
    ¬ SszValue.WellTyped (.uint 1) (.container [.bool true]) := by
  simp [SszValue.wellTyped_iff (.uint _) (.container _)] <;> decide

private theorem wtM06 :
    ¬ SszValue.WellTyped (.bool) (.uint 0) := by
  simp [SszValue.wellTyped_iff (.bool) (.uint _)] <;> decide

private theorem wtM07 :
    SszValue.WellTyped (.bool) (.bool true) := by
  simp [SszValue.wellTyped_iff (.bool) (.bool _)] <;> decide

private theorem wtM08 :
    ¬ SszValue.WellTyped (.bool) (.bytes (ByteArray.mk #[0])) := by
  simp [SszValue.wellTyped_iff (.bool) (.bytes _)] <;> decide

private theorem wtM09 :
    ¬ SszValue.WellTyped (.bool) (.list [.bool true]) := by
  simp [SszValue.wellTyped_iff (.bool) (.list _)] <;> decide

private theorem wtM10 :
    ¬ SszValue.WellTyped (.bool) (.container [.bool true]) := by
  simp [SszValue.wellTyped_iff (.bool) (.container _)] <;> decide

private theorem wtM11 :
    ¬ SszValue.WellTyped (.byteVector 1) (.uint 0) := by
  simp [SszValue.wellTyped_iff (.byteVector _) (.uint _)] <;> decide

private theorem wtM12 :
    ¬ SszValue.WellTyped (.byteVector 1) (.bool true) := by
  simp [SszValue.wellTyped_iff (.byteVector _) (.bool _)] <;> decide

private theorem wtM13 :
    SszValue.WellTyped (.byteVector 1) (.bytes (ByteArray.mk #[0])) := by
  simp [SszValue.wellTyped_iff (.byteVector _) (.bytes _)] <;> decide

private theorem wtM14 :
    ¬ SszValue.WellTyped (.byteVector 1) (.list [.bool true]) := by
  simp [SszValue.wellTyped_iff (.byteVector _) (.list _)] <;> decide

private theorem wtM15 :
    ¬ SszValue.WellTyped (.byteVector 1) (.container [.bool true]) := by
  simp [SszValue.wellTyped_iff (.byteVector _) (.container _)] <;> decide

private theorem wtM16 :
    ¬ SszValue.WellTyped (.byteList 1) (.uint 0) := by
  simp [SszValue.wellTyped_iff (.byteList _) (.uint _)] <;> decide

private theorem wtM17 :
    ¬ SszValue.WellTyped (.byteList 1) (.bool true) := by
  simp [SszValue.wellTyped_iff (.byteList _) (.bool _)] <;> decide

private theorem wtM18 :
    SszValue.WellTyped (.byteList 1) (.bytes (ByteArray.mk #[0])) := by
  simp [SszValue.wellTyped_iff (.byteList _) (.bytes _)] <;> decide

private theorem wtM19 :
    ¬ SszValue.WellTyped (.byteList 1) (.list [.bool true]) := by
  simp [SszValue.wellTyped_iff (.byteList _) (.list _)] <;> decide

private theorem wtM20 :
    ¬ SszValue.WellTyped (.byteList 1) (.container [.bool true]) := by
  simp [SszValue.wellTyped_iff (.byteList _) (.container _)] <;> decide

private theorem wtM21 :
    ¬ SszValue.WellTyped (.list .bool 1) (.uint 0) := by
  simp [SszValue.wellTyped_iff (.list _ _) (.uint _)] <;> decide

private theorem wtM22 :
    ¬ SszValue.WellTyped (.list .bool 1) (.bool true) := by
  simp [SszValue.wellTyped_iff (.list _ _) (.bool _)] <;> decide

private theorem wtM23 :
    ¬ SszValue.WellTyped (.list .bool 1) (.bytes (ByteArray.mk #[0])) := by
  simp [SszValue.wellTyped_iff (.list _ _) (.bytes _)] <;> decide

private theorem wtM24 :
    SszValue.WellTyped (.list .bool 1) (.list [.bool true]) := by
  simp [SszValue.wellTyped_iff (.bool) (.bool _),
    SszValue.wellTyped_iff (.list _ _) (.list _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtM25 :
    ¬ SszValue.WellTyped (.list .bool 1) (.container [.bool true]) := by
  simp [SszValue.wellTyped_iff (.list _ _) (.container _)] <;> decide

private theorem wtM26 :
    ¬ SszValue.WellTyped (.progressiveList .bool) (.uint 0) := by
  simp [SszValue.wellTyped_iff (.progressiveList _) (.uint _)] <;> decide

private theorem wtM27 :
    ¬ SszValue.WellTyped (.progressiveList .bool) (.bool true) := by
  simp [SszValue.wellTyped_iff (.progressiveList _) (.bool _)] <;> decide

private theorem wtM28 :
    ¬ SszValue.WellTyped (.progressiveList .bool) (.bytes (ByteArray.mk #[0])) := by
  simp [SszValue.wellTyped_iff (.progressiveList _) (.bytes _)] <;> decide

private theorem wtM29 :
    SszValue.WellTyped (.progressiveList .bool) (.list [.bool true]) := by
  simp [SszValue.wellTyped_iff (.bool) (.bool _),
    SszValue.wellTyped_iff (.progressiveList _) (.list _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq] <;> decide

private theorem wtM30 :
    ¬ SszValue.WellTyped (.progressiveList .bool) (.container [.bool true]) := by
  simp [SszValue.wellTyped_iff (.progressiveList _) (.container _)] <;> decide

private theorem wtM31 :
    ¬ SszValue.WellTyped (.progressiveByteList) (.uint 0) := by
  simp [SszValue.wellTyped_iff (.progressiveByteList) (.uint _)] <;> decide

private theorem wtM32 :
    ¬ SszValue.WellTyped (.progressiveByteList) (.bool true) := by
  simp [SszValue.wellTyped_iff (.progressiveByteList) (.bool _)] <;> decide

private theorem wtM33 :
    SszValue.WellTyped (.progressiveByteList) (.bytes (ByteArray.mk #[0])) := by
  simp [SszValue.wellTyped_iff (.progressiveByteList) (.bytes _)] <;> decide

private theorem wtM34 :
    ¬ SszValue.WellTyped (.progressiveByteList) (.list [.bool true]) := by
  simp [SszValue.wellTyped_iff (.progressiveByteList) (.list _)] <;> decide

private theorem wtM35 :
    ¬ SszValue.WellTyped (.progressiveByteList) (.container [.bool true]) := by
  simp [SszValue.wellTyped_iff (.progressiveByteList) (.container _)] <;> decide

private theorem wtM36 :
    ¬ SszValue.WellTyped (.container [.bool]) (.uint 0) := by
  simp [SszValue.wellTyped_iff (.container _) (.uint _)] <;> decide

private theorem wtM37 :
    ¬ SszValue.WellTyped (.container [.bool]) (.bool true) := by
  simp [SszValue.wellTyped_iff (.container _) (.bool _)] <;> decide

private theorem wtM38 :
    ¬ SszValue.WellTyped (.container [.bool]) (.bytes (ByteArray.mk #[0])) := by
  simp [SszValue.wellTyped_iff (.container _) (.bytes _)] <;> decide

private theorem wtM39 :
    ¬ SszValue.WellTyped (.container [.bool]) (.list [.bool true]) := by
  simp [SszValue.wellTyped_iff (.container _) (.list _)] <;> decide

private theorem wtM40 :
    SszValue.WellTyped (.container [.bool]) (.container [.bool true]) := by
  simp [SszValue.wellTyped_iff (.bool) (.bool _),
    SszValue.wellTyped_iff (.container _) (.container _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq,
    List.zip_cons_cons,
    List.zip_nil_right,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtM41 :
    ¬ SszValue.WellTyped (.progressiveContainer [false,true] [.bool]) (.uint 0) := by
  simp [SszValue.wellTyped_iff (.progressiveContainer _ _) (.uint _)] <;> decide

private theorem wtM42 :
    ¬ SszValue.WellTyped (.progressiveContainer [false,true] [.bool]) (.bool true) := by
  simp [SszValue.wellTyped_iff (.progressiveContainer _ _) (.bool _)] <;> decide

private theorem wtM43 :
    ¬ SszValue.WellTyped (.progressiveContainer [false,true] [.bool]) (.bytes (ByteArray.mk
      #[0])) := by
  simp [SszValue.wellTyped_iff (.progressiveContainer _ _) (.bytes _)] <;> decide

private theorem wtM44 :
    ¬ SszValue.WellTyped (.progressiveContainer [false,true] [.bool]) (.list [.bool true]) := by
  simp [SszValue.wellTyped_iff (.progressiveContainer _ _) (.list _)] <;> decide

private theorem wtM45 :
    SszValue.WellTyped (.progressiveContainer [false,true] [.bool]) (.container [.bool true]) := by
  simp [SszValue.wellTyped_iff (.bool) (.bool _),
    SszValue.wellTyped_iff (.progressiveContainer _ _) (.container _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq,
    List.zip_cons_cons,
    List.zip_nil_right,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtR01 :
    SszValue.WellTyped (.uint 1) (.uint 255) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtR02 :
    ¬ SszValue.WellTyped (.uint 1) (.uint 256) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtR03 :
    SszValue.WellTyped (.uint 1) (.uint 0) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtR04 :
    SszValue.WellTyped (.uint 2) (.uint 65535) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtR05 :
    ¬ SszValue.WellTyped (.uint 2) (.uint 65536) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtR06 :
    SszValue.WellTyped (.uint 2) (.uint 0) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtR07 :
    SszValue.WellTyped (.uint 4) (.uint (2^32-1)) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtR08 :
    ¬ SszValue.WellTyped (.uint 4) (.uint (2^32)) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtR09 :
    SszValue.WellTyped (.uint 4) (.uint 0) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtR10 :
    SszValue.WellTyped (.uint 8) (.uint (2^64-1)) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtR11 :
    ¬ SszValue.WellTyped (.uint 8) (.uint (2^64)) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtR12 :
    SszValue.WellTyped (.uint 8) (.uint 0) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtR13 :
    SszValue.WellTyped (.uint 16) (.uint (2^128-1)) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtR14 :
    ¬ SszValue.WellTyped (.uint 16) (.uint (2^128)) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtR15 :
    SszValue.WellTyped (.uint 16) (.uint 0) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtR16 :
    SszValue.WellTyped (.uint 32) (.uint (2^256-1)) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtR17 :
    ¬ SszValue.WellTyped (.uint 32) (.uint (2^256)) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtR18 :
    SszValue.WellTyped (.uint 32) (.uint 0) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtR19 :
    SszValue.WellTyped (.uint 0) (.uint 0) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtR20 :
    ¬ SszValue.WellTyped (.uint 0) (.uint 1) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtR21 :
    SszValue.WellTyped (.uint 3) (.uint (2^24-1)) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtR22 :
    ¬ SszValue.WellTyped (.uint 3) (.uint (2^24)) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem wtR23 :
    SszValue.WellTyped (.uint 3) (.uint 0) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _)] <;> decide

private theorem one_uint (width : Nat) (h : 0 < width) :
    SszValue.WellTyped (.uint width) (.uint 1) := by
  apply (SszValue.wellTyped_iff _ _).mpr
  exact Nat.one_lt_pow (Nat.ne_of_gt (Nat.mul_pos (by decide) h)) (by decide)

private theorem wtR24 :
    SszValue.WellTyped (.uint (2^256)) (.uint 1) := by
  exact one_uint _ (Nat.pow_pos (by decide))

private theorem wtB01 :
    SszValue.WellTyped (.byteVector 0) (.bytes ByteArray.empty) := by
  simp [SszValue.wellTyped_iff (.byteVector _) (.bytes _)] <;> decide

private theorem wtB02 :
    ¬ SszValue.WellTyped (.byteVector 0) (.bytes (ByteArray.mk #[0])) := by
  simp [SszValue.wellTyped_iff (.byteVector _) (.bytes _)] <;> decide

private theorem wtB03 :
    ¬ SszValue.WellTyped (.byteVector 1) (.bytes ByteArray.empty) := by
  simp [SszValue.wellTyped_iff (.byteVector _) (.bytes _)] <;> decide

private theorem wtB04 :
    SszValue.WellTyped (.byteVector 1) (.bytes (ByteArray.mk #[0])) := by
  simp [SszValue.wellTyped_iff (.byteVector _) (.bytes _)] <;> decide

private theorem wtB05 :
    SszValue.WellTyped (.byteVector 2) (.bytes (ByteArray.mk #[0,1])) := by
  simp [SszValue.wellTyped_iff (.byteVector _) (.bytes _)] <;> decide

private theorem wtB06 :
    ¬ SszValue.WellTyped (.byteVector 2) (.bytes (ByteArray.mk #[0])) := by
  simp [SszValue.wellTyped_iff (.byteVector _) (.bytes _)] <;> decide

private theorem wtB07 :
    ¬ SszValue.WellTyped (.byteVector 2) (.bytes (ByteArray.mk #[0,1,0])) := by
  simp [SszValue.wellTyped_iff (.byteVector _) (.bytes _)] <;> decide

private theorem wtB08 :
    SszValue.WellTyped (.byteList 0) (.bytes ByteArray.empty) := by
  simp [SszValue.wellTyped_iff (.byteList _) (.bytes _)] <;> decide

private theorem wtB09 :
    ¬ SszValue.WellTyped (.byteList 0) (.bytes (ByteArray.mk #[0])) := by
  simp [SszValue.wellTyped_iff (.byteList _) (.bytes _)] <;> decide

private theorem wtB10 :
    SszValue.WellTyped (.byteList 2) (.bytes (ByteArray.mk #[0,1])) := by
  simp [SszValue.wellTyped_iff (.byteList _) (.bytes _)] <;> decide

private theorem wtB11 :
    ¬ SszValue.WellTyped (.byteList 1) (.bytes (ByteArray.mk #[0,1])) := by
  simp [SszValue.wellTyped_iff (.byteList _) (.bytes _)] <;> decide

private theorem wtB12 :
    SszValue.WellTyped (.byteList (2^256)) (.bytes ByteArray.empty) ∧ SszValue.WellTyped
      (.progressiveByteList) (.bytes ByteArray.empty) ∧ SszValue.WellTyped (.progressiveByteList)
      (.bytes (ByteArray.mk #[0,1,0])) := by
  simp [SszValue.wellTyped_iff (.byteList _) (.bytes _),
    SszValue.wellTyped_iff (.progressiveByteList) (.bytes _)] <;> decide

private theorem wtL01 :
    SszValue.WellTyped (.list (.uint 1) 0) (.list []) := by
  simp [SszValue.wellTyped_iff (.list _ _) (.list _),
    false_implies,
    implies_true,
    List.not_mem_nil,
    List.length_nil] <;> decide

private theorem wtL02 :
    ¬ SszValue.WellTyped (.list (.uint 1) 0) (.list [.uint 0]) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _),
    SszValue.wellTyped_iff (.list _ _) (.list _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtL03 :
    SszValue.WellTyped (.list (.uint 3) 0) (.list []) := by
  simp [SszValue.wellTyped_iff (.list _ _) (.list _),
    false_implies,
    implies_true,
    List.not_mem_nil,
    List.length_nil] <;> decide

private theorem wtL04 :
    SszValue.WellTyped (.list (.container []) 0) (.list []) := by
  simp [SszValue.wellTyped_iff (.list _ _) (.list _),
    false_implies,
    implies_true,
    List.not_mem_nil,
    List.length_nil] <;> decide

private theorem wtL05 :
    SszValue.WellTyped (.progressiveList (.uint 3)) (.list []) := by
  simp [SszValue.wellTyped_iff (.progressiveList _) (.list _),
    false_implies,
    implies_true,
    List.not_mem_nil] <;> decide

private theorem wtL06 :
    SszValue.WellTyped (.progressiveList (.uint 0)) (.list [.uint 0]) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _),
    SszValue.wellTyped_iff (.progressiveList _) (.list _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq] <;> decide

private theorem wtL07 :
    ¬ SszValue.WellTyped (.progressiveList (.uint 0)) (.list [.uint 1]) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _),
    SszValue.wellTyped_iff (.progressiveList _) (.list _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq] <;> decide

private theorem wtL08 :
    SszValue.WellTyped (.list (.uint 1) 2) (.list [.uint 0,.uint 255]) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _),
    SszValue.wellTyped_iff (.list _ _) (.list _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq_or_imp,
    forall_eq,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtL09 :
    ¬ SszValue.WellTyped (.list (.uint 1) 1) (.list [.uint 0,.uint 255]) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _),
    SszValue.wellTyped_iff (.list _ _) (.list _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq_or_imp,
    forall_eq,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtL10 :
    ¬ SszValue.WellTyped (.list (.uint 1) 2) (.list [.uint 0,.uint 256]) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _),
    SszValue.wellTyped_iff (.list _ _) (.list _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq_or_imp,
    forall_eq,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtL11 :
    SszValue.WellTyped (.list .bool 2) (.list [.bool false,.bool true]) := by
  simp [SszValue.wellTyped_iff (.bool) (.bool _),
    SszValue.wellTyped_iff (.list _ _) (.list _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq_or_imp,
    forall_eq,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtL12 :
    ¬ SszValue.WellTyped (.list .bool 2) (.list [.bool true,.uint 1]) := by
  simp [SszValue.wellTyped_iff (.bool) (.uint _),
    SszValue.wellTyped_iff (.bool) (.bool _),
    SszValue.wellTyped_iff (.list _ _) (.list _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq_or_imp,
    forall_eq,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtL13 :
    ¬ SszValue.WellTyped (.list (.uint 1) 2) (.list [.bool true,.uint 1]) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _),
    SszValue.wellTyped_iff (.uint _) (.bool _),
    SszValue.wellTyped_iff (.list _ _) (.list _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq_or_imp,
    forall_eq,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtL14 :
    SszValue.WellTyped (.progressiveList (.uint 1)) (.list [.uint 0,.uint 255,.uint 1]) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _),
    SszValue.wellTyped_iff (.progressiveList _) (.list _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq_or_imp,
    forall_eq] <;> decide

private theorem wtL15 :
    ¬ SszValue.WellTyped (.progressiveList (.uint 1)) (.list [.uint 0,.uint 256]) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _),
    SszValue.wellTyped_iff (.progressiveList _) (.list _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq_or_imp,
    forall_eq] <;> decide

private theorem wtL16 :
    SszValue.WellTyped (.list (.uint 1) (2^256)) (.list [.uint 0]) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _),
    SszValue.wellTyped_iff (.list _ _) (.list _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtF01 :
    SszValue.WellTyped (.container []) (.container []) := by
  simp [SszValue.wellTyped_iff (.container _) (.container _),
    false_implies,
    implies_true,
    List.not_mem_nil,
    List.zip_nil_right,
    List.length_nil] <;> decide

private theorem wtF02 :
    ¬ SszValue.WellTyped (.container []) (.container [.bool true]) := by
  simp [SszValue.wellTyped_iff (.container _) (.container _),
    false_implies,
    implies_true,
    List.not_mem_nil,
    List.zip_nil_left,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtF03 :
    ¬ SszValue.WellTyped (.container [.bool]) (.container []) := by
  simp [SszValue.wellTyped_iff (.container _) (.container _),
    false_implies,
    implies_true,
    List.not_mem_nil,
    List.zip_nil_right,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtF04 :
    SszValue.WellTyped (.container [.bool]) (.container [.bool false]) := by
  simp [SszValue.wellTyped_iff (.bool) (.bool _),
    SszValue.wellTyped_iff (.container _) (.container _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq,
    List.zip_cons_cons,
    List.zip_nil_right,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtF05 :
    ¬ SszValue.WellTyped (.container [.bool]) (.container [.bool false,.bool true]) := by
  simp [SszValue.wellTyped_iff (.bool) (.bool _),
    SszValue.wellTyped_iff (.container _) (.container _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq,
    List.zip_cons_cons,
    List.zip_nil_left,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtF06 :
    SszValue.WellTyped (.container [.uint 1,.bool]) (.container [.uint 1,.bool true]) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _),
    SszValue.wellTyped_iff (.bool) (.bool _),
    SszValue.wellTyped_iff (.container _) (.container _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq_or_imp,
    forall_eq,
    List.zip_cons_cons,
    List.zip_nil_right,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtF07 :
    ¬ SszValue.WellTyped (.container [.uint 1,.bool]) (.container [.bool true,.uint 1]) := by
  simp [SszValue.wellTyped_iff (.uint _) (.bool _),
    SszValue.wellTyped_iff (.bool) (.uint _),
    SszValue.wellTyped_iff (.container _) (.container _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq_or_imp,
    forall_eq,
    List.zip_cons_cons,
    List.zip_nil_right,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtF08 :
    SszValue.WellTyped (.container [.uint 1,.uint 1]) (.container [.uint 0,.uint 255]) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _),
    SszValue.wellTyped_iff (.container _) (.container _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq_or_imp,
    forall_eq,
    List.zip_cons_cons,
    List.zip_nil_right,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtF09 :
    ¬ SszValue.WellTyped (.container [.uint 1,.uint 1]) (.container [.uint 0,.uint 256]) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _),
    SszValue.wellTyped_iff (.container _) (.container _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq_or_imp,
    forall_eq,
    List.zip_cons_cons,
    List.zip_nil_right,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtF10 :
    SszValue.WellTyped (.progressiveContainer [false,true] [.bool]) (.container [.bool true]) := by
  simp [SszValue.wellTyped_iff (.bool) (.bool _),
    SszValue.wellTyped_iff (.progressiveContainer _ _) (.container _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq,
    List.zip_cons_cons,
    List.zip_nil_right,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtF11 :
    SszValue.WellTyped (.progressiveContainer [true,false] [.bool]) (.container [.bool true]) := by
  simp [SszValue.wellTyped_iff (.bool) (.bool _),
    SszValue.wellTyped_iff (.progressiveContainer _ _) (.container _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq,
    List.zip_cons_cons,
    List.zip_nil_right,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtF12 :
    SszValue.WellTyped (.progressiveContainer [] [.bool]) (.container [.bool true]) := by
  simp [SszValue.wellTyped_iff (.bool) (.bool _),
    SszValue.wellTyped_iff (.progressiveContainer _ _) (.container _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq,
    List.zip_cons_cons,
    List.zip_nil_right,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtF13 :
    ¬ SszValue.WellTyped (.progressiveContainer [false,true] [.bool]) (.container []) ∧ ¬
      SszValue.WellTyped (.progressiveContainer [false,true] [.bool]) (.container [.bool
      true,.bool false]) := by
  simp [SszValue.wellTyped_iff (.bool) (.bool _),
    SszValue.wellTyped_iff (.progressiveContainer _ _) (.container _),
    false_implies,
    implies_true,
    List.mem_cons,
    List.not_mem_nil,
    forall_eq,
    List.zip_cons_cons,
    List.zip_nil_left,
    List.zip_nil_right,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtF14 :
    ¬ SszValue.WellTyped (.progressiveContainer [true,false] [.bool]) (.container []) ∧ ¬
      SszValue.WellTyped (.progressiveContainer [true,false] [.bool]) (.container [.bool
      true,.bool false]) := by
  simp [SszValue.wellTyped_iff (.bool) (.bool _),
    SszValue.wellTyped_iff (.progressiveContainer _ _) (.container _),
    false_implies,
    implies_true,
    List.mem_cons,
    List.not_mem_nil,
    forall_eq,
    List.zip_cons_cons,
    List.zip_nil_left,
    List.zip_nil_right,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtF15 :
    ¬ SszValue.WellTyped (.progressiveContainer [] [.bool]) (.container []) ∧ ¬
      SszValue.WellTyped (.progressiveContainer [] [.bool]) (.container [.bool true,.bool false])
      := by
  simp [SszValue.wellTyped_iff (.bool) (.bool _),
    SszValue.wellTyped_iff (.progressiveContainer _ _) (.container _),
    false_implies,
    implies_true,
    List.mem_cons,
    List.not_mem_nil,
    forall_eq,
    List.zip_cons_cons,
    List.zip_nil_left,
    List.zip_nil_right,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtF16 :
    SszValue.WellTyped (.progressiveContainer [true] []) (.container []) ∧ SszValue.WellTyped
      (.progressiveContainer [] []) (.container []) := by
  simp [SszValue.wellTyped_iff (.progressiveContainer _ _) (.container _),
    false_implies,
    implies_true,
    List.not_mem_nil,
    List.zip_nil_right,
    List.length_nil] <;> decide

private theorem wtF17 :
    SszValue.WellTyped (.progressiveContainer [false,true] [.uint 1,.bool]) (.container [.uint
      1,.bool true]) ∧ SszValue.WellTyped (.progressiveContainer [false,true] [.uint 1,.uint 1])
      (.container [.uint 0,.uint 255]) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _),
    SszValue.wellTyped_iff (.bool) (.bool _),
    SszValue.wellTyped_iff (.progressiveContainer _ _) (.container _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq_or_imp,
    forall_eq,
    List.zip_cons_cons,
    List.zip_nil_right,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtF18 :
    ¬ SszValue.WellTyped (.progressiveContainer [false,true] [.uint 1,.bool]) (.container [.bool
      true,.uint 1]) ∧ ¬ SszValue.WellTyped (.progressiveContainer [false,true] [.uint 1,.uint
      1]) (.container [.uint 0,.uint 256]) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _),
    SszValue.wellTyped_iff (.uint _) (.bool _),
    SszValue.wellTyped_iff (.bool) (.uint _),
    SszValue.wellTyped_iff (.progressiveContainer _ _) (.container _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq_or_imp,
    forall_eq,
    List.zip_cons_cons,
    List.zip_nil_right,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtN01 :
    SszValue.WellTyped (.container [.list (.uint 1) 2,.progressiveContainer [false,true]
      [.bool]]) (.container [.list [.uint 0,.uint 255],.container [.bool true]]) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _),
    SszValue.wellTyped_iff (.bool) (.bool _),
    SszValue.wellTyped_iff (.list _ _) (.list _),
    SszValue.wellTyped_iff (.container _) (.container _),
    SszValue.wellTyped_iff (.progressiveContainer _ _) (.container _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq_or_imp,
    forall_eq,
    List.zip_cons_cons,
    List.zip_nil_right,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtN02 :
    ¬ SszValue.WellTyped (.container [.list (.uint 1) 2,.progressiveContainer [false,true]
      [.bool]]) (.container [.list [.uint 0,.uint 256],.container [.bool true]]) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _),
    SszValue.wellTyped_iff (.bool) (.bool _),
    SszValue.wellTyped_iff (.list _ _) (.list _),
    SszValue.wellTyped_iff (.container _) (.container _),
    SszValue.wellTyped_iff (.progressiveContainer _ _) (.container _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq_or_imp,
    forall_eq,
    List.zip_cons_cons,
    List.zip_nil_right,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtN03 :
    ¬ SszValue.WellTyped (.container [.list (.uint 1) 2,.progressiveContainer [false,true]
      [.bool]]) (.container [.list [.uint 0,.uint 255],.container [.uint 1]]) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _),
    SszValue.wellTyped_iff (.bool) (.uint _),
    SszValue.wellTyped_iff (.list _ _) (.list _),
    SszValue.wellTyped_iff (.container _) (.container _),
    SszValue.wellTyped_iff (.progressiveContainer _ _) (.container _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq_or_imp,
    forall_eq,
    List.zip_cons_cons,
    List.zip_nil_right,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtN04 :
    SszValue.WellTyped (.list (.container [.bool]) 2) (.list [.container [.bool false],.container
      [.bool true]]) := by
  simp [SszValue.wellTyped_iff (.bool) (.bool _),
    SszValue.wellTyped_iff (.list _ _) (.list _),
    SszValue.wellTyped_iff (.container _) (.container _),
    List.mem_cons,
    List.not_mem_nil,
    forall_eq_or_imp,
    forall_eq,
    List.zip_cons_cons,
    List.zip_nil_right,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtN05 :
    ¬ SszValue.WellTyped (.list (.container [.bool]) 2) (.list [.container [.bool
      false],.container []]) := by
  simp [SszValue.wellTyped_iff (.bool) (.bool _),
    SszValue.wellTyped_iff (.list _ _) (.list _),
    SszValue.wellTyped_iff (.container _) (.container _),
    false_implies,
    implies_true,
    List.mem_cons,
    List.not_mem_nil,
    forall_eq_or_imp,
    forall_eq,
    List.zip_cons_cons,
    List.zip_nil_right,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtN06 :
    SszValue.WellTyped (.list (.list (.uint 0) 0) 1) (.list [.list []]) := by
  simp [SszValue.wellTyped_iff (.list _ _) (.list _),
    false_implies,
    implies_true,
    List.mem_cons,
    List.not_mem_nil,
    forall_eq,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtN07 :
    SszType.WellFormed (.bool) ∧ ¬ SszValue.WellTyped (.bool) (.uint 0) ∧ ¬ SszValue.WellTyped
      (.bool) (.uint 1) ∧ ¬ SszValue.WellTyped (.bool) (.bytes (ByteArray.mk #[1])) := by
  simp [SszValue.wellTyped_iff (.bool) (.uint _),
    SszValue.wellTyped_iff (.bool) (.bytes _),
    SszType.wellFormed_iff (.bool)] <;> decide

private theorem wtN08 :
    SszType.WellFormed (.uint 1) ∧ ¬ SszValue.WellTyped (.uint 1) (.uint 256) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _),
    SszType.wellFormed_iff (.uint _),
    List.mem_cons,
    List.not_mem_nil] <;> decide

private theorem wtN09 :
    SszValue.WellTyped (.uint 3) (.uint 0) ∧ ¬ SszType.WellFormed (.uint 3) := by
  simp [SszValue.wellTyped_iff (.uint _) (.uint _),
    SszType.wellFormed_iff (.uint _),
    List.mem_cons,
    List.not_mem_nil] <;> decide

private theorem wtN10 :
    SszValue.WellTyped (.list (.uint 3) 0) (.list []) ∧ ¬ SszType.WellFormed (.list (.uint 3) 0)
      := by
  simp [SszValue.wellTyped_iff (.list _ _) (.list _),
    SszType.wellFormed_iff (.uint _),
    SszType.wellFormed_iff (.list _ _),
    false_implies,
    implies_true,
    List.mem_cons,
    List.not_mem_nil,
    List.length_nil] <;> decide

private theorem wtZ01 :
    SszType.WellFormed (SszType.byteVector 0) ∧ (SszType.byteVector 0).fixedSize? = some 0 ∧
      SszValue.WellTyped (.byteVector 0) (.bytes ByteArray.empty) := by
  simp [SszValue.wellTyped_iff (.byteVector _) (.bytes _),
    SszType.wellFormed_iff (.byteVector _)] <;> decide

private theorem wtZ02 :
    SszValue.WellTyped (.list (.byteVector 0) 1) (.list []) ∧ SszValue.WellTyped (.list
      (.byteVector 0) 1) (.list [.bytes ByteArray.empty]) ∧ SszValue.list [] ≠ SszValue.list
      [.bytes ByteArray.empty] := by
  simp [SszValue.wellTyped_iff (.byteVector _) (.bytes _),
    SszValue.wellTyped_iff (.list _ _) (.list _),
    false_implies,
    implies_true,
    List.mem_cons,
    List.not_mem_nil,
    forall_eq,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtZ03 :
    SszValue.WellTyped (.progressiveList (.byteVector 0)) (.list []) ∧ SszValue.WellTyped
      (.progressiveList (.byteVector 0)) (.list [.bytes ByteArray.empty]) ∧ (0:Nat)*0 = 1*0 := by
  simp [SszValue.wellTyped_iff (.byteVector _) (.bytes _),
    SszValue.wellTyped_iff (.progressiveList _) (.list _),
    false_implies,
    implies_true,
    List.mem_cons,
    List.not_mem_nil,
    forall_eq] <;> decide

private theorem wtZ04 :
    SszType.WellFormed (.list (SszType.container [.byteVector 0]) 1) ∧ SszValue.WellTyped (.list
      (.container [.byteVector 0]) 1) (.list []) ∧ SszValue.WellTyped (.list (.container
      [.byteVector 0]) 1) (.list [.container [.bytes ByteArray.empty]]) ∧ (SszType.container
      [.byteVector 0]).fixedSize? = some 0 := by
  simp [SszValue.wellTyped_iff (.byteVector _) (.bytes _),
    SszValue.wellTyped_iff (.list _ _) (.list _),
    SszValue.wellTyped_iff (.container _) (.container _),
    SszType.wellFormed_iff (.byteVector _),
    SszType.wellFormed_iff (.list _ _),
    SszType.wellFormed_iff (.container _),
    false_implies,
    implies_true,
    List.mem_cons,
    List.not_mem_nil,
    forall_eq,
    List.zip_cons_cons,
    List.zip_nil_right,
    List.length_cons,
    List.length_nil] <;> decide

private theorem wtZ05 :
    ¬(∀ xs ys:List SszValue,  SszValue.WellTyped (.list (.byteVector 0) 1) (.list xs) →
      SszValue.WellTyped (.list (.byteVector 0) 1) (.list ys) → xs.length*0 = ys.length*0 → xs =
      ys) := by
  intro h
  have ha : SszValue.WellTyped (.list (.byteVector 0) 1) (.list []) := by
    simp only [SszValue.wellTyped_iff (.list _ _) _,
    SszValue.wellTyped_iff (.byteVector _) _,
    List.length_nil,
    List.not_mem_nil,
    false_implies,
    implies_true]
    decide
  have hb : SszValue.WellTyped (.list (.byteVector 0) 1)
      (.list [.bytes ByteArray.empty]) := by
    simp only [SszValue.wellTyped_iff (.list _ _) _,
    SszValue.wellTyped_iff (.byteVector _) _,
    List.length_nil,
    List.length_cons,
    List.mem_cons,
    List.not_mem_nil,
    forall_eq_or_imp,
    false_implies,
    implies_true]
    decide
  have he := h [] [.bytes ByteArray.empty] ha hb (by simp)
  cases he

end STFSpec.Conformance.Codec
