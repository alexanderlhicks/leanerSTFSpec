/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.SszCountRecoverable

/-!
# SSZ count-recovery semantic controls

Library `EthConformance`. Ordinary kernel-checked finite regressions through the public
constructor and fixed-size laws; no decoder or native Prop producer is introduced.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §4.
-/

namespace STFSpec.Conformance.Codec
open STFSpec.Codec

private theorem tag_row_0 :
    Ssz.CountRecoverable (.uint 0) (.uint 999) ∧
    ¬ Ssz.CountRecoverable (.uint 0) (.bool true) ∧
    ¬ Ssz.CountRecoverable (.uint 0) (.bytes ByteArray.empty) ∧
    ¬ Ssz.CountRecoverable (.uint 0) (.list []) ∧
    ¬ Ssz.CountRecoverable (.uint 0) (.container []) := by
  simp [Ssz.countRecoverable_iff (.uint 0) _]

private theorem tag_row_1 :
    ¬ Ssz.CountRecoverable (.bool) (.uint 999) ∧
    Ssz.CountRecoverable (.bool) (.bool true) ∧
    ¬ Ssz.CountRecoverable (.bool) (.bytes ByteArray.empty) ∧
    ¬ Ssz.CountRecoverable (.bool) (.list []) ∧
    ¬ Ssz.CountRecoverable (.bool) (.container []) := by
  simp [Ssz.countRecoverable_iff (.bool) _]

private theorem tag_row_2 :
    ¬ Ssz.CountRecoverable (.byteVector 0) (.uint 999) ∧
    ¬ Ssz.CountRecoverable (.byteVector 0) (.bool true) ∧
    Ssz.CountRecoverable (.byteVector 0) (.bytes ByteArray.empty) ∧
    ¬ Ssz.CountRecoverable (.byteVector 0) (.list []) ∧
    ¬ Ssz.CountRecoverable (.byteVector 0) (.container []) := by
  simp [Ssz.countRecoverable_iff (.byteVector 0) _]

private theorem tag_row_3 :
    ¬ Ssz.CountRecoverable (.byteList 0) (.uint 999) ∧
    ¬ Ssz.CountRecoverable (.byteList 0) (.bool true) ∧
    Ssz.CountRecoverable (.byteList 0) (.bytes ByteArray.empty) ∧
    ¬ Ssz.CountRecoverable (.byteList 0) (.list []) ∧
    ¬ Ssz.CountRecoverable (.byteList 0) (.container []) := by
  simp [Ssz.countRecoverable_iff (.byteList 0) _]

private theorem tag_row_4 :
    ¬ Ssz.CountRecoverable (.list .bool 0) (.uint 999) ∧
    ¬ Ssz.CountRecoverable (.list .bool 0) (.bool true) ∧
    ¬ Ssz.CountRecoverable (.list .bool 0) (.bytes ByteArray.empty) ∧
    Ssz.CountRecoverable (.list .bool 0) (.list []) ∧
    ¬ Ssz.CountRecoverable (.list .bool 0) (.container []) := by
  simp [Ssz.countRecoverable_iff (.list .bool 0) _, SszType.fixedSize?_eq .bool]

private theorem tag_row_5 :
    ¬ Ssz.CountRecoverable (.progressiveList .bool) (.uint 999) ∧
    ¬ Ssz.CountRecoverable (.progressiveList .bool) (.bool true) ∧
    ¬ Ssz.CountRecoverable (.progressiveList .bool) (.bytes ByteArray.empty) ∧
    Ssz.CountRecoverable (.progressiveList .bool) (.list []) ∧
    ¬ Ssz.CountRecoverable (.progressiveList .bool) (.container []) := by
  simp [Ssz.countRecoverable_iff (.progressiveList .bool) _, SszType.fixedSize?_eq .bool]

private theorem tag_row_6 :
    ¬ Ssz.CountRecoverable (.progressiveByteList) (.uint 999) ∧
    ¬ Ssz.CountRecoverable (.progressiveByteList) (.bool true) ∧
    Ssz.CountRecoverable (.progressiveByteList) (.bytes ByteArray.empty) ∧
    ¬ Ssz.CountRecoverable (.progressiveByteList) (.list []) ∧
    ¬ Ssz.CountRecoverable (.progressiveByteList) (.container []) := by
  simp [Ssz.countRecoverable_iff (.progressiveByteList) _]

private theorem tag_row_7 :
    ¬ Ssz.CountRecoverable (.container []) (.uint 999) ∧
    ¬ Ssz.CountRecoverable (.container []) (.bool true) ∧
    ¬ Ssz.CountRecoverable (.container []) (.bytes ByteArray.empty) ∧
    ¬ Ssz.CountRecoverable (.container []) (.list []) ∧
    Ssz.CountRecoverable (.container []) (.container []) := by
  simp [Ssz.countRecoverable_iff (.container []) _]

private theorem tag_row_8 :
    ¬ Ssz.CountRecoverable (.progressiveContainer [false, true] []) (.uint 999) ∧
    ¬ Ssz.CountRecoverable (.progressiveContainer [false, true] []) (.bool true) ∧
    ¬ Ssz.CountRecoverable (.progressiveContainer [false, true] []) (.bytes ByteArray.empty) ∧
    ¬ Ssz.CountRecoverable (.progressiveContainer [false, true] []) (.list []) ∧
    Ssz.CountRecoverable (.progressiveContainer [false, true] []) (.container []) := by
  simp [Ssz.countRecoverable_iff (.progressiveContainer [false, true] []) _]

private theorem direct_zero_products :
    Ssz.CountRecoverable (.byteVector 0) (.bytes ByteArray.empty) ∧
    Ssz.CountRecoverable (.container []) (.container []) ∧
    Ssz.CountRecoverable (.container [.container [.byteVector 0],
      .container [.byteVector 0, .byteVector 0]])
      (.container [.container [.bytes ByteArray.empty],
        .container [.bytes ByteArray.empty, .bytes ByteArray.empty]]) := by
  simp [Ssz.countRecoverable_iff (.byteVector _) (.bytes _),
    Ssz.countRecoverable_iff (.container _) (.container _)]

private theorem zero_immediate_elements :
    ¬ Ssz.CountRecoverable (.list (.byteVector 0) 0) (.list []) ∧
    ¬ Ssz.CountRecoverable (.list (.byteVector 0) 2) (.list [.bytes ByteArray.empty]) ∧
    ¬ Ssz.CountRecoverable (.progressiveList (.uint 0)) (.list []) ∧
    ¬ Ssz.CountRecoverable (.list (.container []) 0) (.list []) ∧
    ¬ Ssz.CountRecoverable (.progressiveList (.container [.byteVector 0,
      .progressiveContainer [] [.uint 0]])) (.list []) := by
  simp [Ssz.countRecoverable_iff (.byteVector _) (.bytes _),
    Ssz.countRecoverable_iff (.list _ _) (.list _),
    Ssz.countRecoverable_iff (.progressiveList _) (.list _),
    SszType.fixedSize?_eq (.uint _),
    SszType.fixedSize?_eq (.byteVector _),
    SszType.fixedSize?_eq (.container _),
    SszType.fixedSize?_eq (.progressiveContainer _ _)]

private theorem empty_variable_outer :
    Ssz.CountRecoverable (.list (.list (.byteVector 0) 2) 0) (.list []) ∧
    Ssz.CountRecoverable (.progressiveList (.container [.byteVector 0,
      .list (.byteVector 0) 2])) (.list []) ∧
    Ssz.CountRecoverable (.list (.container [.uint 3, .byteList 0]) 0) (.list []) := by
  simp [Ssz.countRecoverable_iff (.list _ _) (.list _),
    Ssz.countRecoverable_iff (.progressiveList _) (.list _),
    SszType.fixedSize?_eq (.uint _),
    SszType.fixedSize?_eq (.byteVector _),
    SszType.fixedSize?_eq (.byteList _),
    SszType.fixedSize?_eq (.list _ _),
    SszType.fixedSize?_eq (.container _)]

private theorem actual_offending_children :
    ¬ Ssz.CountRecoverable (.list (.list (.byteVector 0) 2) 2)
      (.list [.list []]) ∧
    ¬ Ssz.CountRecoverable (.progressiveList (.container [.byteVector 0,
      .list (.byteVector 0) 2]))
      (.list [.container [.bytes ByteArray.empty, .list []]]) ∧
    ¬ Ssz.CountRecoverable (.container [.bool, .list (.uint 0) 0])
      (.container [.bool true, .list []]) := by
  simp [Ssz.countRecoverable_iff (.bool) (.bool _),
    Ssz.countRecoverable_iff (.byteVector _) (.bytes _),
    Ssz.countRecoverable_iff (.list _ _) (.list _),
    Ssz.countRecoverable_iff (.progressiveList _) (.list _),
    Ssz.countRecoverable_iff (.container _) (.container _),
    SszType.fixedSize?_eq (.uint _),
    SszType.fixedSize?_eq (.byteVector _),
    SszType.fixedSize?_eq (.list _ _),
    SszType.fixedSize?_eq (.container _)]

private theorem arity :
    ¬ Ssz.CountRecoverable (.container []) (.container [.uint 0]) ∧
    ¬ Ssz.CountRecoverable (.container [.uint 0]) (.container []) ∧
    ¬ Ssz.CountRecoverable (.progressiveContainer [] []) (.container [.bool false]) ∧
    ¬ Ssz.CountRecoverable (.progressiveContainer [true] [.bool]) (.container []) ∧
    ¬ Ssz.CountRecoverable (.container [.bool, .bool]) (.container [.bool true]) := by
  simp [Ssz.countRecoverable_iff (.bool) (.bool _),
    Ssz.countRecoverable_iff (.container _) (.container _),
    Ssz.countRecoverable_iff (.progressiveContainer _ _) (.container _)]

private theorem leaf_and_limit_independence :
    Ssz.CountRecoverable (.uint 0) (.uint 999) ∧
    Ssz.CountRecoverable (.byteVector 0) (.bytes (ByteArray.mk #[1, 2])) ∧
    Ssz.CountRecoverable (.byteList 0) (.bytes (ByteArray.mk #[1, 2])) ∧
    Ssz.CountRecoverable (.progressiveByteList) (.bytes (ByteArray.mk #[0, 255])) ∧
    Ssz.CountRecoverable (.list (.uint 3) 0) (.list [.uint 999, .uint 0]) := by
  simp [Ssz.countRecoverable_iff (.uint _) (.uint _),
    Ssz.countRecoverable_iff (.byteVector _) (.bytes _),
    Ssz.countRecoverable_iff (.byteList _) (.bytes _),
    Ssz.countRecoverable_iff (.progressiveByteList) (.bytes _),
    Ssz.countRecoverable_iff (.list _ _) (.list _),
    SszType.fixedSize?_eq (.uint _)]

private theorem mask_independence :
    Ssz.CountRecoverable (.progressiveContainer [false, true] [.bool])
      (.container [.bool true]) ∧
    Ssz.CountRecoverable (.progressiveContainer [true, false] [.bool])
      (.container [.bool true]) := by
  simp [Ssz.countRecoverable_iff (.bool) (.bool _),
    Ssz.countRecoverable_iff (.progressiveContainer _ _) (.container _)]

private theorem field_order_and_all_members :
    Ssz.CountRecoverable (.container [.bool, .uint 0])
      (.container [.bool true, .uint 999]) ∧
    ¬ Ssz.CountRecoverable (.container [.bool, .uint 0])
      (.container [.uint 999, .bool true]) ∧
    ¬ Ssz.CountRecoverable (.list .bool 100)
      (.list [.bool true, .bool false, .uint 0]) := by
  simp [Ssz.countRecoverable_iff (.uint _) (.uint _),
    Ssz.countRecoverable_iff (.bool) (.bool _),
    Ssz.countRecoverable_iff (.list _ _) (.list _),
    Ssz.countRecoverable_iff (.container _) (.container _),
    Ssz.countRecoverable_iff (.bool) (.uint _),
    Ssz.countRecoverable_iff (.uint _) (.bool _),
    SszType.fixedSize?_eq (.bool)]

end STFSpec.Conformance.Codec
