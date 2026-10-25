/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Structural SSZ well-formedness signed controls

Library `EthConformance`. Private complete proposition obligations through the public Codec
facade; no executable validator or source-class/codec/root admission is asserted.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–4/§7.
-/

namespace STFSpec.Conformance.Codec

open STFSpec.Codec

private theorem control_w01 : SszType.WellFormed (.uint 1) := by
  simp only [SszType.wellFormed_iff (.uint _), List.mem_cons, Nat.reduceEqDiff, List.not_mem_nil,
    or_self,
    or_false]

private theorem control_w02 : SszType.WellFormed (.uint 2) := by
  simp only [SszType.wellFormed_iff (.uint _), List.mem_cons, Nat.succ_ne_self, Nat.reduceEqDiff,
    List.not_mem_nil, or_self, or_false, or_true]

private theorem control_w03 : SszType.WellFormed (.uint 4) := by
  simp only [SszType.wellFormed_iff (.uint _), List.mem_cons, Nat.reduceEqDiff, List.not_mem_nil,
    or_self,
    or_false, or_true]

private theorem control_w04 : SszType.WellFormed (.uint 8) := by
  simp only [SszType.wellFormed_iff (.uint _), List.mem_cons, Nat.reduceEqDiff, List.not_mem_nil,
    or_self,
    or_false, or_true]

private theorem control_w05 : SszType.WellFormed (.uint 16) := by
  simp only [SszType.wellFormed_iff (.uint _), List.mem_cons, Nat.reduceEqDiff, List.not_mem_nil,
    or_self,
    or_false, or_true]

private theorem control_w06 : SszType.WellFormed (.uint 32) := by
  simp only [SszType.wellFormed_iff (.uint _), List.mem_cons, Nat.reduceEqDiff, List.not_mem_nil,
    or_false,
    or_true]

private theorem control_w07 : ¬ SszType.WellFormed (.uint 0) := by
  simp only [SszType.wellFormed_iff (.uint _), List.mem_cons, Nat.zero_ne_one, reduceCtorEq,
    List.not_mem_nil,
    or_self, not_false_eq_true]

private theorem control_w08 : ¬ SszType.WellFormed (.uint 3) := by
  simp only [SszType.wellFormed_iff (.uint _), List.mem_cons, Nat.reduceEqDiff, Nat.succ_ne_self,
    List.not_mem_nil, or_self, not_false_eq_true]

private theorem control_w09 : ¬ SszType.WellFormed (.uint 7) := by
  simp only [SszType.wellFormed_iff (.uint _), List.mem_cons, Nat.reduceEqDiff, List.not_mem_nil,
    or_self,
    not_false_eq_true]

private theorem control_w10 : ¬ SszType.WellFormed (.uint 31) := by
  simp only [SszType.wellFormed_iff (.uint _), List.mem_cons, Nat.reduceEqDiff, List.not_mem_nil,
    or_self,
    not_false_eq_true]

private theorem control_w11 : ¬ SszType.WellFormed (.uint 33) := by
  simp only [SszType.wellFormed_iff (.uint _), List.mem_cons, Nat.reduceEqDiff, Nat.succ_ne_self,
    List.not_mem_nil, or_self, not_false_eq_true]

private theorem control_w12 : ¬ SszType.WellFormed (.uint (2^256 + 17)) := by
  simp only [Nat.reducePow, Nat.reduceAdd, SszType.wellFormed_iff (.uint _), List.mem_cons,
    Nat.reduceEqDiff,
    List.not_mem_nil, or_self, not_false_eq_true]

private theorem control_w13 : SszType.WellFormed (.bool : SszType) := by
  simp only [SszType.wellFormed_iff .bool]

private theorem control_w14 : SszType.WellFormed (.byteVector 0) := by
  simp only [SszType.wellFormed_iff (.byteVector _)]

private theorem control_w15 : SszType.WellFormed (.byteVector 1) := by
  simp only [SszType.wellFormed_iff (.byteVector _)]

private theorem control_w16 : SszType.WellFormed (.byteVector (2^256 + 17)) := by
  simp only [Nat.reducePow, Nat.reduceAdd, SszType.wellFormed_iff (.byteVector _)]

private theorem control_w17 : SszType.WellFormed (.byteList 0) := by
  simp only [SszType.wellFormed_iff (.byteList _)]

private theorem control_w18 : SszType.WellFormed (.byteList 1) := by
  simp only [SszType.wellFormed_iff (.byteList _)]

private theorem control_w19 : SszType.WellFormed (.byteList (2^256 + 17)) := by
  simp only [Nat.reducePow, Nat.reduceAdd, SszType.wellFormed_iff (.byteList _)]

private theorem control_w20 : SszType.WellFormed (.progressiveByteList : SszType) := by
  simp only [SszType.wellFormed_iff .progressiveByteList]

private theorem control_w21 : SszType.WellFormed (.byteVector 32) := by
  simp only [SszType.wellFormed_iff (.byteVector _)]

private theorem control_w22 : SszType.WellFormed (.byteList (2^32)) := by
  simp only [Nat.reducePow, SszType.wellFormed_iff (.byteList _)]

private theorem control_w23 : SszType.WellFormed (.list (.bool : SszType) 0) := by
  simp only [SszType.wellFormed_iff (.list _ _), SszType.wellFormed_iff .bool]

private theorem control_w24 : ¬ SszType.WellFormed (.list (.uint 3) 0) := by
  simp only [SszType.wellFormed_iff (.list _ _), SszType.wellFormed_iff (.uint _), List.mem_cons,
    Nat.reduceEqDiff, Nat.succ_ne_self, List.not_mem_nil, or_self, not_false_eq_true]

private theorem control_w25 : SszType.WellFormed (.list (.byteVector 0) 1) := by
  simp only [SszType.wellFormed_iff (.list _ _), SszType.wellFormed_iff (.byteVector _)]

private theorem control_w26 : SszType.WellFormed (.list (.byteList 0) 0) := by
  simp only [SszType.wellFormed_iff (.list _ _), SszType.wellFormed_iff (.byteList _)]

private theorem control_w27 : SszType.WellFormed (.progressiveList (.bool : SszType)) := by
  simp only [SszType.wellFormed_iff (.progressiveList _), SszType.wellFormed_iff .bool]

private theorem control_w28 : ¬ SszType.WellFormed (.progressiveList (.uint 3)) := by
  simp only [SszType.wellFormed_iff (.progressiveList _), SszType.wellFormed_iff (.uint _),
    List.mem_cons,
    Nat.reduceEqDiff, Nat.succ_ne_self, List.not_mem_nil, or_self, not_false_eq_true]

private theorem control_w29 : ¬ SszType.WellFormed (.list (.container []) 0) := by
  simp only [SszType.wellFormed_iff (.list _ _), SszType.wellFormed_iff (.container _), ne_eq,
    not_true_eq_false, List.not_mem_nil, false_implies, implies_true, and_true, not_false_eq_true]

private theorem control_w30 :
    SszType.WellFormed (.list (.progressiveList (.container [(.byteVector 0)])) (2^256 + 17)) := by
  simp only [Nat.reducePow, Nat.reduceAdd, SszType.wellFormed_iff (.list _ _),
    SszType.wellFormed_iff (.progressiveList _), SszType.wellFormed_iff (.container _), ne_eq,
    List.cons_ne_self,
    not_false_eq_true, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
    SszType.wellFormed_iff (.byteVector _),
    and_self]

private theorem control_w31 : ¬ SszType.WellFormed (.container []) := by
  simp only [SszType.wellFormed_iff (.container _), ne_eq, not_true_eq_false, List.not_mem_nil,
    false_implies,
    implies_true, and_true, not_false_eq_true]

private theorem control_w32 : SszType.WellFormed (.container [(.bool : SszType)]) := by
  simp only [SszType.wellFormed_iff (.container _), ne_eq, List.cons_ne_self, not_false_eq_true,
    List.mem_cons,
    List.not_mem_nil, or_false, forall_eq, SszType.wellFormed_iff .bool, and_self]

private theorem control_w33 : SszType.WellFormed (.container [(.byteVector 0)]) := by
  simp only [SszType.wellFormed_iff (.container _), ne_eq, List.cons_ne_self, not_false_eq_true,
    List.mem_cons,
    List.not_mem_nil, or_false, forall_eq, SszType.wellFormed_iff (.byteVector _), and_self]

private theorem control_w34 : SszType.WellFormed (.container [(.byteList 0)]) := by
  simp only [SszType.wellFormed_iff (.container _), ne_eq, List.cons_ne_self, not_false_eq_true,
    List.mem_cons,
    List.not_mem_nil, or_false, forall_eq, SszType.wellFormed_iff (.byteList _), and_self]

private theorem control_w35 : ¬ SszType.WellFormed (.container [(.uint 3)]) := by
  simp only [SszType.wellFormed_iff (.container _), ne_eq, List.cons_ne_self, not_false_eq_true,
    List.mem_cons,
    List.not_mem_nil, or_false, forall_eq, SszType.wellFormed_iff (.uint _), Nat.reduceEqDiff,
    Nat.succ_ne_self,
    or_self, and_false]

private theorem control_w36 : ¬ SszType.WellFormed (.container [(.uint 3),
    (.bool : SszType)]) := by
  simp only [SszType.wellFormed_iff (.container _), ne_eq, reduceCtorEq, not_false_eq_true,
    List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, SszType.wellFormed_iff (.uint _),
    Nat.reduceEqDiff, Nat.succ_ne_self,
    or_self, forall_eq, SszType.wellFormed_iff .bool, and_true, and_false]

private theorem control_w37 : ¬ SszType.WellFormed (.container [(.bool : SszType),
    (.uint 3)]) := by
  simp only [SszType.wellFormed_iff (.container _), ne_eq, reduceCtorEq, not_false_eq_true,
    List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, SszType.wellFormed_iff .bool, forall_eq,
    SszType.wellFormed_iff (.uint _), Nat.reduceEqDiff, Nat.succ_ne_self, or_self, and_false]

private theorem control_w38 : SszType.WellFormed (.container [(.bool : SszType),
    (.bool : SszType), (.byteVector 0)]) := by
  simp only [SszType.wellFormed_iff (.container _), ne_eq, reduceCtorEq, not_false_eq_true,
    List.mem_cons,
    List.not_mem_nil, or_false, or_self_left, forall_eq_or_imp, SszType.wellFormed_iff .bool,
    forall_eq,
    SszType.wellFormed_iff (.byteVector _), and_self]

private theorem control_w39 : ¬ SszType.WellFormed (.container [(.bool : SszType),
    (.container [(.container [])])]) := by
  simp only [SszType.wellFormed_iff (.container _), ne_eq, reduceCtorEq, not_false_eq_true,
    List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, SszType.wellFormed_iff .bool, forall_eq,
    List.cons_ne_self,
    not_true_eq_false, false_implies, implies_true, and_true, and_false]

private theorem control_w40 : SszType.WellFormed (.container [(.progressiveContainer [false,
    true] [(.list (.byteVector 0) 0)]), (.progressiveByteList : SszType)]) := by
  simp only [SszType.wellFormed_iff (.container _), ne_eq, reduceCtorEq, not_false_eq_true,
    List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp,
    SszType.wellFormed_iff (.progressiveContainer _ _),
    List.getLast?_cons_cons, List.getLast?_singleton, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.reduceAdd,
    Nat.reduceLeDiff, id_eq, Bool.false_eq_true, List.filter_cons_of_neg,
    List.filter_cons_of_pos, List.filter_nil,
    forall_eq, SszType.wellFormed_iff (.list _ _), SszType.wellFormed_iff (.byteVector _),
    and_self,
    SszType.wellFormed_iff .progressiveByteList]

private theorem control_w41 : ¬ SszType.WellFormed (.progressiveContainer [] []) := by
  simp only [SszType.wellFormed_iff (.progressiveContainer _ _), List.getLast?_nil, reduceCtorEq,
    List.length_nil, Nat.zero_le, List.filter_nil, List.not_mem_nil, false_implies, implies_true,
    and_self, and_true,
    not_false_eq_true]

private theorem control_w42 :
    ¬ SszType.WellFormed (.progressiveContainer [] [(.bool : SszType)]) := by
  simp only [SszType.wellFormed_iff (.progressiveContainer _ _), List.getLast?_nil, reduceCtorEq,
    List.length_nil, Nat.zero_le, List.filter_nil, List.length_cons, Nat.zero_add,
    Nat.zero_ne_one, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq, SszType.wellFormed_iff .bool, and_true, and_false,
    and_self,
    not_false_eq_true]

private theorem control_w43 : ¬ SszType.WellFormed (.progressiveContainer [false] []) := by
  simp only [SszType.wellFormed_iff (.progressiveContainer _ _), List.getLast?_singleton,
    Option.some.injEq,
    Bool.false_eq_true, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceLeDiff, id_eq,
    not_false_eq_true,
    List.filter_cons_of_neg, List.filter_nil, List.not_mem_nil, false_implies, implies_true,
    and_self, and_true]

private theorem control_w44 : ¬ SszType.WellFormed (.progressiveContainer [true] []) := by
  simp only [SszType.wellFormed_iff (.progressiveContainer _ _), List.getLast?_singleton,
    List.length_cons,
    List.length_nil, Nat.zero_add, Nat.reduceLeDiff, id_eq, List.filter_cons_of_pos,
    List.filter_nil, Nat.succ_ne_self,
    List.not_mem_nil, false_implies, implies_true, and_true, and_false, not_false_eq_true]

private theorem control_w45 :
    SszType.WellFormed (.progressiveContainer [true] [(.bool : SszType)]) := by
  simp only [SszType.wellFormed_iff (.progressiveContainer _ _), List.getLast?_singleton,
    List.length_cons,
    List.length_nil, Nat.zero_add, Nat.reduceLeDiff, id_eq, List.filter_cons_of_pos,
    List.filter_nil, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq, SszType.wellFormed_iff .bool, and_self]

private theorem control_w46 : ¬ SszType.WellFormed (.progressiveContainer [true,
    false] [(.bool : SszType)]) := by
  simp only [SszType.wellFormed_iff (.progressiveContainer _ _), List.getLast?_cons_cons,
    List.getLast?_singleton, Option.some.injEq, Bool.false_eq_true, List.length_cons,
    List.length_nil, Nat.zero_add,
    Nat.reduceAdd, Nat.reduceLeDiff, id_eq, List.filter_cons_of_pos, not_false_eq_true,
    List.filter_cons_of_neg,
    List.filter_nil, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
    SszType.wellFormed_iff .bool, and_self,
    and_true]

private theorem control_w47 : SszType.WellFormed (.progressiveContainer [false,
    true] [(.bool : SszType)]) := by
  simp only [SszType.wellFormed_iff (.progressiveContainer _ _), List.getLast?_cons_cons,
    List.getLast?_singleton, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
    Nat.reduceLeDiff, id_eq,
    Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg, List.filter_cons_of_pos,
    List.filter_nil,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq, SszType.wellFormed_iff .bool, and_self]

private theorem control_w48 : ¬ SszType.WellFormed (.progressiveContainer [true,
    true] [(.bool : SszType)]) := by
  simp only [SszType.wellFormed_iff (.progressiveContainer _ _), List.getLast?_cons_cons,
    List.getLast?_singleton, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
    Nat.reduceLeDiff, id_eq,
    List.filter_cons_of_pos, List.filter_nil, Nat.succ_ne_self, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq,
    SszType.wellFormed_iff .bool, and_true, and_false, not_false_eq_true]

private theorem control_w49 :
    ¬ SszType.WellFormed
      (.progressiveContainer [true] [(.bool : SszType), (.bool : SszType)]) := by
  simp only [SszType.wellFormed_iff (.progressiveContainer _ _), List.getLast?_singleton,
    List.length_cons,
    List.length_nil, Nat.zero_add, Nat.reduceLeDiff, id_eq, List.filter_cons_of_pos,
    List.filter_nil, Nat.reduceAdd,
    Nat.reduceEqDiff, List.mem_cons, List.not_mem_nil, or_false, or_self, forall_eq,
    SszType.wellFormed_iff .bool,
    and_true, and_false, not_false_eq_true]

private theorem control_w50 : ¬ SszType.WellFormed (.progressiveContainer [false,
    true] [(.uint 3)]) := by
  simp only [SszType.wellFormed_iff (.progressiveContainer _ _), List.getLast?_cons_cons,
    List.getLast?_singleton, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
    Nat.reduceLeDiff, id_eq,
    Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg, List.filter_cons_of_pos,
    List.filter_nil,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq, SszType.wellFormed_iff (.uint _),
    Nat.reduceEqDiff,
    Nat.succ_ne_self, or_self, and_false]

private theorem control_w51 : ¬ SszType.WellFormed (.progressiveContainer [true,
    true] [(.bool : SszType), (.uint 3)]) := by
  simp only [SszType.wellFormed_iff (.progressiveContainer _ _), List.getLast?_cons_cons,
    List.getLast?_singleton, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
    Nat.reduceLeDiff, id_eq,
    List.filter_cons_of_pos, List.filter_nil, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp,
    SszType.wellFormed_iff .bool, forall_eq, SszType.wellFormed_iff (.uint _), Nat.reduceEqDiff,
    Nat.succ_ne_self,
    or_self, and_false, not_false_eq_true]

private theorem control_w52 : ¬ SszType.WellFormed (.progressiveContainer [true,
    true] [(.uint 3), (.bool : SszType)]) := by
  simp only [SszType.wellFormed_iff (.progressiveContainer _ _), List.getLast?_cons_cons,
    List.getLast?_singleton, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
    Nat.reduceLeDiff, id_eq,
    List.filter_cons_of_pos, List.filter_nil, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp,
    SszType.wellFormed_iff (.uint _), Nat.reduceEqDiff, Nat.succ_ne_self, or_self, forall_eq,
    SszType.wellFormed_iff .bool, and_true, and_false, not_false_eq_true]

private theorem control_w53 :
    SszType.WellFormed (.progressiveContainer [true] [(.byteVector 0)]) := by
  simp only [SszType.wellFormed_iff (.progressiveContainer _ _), List.getLast?_singleton,
    List.length_cons,
    List.length_nil, Nat.zero_add, Nat.reduceLeDiff, id_eq, List.filter_cons_of_pos,
    List.filter_nil, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq, SszType.wellFormed_iff (.byteVector _), and_self]

private theorem control_w54 :
    SszType.WellFormed (.progressiveContainer [true] [(.byteList 0)]) := by
  simp only [SszType.wellFormed_iff (.progressiveContainer _ _), List.getLast?_singleton,
    List.length_cons,
    List.length_nil, Nat.zero_add, Nat.reduceLeDiff, id_eq, List.filter_cons_of_pos,
    List.filter_nil, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq, SszType.wellFormed_iff (.byteList _), and_self]

private theorem control_w55 :
    ¬ SszType.WellFormed (.progressiveContainer [true] [(.container [])]) := by
  simp only [SszType.wellFormed_iff (.progressiveContainer _ _), List.getLast?_singleton,
    List.length_cons,
    List.length_nil, Nat.zero_add, Nat.reduceLeDiff, id_eq, List.filter_cons_of_pos,
    List.filter_nil, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq, SszType.wellFormed_iff (.container _), ne_eq,
    not_true_eq_false,
    false_implies, implies_true, and_true, and_false, not_false_eq_true]

private theorem control_w56 :
    ¬ SszType.WellFormed (.progressiveContainer [true] [(.list (.uint 3) 0)]) := by
  simp only [SszType.wellFormed_iff (.progressiveContainer _ _), List.getLast?_singleton,
    List.length_cons,
    List.length_nil, Nat.zero_add, Nat.reduceLeDiff, id_eq, List.filter_cons_of_pos,
    List.filter_nil, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq, SszType.wellFormed_iff (.list _ _),
    SszType.wellFormed_iff (.uint _),
    Nat.reduceEqDiff, Nat.succ_ne_self, or_self, and_false, not_false_eq_true]

private theorem control_w57 :
    SszType.WellFormed (.progressiveContainer [true] [(.list (.bool : SszType) 0)]) := by
  simp only [SszType.wellFormed_iff (.progressiveContainer _ _), List.getLast?_singleton,
    List.length_cons,
    List.length_nil, Nat.zero_add, Nat.reduceLeDiff, id_eq, List.filter_cons_of_pos,
    List.filter_nil, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq, SszType.wellFormed_iff (.list _ _),
    SszType.wellFormed_iff .bool, and_self]

set_option maxRecDepth 2048 in
private theorem control_w58 :
    SszType.WellFormed
      (.progressiveContainer (List.replicate 255 true) (List.replicate 255 .bool)) := by
  simp only [List.reduceReplicate, SszType.wellFormed_iff (.progressiveContainer _ _),
    List.getLast?_cons_cons,
    List.getLast?_singleton, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
    Nat.reduceLeDiff, id_eq,
    List.filter_cons_of_pos, List.filter_nil, List.mem_cons, List.not_mem_nil, or_false, or_self,
    forall_eq,
    SszType.wellFormed_iff .bool, and_self]

set_option maxRecDepth 2048 in
private theorem control_w59 :
    SszType.WellFormed
      (.progressiveContainer (List.replicate 256 true) (List.replicate 256 .bool)) := by
  simp only [List.reduceReplicate, SszType.wellFormed_iff (.progressiveContainer _ _),
    List.getLast?_cons_cons,
    List.getLast?_singleton, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
    Std.le_refl, id_eq,
    List.filter_cons_of_pos, List.filter_nil, List.mem_cons, List.not_mem_nil, or_false, or_self,
    forall_eq,
    SszType.wellFormed_iff .bool, and_self]

set_option maxRecDepth 2048 in
private theorem control_w60 :
    ¬ SszType.WellFormed
      (.progressiveContainer (List.replicate 257 true) (List.replicate 257 .bool)) := by
  simp only [List.reduceReplicate, SszType.wellFormed_iff (.progressiveContainer _ _),
    List.getLast?_cons_cons,
    List.getLast?_singleton, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
    Nat.reduceLeDiff, id_eq,
    List.filter_cons_of_pos, List.filter_nil, List.mem_cons, List.not_mem_nil, or_false, or_self,
    forall_eq,
    SszType.wellFormed_iff .bool, and_self, and_true, and_false, not_false_eq_true]

set_option maxRecDepth 2048 in
private theorem control_w61 :
    SszType.WellFormed
      (.progressiveContainer (List.replicate 254 false ++ [true]) [(.bool : SszType)]) := by
  simp only [List.reduceReplicate, List.cons_append, List.nil_append,
    SszType.wellFormed_iff (.progressiveContainer _ _), List.getLast?_cons_cons,
    List.getLast?_singleton,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff, id_eq,
    Bool.false_eq_true,
    not_false_eq_true, List.filter_cons_of_neg, List.filter_cons_of_pos, List.filter_nil,
    List.mem_cons,
    List.not_mem_nil, or_false, forall_eq, SszType.wellFormed_iff .bool, and_self]

set_option maxRecDepth 2048 in
private theorem control_w62 :
    SszType.WellFormed
      (.progressiveContainer (List.replicate 255 false ++ [true]) [(.bool : SszType)]) := by
  simp only [List.reduceReplicate, List.cons_append, List.nil_append,
    SszType.wellFormed_iff (.progressiveContainer _ _), List.getLast?_cons_cons,
    List.getLast?_singleton,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Std.le_refl, id_eq,
    Bool.false_eq_true,
    not_false_eq_true, List.filter_cons_of_neg, List.filter_cons_of_pos, List.filter_nil,
    List.mem_cons,
    List.not_mem_nil, or_false, forall_eq, SszType.wellFormed_iff .bool, and_self]

set_option maxRecDepth 2048 in
private theorem control_w63 :
    ¬ SszType.WellFormed
      (.progressiveContainer (List.replicate 256 false ++ [true]) [(.bool : SszType)]) := by
  simp only [List.reduceReplicate, List.cons_append, List.nil_append,
    SszType.wellFormed_iff (.progressiveContainer _ _), List.getLast?_cons_cons,
    List.getLast?_singleton,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff, id_eq,
    Bool.false_eq_true,
    not_false_eq_true, List.filter_cons_of_neg, List.filter_cons_of_pos, List.filter_nil,
    List.mem_cons,
    List.not_mem_nil, or_false, forall_eq, SszType.wellFormed_iff .bool, and_self, and_true,
    and_false]

set_option maxRecDepth 2048 in
private theorem control_w64 :
    ¬ SszType.WellFormed
      (.progressiveContainer (List.replicate 255 true ++ [false]) (List.replicate 255 .bool)) := by
  simp only [List.reduceReplicate, List.cons_append, List.nil_append,
    SszType.wellFormed_iff (.progressiveContainer _ _), List.getLast?_cons_cons,
    List.getLast?_singleton,
    Option.some.injEq, Bool.false_eq_true, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.reduceAdd, Std.le_refl,
    id_eq, List.filter_cons_of_pos, not_false_eq_true, List.filter_cons_of_neg, List.filter_nil,
    List.mem_cons,
    List.not_mem_nil, or_false, or_self, forall_eq, SszType.wellFormed_iff .bool, and_self,
    and_true]

end STFSpec.Conformance.Codec
