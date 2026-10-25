/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Structural SSZ well-formedness facade clients

Library `EthConformance`. Private complete proposition obligations through the public Codec
facade; no executable validator or source-class/codec/root admission is asserted.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–4/§7.
-/

namespace STFSpec.Conformance.Codec

open STFSpec.Codec

private theorem client_c01 (w : Nat) :
    (SszType.uint w).WellFormed ↔ w ∈ [1, 2, 4, 8, 16, 32] := by
  exact SszType.wellFormed_iff _

private theorem client_c02 : SszType.bool.WellFormed := by
  exact (SszType.wellFormed_iff _).mpr True.intro

private theorem client_c03 (n : Nat) : (SszType.byteVector n).WellFormed := by
  exact (SszType.wellFormed_iff _).mpr True.intro

private theorem client_c04 (k : Nat) : (SszType.byteList k).WellFormed := by
  exact (SszType.wellFormed_iff _).mpr True.intro

private theorem client_c05 (t : SszType) (k : Nat) :
    (SszType.list t k).WellFormed ↔ t.WellFormed := by
  exact SszType.wellFormed_iff _

private theorem client_c06 (t : SszType) :
    (SszType.progressiveList t).WellFormed ↔ t.WellFormed := by
  exact SszType.wellFormed_iff _

private theorem client_c07 : SszType.progressiveByteList.WellFormed := by
  exact (SszType.wellFormed_iff _).mpr True.intro

private theorem client_c08 (fs : List SszType) :
    (SszType.container fs).WellFormed ↔ fs ≠ [] ∧ ∀ f ∈ fs, f.WellFormed := by
  exact SszType.wellFormed_iff _

private theorem client_c09 (ms : List Bool) (fs : List SszType) :
    (SszType.progressiveContainer ms fs).WellFormed ↔
      ms.getLast? = some true ∧ ms.length ≤ 256 ∧
      (ms.filter id).length = fs.length ∧ ∀ f ∈ fs, f.WellFormed := by
  exact SszType.wellFormed_iff _

private theorem client_c10 (t : SszType) (k l : Nat) :
    ((SszType.list t k).WellFormed ↔ (SszType.list t l).WellFormed) ∧
    ((SszType.list t 0).WellFormed → t.WellFormed) := by
  constructor
  · exact (SszType.wellFormed_iff (.list t k)).trans
      (SszType.wellFormed_iff (.list t l)).symm
  · exact (SszType.wellFormed_iff _).mp

private theorem client_c11 (fs : List SszType) (f : SszType)
    (h : (SszType.container fs).WellFormed) (hf : f ∈ fs) : f.WellFormed := by
  exact ((SszType.wellFormed_iff _).mp h).2 f hf

private theorem client_c12 (ms : List Bool) (fs : List SszType) (f : SszType)
    (h : (SszType.progressiveContainer ms fs).WellFormed) (hf : f ∈ fs) :
    f.WellFormed := by
  exact ((SszType.wellFormed_iff _).mp h).2.2.2 f hf

private theorem client_c13 :
    ¬ (SszType.uint 3).WellFormed ∧ (SszType.uint 3).fixedSize? = some 3 ∧
    ¬ (SszType.container []).WellFormed ∧ (SszType.container []).fixedSize? = some 0 ∧
    ¬ (SszType.progressiveContainer [] [.bool]).WellFormed ∧
    (SszType.progressiveContainer [] [.bool]).fixedSize? = some 1 := by
  simp only [SszType.wellFormed_iff (.uint _), List.mem_cons, Nat.reduceEqDiff, Nat.succ_ne_self,
    List.not_mem_nil, or_self, not_false_eq_true, SszType.fixedSize?_eq (.uint _),
    SszType.wellFormed_iff (.container _), ne_eq, not_true_eq_false, false_implies, implies_true,
    and_true,
    SszType.fixedSize?_eq (.container _), List.foldr_nil,
    SszType.wellFormed_iff (.progressiveContainer _ _),
    List.getLast?_nil, reduceCtorEq, List.length_nil, Nat.zero_le, List.filter_nil,
    List.length_cons, Nat.zero_add,
    Nat.zero_ne_one, or_false, forall_eq, SszType.wellFormed_iff .bool, and_false, and_self,
    SszType.fixedSize?_eq (.progressiveContainer _ _), List.foldr_cons,
    SszType.fixedSize?_eq .bool, Nat.add_zero]

private theorem client_c14 :
    (SszType.byteVector 0).WellFormed ∧ (SszType.byteVector 0).fixedSize? = some 0 ∧
    (SszType.container [.byteVector 0]).WellFormed ∧
    (SszType.container [.byteVector 0]).fixedSize? = some 0 ∧
    (SszType.list (.byteVector 0) 1).WellFormed ∧
    (SszType.list (.byteVector 0) 1).fixedSize? = none ∧
    ¬ (∀ (t : SszType) (n : Nat), t.WellFormed → t.fixedSize? = some n → 0 < n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [SszType.wellFormed_iff (.byteVector _)]
  · exact SszType.fixedSize?_eq _
  · simp only [SszType.wellFormed_iff (.container _), ne_eq, List.cons_ne_self,
      not_false_eq_true, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq, SszType.wellFormed_iff (.byteVector _), and_self]
  · simp only [SszType.fixedSize?_eq (.container _), List.foldr_cons,
      SszType.fixedSize?_eq (.byteVector _),
    List.foldr_nil, Nat.add_zero]
  · simp only [SszType.wellFormed_iff (.list _ _), SszType.wellFormed_iff (.byteVector _)]
  · exact SszType.fixedSize?_eq _
  · intro h
    have hw : (SszType.byteVector 0).WellFormed :=
      (SszType.wellFormed_iff _).mpr True.intro
    have hs : (SszType.byteVector 0).fixedSize? = some 0 := SszType.fixedSize?_eq _
    exact (Nat.lt_irrefl 0) (h (.byteVector 0) 0 hw hs)

private theorem client_c15 :
    (SszType.progressiveContainer [false, true] [.bool]).WellFormed ∧
    ¬ (SszType.progressiveContainer [true, false] [.bool]).WellFormed ∧
    (SszType.progressiveContainer [false, true] [.bool]).fixedSize? =
      (SszType.progressiveContainer [true, false] [.bool]).fixedSize? ∧
    SszValue.list [] ≠ SszValue.list [.bytes ByteArray.empty] ∧ (0 : Nat) * 0 = 1 * 0 := by
  simp only [SszType.wellFormed_iff (.progressiveContainer _ _), List.getLast?_cons_cons,
    List.getLast?_singleton, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
    Nat.reduceLeDiff, id_eq,
    Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg, List.filter_cons_of_pos,
    List.filter_nil,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq, SszType.wellFormed_iff .bool, and_self,
    Option.some.injEq,
    and_true, SszType.fixedSize?_eq (.progressiveContainer _ _), List.foldr_cons,
    SszType.fixedSize?_eq .bool,
    List.foldr_nil, Nat.add_zero, ne_eq, SszValue.list.injEq, List.ne_cons_self, Nat.mul_zero]

end STFSpec.Conformance.Codec
