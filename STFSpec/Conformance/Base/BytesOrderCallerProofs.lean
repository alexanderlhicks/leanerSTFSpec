/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.BytesOrder
import Std.Data.TreeMap.Lemmas

/-!
# Byte-content ordering public-law clients

Library `EthConformance`. Symbolic clients use public observations and model laws;
map clients instantiate the supplied lawful order on the existing equality.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §3/§7.
-/

namespace STFSpec.Conformance.Base.BytesOrderCallerProofs

open STFSpec.Base

/-- The executable comparator has its public all-input reference equation. -/
theorem reference (a b : Bytes) : Bytes.compare a b = Bytes.compareReference a b :=
  Bytes.compare_eq_reference a b

/-- The instance comparison commutes with the public list observer. -/
theorem list_model (a b : Bytes) : Ord.compare a b = Ord.compare a.toList b.toList :=
  Bytes.compare_toList a b

/-- Comparison equality is actual existing equality. -/
theorem actual_equality (a b : Bytes) : Ord.compare a b = .eq ↔ a = b :=
  Bytes.compare_eq_eq_iff a b

/-- The public packed export uses precisely core ByteArray's list observation. -/
theorem packed_model (a : Bytes) : a.toByteArray.toList = a.toList :=
  Bytes.toByteArray_toList a

/-- No representation premise is needed for reflexivity. -/
theorem reflexive (a : Bytes) : Ord.compare a a = .eq := Std.ReflCmp.compare_self

/-- Reversing arguments swaps the comparison. -/
theorem oriented (a b : Bytes) : (Ord.compare a b).swap = Ord.compare b a :=
  Std.OrientedCmp.eq_swap.symm

/-- Transitivity is supplied at the symbolic Bytes type. -/
theorem transitive {a b c : Bytes}
    (hab : (Ord.compare a b).isLE) (hbc : (Ord.compare b c).isLE) :
    (Ord.compare a c).isLE := Std.TransCmp.isLE_trans hab hbc

/-- Equal public byte models compare equally, independent of construction. -/
theorem equal_models {a b : Bytes} (h : a.toList = b.toList) : Ord.compare a b = .eq :=
  (Bytes.compare_eq_eq_iff a b).mpr (Bytes.ext h)

/-- Public reconstruction supplies a comparison-equal key. -/
theorem reconstructed (a : Bytes) : Ord.compare (Bytes.ofList a.toList) a = .eq :=
  (Bytes.compare_eq_eq_iff _ _).mpr (Bytes.ofList_toList a)

/-- Public Std insertion uses the existing equality rather than a separate key relation. -/
theorem lookup_insert {β : Type} (m : Std.TreeMap Bytes β) (key query : Bytes) (v : β) :
    (m.insert key v)[query]? = if key = query then some v else m[query]? := by
  rw [Std.TreeMap.getElem?_insert]
  simp only [Bytes.compare_eq_eq_iff]

/-- Repeated insertion of the same byte-content key retains the latest value. -/
theorem overwrite {β : Type} (m : Std.TreeMap Bytes β) (key : Bytes) (v latest : β) :
    ((m.insert key v).insert key latest)[key]? = some latest :=
  Std.TreeMap.getElem?_insert_self

/-- Insertion of a different key preserves lookup. -/
theorem different_key {β : Type} (m : Std.TreeMap Bytes β) (key query : Bytes) (v : β)
    (h : key ≠ query) : (m.insert key v)[query]? = m[query]? := by
  rw [lookup_insert, ite_eq_right h]

/-- Independently reconstructed equal-content keys retrieve the inserted value. -/
theorem reconstructed_lookup {β : Type} (m : Std.TreeMap Bytes β) (key : Bytes) (v : β) :
    (m.insert key v)[Bytes.ofList key.toList]? = some v := by
  rw [Bytes.ofList_toList]
  exact Std.TreeMap.getElem?_insert_self

end STFSpec.Conformance.Base.BytesOrderCallerProofs
