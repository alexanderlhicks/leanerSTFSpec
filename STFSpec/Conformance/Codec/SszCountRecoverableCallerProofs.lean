/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.SszCountRecoverable

/-!
# SSZ count-recovery public-law clients

Library `EthConformance`. Private ordinary proofs use only the complete public
count-recovery equation and structural fixed-size equation. They give no decoder
implementation, source refinement or inverse theorem.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §4/§7.
-/

namespace STFSpec.Conformance.Codec
open STFSpec.Codec

private theorem leaves (width n size limit : Nat) (b : Bool) (bytes : ByteArray) :
    Ssz.CountRecoverable (.uint width) (.uint n) ∧
    Ssz.CountRecoverable .bool (.bool b) ∧
    Ssz.CountRecoverable (.byteVector size) (.bytes bytes) ∧
    Ssz.CountRecoverable (.byteList limit) (.bytes bytes) ∧
    Ssz.CountRecoverable .progressiveByteList (.bytes bytes) := by
  simp [Ssz.countRecoverable_iff (.uint _) (.uint _),
    Ssz.countRecoverable_iff .bool (.bool _),
    Ssz.countRecoverable_iff (.byteVector _) (.bytes _),
    Ssz.countRecoverable_iff (.byteList _) (.bytes _),
    Ssz.countRecoverable_iff .progressiveByteList (.bytes _)]

private theorem lists (e : SszType) (xs : List SszValue) (a b : Nat) :
    (Ssz.CountRecoverable (.list e a) (.list xs) ↔
      e.fixedSize? ≠ some 0 ∧ ∀ x ∈ xs, Ssz.CountRecoverable e x) ∧
    (Ssz.CountRecoverable (.progressiveList e) (.list xs) ↔
      Ssz.CountRecoverable (.list e b) (.list xs)) := by
  simp only [Ssz.countRecoverable_iff (.list _ _) (.list _),
    Ssz.countRecoverable_iff (.progressiveList _) (.list _), iff_self, and_self]

private theorem containers (fs : List SszType) (xs : List SszValue) (mask : List Bool) :
    (Ssz.CountRecoverable (.container fs) (.container xs) ↔
      fs.length = xs.length ∧ ∀ p ∈ fs.zip xs, Ssz.CountRecoverable p.1 p.2) ∧
    (Ssz.CountRecoverable (.progressiveContainer mask fs) (.container xs) ↔
      Ssz.CountRecoverable (.container fs) (.container xs)) := by
  simp only [Ssz.countRecoverable_iff (.container _) (.container _),
    Ssz.countRecoverable_iff (.progressiveContainer _ _) (.container _), iff_self, and_self]

private theorem empty_list (e : SszType) (limit : Nat) :
    Ssz.CountRecoverable (.list e limit) (.list []) ↔ e.fixedSize? ≠ some 0 := by
  simp [Ssz.countRecoverable_iff (.list _ _) (.list [])]

private theorem zero_list (e : SszType) (xs : List SszValue) (limit : Nat)
    (hz : e.fixedSize? = some 0) :
    ¬ Ssz.CountRecoverable (.list e limit) (.list xs) ∧
      ¬ Ssz.CountRecoverable (.progressiveList e) (.list xs) := by
  simp [Ssz.countRecoverable_iff (.list _ _) (.list _),
    Ssz.countRecoverable_iff (.progressiveList _) (.list _), hz]

private theorem unused_nested_schema (e : SszType) (a b : Nat) :
    Ssz.CountRecoverable (.list (.list e a) b) (.list []) ∧
    Ssz.CountRecoverable (.progressiveList (.list e a)) (.list []) := by
  simp [Ssz.countRecoverable_iff (.list _ _) (.list []),
    Ssz.countRecoverable_iff (.progressiveList _) (.list []),
    SszType.fixedSize?_eq (.list _ _)]

private theorem member_obligations (e : SszType) (xs : List SszValue) (limit : Nat)
    (h : Ssz.CountRecoverable (.list e limit) (.list xs)) :
    e.fixedSize? ≠ some 0 ∧ ∀ x ∈ xs, Ssz.CountRecoverable e x :=
  (Ssz.countRecoverable_iff _ _).mp h

private theorem paired_obligations (fs : List SszType) (xs : List SszValue)
    (mask : List Bool)
    (h : Ssz.CountRecoverable (.progressiveContainer mask fs) (.container xs)) :
    fs.length = xs.length ∧ ∀ p ∈ fs.zip xs, Ssz.CountRecoverable p.1 p.2 :=
  (Ssz.countRecoverable_iff _ _).mp h

private theorem assemble (e : SszType) (xs : List SszValue) (v : SszValue)
    (limit : Nat) (mask : List Bool) (hw : e.fixedSize? ≠ some 0)
    (hx : ∀ x ∈ xs, Ssz.CountRecoverable e x) (hv : Ssz.CountRecoverable e v) :
    Ssz.CountRecoverable (.container [.list e limit, .progressiveContainer mask [e]])
      (.container [.list xs, .container [v]]) := by
  simp [Ssz.countRecoverable_iff (.container _) (.container _),
    Ssz.countRecoverable_iff (.list _ _) (.list _),
    Ssz.countRecoverable_iff (.progressiveContainer _ _) (.container _),
    hw, hv]
  exact hx

private theorem all_fields (e : SszType) (xs : List SszValue) (v : SszValue)
    (limit : Nat) (mask : List Bool)
    (h : Ssz.CountRecoverable
      (.container [.list e limit, .progressiveContainer mask [e]])
      (.container [.list xs, .container [v]])) :
    (∀ x ∈ xs, Ssz.CountRecoverable e x) ∧ Ssz.CountRecoverable e v := by
  have hp := ((Ssz.countRecoverable_iff _ _).mp h).2
  have hx : Ssz.CountRecoverable (.list e limit) (.list xs) :=
    hp (.list e limit, .list xs) (by simp)
  have hv : Ssz.CountRecoverable (.progressiveContainer mask [e]) (.container [v]) :=
    hp (.progressiveContainer mask [e], .container [v]) (by simp)
  exact ⟨((Ssz.countRecoverable_iff _ _).mp hx).2,
    ((Ssz.countRecoverable_iff _ _).mp hv).2 (e, v) (by simp)⟩

end STFSpec.Conformance.Codec
