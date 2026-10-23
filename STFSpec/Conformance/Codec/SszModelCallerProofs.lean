/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Raw SSZ model consumers

Library `EthConformance`. Private consumers recover arbitrary complete payloads
from nested envelopes and distinguish ordered shapes and nominal diagnostic tags.
They use only the public raw constructors and ordinary inductive elimination.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §4/§7.
-/

namespace STFSpec.Conformance.Codec.SszModelCallerProofs

open STFSpec.Codec

private theorem nested_type_payloads
    (maskA maskB : List Bool) (fieldsA fieldsB : List SszType) (limitA limitB : Nat)
    (h : SszType.list (.progressiveContainer maskA fieldsA) limitA =
      SszType.list (.progressiveContainer maskB fieldsB) limitB) :
    maskA = maskB ∧ fieldsA = fieldsB ∧ limitA = limitB := by
  injection h with hElem hLimit
  injection hElem with hMask hFields
  exact ⟨hMask, hFields, hLimit⟩

private theorem ordinary_ne_progressive (fields : List SszType) (mask : List Bool) :
    SszType.container fields ≠ SszType.progressiveContainer mask fields := by
  intro h
  cases h

private theorem nested_value_payloads
    (n m : Nat) (p q : Bool) (b c : ByteArray) (xs ys : List SszValue)
    (h : SszValue.container [.uint n, .bool p, .bytes b, .list xs] =
      SszValue.container [.uint m, .bool q, .bytes c, .list ys]) :
    n = m ∧ p = q ∧ b = c ∧ xs = ys := by
  simpa only [SszValue.container.injEq, List.cons.injEq, SszValue.uint.injEq,
    SszValue.bool.injEq, SszValue.bytes.injEq, SszValue.list.injEq, and_true] using h

private theorem nested_shapes_distinct (xs ys : List SszValue) :
    SszValue.list [.container xs] ≠ SszValue.container [.list ys] := by
  intro h
  cases h

private theorem error_tags_distinct :
    List.Pairwise (· ≠ ·)
      [SszError.length, .offset, .limit, .boolByte, .trailing, .shape] := by
  simp [List.pairwise_cons]

end STFSpec.Conformance.Codec.SszModelCallerProofs
