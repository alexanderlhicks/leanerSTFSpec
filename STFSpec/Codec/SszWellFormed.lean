/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.SszModel

/-!
# Structural SSZ schema well-formedness

Library `EthCodec`. Nameless structural schema validity (Q70), separate from value typing,
source class/name admission, sizing and operation domains. Source interpretation uses
`src/ethereum/utils/ssz.py:91–120,179–225,231–260` and eth-remerkleable 0.1.31.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Codec

mutual
  private def wellFormed : SszType → Prop
    | .uint w => w ∈ [1, 2, 4, 8, 16, 32]
    | .bool | .byteVector _ | .byteList _ | .progressiveByteList => True
    | .list elem _ | .progressiveList elem => wellFormed elem
    | .container fields => fields ≠ [] ∧ wellFormedFields fields
    | .progressiveContainer mask fields =>
        mask.getLast? = some true ∧ mask.length ≤ 256 ∧
        (mask.filter id).length = fields.length ∧ wellFormedFields fields
  private def wellFormedFields : List SszType → Prop
    | [] => True
    | field :: fields => wellFormed field ∧ wellFormedFields fields
end

/-- Nameless structural schema validity (Q70).
Corresponds structurally to `src/ethereum/utils/ssz.py:91–120,179–225,231–260` under
actual mapped classes/fields. No Python class, value, codec or root admission is asserted. -/
def SszType.WellFormed : SszType → Prop := wellFormed

private theorem wellFormedFields_iff (fields : List SszType) :
    wellFormedFields fields ↔ ∀ field ∈ fields, field.WellFormed := by
  induction fields with
  | nil => simp only [wellFormedFields, List.not_mem_nil, false_implies, implies_true]
  | cons field fields ih =>
    simp only [wellFormedFields, ih, List.mem_cons, forall_eq_or_imp, SszType.WellFormed]

private theorem wellFormed_iff_impl (t : SszType) :
    t.WellFormed ↔
      match t with
      | .uint w => w ∈ [1, 2, 4, 8, 16, 32]
      | .bool => True
      | .byteVector _ => True
      | .byteList _ => True
      | .list elem _ => elem.WellFormed
      | .progressiveList elem => elem.WellFormed
      | .progressiveByteList => True
      | .container fields =>
          fields ≠ [] ∧ ∀ field ∈ fields, field.WellFormed
      | .progressiveContainer mask fields =>
          mask.getLast? = some true ∧
          mask.length ≤ 256 ∧
          (mask.filter id).length = fields.length ∧
          ∀ field ∈ fields, field.WellFormed := by
  cases t <;> simp only [SszType.WellFormed, wellFormed, wellFormedFields_iff]

/-- Complete structural schema equation on all nine raw constructors (Q70).
Zero vectors/limits and sparse masks up to length 256 remain structurally admissible;
every actual child is checked, independently of value counts or operation domains. -/
theorem SszType.wellFormed_iff (t : SszType) :
    t.WellFormed ↔
      match t with
      | .uint w => w ∈ [1, 2, 4, 8, 16, 32]
      | .bool => True
      | .byteVector _ => True
      | .byteList _ => True
      | .list elem _ => elem.WellFormed
      | .progressiveList elem => elem.WellFormed
      | .progressiveByteList => True
      | .container fields =>
          fields ≠ [] ∧ ∀ field ∈ fields, field.WellFormed
      | .progressiveContainer mask fields =>
          mask.getLast? = some true ∧
          mask.length ≤ 256 ∧
          (mask.filter id).length = fields.length ∧
          ∀ field ∈ fields, field.WellFormed := wellFormed_iff_impl t

end STFSpec.Codec
