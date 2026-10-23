/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.SszModel

/-!
# Structural SSZ fixed-class widths

Library `EthCodec`. Raw structural classification with the Q67 total completion.
Source interpretation is conditional on actual mapped classes and ordered fields:
`src/ethereum/utils/ssz.py:179–225,231–258` and eth-remerkleable 0.1.31 sizing methods.
This classifier supplies no schema admission, codec, root or positive-width premise.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Codec

mutual
  /-- Raw structural fixed-class byte width, including zero (Q67).
  Conditional source sizing: `src/ethereum/utils/ssz.py:179–225,231–258` through
  eth-remerkleable 0.1.31. Lists are variable without inspecting their children;
  progressive masks do not select fields. No source-class admission is asserted. -/
  def SszType.fixedSize? : SszType → Option Nat
    | .uint w => some w
    | .bool => some 1
    | .byteVector n => some n
    | .byteList _ => none
    | .list _ _ => none
    | .progressiveList _ => none
    | .progressiveByteList => none
    | .container fields | .progressiveContainer _ fields => fixedFields fields
  private def fixedFields : List SszType → Option Nat
    | [] => some 0
    | field :: fields =>
        match field.fixedSize? with
        | none => none
        | some n =>
            match fixedFields fields with
            | none => none
            | some m => some (n + m)
end

private theorem fixedFields_eq (fields : List SszType) :
    fixedFields fields = fields.foldr
      (fun field acc =>
        match field.fixedSize?, acc with
        | some n, some m => some (n + m)
        | _, _ => none)
      (some 0) := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
    simp only [fixedFields, List.foldr_cons, ← ih]
    cases field.fixedSize? <;> cases fixedFields fields <;> rfl

/-- Complete structural sizing equation on every raw descriptor (Q67).
The ordered fold retains every field occurrence and ignores progressive masks. -/
theorem SszType.fixedSize?_eq (t : SszType) :
  t.fixedSize? =
    match t with
    | .uint w => some w
    | .bool => some 1
    | .byteVector n => some n
    | .byteList _ => none
    | .list _ _ => none
    | .progressiveList _ => none
    | .progressiveByteList => none
    | .container fields | .progressiveContainer _ fields =>
        fields.foldr
          (fun field acc =>
            match field.fixedSize?, acc with
            | some n, some m => some (n + m)
            | _, _ => none)
          (some 0) := by
  cases t <;> first | exact fixedFields_eq _ | rfl

end STFSpec.Codec
