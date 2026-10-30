/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Field.ReferenceInverse

/-!
# Natural-reference residue division

Library `EthField`. Division composes canonical multiplication with the complete
reference inverse, including zero and composite nonunits, for every admitted modulus.
Spec guidance: `STFSpec/informal/modules/EthField.md` §§3–7.
-/

namespace STFSpec.Field.PrimeFieldRef

variable {p : Nat} [FieldModulus p]

/-- Residue division, as `FQ.__truediv__` delegating to `FQ.__div__` in pinned
py-ecc 8.0.0 `py_ecc/fields/optimized_field_elements.py:127–142`, using
`py_ecc/utils.py:21–39`. Metadata is unread; zero and nonunits retain `inv0` behavior. -/
def div (a b : PrimeFieldRef p) : PrimeFieldRef p := mul a (inv0 b)

/-- Division observes the complete inverse result multiplied by the numerator and reduced. -/
theorem toNat_div (a b : PrimeFieldRef p) :
    (div a b).toNat = (a.toNat * (inv0 b).toNat) % p := by
  exact toNat_mul a (inv0 b)

/-- Division notation delegates directly to the named reference operation. -/
instance : Div (PrimeFieldRef p) where
  div := div

end STFSpec.Field.PrimeFieldRef
