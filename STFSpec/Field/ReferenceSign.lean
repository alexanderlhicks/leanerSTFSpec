/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Field.Reference

/-!
# Canonical natural-reference sign

Library `EthField`. Sign observes the parity of the canonical natural residue,
for every admitted modulus and arbitrary unread square-root metadata.
Spec guidance: `STFSpec/informal/modules/EthField.md` §§3–7.
-/

namespace STFSpec.Field.PrimeFieldRef

variable {p : Nat} [FieldModulus p]

/-- Canonical residue parity, as `FQ.sgn0` in pinned py-ecc 8.0.0
`py_ecc/fields/optimized_field_elements.py:204–215`.
The source's integer zero/one is represented by Boolean false/true. -/
def sgn0 (a : PrimeFieldRef p) : Bool := decide (a.toNat % 2 = 1)

/-- Sign decides exactly oddness of the canonical natural observation. -/
theorem sgn0_eq (a : PrimeFieldRef p) : sgn0 a = decide (a.toNat % 2 = 1) := rfl

end STFSpec.Field.PrimeFieldRef
