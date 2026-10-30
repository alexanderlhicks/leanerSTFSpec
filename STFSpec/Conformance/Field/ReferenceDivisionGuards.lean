/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Field

/-!
# Natural-reference division finite literal controls

Library `EthConformance`. Asymmetric, zero, wrap, nonunit, signed-coefficient and
composite Fermat traps run under three unread metadata choices.
Spec guidance: `STFSpec/informal/modules/EthField.md` §§3–7.
-/

namespace STFSpec.Conformance.Field
open STFSpec.Field

private def checkDivision (p : Nat) (hp : 1 < p) (rawA rawB a b inverse result : Nat) : Bool :=
  [none, some 0, some (2 ^ 4096 + 17)].all fun metadata ↦
    letI : FieldModulus p := ⟨hp, metadata⟩
    let x : PrimeFieldRef p := PrimeFieldRef.ofNat rawA
    let y : PrimeFieldRef p := PrimeFieldRef.ofNat rawB
    x.toNat == a && y.toNat == b && (PrimeFieldRef.inv0 y).toNat == inverse &&
      (PrimeFieldRef.div x y).toNat == result && (x / y).toNat == result &&
      decide ((x / y).toNat < p)

#guard checkDivision 2 (by decide) 1 0 1 0 0 0
#guard checkDivision 2 (by decide) 1 1 1 1 1 1
#guard checkDivision 4 (by decide) 1 2 1 2 2 2
#guard checkDivision 4 (by decide) 2 2 2 2 2 0
#guard checkDivision 4 (by decide) 3 2 3 2 2 2
#guard checkDivision 9 (by decide) 1 3 1 3 6 6
#guard checkDivision 9 (by decide) 2 3 2 3 6 3
#guard checkDivision 9 (by decide) 3 2 3 2 5 6
#guard checkDivision 9 (by decide) 1 2 1 2 5 5
#guard checkDivision 5 (by decide) 1 2 1 2 3 3
#guard checkDivision 5 (by decide) 2 3 2 3 2 4
#guard checkDivision 5 (by decide) 3 2 3 2 3 4
#guard checkDivision 5 (by decide) 8 12 3 2 3 4
#guard checkDivision 17 (by decide) 4 3 4 3 6 7
#guard checkDivision 17 (by decide) 3 4 3 4 13 5
#guard checkDivision 17 (by decide) 34 19 0 2 9 0
#guard checkDivision 17 (by decide) 16 0 16 0 0 0
#guard checkDivision 17 (by decide) 16 16 16 16 16 1

end STFSpec.Conformance.Field
