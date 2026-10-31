/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Field

/-!
# Natural residue arithmetic controls

Library `EthConformance`. Complete small canonical pairs, signed integer models,
notation delegation, zero divisors and independent distinguishing literals.
Spec guidance: `STFSpec/informal/modules/EthField.md` §§3–4.
-/

namespace STFSpec.Conformance.Field
open STFSpec.Field
open PrimeFieldRef

private def huge : Nat := 2 ^ 4096 + 17

private def completePair (p : Nat) (hp : 1 < p) (metadata : Option Nat)
    (n m : Nat) : Bool :=
  letI : FieldModulus p := ⟨hp, metadata⟩
  let a := ofNat (p := p) n
  let b := ofNat (p := p) m
  let ra := a.toNat
  let rb := b.toNat
  decide ((add a b).toNat = (ra + rb) % p) &&
    decide (((sub a b).toNat : Int) = ((ra : Int) - (rb : Int)) % (p : Int)) &&
    decide (((neg a).toNat : Int) = -(ra : Int) % (p : Int)) &&
    decide ((mul a b).toNat = (ra * rb) % p) &&
    decide (isZero a = decide (ra = 0)) &&
    decide (a + b = add a b) && decide (a - b = sub a b) &&
    decide (-a = neg a) && decide (a * b = mul a b) &&
    decide ((a + b).toNat < p) && decide ((a - b).toNat < p) &&
    decide ((-a).toNat < p) && decide ((a * b).toNat < p) &&
    decide ((a - b) + b = a) && decide ((-a) + a = zero)

private def completeModulus (p : Nat) (hp : 1 < p) (metadata : Option Nat) : Bool :=
  (List.range p).all fun a ↦ (List.range p).all fun b ↦ completePair p hp metadata a b

private def reducingPairs (p : Nat) (hp : 1 < p) (metadata : Option Nat) : Bool :=
  let inputs := [0, 1, p - 1, p, p + 1, 2 * p + 3, huge]
  inputs.all fun a ↦ inputs.all fun b ↦ completePair p hp metadata a b

#guard completeModulus 2 (by decide) none
#guard reducingPairs 2 (by decide) none
#guard completeModulus 2 (by decide) (some 0)
#guard reducingPairs 2 (by decide) (some 0)
#guard completeModulus 2 (by decide) (some huge)
#guard reducingPairs 2 (by decide) (some huge)
#guard completeModulus 3 (by decide) none
#guard reducingPairs 3 (by decide) none
#guard completeModulus 3 (by decide) (some 0)
#guard reducingPairs 3 (by decide) (some 0)
#guard completeModulus 3 (by decide) (some huge)
#guard reducingPairs 3 (by decide) (some huge)
#guard completeModulus 4 (by decide) none
#guard reducingPairs 4 (by decide) none
#guard completeModulus 4 (by decide) (some 0)
#guard reducingPairs 4 (by decide) (some 0)
#guard completeModulus 4 (by decide) (some huge)
#guard reducingPairs 4 (by decide) (some huge)
#guard completeModulus 5 (by decide) none
#guard reducingPairs 5 (by decide) none
#guard completeModulus 5 (by decide) (some 0)
#guard reducingPairs 5 (by decide) (some 0)
#guard completeModulus 5 (by decide) (some huge)
#guard reducingPairs 5 (by decide) (some huge)
#guard completeModulus 9 (by decide) none
#guard reducingPairs 9 (by decide) none
#guard completeModulus 9 (by decide) (some 0)
#guard reducingPairs 9 (by decide) (some 0)
#guard completeModulus 9 (by decide) (some huge)
#guard reducingPairs 9 (by decide) (some huge)
#guard completeModulus 15 (by decide) none
#guard reducingPairs 15 (by decide) none
#guard completeModulus 15 (by decide) (some 0)
#guard reducingPairs 15 (by decide) (some 0)
#guard completeModulus 15 (by decide) (some huge)
#guard reducingPairs 15 (by decide) (some huge)
#guard completeModulus 17 (by decide) none
#guard reducingPairs 17 (by decide) none
#guard completeModulus 17 (by decide) (some 0)
#guard reducingPairs 17 (by decide) (some 0)
#guard completeModulus 17 (by decide) (some huge)
#guard reducingPairs 17 (by decide) (some huge)

private def literals (metadata : Option Nat) : Bool :=
  letI : FieldModulus 4 := ⟨by decide, metadata⟩
  letI : FieldModulus 5 := ⟨by decide, metadata⟩
  letI : FieldModulus 9 := ⟨by decide, metadata⟩
  let two4 := ofNat (p := 4) 2
  let a5 := ofNat (p := 5) 1
  let b5 := ofNat (p := 5) 3
  let a9 := ofNat (p := 9) 2
  let b9 := ofNat (p := 9) 4
  decide ((two4 * two4).toNat = 0) && isZero (two4 * two4) &&
    decide ((a5 - b5).toNat = 3) && decide ((1 - 3 : Nat) % 5 = 0) &&
    decide ((a9 + b9).toNat = 6) && decide ((a9 - b9).toNat = 7) &&
    decide ((-a9).toNat = 7) && decide ((a9 * b9).toNat = 8) &&
    !isZero a9 && isZero (zero : PrimeFieldRef 9)

#guard literals none
#guard literals (some 0)
#guard literals (some huge)

end STFSpec.Conformance.Field
