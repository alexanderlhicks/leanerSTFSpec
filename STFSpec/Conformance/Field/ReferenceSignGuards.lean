/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Field

/-!
# Canonical sign complete finite controls

Library `EthConformance`. Full canonical residues and independent literal parity
results cover small moduli, reduction traps, wraps, adjacent large bit boundaries and
large canonical residues in the BN254 and BLS12-381 base fields.
Spec guidance: `STFSpec/informal/modules/EthField.md` §§3–7.
-/

namespace STFSpec.Conformance.Field
open STFSpec.Field

private def checkSign (p : Nat) (hp : 1 < p) (raw canonical : Nat)
    (expected : Bool) : Bool :=
  [none, some 0, some (2 ^ 4096 + 17)].all fun metadata ↦
    letI : FieldModulus p := ⟨hp, metadata⟩
    let a : PrimeFieldRef p := PrimeFieldRef.ofNat raw
    a.toNat == canonical && PrimeFieldRef.sgn0 a == expected && decide (a.toNat < p)

#guard checkSign 2 (by decide) 0 0 false
#guard checkSign 2 (by decide) 1 1 true
#guard checkSign 2 (by decide) 2 0 false
#guard checkSign 2 (by decide) 3 1 true
#guard checkSign 2 (by decide) 4 0 false
#guard checkSign 2 (by decide) 5 1 true
#guard checkSign 2 (by decide) 10 0 false
#guard checkSign 2 (by decide) (2 ^ 8 - 1) 1 true
#guard checkSign 2 (by decide) (2 ^ 8) 0 false
#guard checkSign 2 (by decide) (2 ^ 8 + 1) 1 true
#guard checkSign 2 (by decide) (2 ^ 32 - 1) 1 true
#guard checkSign 2 (by decide) (2 ^ 32) 0 false
#guard checkSign 2 (by decide) (2 ^ 32 + 1) 1 true
#guard checkSign 2 (by decide) (2 ^ 64 - 1) 1 true
#guard checkSign 2 (by decide) (2 ^ 64) 0 false
#guard checkSign 2 (by decide) (2 ^ 64 + 1) 1 true
#guard checkSign 2 (by decide) (2 ^ 255 - 1) 1 true
#guard checkSign 2 (by decide) (2 ^ 255) 0 false
#guard checkSign 2 (by decide) (2 ^ 255 + 1) 1 true
#guard checkSign 2 (by decide) (2 ^ 256 - 1) 1 true
#guard checkSign 2 (by decide) (2 ^ 256) 0 false
#guard checkSign 2 (by decide) (2 ^ 256 + 1) 1 true
#guard checkSign 2 (by decide) (2 ^ 381 - 1) 1 true
#guard checkSign 2 (by decide) (2 ^ 381) 0 false
#guard checkSign 2 (by decide) (2 ^ 381 + 1) 1 true
#guard checkSign 2 (by decide) (2 ^ 2048 - 1) 1 true
#guard checkSign 2 (by decide) (2 ^ 2048) 0 false
#guard checkSign 2 (by decide) (2 ^ 2048 + 1) 1 true
#guard checkSign 3 (by decide) 0 0 false
#guard checkSign 3 (by decide) 1 1 true
#guard checkSign 3 (by decide) 2 2 false
#guard checkSign 3 (by decide) 3 0 false
#guard checkSign 3 (by decide) 4 1 true
#guard checkSign 3 (by decide) 5 2 false
#guard checkSign 3 (by decide) 6 0 false
#guard checkSign 3 (by decide) 7 1 true
#guard checkSign 3 (by decide) 13 1 true
#guard checkSign 3 (by decide) (2 ^ 8 - 1) 0 false
#guard checkSign 3 (by decide) (2 ^ 8) 1 true
#guard checkSign 3 (by decide) (2 ^ 8 + 1) 2 false
#guard checkSign 3 (by decide) (2 ^ 32 - 1) 0 false
#guard checkSign 3 (by decide) (2 ^ 32) 1 true
#guard checkSign 3 (by decide) (2 ^ 32 + 1) 2 false
#guard checkSign 3 (by decide) (2 ^ 64 - 1) 0 false
#guard checkSign 3 (by decide) (2 ^ 64) 1 true
#guard checkSign 3 (by decide) (2 ^ 64 + 1) 2 false
#guard checkSign 3 (by decide) (2 ^ 255 - 1) 1 true
#guard checkSign 3 (by decide) (2 ^ 255) 2 false
#guard checkSign 3 (by decide) (2 ^ 255 + 1) 0 false
#guard checkSign 3 (by decide) (2 ^ 256 - 1) 0 false
#guard checkSign 3 (by decide) (2 ^ 256) 1 true
#guard checkSign 3 (by decide) (2 ^ 256 + 1) 2 false
#guard checkSign 3 (by decide) (2 ^ 381 - 1) 1 true
#guard checkSign 3 (by decide) (2 ^ 381) 2 false
#guard checkSign 3 (by decide) (2 ^ 381 + 1) 0 false
#guard checkSign 3 (by decide) (2 ^ 2048 - 1) 0 false
#guard checkSign 3 (by decide) (2 ^ 2048) 1 true
#guard checkSign 3 (by decide) (2 ^ 2048 + 1) 2 false
#guard checkSign 4 (by decide) 0 0 false
#guard checkSign 4 (by decide) 1 1 true
#guard checkSign 4 (by decide) 2 2 false
#guard checkSign 4 (by decide) 3 3 true
#guard checkSign 4 (by decide) 4 0 false
#guard checkSign 4 (by decide) 5 1 true
#guard checkSign 4 (by decide) 7 3 true
#guard checkSign 4 (by decide) 8 0 false
#guard checkSign 4 (by decide) 9 1 true
#guard checkSign 4 (by decide) 16 0 false
#guard checkSign 4 (by decide) (2 ^ 8 - 1) 3 true
#guard checkSign 4 (by decide) (2 ^ 8) 0 false
#guard checkSign 4 (by decide) (2 ^ 8 + 1) 1 true
#guard checkSign 4 (by decide) (2 ^ 32 - 1) 3 true
#guard checkSign 4 (by decide) (2 ^ 32) 0 false
#guard checkSign 4 (by decide) (2 ^ 32 + 1) 1 true
#guard checkSign 4 (by decide) (2 ^ 64 - 1) 3 true
#guard checkSign 4 (by decide) (2 ^ 64) 0 false
#guard checkSign 4 (by decide) (2 ^ 64 + 1) 1 true
#guard checkSign 4 (by decide) (2 ^ 255 - 1) 3 true
#guard checkSign 4 (by decide) (2 ^ 255) 0 false
#guard checkSign 4 (by decide) (2 ^ 255 + 1) 1 true
#guard checkSign 4 (by decide) (2 ^ 256 - 1) 3 true
#guard checkSign 4 (by decide) (2 ^ 256) 0 false
#guard checkSign 4 (by decide) (2 ^ 256 + 1) 1 true
#guard checkSign 4 (by decide) (2 ^ 381 - 1) 3 true
#guard checkSign 4 (by decide) (2 ^ 381) 0 false
#guard checkSign 4 (by decide) (2 ^ 381 + 1) 1 true
#guard checkSign 4 (by decide) (2 ^ 2048 - 1) 3 true
#guard checkSign 4 (by decide) (2 ^ 2048) 0 false
#guard checkSign 4 (by decide) (2 ^ 2048 + 1) 1 true
#guard checkSign 5 (by decide) 0 0 false
#guard checkSign 5 (by decide) 1 1 true
#guard checkSign 5 (by decide) 2 2 false
#guard checkSign 5 (by decide) 3 3 true
#guard checkSign 5 (by decide) 4 4 false
#guard checkSign 5 (by decide) 5 0 false
#guard checkSign 5 (by decide) 6 1 true
#guard checkSign 5 (by decide) 9 4 false
#guard checkSign 5 (by decide) 10 0 false
#guard checkSign 5 (by decide) 11 1 true
#guard checkSign 5 (by decide) 19 4 false
#guard checkSign 5 (by decide) (2 ^ 8 - 1) 0 false
#guard checkSign 5 (by decide) (2 ^ 8) 1 true
#guard checkSign 5 (by decide) (2 ^ 8 + 1) 2 false
#guard checkSign 5 (by decide) (2 ^ 32 - 1) 0 false
#guard checkSign 5 (by decide) (2 ^ 32) 1 true
#guard checkSign 5 (by decide) (2 ^ 32 + 1) 2 false
#guard checkSign 5 (by decide) (2 ^ 64 - 1) 0 false
#guard checkSign 5 (by decide) (2 ^ 64) 1 true
#guard checkSign 5 (by decide) (2 ^ 64 + 1) 2 false
#guard checkSign 5 (by decide) (2 ^ 255 - 1) 2 false
#guard checkSign 5 (by decide) (2 ^ 255) 3 true
#guard checkSign 5 (by decide) (2 ^ 255 + 1) 4 false
#guard checkSign 5 (by decide) (2 ^ 256 - 1) 0 false
#guard checkSign 5 (by decide) (2 ^ 256) 1 true
#guard checkSign 5 (by decide) (2 ^ 256 + 1) 2 false
#guard checkSign 5 (by decide) (2 ^ 381 - 1) 1 true
#guard checkSign 5 (by decide) (2 ^ 381) 2 false
#guard checkSign 5 (by decide) (2 ^ 381 + 1) 3 true
#guard checkSign 5 (by decide) (2 ^ 2048 - 1) 0 false
#guard checkSign 5 (by decide) (2 ^ 2048) 1 true
#guard checkSign 5 (by decide) (2 ^ 2048 + 1) 2 false
#guard checkSign 6 (by decide) 0 0 false
#guard checkSign 6 (by decide) 1 1 true
#guard checkSign 6 (by decide) 2 2 false
#guard checkSign 6 (by decide) 3 3 true
#guard checkSign 6 (by decide) 4 4 false
#guard checkSign 6 (by decide) 5 5 true
#guard checkSign 6 (by decide) 6 0 false
#guard checkSign 6 (by decide) 7 1 true
#guard checkSign 6 (by decide) 11 5 true
#guard checkSign 6 (by decide) 12 0 false
#guard checkSign 6 (by decide) 13 1 true
#guard checkSign 6 (by decide) 22 4 false
#guard checkSign 6 (by decide) (2 ^ 8 - 1) 3 true
#guard checkSign 6 (by decide) (2 ^ 8) 4 false
#guard checkSign 6 (by decide) (2 ^ 8 + 1) 5 true
#guard checkSign 6 (by decide) (2 ^ 32 - 1) 3 true
#guard checkSign 6 (by decide) (2 ^ 32) 4 false
#guard checkSign 6 (by decide) (2 ^ 32 + 1) 5 true
#guard checkSign 6 (by decide) (2 ^ 64 - 1) 3 true
#guard checkSign 6 (by decide) (2 ^ 64) 4 false
#guard checkSign 6 (by decide) (2 ^ 64 + 1) 5 true
#guard checkSign 6 (by decide) (2 ^ 255 - 1) 1 true
#guard checkSign 6 (by decide) (2 ^ 255) 2 false
#guard checkSign 6 (by decide) (2 ^ 255 + 1) 3 true
#guard checkSign 6 (by decide) (2 ^ 256 - 1) 3 true
#guard checkSign 6 (by decide) (2 ^ 256) 4 false
#guard checkSign 6 (by decide) (2 ^ 256 + 1) 5 true
#guard checkSign 6 (by decide) (2 ^ 381 - 1) 1 true
#guard checkSign 6 (by decide) (2 ^ 381) 2 false
#guard checkSign 6 (by decide) (2 ^ 381 + 1) 3 true
#guard checkSign 6 (by decide) (2 ^ 2048 - 1) 3 true
#guard checkSign 6 (by decide) (2 ^ 2048) 4 false
#guard checkSign 6 (by decide) (2 ^ 2048 + 1) 5 true
#guard checkSign 8 (by decide) 0 0 false
#guard checkSign 8 (by decide) 1 1 true
#guard checkSign 8 (by decide) 2 2 false
#guard checkSign 8 (by decide) 3 3 true
#guard checkSign 8 (by decide) 4 4 false
#guard checkSign 8 (by decide) 5 5 true
#guard checkSign 8 (by decide) 6 6 false
#guard checkSign 8 (by decide) 7 7 true
#guard checkSign 8 (by decide) 8 0 false
#guard checkSign 8 (by decide) 9 1 true
#guard checkSign 8 (by decide) 15 7 true
#guard checkSign 8 (by decide) 16 0 false
#guard checkSign 8 (by decide) 17 1 true
#guard checkSign 8 (by decide) 28 4 false
#guard checkSign 8 (by decide) (2 ^ 8 - 1) 7 true
#guard checkSign 8 (by decide) (2 ^ 8) 0 false
#guard checkSign 8 (by decide) (2 ^ 8 + 1) 1 true
#guard checkSign 8 (by decide) (2 ^ 32 - 1) 7 true
#guard checkSign 8 (by decide) (2 ^ 32) 0 false
#guard checkSign 8 (by decide) (2 ^ 32 + 1) 1 true
#guard checkSign 8 (by decide) (2 ^ 64 - 1) 7 true
#guard checkSign 8 (by decide) (2 ^ 64) 0 false
#guard checkSign 8 (by decide) (2 ^ 64 + 1) 1 true
#guard checkSign 8 (by decide) (2 ^ 255 - 1) 7 true
#guard checkSign 8 (by decide) (2 ^ 255) 0 false
#guard checkSign 8 (by decide) (2 ^ 255 + 1) 1 true
#guard checkSign 8 (by decide) (2 ^ 256 - 1) 7 true
#guard checkSign 8 (by decide) (2 ^ 256) 0 false
#guard checkSign 8 (by decide) (2 ^ 256 + 1) 1 true
#guard checkSign 8 (by decide) (2 ^ 381 - 1) 7 true
#guard checkSign 8 (by decide) (2 ^ 381) 0 false
#guard checkSign 8 (by decide) (2 ^ 381 + 1) 1 true
#guard checkSign 8 (by decide) (2 ^ 2048 - 1) 7 true
#guard checkSign 8 (by decide) (2 ^ 2048) 0 false
#guard checkSign 8 (by decide) (2 ^ 2048 + 1) 1 true
#guard checkSign 9 (by decide) 0 0 false
#guard checkSign 9 (by decide) 1 1 true
#guard checkSign 9 (by decide) 2 2 false
#guard checkSign 9 (by decide) 3 3 true
#guard checkSign 9 (by decide) 4 4 false
#guard checkSign 9 (by decide) 5 5 true
#guard checkSign 9 (by decide) 6 6 false
#guard checkSign 9 (by decide) 7 7 true
#guard checkSign 9 (by decide) 8 8 false
#guard checkSign 9 (by decide) 9 0 false
#guard checkSign 9 (by decide) 10 1 true
#guard checkSign 9 (by decide) 17 8 false
#guard checkSign 9 (by decide) 18 0 false
#guard checkSign 9 (by decide) 19 1 true
#guard checkSign 9 (by decide) 31 4 false
#guard checkSign 9 (by decide) (2 ^ 8 - 1) 3 true
#guard checkSign 9 (by decide) (2 ^ 8) 4 false
#guard checkSign 9 (by decide) (2 ^ 8 + 1) 5 true
#guard checkSign 9 (by decide) (2 ^ 32 - 1) 3 true
#guard checkSign 9 (by decide) (2 ^ 32) 4 false
#guard checkSign 9 (by decide) (2 ^ 32 + 1) 5 true
#guard checkSign 9 (by decide) (2 ^ 64 - 1) 6 false
#guard checkSign 9 (by decide) (2 ^ 64) 7 true
#guard checkSign 9 (by decide) (2 ^ 64 + 1) 8 false
#guard checkSign 9 (by decide) (2 ^ 255 - 1) 7 true
#guard checkSign 9 (by decide) (2 ^ 255) 8 false
#guard checkSign 9 (by decide) (2 ^ 255 + 1) 0 false
#guard checkSign 9 (by decide) (2 ^ 256 - 1) 6 false
#guard checkSign 9 (by decide) (2 ^ 256) 7 true
#guard checkSign 9 (by decide) (2 ^ 256 + 1) 8 false
#guard checkSign 9 (by decide) (2 ^ 381 - 1) 7 true
#guard checkSign 9 (by decide) (2 ^ 381) 8 false
#guard checkSign 9 (by decide) (2 ^ 381 + 1) 0 false
#guard checkSign 9 (by decide) (2 ^ 2048 - 1) 3 true
#guard checkSign 9 (by decide) (2 ^ 2048) 4 false
#guard checkSign 9 (by decide) (2 ^ 2048 + 1) 5 true
#guard checkSign 15 (by decide) 0 0 false
#guard checkSign 15 (by decide) 1 1 true
#guard checkSign 15 (by decide) 2 2 false
#guard checkSign 15 (by decide) 3 3 true
#guard checkSign 15 (by decide) 4 4 false
#guard checkSign 15 (by decide) 5 5 true
#guard checkSign 15 (by decide) 6 6 false
#guard checkSign 15 (by decide) 7 7 true
#guard checkSign 15 (by decide) 8 8 false
#guard checkSign 15 (by decide) 9 9 true
#guard checkSign 15 (by decide) 10 10 false
#guard checkSign 15 (by decide) 11 11 true
#guard checkSign 15 (by decide) 12 12 false
#guard checkSign 15 (by decide) 13 13 true
#guard checkSign 15 (by decide) 14 14 false
#guard checkSign 15 (by decide) 15 0 false
#guard checkSign 15 (by decide) 16 1 true
#guard checkSign 15 (by decide) 29 14 false
#guard checkSign 15 (by decide) 30 0 false
#guard checkSign 15 (by decide) 31 1 true
#guard checkSign 15 (by decide) 49 4 false
#guard checkSign 15 (by decide) (2 ^ 8 - 1) 0 false
#guard checkSign 15 (by decide) (2 ^ 8) 1 true
#guard checkSign 15 (by decide) (2 ^ 8 + 1) 2 false
#guard checkSign 15 (by decide) (2 ^ 32 - 1) 0 false
#guard checkSign 15 (by decide) (2 ^ 32) 1 true
#guard checkSign 15 (by decide) (2 ^ 32 + 1) 2 false
#guard checkSign 15 (by decide) (2 ^ 64 - 1) 0 false
#guard checkSign 15 (by decide) (2 ^ 64) 1 true
#guard checkSign 15 (by decide) (2 ^ 64 + 1) 2 false
#guard checkSign 15 (by decide) (2 ^ 255 - 1) 7 true
#guard checkSign 15 (by decide) (2 ^ 255) 8 false
#guard checkSign 15 (by decide) (2 ^ 255 + 1) 9 true
#guard checkSign 15 (by decide) (2 ^ 256 - 1) 0 false
#guard checkSign 15 (by decide) (2 ^ 256) 1 true
#guard checkSign 15 (by decide) (2 ^ 256 + 1) 2 false
#guard checkSign 15 (by decide) (2 ^ 381 - 1) 1 true
#guard checkSign 15 (by decide) (2 ^ 381) 2 false
#guard checkSign 15 (by decide) (2 ^ 381 + 1) 3 true
#guard checkSign 15 (by decide) (2 ^ 2048 - 1) 0 false
#guard checkSign 15 (by decide) (2 ^ 2048) 1 true
#guard checkSign 15 (by decide) (2 ^ 2048 + 1) 2 false
#guard checkSign 17 (by decide) 0 0 false
#guard checkSign 17 (by decide) 1 1 true
#guard checkSign 17 (by decide) 2 2 false
#guard checkSign 17 (by decide) 3 3 true
#guard checkSign 17 (by decide) 4 4 false
#guard checkSign 17 (by decide) 5 5 true
#guard checkSign 17 (by decide) 6 6 false
#guard checkSign 17 (by decide) 7 7 true
#guard checkSign 17 (by decide) 8 8 false
#guard checkSign 17 (by decide) 9 9 true
#guard checkSign 17 (by decide) 10 10 false
#guard checkSign 17 (by decide) 11 11 true
#guard checkSign 17 (by decide) 12 12 false
#guard checkSign 17 (by decide) 13 13 true
#guard checkSign 17 (by decide) 14 14 false
#guard checkSign 17 (by decide) 15 15 true
#guard checkSign 17 (by decide) 16 16 false
#guard checkSign 17 (by decide) 17 0 false
#guard checkSign 17 (by decide) 18 1 true
#guard checkSign 17 (by decide) 33 16 false
#guard checkSign 17 (by decide) 34 0 false
#guard checkSign 17 (by decide) 35 1 true
#guard checkSign 17 (by decide) 55 4 false
#guard checkSign 17 (by decide) (2 ^ 8 - 1) 0 false
#guard checkSign 17 (by decide) (2 ^ 8) 1 true
#guard checkSign 17 (by decide) (2 ^ 8 + 1) 2 false
#guard checkSign 17 (by decide) (2 ^ 32 - 1) 0 false
#guard checkSign 17 (by decide) (2 ^ 32) 1 true
#guard checkSign 17 (by decide) (2 ^ 32 + 1) 2 false
#guard checkSign 17 (by decide) (2 ^ 64 - 1) 0 false
#guard checkSign 17 (by decide) (2 ^ 64) 1 true
#guard checkSign 17 (by decide) (2 ^ 64 + 1) 2 false
#guard checkSign 17 (by decide) (2 ^ 255 - 1) 8 false
#guard checkSign 17 (by decide) (2 ^ 255) 9 true
#guard checkSign 17 (by decide) (2 ^ 255 + 1) 10 false
#guard checkSign 17 (by decide) (2 ^ 256 - 1) 0 false
#guard checkSign 17 (by decide) (2 ^ 256) 1 true
#guard checkSign 17 (by decide) (2 ^ 256 + 1) 2 false
#guard checkSign 17 (by decide) (2 ^ 381 - 1) 14 false
#guard checkSign 17 (by decide) (2 ^ 381) 15 true
#guard checkSign 17 (by decide) (2 ^ 381 + 1) 16 false
#guard checkSign 17 (by decide) (2 ^ 2048 - 1) 0 false
#guard checkSign 17 (by decide) (2 ^ 2048) 1 true
#guard checkSign 17 (by decide) (2 ^ 2048 + 1) 2 false

-- Large canonical residues in the BN254 and BLS12-381 base fields (both moduli odd).
#guard checkSign Bn254.q (by decide) (Bn254.q - 1) (Bn254.q - 1) false
#guard checkSign Bn254.q (by decide) (Bn254.q - 2) (Bn254.q - 2) true
#guard checkSign Bls12381.q (by decide) (Bls12381.q - 1) (Bls12381.q - 1) false
#guard checkSign Bls12381.q (by decide) (Bls12381.q - 2) (Bls12381.q - 2) true

end STFSpec.Conformance.Field
