/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Field

/-!
# Natural-reference power complete finite controls

Library `EthConformance`. Independent literal results check natural powers,
canonical bases, notation and range under three unrelated metadata choices.
Spec guidance: `STFSpec/informal/modules/EthField.md` §§3–7.
-/

namespace STFSpec.Conformance.Field
open STFSpec.Field

private def checkPower (p : Nat) (hp : 1 < p) (raw e canonical expected : Nat) : Bool :=
  [none, some 0, some (2 ^ 4096 + 17)].all fun metadata ↦
    letI : FieldModulus p := ⟨hp, metadata⟩
    let a : PrimeFieldRef p := PrimeFieldRef.ofNat raw
    a.toNat == canonical && (PrimeFieldRef.pow a e).toNat == expected &&
      (a ^ e).toNat == expected && decide ((a ^ e).toNat < p)

#guard checkPower 2 (by decide) 0 0 0 1
#guard checkPower 2 (by decide) 0 1 0 0
#guard checkPower 2 (by decide) 0 2 0 0
#guard checkPower 2 (by decide) 0 3 0 0
#guard checkPower 2 (by decide) 0 4 0 0
#guard checkPower 2 (by decide) 0 7 0 0
#guard checkPower 2 (by decide) 0 8 0 0
#guard checkPower 2 (by decide) 0 9 0 0
#guard checkPower 2 (by decide) 0 31 0 0
#guard checkPower 2 (by decide) 0 32 0 0
#guard checkPower 2 (by decide) 0 33 0 0
#guard checkPower 2 (by decide) 0 63 0 0
#guard checkPower 2 (by decide) 0 64 0 0
#guard checkPower 2 (by decide) 0 65 0 0
#guard checkPower 2 (by decide) 0 127 0 0
#guard checkPower 2 (by decide) 0 128 0 0
#guard checkPower 2 (by decide) 0 129 0 0
#guard checkPower 2 (by decide) 0 255 0 0
#guard checkPower 2 (by decide) 0 256 0 0
#guard checkPower 2 (by decide) 0 257 0 0
#guard checkPower 2 (by decide) 0 (2 ^ 32 - 1) 0 0
#guard checkPower 2 (by decide) 0 (2 ^ 32) 0 0
#guard checkPower 2 (by decide) 0 (2 ^ 32 + 1) 0 0
#guard checkPower 2 (by decide) 0 (2 ^ 64 - 1) 0 0
#guard checkPower 2 (by decide) 0 (2 ^ 64) 0 0
#guard checkPower 2 (by decide) 0 (2 ^ 64 + 1) 0 0
#guard checkPower 2 (by decide) 0 (2 ^ 255 - 1) 0 0
#guard checkPower 2 (by decide) 0 (2 ^ 255) 0 0
#guard checkPower 2 (by decide) 0 (2 ^ 255 + 1) 0 0
#guard checkPower 2 (by decide) 0 (2 ^ 256 + 1) 0 0
#guard checkPower 2 (by decide) 1 0 1 1
#guard checkPower 2 (by decide) 1 1 1 1
#guard checkPower 2 (by decide) 1 2 1 1
#guard checkPower 2 (by decide) 1 3 1 1
#guard checkPower 2 (by decide) 1 4 1 1
#guard checkPower 2 (by decide) 1 7 1 1
#guard checkPower 2 (by decide) 1 8 1 1
#guard checkPower 2 (by decide) 1 9 1 1
#guard checkPower 2 (by decide) 1 31 1 1
#guard checkPower 2 (by decide) 1 32 1 1
#guard checkPower 2 (by decide) 1 33 1 1
#guard checkPower 2 (by decide) 1 63 1 1
#guard checkPower 2 (by decide) 1 64 1 1
#guard checkPower 2 (by decide) 1 65 1 1
#guard checkPower 2 (by decide) 1 127 1 1
#guard checkPower 2 (by decide) 1 128 1 1
#guard checkPower 2 (by decide) 1 129 1 1
#guard checkPower 2 (by decide) 1 255 1 1
#guard checkPower 2 (by decide) 1 256 1 1
#guard checkPower 2 (by decide) 1 257 1 1
#guard checkPower 2 (by decide) 1 (2 ^ 32 - 1) 1 1
#guard checkPower 2 (by decide) 1 (2 ^ 32) 1 1
#guard checkPower 2 (by decide) 1 (2 ^ 32 + 1) 1 1
#guard checkPower 2 (by decide) 1 (2 ^ 64 - 1) 1 1
#guard checkPower 2 (by decide) 1 (2 ^ 64) 1 1
#guard checkPower 2 (by decide) 1 (2 ^ 64 + 1) 1 1
#guard checkPower 2 (by decide) 1 (2 ^ 255 - 1) 1 1
#guard checkPower 2 (by decide) 1 (2 ^ 255) 1 1
#guard checkPower 2 (by decide) 1 (2 ^ 255 + 1) 1 1
#guard checkPower 2 (by decide) 1 (2 ^ 256 + 1) 1 1
#guard checkPower 2 (by decide) 1 0 1 1
#guard checkPower 2 (by decide) 1 1 1 1
#guard checkPower 2 (by decide) 1 2 1 1
#guard checkPower 2 (by decide) 1 3 1 1
#guard checkPower 2 (by decide) 1 4 1 1
#guard checkPower 2 (by decide) 1 7 1 1
#guard checkPower 2 (by decide) 1 8 1 1
#guard checkPower 2 (by decide) 1 9 1 1
#guard checkPower 2 (by decide) 1 31 1 1
#guard checkPower 2 (by decide) 1 32 1 1
#guard checkPower 2 (by decide) 1 33 1 1
#guard checkPower 2 (by decide) 1 63 1 1
#guard checkPower 2 (by decide) 1 64 1 1
#guard checkPower 2 (by decide) 1 65 1 1
#guard checkPower 2 (by decide) 1 127 1 1
#guard checkPower 2 (by decide) 1 128 1 1
#guard checkPower 2 (by decide) 1 129 1 1
#guard checkPower 2 (by decide) 1 255 1 1
#guard checkPower 2 (by decide) 1 256 1 1
#guard checkPower 2 (by decide) 1 257 1 1
#guard checkPower 2 (by decide) 1 (2 ^ 32 - 1) 1 1
#guard checkPower 2 (by decide) 1 (2 ^ 32) 1 1
#guard checkPower 2 (by decide) 1 (2 ^ 32 + 1) 1 1
#guard checkPower 2 (by decide) 1 (2 ^ 64 - 1) 1 1
#guard checkPower 2 (by decide) 1 (2 ^ 64) 1 1
#guard checkPower 2 (by decide) 1 (2 ^ 64 + 1) 1 1
#guard checkPower 2 (by decide) 1 (2 ^ 255 - 1) 1 1
#guard checkPower 2 (by decide) 1 (2 ^ 255) 1 1
#guard checkPower 2 (by decide) 1 (2 ^ 255 + 1) 1 1
#guard checkPower 2 (by decide) 1 (2 ^ 256 + 1) 1 1
#guard checkPower 2 (by decide) 2 0 0 1
#guard checkPower 2 (by decide) 2 1 0 0
#guard checkPower 2 (by decide) 2 2 0 0
#guard checkPower 2 (by decide) 2 3 0 0
#guard checkPower 2 (by decide) 2 4 0 0
#guard checkPower 2 (by decide) 2 7 0 0
#guard checkPower 2 (by decide) 2 8 0 0
#guard checkPower 2 (by decide) 2 9 0 0
#guard checkPower 2 (by decide) 2 31 0 0
#guard checkPower 2 (by decide) 2 32 0 0
#guard checkPower 2 (by decide) 2 33 0 0
#guard checkPower 2 (by decide) 2 63 0 0
#guard checkPower 2 (by decide) 2 64 0 0
#guard checkPower 2 (by decide) 2 65 0 0
#guard checkPower 2 (by decide) 2 127 0 0
#guard checkPower 2 (by decide) 2 128 0 0
#guard checkPower 2 (by decide) 2 129 0 0
#guard checkPower 2 (by decide) 2 255 0 0
#guard checkPower 2 (by decide) 2 256 0 0
#guard checkPower 2 (by decide) 2 257 0 0
#guard checkPower 2 (by decide) 2 (2 ^ 32 - 1) 0 0
#guard checkPower 2 (by decide) 2 (2 ^ 32) 0 0
#guard checkPower 2 (by decide) 2 (2 ^ 32 + 1) 0 0
#guard checkPower 2 (by decide) 2 (2 ^ 64 - 1) 0 0
#guard checkPower 2 (by decide) 2 (2 ^ 64) 0 0
#guard checkPower 2 (by decide) 2 (2 ^ 64 + 1) 0 0
#guard checkPower 2 (by decide) 2 (2 ^ 255 - 1) 0 0
#guard checkPower 2 (by decide) 2 (2 ^ 255) 0 0
#guard checkPower 2 (by decide) 2 (2 ^ 255 + 1) 0 0
#guard checkPower 2 (by decide) 2 (2 ^ 256 + 1) 0 0
#guard checkPower 2 (by decide) 3 0 1 1
#guard checkPower 2 (by decide) 3 1 1 1
#guard checkPower 2 (by decide) 3 2 1 1
#guard checkPower 2 (by decide) 3 3 1 1
#guard checkPower 2 (by decide) 3 4 1 1
#guard checkPower 2 (by decide) 3 7 1 1
#guard checkPower 2 (by decide) 3 8 1 1
#guard checkPower 2 (by decide) 3 9 1 1
#guard checkPower 2 (by decide) 3 31 1 1
#guard checkPower 2 (by decide) 3 32 1 1
#guard checkPower 2 (by decide) 3 33 1 1
#guard checkPower 2 (by decide) 3 63 1 1
#guard checkPower 2 (by decide) 3 64 1 1
#guard checkPower 2 (by decide) 3 65 1 1
#guard checkPower 2 (by decide) 3 127 1 1
#guard checkPower 2 (by decide) 3 128 1 1
#guard checkPower 2 (by decide) 3 129 1 1
#guard checkPower 2 (by decide) 3 255 1 1
#guard checkPower 2 (by decide) 3 256 1 1
#guard checkPower 2 (by decide) 3 257 1 1
#guard checkPower 2 (by decide) 3 (2 ^ 32 - 1) 1 1
#guard checkPower 2 (by decide) 3 (2 ^ 32) 1 1
#guard checkPower 2 (by decide) 3 (2 ^ 32 + 1) 1 1
#guard checkPower 2 (by decide) 3 (2 ^ 64 - 1) 1 1
#guard checkPower 2 (by decide) 3 (2 ^ 64) 1 1
#guard checkPower 2 (by decide) 3 (2 ^ 64 + 1) 1 1
#guard checkPower 2 (by decide) 3 (2 ^ 255 - 1) 1 1
#guard checkPower 2 (by decide) 3 (2 ^ 255) 1 1
#guard checkPower 2 (by decide) 3 (2 ^ 255 + 1) 1 1
#guard checkPower 2 (by decide) 3 (2 ^ 256 + 1) 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) 0 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) 1 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) 2 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) 3 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) 4 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) 7 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) 8 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) 9 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) 31 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) 32 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) 33 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) 63 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) 64 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) 65 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) 127 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) 128 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) 129 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) 255 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) 256 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) 257 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) (2 ^ 32 - 1) 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) (2 ^ 32) 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) (2 ^ 32 + 1) 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) (2 ^ 64 - 1) 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) (2 ^ 64) 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) (2 ^ 64 + 1) 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) (2 ^ 255 - 1) 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) (2 ^ 255) 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) (2 ^ 255 + 1) 1 1
#guard checkPower 2 (by decide) (2 ^ 4096 + 17) (2 ^ 256 + 1) 1 1
#guard checkPower 3 (by decide) 0 0 0 1
#guard checkPower 3 (by decide) 0 1 0 0
#guard checkPower 3 (by decide) 0 2 0 0
#guard checkPower 3 (by decide) 0 3 0 0
#guard checkPower 3 (by decide) 0 4 0 0
#guard checkPower 3 (by decide) 0 7 0 0
#guard checkPower 3 (by decide) 0 8 0 0
#guard checkPower 3 (by decide) 0 9 0 0
#guard checkPower 3 (by decide) 0 31 0 0
#guard checkPower 3 (by decide) 0 32 0 0
#guard checkPower 3 (by decide) 0 33 0 0
#guard checkPower 3 (by decide) 0 63 0 0
#guard checkPower 3 (by decide) 0 64 0 0
#guard checkPower 3 (by decide) 0 65 0 0
#guard checkPower 3 (by decide) 0 127 0 0
#guard checkPower 3 (by decide) 0 128 0 0
#guard checkPower 3 (by decide) 0 129 0 0
#guard checkPower 3 (by decide) 0 255 0 0
#guard checkPower 3 (by decide) 0 256 0 0
#guard checkPower 3 (by decide) 0 257 0 0
#guard checkPower 3 (by decide) 0 (2 ^ 32 - 1) 0 0
#guard checkPower 3 (by decide) 0 (2 ^ 32) 0 0
#guard checkPower 3 (by decide) 0 (2 ^ 32 + 1) 0 0
#guard checkPower 3 (by decide) 0 (2 ^ 64 - 1) 0 0
#guard checkPower 3 (by decide) 0 (2 ^ 64) 0 0
#guard checkPower 3 (by decide) 0 (2 ^ 64 + 1) 0 0
#guard checkPower 3 (by decide) 0 (2 ^ 255 - 1) 0 0
#guard checkPower 3 (by decide) 0 (2 ^ 255) 0 0
#guard checkPower 3 (by decide) 0 (2 ^ 255 + 1) 0 0
#guard checkPower 3 (by decide) 0 (2 ^ 256 + 1) 0 0
#guard checkPower 3 (by decide) 1 0 1 1
#guard checkPower 3 (by decide) 1 1 1 1
#guard checkPower 3 (by decide) 1 2 1 1
#guard checkPower 3 (by decide) 1 3 1 1
#guard checkPower 3 (by decide) 1 4 1 1
#guard checkPower 3 (by decide) 1 7 1 1
#guard checkPower 3 (by decide) 1 8 1 1
#guard checkPower 3 (by decide) 1 9 1 1
#guard checkPower 3 (by decide) 1 31 1 1
#guard checkPower 3 (by decide) 1 32 1 1
#guard checkPower 3 (by decide) 1 33 1 1
#guard checkPower 3 (by decide) 1 63 1 1
#guard checkPower 3 (by decide) 1 64 1 1
#guard checkPower 3 (by decide) 1 65 1 1
#guard checkPower 3 (by decide) 1 127 1 1
#guard checkPower 3 (by decide) 1 128 1 1
#guard checkPower 3 (by decide) 1 129 1 1
#guard checkPower 3 (by decide) 1 255 1 1
#guard checkPower 3 (by decide) 1 256 1 1
#guard checkPower 3 (by decide) 1 257 1 1
#guard checkPower 3 (by decide) 1 (2 ^ 32 - 1) 1 1
#guard checkPower 3 (by decide) 1 (2 ^ 32) 1 1
#guard checkPower 3 (by decide) 1 (2 ^ 32 + 1) 1 1
#guard checkPower 3 (by decide) 1 (2 ^ 64 - 1) 1 1
#guard checkPower 3 (by decide) 1 (2 ^ 64) 1 1
#guard checkPower 3 (by decide) 1 (2 ^ 64 + 1) 1 1
#guard checkPower 3 (by decide) 1 (2 ^ 255 - 1) 1 1
#guard checkPower 3 (by decide) 1 (2 ^ 255) 1 1
#guard checkPower 3 (by decide) 1 (2 ^ 255 + 1) 1 1
#guard checkPower 3 (by decide) 1 (2 ^ 256 + 1) 1 1
#guard checkPower 3 (by decide) 2 0 2 1
#guard checkPower 3 (by decide) 2 1 2 2
#guard checkPower 3 (by decide) 2 2 2 1
#guard checkPower 3 (by decide) 2 3 2 2
#guard checkPower 3 (by decide) 2 4 2 1
#guard checkPower 3 (by decide) 2 7 2 2
#guard checkPower 3 (by decide) 2 8 2 1
#guard checkPower 3 (by decide) 2 9 2 2
#guard checkPower 3 (by decide) 2 31 2 2
#guard checkPower 3 (by decide) 2 32 2 1
#guard checkPower 3 (by decide) 2 33 2 2
#guard checkPower 3 (by decide) 2 63 2 2
#guard checkPower 3 (by decide) 2 64 2 1
#guard checkPower 3 (by decide) 2 65 2 2
#guard checkPower 3 (by decide) 2 127 2 2
#guard checkPower 3 (by decide) 2 128 2 1
#guard checkPower 3 (by decide) 2 129 2 2
#guard checkPower 3 (by decide) 2 255 2 2
#guard checkPower 3 (by decide) 2 256 2 1
#guard checkPower 3 (by decide) 2 257 2 2
#guard checkPower 3 (by decide) 2 (2 ^ 32 - 1) 2 2
#guard checkPower 3 (by decide) 2 (2 ^ 32) 2 1
#guard checkPower 3 (by decide) 2 (2 ^ 32 + 1) 2 2
#guard checkPower 3 (by decide) 2 (2 ^ 64 - 1) 2 2
#guard checkPower 3 (by decide) 2 (2 ^ 64) 2 1
#guard checkPower 3 (by decide) 2 (2 ^ 64 + 1) 2 2
#guard checkPower 3 (by decide) 2 (2 ^ 255 - 1) 2 2
#guard checkPower 3 (by decide) 2 (2 ^ 255) 2 1
#guard checkPower 3 (by decide) 2 (2 ^ 255 + 1) 2 2
#guard checkPower 3 (by decide) 2 (2 ^ 256 + 1) 2 2
#guard checkPower 3 (by decide) 3 0 0 1
#guard checkPower 3 (by decide) 3 1 0 0
#guard checkPower 3 (by decide) 3 2 0 0
#guard checkPower 3 (by decide) 3 3 0 0
#guard checkPower 3 (by decide) 3 4 0 0
#guard checkPower 3 (by decide) 3 7 0 0
#guard checkPower 3 (by decide) 3 8 0 0
#guard checkPower 3 (by decide) 3 9 0 0
#guard checkPower 3 (by decide) 3 31 0 0
#guard checkPower 3 (by decide) 3 32 0 0
#guard checkPower 3 (by decide) 3 33 0 0
#guard checkPower 3 (by decide) 3 63 0 0
#guard checkPower 3 (by decide) 3 64 0 0
#guard checkPower 3 (by decide) 3 65 0 0
#guard checkPower 3 (by decide) 3 127 0 0
#guard checkPower 3 (by decide) 3 128 0 0
#guard checkPower 3 (by decide) 3 129 0 0
#guard checkPower 3 (by decide) 3 255 0 0
#guard checkPower 3 (by decide) 3 256 0 0
#guard checkPower 3 (by decide) 3 257 0 0
#guard checkPower 3 (by decide) 3 (2 ^ 32 - 1) 0 0
#guard checkPower 3 (by decide) 3 (2 ^ 32) 0 0
#guard checkPower 3 (by decide) 3 (2 ^ 32 + 1) 0 0
#guard checkPower 3 (by decide) 3 (2 ^ 64 - 1) 0 0
#guard checkPower 3 (by decide) 3 (2 ^ 64) 0 0
#guard checkPower 3 (by decide) 3 (2 ^ 64 + 1) 0 0
#guard checkPower 3 (by decide) 3 (2 ^ 255 - 1) 0 0
#guard checkPower 3 (by decide) 3 (2 ^ 255) 0 0
#guard checkPower 3 (by decide) 3 (2 ^ 255 + 1) 0 0
#guard checkPower 3 (by decide) 3 (2 ^ 256 + 1) 0 0
#guard checkPower 3 (by decide) 4 0 1 1
#guard checkPower 3 (by decide) 4 1 1 1
#guard checkPower 3 (by decide) 4 2 1 1
#guard checkPower 3 (by decide) 4 3 1 1
#guard checkPower 3 (by decide) 4 4 1 1
#guard checkPower 3 (by decide) 4 7 1 1
#guard checkPower 3 (by decide) 4 8 1 1
#guard checkPower 3 (by decide) 4 9 1 1
#guard checkPower 3 (by decide) 4 31 1 1
#guard checkPower 3 (by decide) 4 32 1 1
#guard checkPower 3 (by decide) 4 33 1 1
#guard checkPower 3 (by decide) 4 63 1 1
#guard checkPower 3 (by decide) 4 64 1 1
#guard checkPower 3 (by decide) 4 65 1 1
#guard checkPower 3 (by decide) 4 127 1 1
#guard checkPower 3 (by decide) 4 128 1 1
#guard checkPower 3 (by decide) 4 129 1 1
#guard checkPower 3 (by decide) 4 255 1 1
#guard checkPower 3 (by decide) 4 256 1 1
#guard checkPower 3 (by decide) 4 257 1 1
#guard checkPower 3 (by decide) 4 (2 ^ 32 - 1) 1 1
#guard checkPower 3 (by decide) 4 (2 ^ 32) 1 1
#guard checkPower 3 (by decide) 4 (2 ^ 32 + 1) 1 1
#guard checkPower 3 (by decide) 4 (2 ^ 64 - 1) 1 1
#guard checkPower 3 (by decide) 4 (2 ^ 64) 1 1
#guard checkPower 3 (by decide) 4 (2 ^ 64 + 1) 1 1
#guard checkPower 3 (by decide) 4 (2 ^ 255 - 1) 1 1
#guard checkPower 3 (by decide) 4 (2 ^ 255) 1 1
#guard checkPower 3 (by decide) 4 (2 ^ 255 + 1) 1 1
#guard checkPower 3 (by decide) 4 (2 ^ 256 + 1) 1 1
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) 0 0 1
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) 1 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) 2 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) 3 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) 4 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) 7 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) 8 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) 9 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) 31 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) 32 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) 33 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) 63 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) 64 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) 65 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) 127 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) 128 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) 129 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) 255 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) 256 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) 257 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) (2 ^ 32 - 1) 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) (2 ^ 32) 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) (2 ^ 32 + 1) 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) (2 ^ 64 - 1) 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) (2 ^ 64) 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) (2 ^ 64 + 1) 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) (2 ^ 255 - 1) 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) (2 ^ 255) 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) (2 ^ 255 + 1) 0 0
#guard checkPower 3 (by decide) (2 ^ 4096 + 17) (2 ^ 256 + 1) 0 0
#guard checkPower 4 (by decide) 0 0 0 1
#guard checkPower 4 (by decide) 0 1 0 0
#guard checkPower 4 (by decide) 0 2 0 0
#guard checkPower 4 (by decide) 0 3 0 0
#guard checkPower 4 (by decide) 0 4 0 0
#guard checkPower 4 (by decide) 0 7 0 0
#guard checkPower 4 (by decide) 0 8 0 0
#guard checkPower 4 (by decide) 0 9 0 0
#guard checkPower 4 (by decide) 0 31 0 0
#guard checkPower 4 (by decide) 0 32 0 0
#guard checkPower 4 (by decide) 0 33 0 0
#guard checkPower 4 (by decide) 0 63 0 0
#guard checkPower 4 (by decide) 0 64 0 0
#guard checkPower 4 (by decide) 0 65 0 0
#guard checkPower 4 (by decide) 0 127 0 0
#guard checkPower 4 (by decide) 0 128 0 0
#guard checkPower 4 (by decide) 0 129 0 0
#guard checkPower 4 (by decide) 0 255 0 0
#guard checkPower 4 (by decide) 0 256 0 0
#guard checkPower 4 (by decide) 0 257 0 0
#guard checkPower 4 (by decide) 0 (2 ^ 32 - 1) 0 0
#guard checkPower 4 (by decide) 0 (2 ^ 32) 0 0
#guard checkPower 4 (by decide) 0 (2 ^ 32 + 1) 0 0
#guard checkPower 4 (by decide) 0 (2 ^ 64 - 1) 0 0
#guard checkPower 4 (by decide) 0 (2 ^ 64) 0 0
#guard checkPower 4 (by decide) 0 (2 ^ 64 + 1) 0 0
#guard checkPower 4 (by decide) 0 (2 ^ 255 - 1) 0 0
#guard checkPower 4 (by decide) 0 (2 ^ 255) 0 0
#guard checkPower 4 (by decide) 0 (2 ^ 255 + 1) 0 0
#guard checkPower 4 (by decide) 0 (2 ^ 256 + 1) 0 0
#guard checkPower 4 (by decide) 1 0 1 1
#guard checkPower 4 (by decide) 1 1 1 1
#guard checkPower 4 (by decide) 1 2 1 1
#guard checkPower 4 (by decide) 1 3 1 1
#guard checkPower 4 (by decide) 1 4 1 1
#guard checkPower 4 (by decide) 1 7 1 1
#guard checkPower 4 (by decide) 1 8 1 1
#guard checkPower 4 (by decide) 1 9 1 1
#guard checkPower 4 (by decide) 1 31 1 1
#guard checkPower 4 (by decide) 1 32 1 1
#guard checkPower 4 (by decide) 1 33 1 1
#guard checkPower 4 (by decide) 1 63 1 1
#guard checkPower 4 (by decide) 1 64 1 1
#guard checkPower 4 (by decide) 1 65 1 1
#guard checkPower 4 (by decide) 1 127 1 1
#guard checkPower 4 (by decide) 1 128 1 1
#guard checkPower 4 (by decide) 1 129 1 1
#guard checkPower 4 (by decide) 1 255 1 1
#guard checkPower 4 (by decide) 1 256 1 1
#guard checkPower 4 (by decide) 1 257 1 1
#guard checkPower 4 (by decide) 1 (2 ^ 32 - 1) 1 1
#guard checkPower 4 (by decide) 1 (2 ^ 32) 1 1
#guard checkPower 4 (by decide) 1 (2 ^ 32 + 1) 1 1
#guard checkPower 4 (by decide) 1 (2 ^ 64 - 1) 1 1
#guard checkPower 4 (by decide) 1 (2 ^ 64) 1 1
#guard checkPower 4 (by decide) 1 (2 ^ 64 + 1) 1 1
#guard checkPower 4 (by decide) 1 (2 ^ 255 - 1) 1 1
#guard checkPower 4 (by decide) 1 (2 ^ 255) 1 1
#guard checkPower 4 (by decide) 1 (2 ^ 255 + 1) 1 1
#guard checkPower 4 (by decide) 1 (2 ^ 256 + 1) 1 1
#guard checkPower 4 (by decide) 3 0 3 1
#guard checkPower 4 (by decide) 3 1 3 3
#guard checkPower 4 (by decide) 3 2 3 1
#guard checkPower 4 (by decide) 3 3 3 3
#guard checkPower 4 (by decide) 3 4 3 1
#guard checkPower 4 (by decide) 3 7 3 3
#guard checkPower 4 (by decide) 3 8 3 1
#guard checkPower 4 (by decide) 3 9 3 3
#guard checkPower 4 (by decide) 3 31 3 3
#guard checkPower 4 (by decide) 3 32 3 1
#guard checkPower 4 (by decide) 3 33 3 3
#guard checkPower 4 (by decide) 3 63 3 3
#guard checkPower 4 (by decide) 3 64 3 1
#guard checkPower 4 (by decide) 3 65 3 3
#guard checkPower 4 (by decide) 3 127 3 3
#guard checkPower 4 (by decide) 3 128 3 1
#guard checkPower 4 (by decide) 3 129 3 3
#guard checkPower 4 (by decide) 3 255 3 3
#guard checkPower 4 (by decide) 3 256 3 1
#guard checkPower 4 (by decide) 3 257 3 3
#guard checkPower 4 (by decide) 3 (2 ^ 32 - 1) 3 3
#guard checkPower 4 (by decide) 3 (2 ^ 32) 3 1
#guard checkPower 4 (by decide) 3 (2 ^ 32 + 1) 3 3
#guard checkPower 4 (by decide) 3 (2 ^ 64 - 1) 3 3
#guard checkPower 4 (by decide) 3 (2 ^ 64) 3 1
#guard checkPower 4 (by decide) 3 (2 ^ 64 + 1) 3 3
#guard checkPower 4 (by decide) 3 (2 ^ 255 - 1) 3 3
#guard checkPower 4 (by decide) 3 (2 ^ 255) 3 1
#guard checkPower 4 (by decide) 3 (2 ^ 255 + 1) 3 3
#guard checkPower 4 (by decide) 3 (2 ^ 256 + 1) 3 3
#guard checkPower 4 (by decide) 4 0 0 1
#guard checkPower 4 (by decide) 4 1 0 0
#guard checkPower 4 (by decide) 4 2 0 0
#guard checkPower 4 (by decide) 4 3 0 0
#guard checkPower 4 (by decide) 4 4 0 0
#guard checkPower 4 (by decide) 4 7 0 0
#guard checkPower 4 (by decide) 4 8 0 0
#guard checkPower 4 (by decide) 4 9 0 0
#guard checkPower 4 (by decide) 4 31 0 0
#guard checkPower 4 (by decide) 4 32 0 0
#guard checkPower 4 (by decide) 4 33 0 0
#guard checkPower 4 (by decide) 4 63 0 0
#guard checkPower 4 (by decide) 4 64 0 0
#guard checkPower 4 (by decide) 4 65 0 0
#guard checkPower 4 (by decide) 4 127 0 0
#guard checkPower 4 (by decide) 4 128 0 0
#guard checkPower 4 (by decide) 4 129 0 0
#guard checkPower 4 (by decide) 4 255 0 0
#guard checkPower 4 (by decide) 4 256 0 0
#guard checkPower 4 (by decide) 4 257 0 0
#guard checkPower 4 (by decide) 4 (2 ^ 32 - 1) 0 0
#guard checkPower 4 (by decide) 4 (2 ^ 32) 0 0
#guard checkPower 4 (by decide) 4 (2 ^ 32 + 1) 0 0
#guard checkPower 4 (by decide) 4 (2 ^ 64 - 1) 0 0
#guard checkPower 4 (by decide) 4 (2 ^ 64) 0 0
#guard checkPower 4 (by decide) 4 (2 ^ 64 + 1) 0 0
#guard checkPower 4 (by decide) 4 (2 ^ 255 - 1) 0 0
#guard checkPower 4 (by decide) 4 (2 ^ 255) 0 0
#guard checkPower 4 (by decide) 4 (2 ^ 255 + 1) 0 0
#guard checkPower 4 (by decide) 4 (2 ^ 256 + 1) 0 0
#guard checkPower 4 (by decide) 5 0 1 1
#guard checkPower 4 (by decide) 5 1 1 1
#guard checkPower 4 (by decide) 5 2 1 1
#guard checkPower 4 (by decide) 5 3 1 1
#guard checkPower 4 (by decide) 5 4 1 1
#guard checkPower 4 (by decide) 5 7 1 1
#guard checkPower 4 (by decide) 5 8 1 1
#guard checkPower 4 (by decide) 5 9 1 1
#guard checkPower 4 (by decide) 5 31 1 1
#guard checkPower 4 (by decide) 5 32 1 1
#guard checkPower 4 (by decide) 5 33 1 1
#guard checkPower 4 (by decide) 5 63 1 1
#guard checkPower 4 (by decide) 5 64 1 1
#guard checkPower 4 (by decide) 5 65 1 1
#guard checkPower 4 (by decide) 5 127 1 1
#guard checkPower 4 (by decide) 5 128 1 1
#guard checkPower 4 (by decide) 5 129 1 1
#guard checkPower 4 (by decide) 5 255 1 1
#guard checkPower 4 (by decide) 5 256 1 1
#guard checkPower 4 (by decide) 5 257 1 1
#guard checkPower 4 (by decide) 5 (2 ^ 32 - 1) 1 1
#guard checkPower 4 (by decide) 5 (2 ^ 32) 1 1
#guard checkPower 4 (by decide) 5 (2 ^ 32 + 1) 1 1
#guard checkPower 4 (by decide) 5 (2 ^ 64 - 1) 1 1
#guard checkPower 4 (by decide) 5 (2 ^ 64) 1 1
#guard checkPower 4 (by decide) 5 (2 ^ 64 + 1) 1 1
#guard checkPower 4 (by decide) 5 (2 ^ 255 - 1) 1 1
#guard checkPower 4 (by decide) 5 (2 ^ 255) 1 1
#guard checkPower 4 (by decide) 5 (2 ^ 255 + 1) 1 1
#guard checkPower 4 (by decide) 5 (2 ^ 256 + 1) 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) 0 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) 1 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) 2 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) 3 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) 4 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) 7 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) 8 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) 9 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) 31 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) 32 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) 33 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) 63 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) 64 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) 65 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) 127 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) 128 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) 129 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) 255 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) 256 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) 257 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) (2 ^ 32 - 1) 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) (2 ^ 32) 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) (2 ^ 32 + 1) 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) (2 ^ 64 - 1) 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) (2 ^ 64) 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) (2 ^ 64 + 1) 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) (2 ^ 255 - 1) 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) (2 ^ 255) 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) (2 ^ 255 + 1) 1 1
#guard checkPower 4 (by decide) (2 ^ 4096 + 17) (2 ^ 256 + 1) 1 1
#guard checkPower 5 (by decide) 0 0 0 1
#guard checkPower 5 (by decide) 0 1 0 0
#guard checkPower 5 (by decide) 0 2 0 0
#guard checkPower 5 (by decide) 0 3 0 0
#guard checkPower 5 (by decide) 0 4 0 0
#guard checkPower 5 (by decide) 0 7 0 0
#guard checkPower 5 (by decide) 0 8 0 0
#guard checkPower 5 (by decide) 0 9 0 0
#guard checkPower 5 (by decide) 0 31 0 0
#guard checkPower 5 (by decide) 0 32 0 0
#guard checkPower 5 (by decide) 0 33 0 0
#guard checkPower 5 (by decide) 0 63 0 0
#guard checkPower 5 (by decide) 0 64 0 0
#guard checkPower 5 (by decide) 0 65 0 0
#guard checkPower 5 (by decide) 0 127 0 0
#guard checkPower 5 (by decide) 0 128 0 0
#guard checkPower 5 (by decide) 0 129 0 0
#guard checkPower 5 (by decide) 0 255 0 0
#guard checkPower 5 (by decide) 0 256 0 0
#guard checkPower 5 (by decide) 0 257 0 0
#guard checkPower 5 (by decide) 0 (2 ^ 32 - 1) 0 0
#guard checkPower 5 (by decide) 0 (2 ^ 32) 0 0
#guard checkPower 5 (by decide) 0 (2 ^ 32 + 1) 0 0
#guard checkPower 5 (by decide) 0 (2 ^ 64 - 1) 0 0
#guard checkPower 5 (by decide) 0 (2 ^ 64) 0 0
#guard checkPower 5 (by decide) 0 (2 ^ 64 + 1) 0 0
#guard checkPower 5 (by decide) 0 (2 ^ 255 - 1) 0 0
#guard checkPower 5 (by decide) 0 (2 ^ 255) 0 0
#guard checkPower 5 (by decide) 0 (2 ^ 255 + 1) 0 0
#guard checkPower 5 (by decide) 0 (2 ^ 256 + 1) 0 0
#guard checkPower 5 (by decide) 1 0 1 1
#guard checkPower 5 (by decide) 1 1 1 1
#guard checkPower 5 (by decide) 1 2 1 1
#guard checkPower 5 (by decide) 1 3 1 1
#guard checkPower 5 (by decide) 1 4 1 1
#guard checkPower 5 (by decide) 1 7 1 1
#guard checkPower 5 (by decide) 1 8 1 1
#guard checkPower 5 (by decide) 1 9 1 1
#guard checkPower 5 (by decide) 1 31 1 1
#guard checkPower 5 (by decide) 1 32 1 1
#guard checkPower 5 (by decide) 1 33 1 1
#guard checkPower 5 (by decide) 1 63 1 1
#guard checkPower 5 (by decide) 1 64 1 1
#guard checkPower 5 (by decide) 1 65 1 1
#guard checkPower 5 (by decide) 1 127 1 1
#guard checkPower 5 (by decide) 1 128 1 1
#guard checkPower 5 (by decide) 1 129 1 1
#guard checkPower 5 (by decide) 1 255 1 1
#guard checkPower 5 (by decide) 1 256 1 1
#guard checkPower 5 (by decide) 1 257 1 1
#guard checkPower 5 (by decide) 1 (2 ^ 32 - 1) 1 1
#guard checkPower 5 (by decide) 1 (2 ^ 32) 1 1
#guard checkPower 5 (by decide) 1 (2 ^ 32 + 1) 1 1
#guard checkPower 5 (by decide) 1 (2 ^ 64 - 1) 1 1
#guard checkPower 5 (by decide) 1 (2 ^ 64) 1 1
#guard checkPower 5 (by decide) 1 (2 ^ 64 + 1) 1 1
#guard checkPower 5 (by decide) 1 (2 ^ 255 - 1) 1 1
#guard checkPower 5 (by decide) 1 (2 ^ 255) 1 1
#guard checkPower 5 (by decide) 1 (2 ^ 255 + 1) 1 1
#guard checkPower 5 (by decide) 1 (2 ^ 256 + 1) 1 1
#guard checkPower 5 (by decide) 4 0 4 1
#guard checkPower 5 (by decide) 4 1 4 4
#guard checkPower 5 (by decide) 4 2 4 1
#guard checkPower 5 (by decide) 4 3 4 4
#guard checkPower 5 (by decide) 4 4 4 1
#guard checkPower 5 (by decide) 4 7 4 4
#guard checkPower 5 (by decide) 4 8 4 1
#guard checkPower 5 (by decide) 4 9 4 4
#guard checkPower 5 (by decide) 4 31 4 4
#guard checkPower 5 (by decide) 4 32 4 1
#guard checkPower 5 (by decide) 4 33 4 4
#guard checkPower 5 (by decide) 4 63 4 4
#guard checkPower 5 (by decide) 4 64 4 1
#guard checkPower 5 (by decide) 4 65 4 4
#guard checkPower 5 (by decide) 4 127 4 4
#guard checkPower 5 (by decide) 4 128 4 1
#guard checkPower 5 (by decide) 4 129 4 4
#guard checkPower 5 (by decide) 4 255 4 4
#guard checkPower 5 (by decide) 4 256 4 1
#guard checkPower 5 (by decide) 4 257 4 4
#guard checkPower 5 (by decide) 4 (2 ^ 32 - 1) 4 4
#guard checkPower 5 (by decide) 4 (2 ^ 32) 4 1
#guard checkPower 5 (by decide) 4 (2 ^ 32 + 1) 4 4
#guard checkPower 5 (by decide) 4 (2 ^ 64 - 1) 4 4
#guard checkPower 5 (by decide) 4 (2 ^ 64) 4 1
#guard checkPower 5 (by decide) 4 (2 ^ 64 + 1) 4 4
#guard checkPower 5 (by decide) 4 (2 ^ 255 - 1) 4 4
#guard checkPower 5 (by decide) 4 (2 ^ 255) 4 1
#guard checkPower 5 (by decide) 4 (2 ^ 255 + 1) 4 4
#guard checkPower 5 (by decide) 4 (2 ^ 256 + 1) 4 4
#guard checkPower 5 (by decide) 5 0 0 1
#guard checkPower 5 (by decide) 5 1 0 0
#guard checkPower 5 (by decide) 5 2 0 0
#guard checkPower 5 (by decide) 5 3 0 0
#guard checkPower 5 (by decide) 5 4 0 0
#guard checkPower 5 (by decide) 5 7 0 0
#guard checkPower 5 (by decide) 5 8 0 0
#guard checkPower 5 (by decide) 5 9 0 0
#guard checkPower 5 (by decide) 5 31 0 0
#guard checkPower 5 (by decide) 5 32 0 0
#guard checkPower 5 (by decide) 5 33 0 0
#guard checkPower 5 (by decide) 5 63 0 0
#guard checkPower 5 (by decide) 5 64 0 0
#guard checkPower 5 (by decide) 5 65 0 0
#guard checkPower 5 (by decide) 5 127 0 0
#guard checkPower 5 (by decide) 5 128 0 0
#guard checkPower 5 (by decide) 5 129 0 0
#guard checkPower 5 (by decide) 5 255 0 0
#guard checkPower 5 (by decide) 5 256 0 0
#guard checkPower 5 (by decide) 5 257 0 0
#guard checkPower 5 (by decide) 5 (2 ^ 32 - 1) 0 0
#guard checkPower 5 (by decide) 5 (2 ^ 32) 0 0
#guard checkPower 5 (by decide) 5 (2 ^ 32 + 1) 0 0
#guard checkPower 5 (by decide) 5 (2 ^ 64 - 1) 0 0
#guard checkPower 5 (by decide) 5 (2 ^ 64) 0 0
#guard checkPower 5 (by decide) 5 (2 ^ 64 + 1) 0 0
#guard checkPower 5 (by decide) 5 (2 ^ 255 - 1) 0 0
#guard checkPower 5 (by decide) 5 (2 ^ 255) 0 0
#guard checkPower 5 (by decide) 5 (2 ^ 255 + 1) 0 0
#guard checkPower 5 (by decide) 5 (2 ^ 256 + 1) 0 0
#guard checkPower 5 (by decide) 6 0 1 1
#guard checkPower 5 (by decide) 6 1 1 1
#guard checkPower 5 (by decide) 6 2 1 1
#guard checkPower 5 (by decide) 6 3 1 1
#guard checkPower 5 (by decide) 6 4 1 1
#guard checkPower 5 (by decide) 6 7 1 1
#guard checkPower 5 (by decide) 6 8 1 1
#guard checkPower 5 (by decide) 6 9 1 1
#guard checkPower 5 (by decide) 6 31 1 1
#guard checkPower 5 (by decide) 6 32 1 1
#guard checkPower 5 (by decide) 6 33 1 1
#guard checkPower 5 (by decide) 6 63 1 1
#guard checkPower 5 (by decide) 6 64 1 1
#guard checkPower 5 (by decide) 6 65 1 1
#guard checkPower 5 (by decide) 6 127 1 1
#guard checkPower 5 (by decide) 6 128 1 1
#guard checkPower 5 (by decide) 6 129 1 1
#guard checkPower 5 (by decide) 6 255 1 1
#guard checkPower 5 (by decide) 6 256 1 1
#guard checkPower 5 (by decide) 6 257 1 1
#guard checkPower 5 (by decide) 6 (2 ^ 32 - 1) 1 1
#guard checkPower 5 (by decide) 6 (2 ^ 32) 1 1
#guard checkPower 5 (by decide) 6 (2 ^ 32 + 1) 1 1
#guard checkPower 5 (by decide) 6 (2 ^ 64 - 1) 1 1
#guard checkPower 5 (by decide) 6 (2 ^ 64) 1 1
#guard checkPower 5 (by decide) 6 (2 ^ 64 + 1) 1 1
#guard checkPower 5 (by decide) 6 (2 ^ 255 - 1) 1 1
#guard checkPower 5 (by decide) 6 (2 ^ 255) 1 1
#guard checkPower 5 (by decide) 6 (2 ^ 255 + 1) 1 1
#guard checkPower 5 (by decide) 6 (2 ^ 256 + 1) 1 1
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) 0 3 1
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) 1 3 3
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) 2 3 4
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) 3 3 2
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) 4 3 1
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) 7 3 2
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) 8 3 1
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) 9 3 3
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) 31 3 2
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) 32 3 1
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) 33 3 3
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) 63 3 2
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) 64 3 1
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) 65 3 3
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) 127 3 2
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) 128 3 1
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) 129 3 3
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) 255 3 2
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) 256 3 1
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) 257 3 3
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) (2 ^ 32 - 1) 3 2
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) (2 ^ 32) 3 1
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) (2 ^ 32 + 1) 3 3
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) (2 ^ 64 - 1) 3 2
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) (2 ^ 64) 3 1
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) (2 ^ 64 + 1) 3 3
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) (2 ^ 255 - 1) 3 2
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) (2 ^ 255) 3 1
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) (2 ^ 255 + 1) 3 3
#guard checkPower 5 (by decide) (2 ^ 4096 + 17) (2 ^ 256 + 1) 3 3
#guard checkPower 6 (by decide) 0 0 0 1
#guard checkPower 6 (by decide) 0 1 0 0
#guard checkPower 6 (by decide) 0 2 0 0
#guard checkPower 6 (by decide) 0 3 0 0
#guard checkPower 6 (by decide) 0 4 0 0
#guard checkPower 6 (by decide) 0 7 0 0
#guard checkPower 6 (by decide) 0 8 0 0
#guard checkPower 6 (by decide) 0 9 0 0
#guard checkPower 6 (by decide) 0 31 0 0
#guard checkPower 6 (by decide) 0 32 0 0
#guard checkPower 6 (by decide) 0 33 0 0
#guard checkPower 6 (by decide) 0 63 0 0
#guard checkPower 6 (by decide) 0 64 0 0
#guard checkPower 6 (by decide) 0 65 0 0
#guard checkPower 6 (by decide) 0 127 0 0
#guard checkPower 6 (by decide) 0 128 0 0
#guard checkPower 6 (by decide) 0 129 0 0
#guard checkPower 6 (by decide) 0 255 0 0
#guard checkPower 6 (by decide) 0 256 0 0
#guard checkPower 6 (by decide) 0 257 0 0
#guard checkPower 6 (by decide) 0 (2 ^ 32 - 1) 0 0
#guard checkPower 6 (by decide) 0 (2 ^ 32) 0 0
#guard checkPower 6 (by decide) 0 (2 ^ 32 + 1) 0 0
#guard checkPower 6 (by decide) 0 (2 ^ 64 - 1) 0 0
#guard checkPower 6 (by decide) 0 (2 ^ 64) 0 0
#guard checkPower 6 (by decide) 0 (2 ^ 64 + 1) 0 0
#guard checkPower 6 (by decide) 0 (2 ^ 255 - 1) 0 0
#guard checkPower 6 (by decide) 0 (2 ^ 255) 0 0
#guard checkPower 6 (by decide) 0 (2 ^ 255 + 1) 0 0
#guard checkPower 6 (by decide) 0 (2 ^ 256 + 1) 0 0
#guard checkPower 6 (by decide) 1 0 1 1
#guard checkPower 6 (by decide) 1 1 1 1
#guard checkPower 6 (by decide) 1 2 1 1
#guard checkPower 6 (by decide) 1 3 1 1
#guard checkPower 6 (by decide) 1 4 1 1
#guard checkPower 6 (by decide) 1 7 1 1
#guard checkPower 6 (by decide) 1 8 1 1
#guard checkPower 6 (by decide) 1 9 1 1
#guard checkPower 6 (by decide) 1 31 1 1
#guard checkPower 6 (by decide) 1 32 1 1
#guard checkPower 6 (by decide) 1 33 1 1
#guard checkPower 6 (by decide) 1 63 1 1
#guard checkPower 6 (by decide) 1 64 1 1
#guard checkPower 6 (by decide) 1 65 1 1
#guard checkPower 6 (by decide) 1 127 1 1
#guard checkPower 6 (by decide) 1 128 1 1
#guard checkPower 6 (by decide) 1 129 1 1
#guard checkPower 6 (by decide) 1 255 1 1
#guard checkPower 6 (by decide) 1 256 1 1
#guard checkPower 6 (by decide) 1 257 1 1
#guard checkPower 6 (by decide) 1 (2 ^ 32 - 1) 1 1
#guard checkPower 6 (by decide) 1 (2 ^ 32) 1 1
#guard checkPower 6 (by decide) 1 (2 ^ 32 + 1) 1 1
#guard checkPower 6 (by decide) 1 (2 ^ 64 - 1) 1 1
#guard checkPower 6 (by decide) 1 (2 ^ 64) 1 1
#guard checkPower 6 (by decide) 1 (2 ^ 64 + 1) 1 1
#guard checkPower 6 (by decide) 1 (2 ^ 255 - 1) 1 1
#guard checkPower 6 (by decide) 1 (2 ^ 255) 1 1
#guard checkPower 6 (by decide) 1 (2 ^ 255 + 1) 1 1
#guard checkPower 6 (by decide) 1 (2 ^ 256 + 1) 1 1
#guard checkPower 6 (by decide) 5 0 5 1
#guard checkPower 6 (by decide) 5 1 5 5
#guard checkPower 6 (by decide) 5 2 5 1
#guard checkPower 6 (by decide) 5 3 5 5
#guard checkPower 6 (by decide) 5 4 5 1
#guard checkPower 6 (by decide) 5 7 5 5
#guard checkPower 6 (by decide) 5 8 5 1
#guard checkPower 6 (by decide) 5 9 5 5
#guard checkPower 6 (by decide) 5 31 5 5
#guard checkPower 6 (by decide) 5 32 5 1
#guard checkPower 6 (by decide) 5 33 5 5
#guard checkPower 6 (by decide) 5 63 5 5
#guard checkPower 6 (by decide) 5 64 5 1
#guard checkPower 6 (by decide) 5 65 5 5
#guard checkPower 6 (by decide) 5 127 5 5
#guard checkPower 6 (by decide) 5 128 5 1
#guard checkPower 6 (by decide) 5 129 5 5
#guard checkPower 6 (by decide) 5 255 5 5
#guard checkPower 6 (by decide) 5 256 5 1
#guard checkPower 6 (by decide) 5 257 5 5
#guard checkPower 6 (by decide) 5 (2 ^ 32 - 1) 5 5
#guard checkPower 6 (by decide) 5 (2 ^ 32) 5 1
#guard checkPower 6 (by decide) 5 (2 ^ 32 + 1) 5 5
#guard checkPower 6 (by decide) 5 (2 ^ 64 - 1) 5 5
#guard checkPower 6 (by decide) 5 (2 ^ 64) 5 1
#guard checkPower 6 (by decide) 5 (2 ^ 64 + 1) 5 5
#guard checkPower 6 (by decide) 5 (2 ^ 255 - 1) 5 5
#guard checkPower 6 (by decide) 5 (2 ^ 255) 5 1
#guard checkPower 6 (by decide) 5 (2 ^ 255 + 1) 5 5
#guard checkPower 6 (by decide) 5 (2 ^ 256 + 1) 5 5
#guard checkPower 6 (by decide) 6 0 0 1
#guard checkPower 6 (by decide) 6 1 0 0
#guard checkPower 6 (by decide) 6 2 0 0
#guard checkPower 6 (by decide) 6 3 0 0
#guard checkPower 6 (by decide) 6 4 0 0
#guard checkPower 6 (by decide) 6 7 0 0
#guard checkPower 6 (by decide) 6 8 0 0
#guard checkPower 6 (by decide) 6 9 0 0
#guard checkPower 6 (by decide) 6 31 0 0
#guard checkPower 6 (by decide) 6 32 0 0
#guard checkPower 6 (by decide) 6 33 0 0
#guard checkPower 6 (by decide) 6 63 0 0
#guard checkPower 6 (by decide) 6 64 0 0
#guard checkPower 6 (by decide) 6 65 0 0
#guard checkPower 6 (by decide) 6 127 0 0
#guard checkPower 6 (by decide) 6 128 0 0
#guard checkPower 6 (by decide) 6 129 0 0
#guard checkPower 6 (by decide) 6 255 0 0
#guard checkPower 6 (by decide) 6 256 0 0
#guard checkPower 6 (by decide) 6 257 0 0
#guard checkPower 6 (by decide) 6 (2 ^ 32 - 1) 0 0
#guard checkPower 6 (by decide) 6 (2 ^ 32) 0 0
#guard checkPower 6 (by decide) 6 (2 ^ 32 + 1) 0 0
#guard checkPower 6 (by decide) 6 (2 ^ 64 - 1) 0 0
#guard checkPower 6 (by decide) 6 (2 ^ 64) 0 0
#guard checkPower 6 (by decide) 6 (2 ^ 64 + 1) 0 0
#guard checkPower 6 (by decide) 6 (2 ^ 255 - 1) 0 0
#guard checkPower 6 (by decide) 6 (2 ^ 255) 0 0
#guard checkPower 6 (by decide) 6 (2 ^ 255 + 1) 0 0
#guard checkPower 6 (by decide) 6 (2 ^ 256 + 1) 0 0
#guard checkPower 6 (by decide) 7 0 1 1
#guard checkPower 6 (by decide) 7 1 1 1
#guard checkPower 6 (by decide) 7 2 1 1
#guard checkPower 6 (by decide) 7 3 1 1
#guard checkPower 6 (by decide) 7 4 1 1
#guard checkPower 6 (by decide) 7 7 1 1
#guard checkPower 6 (by decide) 7 8 1 1
#guard checkPower 6 (by decide) 7 9 1 1
#guard checkPower 6 (by decide) 7 31 1 1
#guard checkPower 6 (by decide) 7 32 1 1
#guard checkPower 6 (by decide) 7 33 1 1
#guard checkPower 6 (by decide) 7 63 1 1
#guard checkPower 6 (by decide) 7 64 1 1
#guard checkPower 6 (by decide) 7 65 1 1
#guard checkPower 6 (by decide) 7 127 1 1
#guard checkPower 6 (by decide) 7 128 1 1
#guard checkPower 6 (by decide) 7 129 1 1
#guard checkPower 6 (by decide) 7 255 1 1
#guard checkPower 6 (by decide) 7 256 1 1
#guard checkPower 6 (by decide) 7 257 1 1
#guard checkPower 6 (by decide) 7 (2 ^ 32 - 1) 1 1
#guard checkPower 6 (by decide) 7 (2 ^ 32) 1 1
#guard checkPower 6 (by decide) 7 (2 ^ 32 + 1) 1 1
#guard checkPower 6 (by decide) 7 (2 ^ 64 - 1) 1 1
#guard checkPower 6 (by decide) 7 (2 ^ 64) 1 1
#guard checkPower 6 (by decide) 7 (2 ^ 64 + 1) 1 1
#guard checkPower 6 (by decide) 7 (2 ^ 255 - 1) 1 1
#guard checkPower 6 (by decide) 7 (2 ^ 255) 1 1
#guard checkPower 6 (by decide) 7 (2 ^ 255 + 1) 1 1
#guard checkPower 6 (by decide) 7 (2 ^ 256 + 1) 1 1
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) 0 3 1
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) 1 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) 2 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) 3 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) 4 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) 7 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) 8 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) 9 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) 31 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) 32 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) 33 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) 63 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) 64 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) 65 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) 127 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) 128 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) 129 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) 255 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) 256 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) 257 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) (2 ^ 32 - 1) 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) (2 ^ 32) 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) (2 ^ 32 + 1) 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) (2 ^ 64 - 1) 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) (2 ^ 64) 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) (2 ^ 64 + 1) 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) (2 ^ 255 - 1) 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) (2 ^ 255) 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) (2 ^ 255 + 1) 3 3
#guard checkPower 6 (by decide) (2 ^ 4096 + 17) (2 ^ 256 + 1) 3 3
#guard checkPower 8 (by decide) 0 0 0 1
#guard checkPower 8 (by decide) 0 1 0 0
#guard checkPower 8 (by decide) 0 2 0 0
#guard checkPower 8 (by decide) 0 3 0 0
#guard checkPower 8 (by decide) 0 4 0 0
#guard checkPower 8 (by decide) 0 7 0 0
#guard checkPower 8 (by decide) 0 8 0 0
#guard checkPower 8 (by decide) 0 9 0 0
#guard checkPower 8 (by decide) 0 31 0 0
#guard checkPower 8 (by decide) 0 32 0 0
#guard checkPower 8 (by decide) 0 33 0 0
#guard checkPower 8 (by decide) 0 63 0 0
#guard checkPower 8 (by decide) 0 64 0 0
#guard checkPower 8 (by decide) 0 65 0 0
#guard checkPower 8 (by decide) 0 127 0 0
#guard checkPower 8 (by decide) 0 128 0 0
#guard checkPower 8 (by decide) 0 129 0 0
#guard checkPower 8 (by decide) 0 255 0 0
#guard checkPower 8 (by decide) 0 256 0 0
#guard checkPower 8 (by decide) 0 257 0 0
#guard checkPower 8 (by decide) 0 (2 ^ 32 - 1) 0 0
#guard checkPower 8 (by decide) 0 (2 ^ 32) 0 0
#guard checkPower 8 (by decide) 0 (2 ^ 32 + 1) 0 0
#guard checkPower 8 (by decide) 0 (2 ^ 64 - 1) 0 0
#guard checkPower 8 (by decide) 0 (2 ^ 64) 0 0
#guard checkPower 8 (by decide) 0 (2 ^ 64 + 1) 0 0
#guard checkPower 8 (by decide) 0 (2 ^ 255 - 1) 0 0
#guard checkPower 8 (by decide) 0 (2 ^ 255) 0 0
#guard checkPower 8 (by decide) 0 (2 ^ 255 + 1) 0 0
#guard checkPower 8 (by decide) 0 (2 ^ 256 + 1) 0 0
#guard checkPower 8 (by decide) 1 0 1 1
#guard checkPower 8 (by decide) 1 1 1 1
#guard checkPower 8 (by decide) 1 2 1 1
#guard checkPower 8 (by decide) 1 3 1 1
#guard checkPower 8 (by decide) 1 4 1 1
#guard checkPower 8 (by decide) 1 7 1 1
#guard checkPower 8 (by decide) 1 8 1 1
#guard checkPower 8 (by decide) 1 9 1 1
#guard checkPower 8 (by decide) 1 31 1 1
#guard checkPower 8 (by decide) 1 32 1 1
#guard checkPower 8 (by decide) 1 33 1 1
#guard checkPower 8 (by decide) 1 63 1 1
#guard checkPower 8 (by decide) 1 64 1 1
#guard checkPower 8 (by decide) 1 65 1 1
#guard checkPower 8 (by decide) 1 127 1 1
#guard checkPower 8 (by decide) 1 128 1 1
#guard checkPower 8 (by decide) 1 129 1 1
#guard checkPower 8 (by decide) 1 255 1 1
#guard checkPower 8 (by decide) 1 256 1 1
#guard checkPower 8 (by decide) 1 257 1 1
#guard checkPower 8 (by decide) 1 (2 ^ 32 - 1) 1 1
#guard checkPower 8 (by decide) 1 (2 ^ 32) 1 1
#guard checkPower 8 (by decide) 1 (2 ^ 32 + 1) 1 1
#guard checkPower 8 (by decide) 1 (2 ^ 64 - 1) 1 1
#guard checkPower 8 (by decide) 1 (2 ^ 64) 1 1
#guard checkPower 8 (by decide) 1 (2 ^ 64 + 1) 1 1
#guard checkPower 8 (by decide) 1 (2 ^ 255 - 1) 1 1
#guard checkPower 8 (by decide) 1 (2 ^ 255) 1 1
#guard checkPower 8 (by decide) 1 (2 ^ 255 + 1) 1 1
#guard checkPower 8 (by decide) 1 (2 ^ 256 + 1) 1 1
#guard checkPower 8 (by decide) 7 0 7 1
#guard checkPower 8 (by decide) 7 1 7 7
#guard checkPower 8 (by decide) 7 2 7 1
#guard checkPower 8 (by decide) 7 3 7 7
#guard checkPower 8 (by decide) 7 4 7 1
#guard checkPower 8 (by decide) 7 7 7 7
#guard checkPower 8 (by decide) 7 8 7 1
#guard checkPower 8 (by decide) 7 9 7 7
#guard checkPower 8 (by decide) 7 31 7 7
#guard checkPower 8 (by decide) 7 32 7 1
#guard checkPower 8 (by decide) 7 33 7 7
#guard checkPower 8 (by decide) 7 63 7 7
#guard checkPower 8 (by decide) 7 64 7 1
#guard checkPower 8 (by decide) 7 65 7 7
#guard checkPower 8 (by decide) 7 127 7 7
#guard checkPower 8 (by decide) 7 128 7 1
#guard checkPower 8 (by decide) 7 129 7 7
#guard checkPower 8 (by decide) 7 255 7 7
#guard checkPower 8 (by decide) 7 256 7 1
#guard checkPower 8 (by decide) 7 257 7 7
#guard checkPower 8 (by decide) 7 (2 ^ 32 - 1) 7 7
#guard checkPower 8 (by decide) 7 (2 ^ 32) 7 1
#guard checkPower 8 (by decide) 7 (2 ^ 32 + 1) 7 7
#guard checkPower 8 (by decide) 7 (2 ^ 64 - 1) 7 7
#guard checkPower 8 (by decide) 7 (2 ^ 64) 7 1
#guard checkPower 8 (by decide) 7 (2 ^ 64 + 1) 7 7
#guard checkPower 8 (by decide) 7 (2 ^ 255 - 1) 7 7
#guard checkPower 8 (by decide) 7 (2 ^ 255) 7 1
#guard checkPower 8 (by decide) 7 (2 ^ 255 + 1) 7 7
#guard checkPower 8 (by decide) 7 (2 ^ 256 + 1) 7 7
#guard checkPower 8 (by decide) 8 0 0 1
#guard checkPower 8 (by decide) 8 1 0 0
#guard checkPower 8 (by decide) 8 2 0 0
#guard checkPower 8 (by decide) 8 3 0 0
#guard checkPower 8 (by decide) 8 4 0 0
#guard checkPower 8 (by decide) 8 7 0 0
#guard checkPower 8 (by decide) 8 8 0 0
#guard checkPower 8 (by decide) 8 9 0 0
#guard checkPower 8 (by decide) 8 31 0 0
#guard checkPower 8 (by decide) 8 32 0 0
#guard checkPower 8 (by decide) 8 33 0 0
#guard checkPower 8 (by decide) 8 63 0 0
#guard checkPower 8 (by decide) 8 64 0 0
#guard checkPower 8 (by decide) 8 65 0 0
#guard checkPower 8 (by decide) 8 127 0 0
#guard checkPower 8 (by decide) 8 128 0 0
#guard checkPower 8 (by decide) 8 129 0 0
#guard checkPower 8 (by decide) 8 255 0 0
#guard checkPower 8 (by decide) 8 256 0 0
#guard checkPower 8 (by decide) 8 257 0 0
#guard checkPower 8 (by decide) 8 (2 ^ 32 - 1) 0 0
#guard checkPower 8 (by decide) 8 (2 ^ 32) 0 0
#guard checkPower 8 (by decide) 8 (2 ^ 32 + 1) 0 0
#guard checkPower 8 (by decide) 8 (2 ^ 64 - 1) 0 0
#guard checkPower 8 (by decide) 8 (2 ^ 64) 0 0
#guard checkPower 8 (by decide) 8 (2 ^ 64 + 1) 0 0
#guard checkPower 8 (by decide) 8 (2 ^ 255 - 1) 0 0
#guard checkPower 8 (by decide) 8 (2 ^ 255) 0 0
#guard checkPower 8 (by decide) 8 (2 ^ 255 + 1) 0 0
#guard checkPower 8 (by decide) 8 (2 ^ 256 + 1) 0 0
#guard checkPower 8 (by decide) 9 0 1 1
#guard checkPower 8 (by decide) 9 1 1 1
#guard checkPower 8 (by decide) 9 2 1 1
#guard checkPower 8 (by decide) 9 3 1 1
#guard checkPower 8 (by decide) 9 4 1 1
#guard checkPower 8 (by decide) 9 7 1 1
#guard checkPower 8 (by decide) 9 8 1 1
#guard checkPower 8 (by decide) 9 9 1 1
#guard checkPower 8 (by decide) 9 31 1 1
#guard checkPower 8 (by decide) 9 32 1 1
#guard checkPower 8 (by decide) 9 33 1 1
#guard checkPower 8 (by decide) 9 63 1 1
#guard checkPower 8 (by decide) 9 64 1 1
#guard checkPower 8 (by decide) 9 65 1 1
#guard checkPower 8 (by decide) 9 127 1 1
#guard checkPower 8 (by decide) 9 128 1 1
#guard checkPower 8 (by decide) 9 129 1 1
#guard checkPower 8 (by decide) 9 255 1 1
#guard checkPower 8 (by decide) 9 256 1 1
#guard checkPower 8 (by decide) 9 257 1 1
#guard checkPower 8 (by decide) 9 (2 ^ 32 - 1) 1 1
#guard checkPower 8 (by decide) 9 (2 ^ 32) 1 1
#guard checkPower 8 (by decide) 9 (2 ^ 32 + 1) 1 1
#guard checkPower 8 (by decide) 9 (2 ^ 64 - 1) 1 1
#guard checkPower 8 (by decide) 9 (2 ^ 64) 1 1
#guard checkPower 8 (by decide) 9 (2 ^ 64 + 1) 1 1
#guard checkPower 8 (by decide) 9 (2 ^ 255 - 1) 1 1
#guard checkPower 8 (by decide) 9 (2 ^ 255) 1 1
#guard checkPower 8 (by decide) 9 (2 ^ 255 + 1) 1 1
#guard checkPower 8 (by decide) 9 (2 ^ 256 + 1) 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) 0 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) 1 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) 2 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) 3 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) 4 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) 7 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) 8 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) 9 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) 31 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) 32 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) 33 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) 63 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) 64 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) 65 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) 127 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) 128 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) 129 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) 255 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) 256 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) 257 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) (2 ^ 32 - 1) 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) (2 ^ 32) 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) (2 ^ 32 + 1) 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) (2 ^ 64 - 1) 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) (2 ^ 64) 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) (2 ^ 64 + 1) 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) (2 ^ 255 - 1) 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) (2 ^ 255) 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) (2 ^ 255 + 1) 1 1
#guard checkPower 8 (by decide) (2 ^ 4096 + 17) (2 ^ 256 + 1) 1 1
#guard checkPower 9 (by decide) 0 0 0 1
#guard checkPower 9 (by decide) 0 1 0 0
#guard checkPower 9 (by decide) 0 2 0 0
#guard checkPower 9 (by decide) 0 3 0 0
#guard checkPower 9 (by decide) 0 4 0 0
#guard checkPower 9 (by decide) 0 7 0 0
#guard checkPower 9 (by decide) 0 8 0 0
#guard checkPower 9 (by decide) 0 9 0 0
#guard checkPower 9 (by decide) 0 31 0 0
#guard checkPower 9 (by decide) 0 32 0 0
#guard checkPower 9 (by decide) 0 33 0 0
#guard checkPower 9 (by decide) 0 63 0 0
#guard checkPower 9 (by decide) 0 64 0 0
#guard checkPower 9 (by decide) 0 65 0 0
#guard checkPower 9 (by decide) 0 127 0 0
#guard checkPower 9 (by decide) 0 128 0 0
#guard checkPower 9 (by decide) 0 129 0 0
#guard checkPower 9 (by decide) 0 255 0 0
#guard checkPower 9 (by decide) 0 256 0 0
#guard checkPower 9 (by decide) 0 257 0 0
#guard checkPower 9 (by decide) 0 (2 ^ 32 - 1) 0 0
#guard checkPower 9 (by decide) 0 (2 ^ 32) 0 0
#guard checkPower 9 (by decide) 0 (2 ^ 32 + 1) 0 0
#guard checkPower 9 (by decide) 0 (2 ^ 64 - 1) 0 0
#guard checkPower 9 (by decide) 0 (2 ^ 64) 0 0
#guard checkPower 9 (by decide) 0 (2 ^ 64 + 1) 0 0
#guard checkPower 9 (by decide) 0 (2 ^ 255 - 1) 0 0
#guard checkPower 9 (by decide) 0 (2 ^ 255) 0 0
#guard checkPower 9 (by decide) 0 (2 ^ 255 + 1) 0 0
#guard checkPower 9 (by decide) 0 (2 ^ 256 + 1) 0 0
#guard checkPower 9 (by decide) 1 0 1 1
#guard checkPower 9 (by decide) 1 1 1 1
#guard checkPower 9 (by decide) 1 2 1 1
#guard checkPower 9 (by decide) 1 3 1 1
#guard checkPower 9 (by decide) 1 4 1 1
#guard checkPower 9 (by decide) 1 7 1 1
#guard checkPower 9 (by decide) 1 8 1 1
#guard checkPower 9 (by decide) 1 9 1 1
#guard checkPower 9 (by decide) 1 31 1 1
#guard checkPower 9 (by decide) 1 32 1 1
#guard checkPower 9 (by decide) 1 33 1 1
#guard checkPower 9 (by decide) 1 63 1 1
#guard checkPower 9 (by decide) 1 64 1 1
#guard checkPower 9 (by decide) 1 65 1 1
#guard checkPower 9 (by decide) 1 127 1 1
#guard checkPower 9 (by decide) 1 128 1 1
#guard checkPower 9 (by decide) 1 129 1 1
#guard checkPower 9 (by decide) 1 255 1 1
#guard checkPower 9 (by decide) 1 256 1 1
#guard checkPower 9 (by decide) 1 257 1 1
#guard checkPower 9 (by decide) 1 (2 ^ 32 - 1) 1 1
#guard checkPower 9 (by decide) 1 (2 ^ 32) 1 1
#guard checkPower 9 (by decide) 1 (2 ^ 32 + 1) 1 1
#guard checkPower 9 (by decide) 1 (2 ^ 64 - 1) 1 1
#guard checkPower 9 (by decide) 1 (2 ^ 64) 1 1
#guard checkPower 9 (by decide) 1 (2 ^ 64 + 1) 1 1
#guard checkPower 9 (by decide) 1 (2 ^ 255 - 1) 1 1
#guard checkPower 9 (by decide) 1 (2 ^ 255) 1 1
#guard checkPower 9 (by decide) 1 (2 ^ 255 + 1) 1 1
#guard checkPower 9 (by decide) 1 (2 ^ 256 + 1) 1 1
#guard checkPower 9 (by decide) 8 0 8 1
#guard checkPower 9 (by decide) 8 1 8 8
#guard checkPower 9 (by decide) 8 2 8 1
#guard checkPower 9 (by decide) 8 3 8 8
#guard checkPower 9 (by decide) 8 4 8 1
#guard checkPower 9 (by decide) 8 7 8 8
#guard checkPower 9 (by decide) 8 8 8 1
#guard checkPower 9 (by decide) 8 9 8 8
#guard checkPower 9 (by decide) 8 31 8 8
#guard checkPower 9 (by decide) 8 32 8 1
#guard checkPower 9 (by decide) 8 33 8 8
#guard checkPower 9 (by decide) 8 63 8 8
#guard checkPower 9 (by decide) 8 64 8 1
#guard checkPower 9 (by decide) 8 65 8 8
#guard checkPower 9 (by decide) 8 127 8 8
#guard checkPower 9 (by decide) 8 128 8 1
#guard checkPower 9 (by decide) 8 129 8 8
#guard checkPower 9 (by decide) 8 255 8 8
#guard checkPower 9 (by decide) 8 256 8 1
#guard checkPower 9 (by decide) 8 257 8 8
#guard checkPower 9 (by decide) 8 (2 ^ 32 - 1) 8 8
#guard checkPower 9 (by decide) 8 (2 ^ 32) 8 1
#guard checkPower 9 (by decide) 8 (2 ^ 32 + 1) 8 8
#guard checkPower 9 (by decide) 8 (2 ^ 64 - 1) 8 8
#guard checkPower 9 (by decide) 8 (2 ^ 64) 8 1
#guard checkPower 9 (by decide) 8 (2 ^ 64 + 1) 8 8
#guard checkPower 9 (by decide) 8 (2 ^ 255 - 1) 8 8
#guard checkPower 9 (by decide) 8 (2 ^ 255) 8 1
#guard checkPower 9 (by decide) 8 (2 ^ 255 + 1) 8 8
#guard checkPower 9 (by decide) 8 (2 ^ 256 + 1) 8 8
#guard checkPower 9 (by decide) 9 0 0 1
#guard checkPower 9 (by decide) 9 1 0 0
#guard checkPower 9 (by decide) 9 2 0 0
#guard checkPower 9 (by decide) 9 3 0 0
#guard checkPower 9 (by decide) 9 4 0 0
#guard checkPower 9 (by decide) 9 7 0 0
#guard checkPower 9 (by decide) 9 8 0 0
#guard checkPower 9 (by decide) 9 9 0 0
#guard checkPower 9 (by decide) 9 31 0 0
#guard checkPower 9 (by decide) 9 32 0 0
#guard checkPower 9 (by decide) 9 33 0 0
#guard checkPower 9 (by decide) 9 63 0 0
#guard checkPower 9 (by decide) 9 64 0 0
#guard checkPower 9 (by decide) 9 65 0 0
#guard checkPower 9 (by decide) 9 127 0 0
#guard checkPower 9 (by decide) 9 128 0 0
#guard checkPower 9 (by decide) 9 129 0 0
#guard checkPower 9 (by decide) 9 255 0 0
#guard checkPower 9 (by decide) 9 256 0 0
#guard checkPower 9 (by decide) 9 257 0 0
#guard checkPower 9 (by decide) 9 (2 ^ 32 - 1) 0 0
#guard checkPower 9 (by decide) 9 (2 ^ 32) 0 0
#guard checkPower 9 (by decide) 9 (2 ^ 32 + 1) 0 0
#guard checkPower 9 (by decide) 9 (2 ^ 64 - 1) 0 0
#guard checkPower 9 (by decide) 9 (2 ^ 64) 0 0
#guard checkPower 9 (by decide) 9 (2 ^ 64 + 1) 0 0
#guard checkPower 9 (by decide) 9 (2 ^ 255 - 1) 0 0
#guard checkPower 9 (by decide) 9 (2 ^ 255) 0 0
#guard checkPower 9 (by decide) 9 (2 ^ 255 + 1) 0 0
#guard checkPower 9 (by decide) 9 (2 ^ 256 + 1) 0 0
#guard checkPower 9 (by decide) 10 0 1 1
#guard checkPower 9 (by decide) 10 1 1 1
#guard checkPower 9 (by decide) 10 2 1 1
#guard checkPower 9 (by decide) 10 3 1 1
#guard checkPower 9 (by decide) 10 4 1 1
#guard checkPower 9 (by decide) 10 7 1 1
#guard checkPower 9 (by decide) 10 8 1 1
#guard checkPower 9 (by decide) 10 9 1 1
#guard checkPower 9 (by decide) 10 31 1 1
#guard checkPower 9 (by decide) 10 32 1 1
#guard checkPower 9 (by decide) 10 33 1 1
#guard checkPower 9 (by decide) 10 63 1 1
#guard checkPower 9 (by decide) 10 64 1 1
#guard checkPower 9 (by decide) 10 65 1 1
#guard checkPower 9 (by decide) 10 127 1 1
#guard checkPower 9 (by decide) 10 128 1 1
#guard checkPower 9 (by decide) 10 129 1 1
#guard checkPower 9 (by decide) 10 255 1 1
#guard checkPower 9 (by decide) 10 256 1 1
#guard checkPower 9 (by decide) 10 257 1 1
#guard checkPower 9 (by decide) 10 (2 ^ 32 - 1) 1 1
#guard checkPower 9 (by decide) 10 (2 ^ 32) 1 1
#guard checkPower 9 (by decide) 10 (2 ^ 32 + 1) 1 1
#guard checkPower 9 (by decide) 10 (2 ^ 64 - 1) 1 1
#guard checkPower 9 (by decide) 10 (2 ^ 64) 1 1
#guard checkPower 9 (by decide) 10 (2 ^ 64 + 1) 1 1
#guard checkPower 9 (by decide) 10 (2 ^ 255 - 1) 1 1
#guard checkPower 9 (by decide) 10 (2 ^ 255) 1 1
#guard checkPower 9 (by decide) 10 (2 ^ 255 + 1) 1 1
#guard checkPower 9 (by decide) 10 (2 ^ 256 + 1) 1 1
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) 0 6 1
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) 1 6 6
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) 2 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) 3 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) 4 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) 7 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) 8 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) 9 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) 31 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) 32 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) 33 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) 63 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) 64 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) 65 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) 127 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) 128 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) 129 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) 255 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) 256 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) 257 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) (2 ^ 32 - 1) 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) (2 ^ 32) 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) (2 ^ 32 + 1) 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) (2 ^ 64 - 1) 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) (2 ^ 64) 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) (2 ^ 64 + 1) 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) (2 ^ 255 - 1) 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) (2 ^ 255) 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) (2 ^ 255 + 1) 6 0
#guard checkPower 9 (by decide) (2 ^ 4096 + 17) (2 ^ 256 + 1) 6 0
#guard checkPower 15 (by decide) 0 0 0 1
#guard checkPower 15 (by decide) 0 1 0 0
#guard checkPower 15 (by decide) 0 2 0 0
#guard checkPower 15 (by decide) 0 3 0 0
#guard checkPower 15 (by decide) 0 4 0 0
#guard checkPower 15 (by decide) 0 7 0 0
#guard checkPower 15 (by decide) 0 8 0 0
#guard checkPower 15 (by decide) 0 9 0 0
#guard checkPower 15 (by decide) 0 31 0 0
#guard checkPower 15 (by decide) 0 32 0 0
#guard checkPower 15 (by decide) 0 33 0 0
#guard checkPower 15 (by decide) 0 63 0 0
#guard checkPower 15 (by decide) 0 64 0 0
#guard checkPower 15 (by decide) 0 65 0 0
#guard checkPower 15 (by decide) 0 127 0 0
#guard checkPower 15 (by decide) 0 128 0 0
#guard checkPower 15 (by decide) 0 129 0 0
#guard checkPower 15 (by decide) 0 255 0 0
#guard checkPower 15 (by decide) 0 256 0 0
#guard checkPower 15 (by decide) 0 257 0 0
#guard checkPower 15 (by decide) 0 (2 ^ 32 - 1) 0 0
#guard checkPower 15 (by decide) 0 (2 ^ 32) 0 0
#guard checkPower 15 (by decide) 0 (2 ^ 32 + 1) 0 0
#guard checkPower 15 (by decide) 0 (2 ^ 64 - 1) 0 0
#guard checkPower 15 (by decide) 0 (2 ^ 64) 0 0
#guard checkPower 15 (by decide) 0 (2 ^ 64 + 1) 0 0
#guard checkPower 15 (by decide) 0 (2 ^ 255 - 1) 0 0
#guard checkPower 15 (by decide) 0 (2 ^ 255) 0 0
#guard checkPower 15 (by decide) 0 (2 ^ 255 + 1) 0 0
#guard checkPower 15 (by decide) 0 (2 ^ 256 + 1) 0 0
#guard checkPower 15 (by decide) 1 0 1 1
#guard checkPower 15 (by decide) 1 1 1 1
#guard checkPower 15 (by decide) 1 2 1 1
#guard checkPower 15 (by decide) 1 3 1 1
#guard checkPower 15 (by decide) 1 4 1 1
#guard checkPower 15 (by decide) 1 7 1 1
#guard checkPower 15 (by decide) 1 8 1 1
#guard checkPower 15 (by decide) 1 9 1 1
#guard checkPower 15 (by decide) 1 31 1 1
#guard checkPower 15 (by decide) 1 32 1 1
#guard checkPower 15 (by decide) 1 33 1 1
#guard checkPower 15 (by decide) 1 63 1 1
#guard checkPower 15 (by decide) 1 64 1 1
#guard checkPower 15 (by decide) 1 65 1 1
#guard checkPower 15 (by decide) 1 127 1 1
#guard checkPower 15 (by decide) 1 128 1 1
#guard checkPower 15 (by decide) 1 129 1 1
#guard checkPower 15 (by decide) 1 255 1 1
#guard checkPower 15 (by decide) 1 256 1 1
#guard checkPower 15 (by decide) 1 257 1 1
#guard checkPower 15 (by decide) 1 (2 ^ 32 - 1) 1 1
#guard checkPower 15 (by decide) 1 (2 ^ 32) 1 1
#guard checkPower 15 (by decide) 1 (2 ^ 32 + 1) 1 1
#guard checkPower 15 (by decide) 1 (2 ^ 64 - 1) 1 1
#guard checkPower 15 (by decide) 1 (2 ^ 64) 1 1
#guard checkPower 15 (by decide) 1 (2 ^ 64 + 1) 1 1
#guard checkPower 15 (by decide) 1 (2 ^ 255 - 1) 1 1
#guard checkPower 15 (by decide) 1 (2 ^ 255) 1 1
#guard checkPower 15 (by decide) 1 (2 ^ 255 + 1) 1 1
#guard checkPower 15 (by decide) 1 (2 ^ 256 + 1) 1 1
#guard checkPower 15 (by decide) 14 0 14 1
#guard checkPower 15 (by decide) 14 1 14 14
#guard checkPower 15 (by decide) 14 2 14 1
#guard checkPower 15 (by decide) 14 3 14 14
#guard checkPower 15 (by decide) 14 4 14 1
#guard checkPower 15 (by decide) 14 7 14 14
#guard checkPower 15 (by decide) 14 8 14 1
#guard checkPower 15 (by decide) 14 9 14 14
#guard checkPower 15 (by decide) 14 31 14 14
#guard checkPower 15 (by decide) 14 32 14 1
#guard checkPower 15 (by decide) 14 33 14 14
#guard checkPower 15 (by decide) 14 63 14 14
#guard checkPower 15 (by decide) 14 64 14 1
#guard checkPower 15 (by decide) 14 65 14 14
#guard checkPower 15 (by decide) 14 127 14 14
#guard checkPower 15 (by decide) 14 128 14 1
#guard checkPower 15 (by decide) 14 129 14 14
#guard checkPower 15 (by decide) 14 255 14 14
#guard checkPower 15 (by decide) 14 256 14 1
#guard checkPower 15 (by decide) 14 257 14 14
#guard checkPower 15 (by decide) 14 (2 ^ 32 - 1) 14 14
#guard checkPower 15 (by decide) 14 (2 ^ 32) 14 1
#guard checkPower 15 (by decide) 14 (2 ^ 32 + 1) 14 14
#guard checkPower 15 (by decide) 14 (2 ^ 64 - 1) 14 14
#guard checkPower 15 (by decide) 14 (2 ^ 64) 14 1
#guard checkPower 15 (by decide) 14 (2 ^ 64 + 1) 14 14
#guard checkPower 15 (by decide) 14 (2 ^ 255 - 1) 14 14
#guard checkPower 15 (by decide) 14 (2 ^ 255) 14 1
#guard checkPower 15 (by decide) 14 (2 ^ 255 + 1) 14 14
#guard checkPower 15 (by decide) 14 (2 ^ 256 + 1) 14 14
#guard checkPower 15 (by decide) 15 0 0 1
#guard checkPower 15 (by decide) 15 1 0 0
#guard checkPower 15 (by decide) 15 2 0 0
#guard checkPower 15 (by decide) 15 3 0 0
#guard checkPower 15 (by decide) 15 4 0 0
#guard checkPower 15 (by decide) 15 7 0 0
#guard checkPower 15 (by decide) 15 8 0 0
#guard checkPower 15 (by decide) 15 9 0 0
#guard checkPower 15 (by decide) 15 31 0 0
#guard checkPower 15 (by decide) 15 32 0 0
#guard checkPower 15 (by decide) 15 33 0 0
#guard checkPower 15 (by decide) 15 63 0 0
#guard checkPower 15 (by decide) 15 64 0 0
#guard checkPower 15 (by decide) 15 65 0 0
#guard checkPower 15 (by decide) 15 127 0 0
#guard checkPower 15 (by decide) 15 128 0 0
#guard checkPower 15 (by decide) 15 129 0 0
#guard checkPower 15 (by decide) 15 255 0 0
#guard checkPower 15 (by decide) 15 256 0 0
#guard checkPower 15 (by decide) 15 257 0 0
#guard checkPower 15 (by decide) 15 (2 ^ 32 - 1) 0 0
#guard checkPower 15 (by decide) 15 (2 ^ 32) 0 0
#guard checkPower 15 (by decide) 15 (2 ^ 32 + 1) 0 0
#guard checkPower 15 (by decide) 15 (2 ^ 64 - 1) 0 0
#guard checkPower 15 (by decide) 15 (2 ^ 64) 0 0
#guard checkPower 15 (by decide) 15 (2 ^ 64 + 1) 0 0
#guard checkPower 15 (by decide) 15 (2 ^ 255 - 1) 0 0
#guard checkPower 15 (by decide) 15 (2 ^ 255) 0 0
#guard checkPower 15 (by decide) 15 (2 ^ 255 + 1) 0 0
#guard checkPower 15 (by decide) 15 (2 ^ 256 + 1) 0 0
#guard checkPower 15 (by decide) 16 0 1 1
#guard checkPower 15 (by decide) 16 1 1 1
#guard checkPower 15 (by decide) 16 2 1 1
#guard checkPower 15 (by decide) 16 3 1 1
#guard checkPower 15 (by decide) 16 4 1 1
#guard checkPower 15 (by decide) 16 7 1 1
#guard checkPower 15 (by decide) 16 8 1 1
#guard checkPower 15 (by decide) 16 9 1 1
#guard checkPower 15 (by decide) 16 31 1 1
#guard checkPower 15 (by decide) 16 32 1 1
#guard checkPower 15 (by decide) 16 33 1 1
#guard checkPower 15 (by decide) 16 63 1 1
#guard checkPower 15 (by decide) 16 64 1 1
#guard checkPower 15 (by decide) 16 65 1 1
#guard checkPower 15 (by decide) 16 127 1 1
#guard checkPower 15 (by decide) 16 128 1 1
#guard checkPower 15 (by decide) 16 129 1 1
#guard checkPower 15 (by decide) 16 255 1 1
#guard checkPower 15 (by decide) 16 256 1 1
#guard checkPower 15 (by decide) 16 257 1 1
#guard checkPower 15 (by decide) 16 (2 ^ 32 - 1) 1 1
#guard checkPower 15 (by decide) 16 (2 ^ 32) 1 1
#guard checkPower 15 (by decide) 16 (2 ^ 32 + 1) 1 1
#guard checkPower 15 (by decide) 16 (2 ^ 64 - 1) 1 1
#guard checkPower 15 (by decide) 16 (2 ^ 64) 1 1
#guard checkPower 15 (by decide) 16 (2 ^ 64 + 1) 1 1
#guard checkPower 15 (by decide) 16 (2 ^ 255 - 1) 1 1
#guard checkPower 15 (by decide) 16 (2 ^ 255) 1 1
#guard checkPower 15 (by decide) 16 (2 ^ 255 + 1) 1 1
#guard checkPower 15 (by decide) 16 (2 ^ 256 + 1) 1 1
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) 0 3 1
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) 1 3 3
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) 2 3 9
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) 3 3 12
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) 4 3 6
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) 7 3 12
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) 8 3 6
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) 9 3 3
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) 31 3 12
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) 32 3 6
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) 33 3 3
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) 63 3 12
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) 64 3 6
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) 65 3 3
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) 127 3 12
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) 128 3 6
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) 129 3 3
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) 255 3 12
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) 256 3 6
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) 257 3 3
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) (2 ^ 32 - 1) 3 12
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) (2 ^ 32) 3 6
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) (2 ^ 32 + 1) 3 3
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) (2 ^ 64 - 1) 3 12
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) (2 ^ 64) 3 6
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) (2 ^ 64 + 1) 3 3
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) (2 ^ 255 - 1) 3 12
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) (2 ^ 255) 3 6
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) (2 ^ 255 + 1) 3 3
#guard checkPower 15 (by decide) (2 ^ 4096 + 17) (2 ^ 256 + 1) 3 3
#guard checkPower 17 (by decide) 0 0 0 1
#guard checkPower 17 (by decide) 0 1 0 0
#guard checkPower 17 (by decide) 0 2 0 0
#guard checkPower 17 (by decide) 0 3 0 0
#guard checkPower 17 (by decide) 0 4 0 0
#guard checkPower 17 (by decide) 0 7 0 0
#guard checkPower 17 (by decide) 0 8 0 0
#guard checkPower 17 (by decide) 0 9 0 0
#guard checkPower 17 (by decide) 0 31 0 0
#guard checkPower 17 (by decide) 0 32 0 0
#guard checkPower 17 (by decide) 0 33 0 0
#guard checkPower 17 (by decide) 0 63 0 0
#guard checkPower 17 (by decide) 0 64 0 0
#guard checkPower 17 (by decide) 0 65 0 0
#guard checkPower 17 (by decide) 0 127 0 0
#guard checkPower 17 (by decide) 0 128 0 0
#guard checkPower 17 (by decide) 0 129 0 0
#guard checkPower 17 (by decide) 0 255 0 0
#guard checkPower 17 (by decide) 0 256 0 0
#guard checkPower 17 (by decide) 0 257 0 0
#guard checkPower 17 (by decide) 0 (2 ^ 32 - 1) 0 0
#guard checkPower 17 (by decide) 0 (2 ^ 32) 0 0
#guard checkPower 17 (by decide) 0 (2 ^ 32 + 1) 0 0
#guard checkPower 17 (by decide) 0 (2 ^ 64 - 1) 0 0
#guard checkPower 17 (by decide) 0 (2 ^ 64) 0 0
#guard checkPower 17 (by decide) 0 (2 ^ 64 + 1) 0 0
#guard checkPower 17 (by decide) 0 (2 ^ 255 - 1) 0 0
#guard checkPower 17 (by decide) 0 (2 ^ 255) 0 0
#guard checkPower 17 (by decide) 0 (2 ^ 255 + 1) 0 0
#guard checkPower 17 (by decide) 0 (2 ^ 256 + 1) 0 0
#guard checkPower 17 (by decide) 1 0 1 1
#guard checkPower 17 (by decide) 1 1 1 1
#guard checkPower 17 (by decide) 1 2 1 1
#guard checkPower 17 (by decide) 1 3 1 1
#guard checkPower 17 (by decide) 1 4 1 1
#guard checkPower 17 (by decide) 1 7 1 1
#guard checkPower 17 (by decide) 1 8 1 1
#guard checkPower 17 (by decide) 1 9 1 1
#guard checkPower 17 (by decide) 1 31 1 1
#guard checkPower 17 (by decide) 1 32 1 1
#guard checkPower 17 (by decide) 1 33 1 1
#guard checkPower 17 (by decide) 1 63 1 1
#guard checkPower 17 (by decide) 1 64 1 1
#guard checkPower 17 (by decide) 1 65 1 1
#guard checkPower 17 (by decide) 1 127 1 1
#guard checkPower 17 (by decide) 1 128 1 1
#guard checkPower 17 (by decide) 1 129 1 1
#guard checkPower 17 (by decide) 1 255 1 1
#guard checkPower 17 (by decide) 1 256 1 1
#guard checkPower 17 (by decide) 1 257 1 1
#guard checkPower 17 (by decide) 1 (2 ^ 32 - 1) 1 1
#guard checkPower 17 (by decide) 1 (2 ^ 32) 1 1
#guard checkPower 17 (by decide) 1 (2 ^ 32 + 1) 1 1
#guard checkPower 17 (by decide) 1 (2 ^ 64 - 1) 1 1
#guard checkPower 17 (by decide) 1 (2 ^ 64) 1 1
#guard checkPower 17 (by decide) 1 (2 ^ 64 + 1) 1 1
#guard checkPower 17 (by decide) 1 (2 ^ 255 - 1) 1 1
#guard checkPower 17 (by decide) 1 (2 ^ 255) 1 1
#guard checkPower 17 (by decide) 1 (2 ^ 255 + 1) 1 1
#guard checkPower 17 (by decide) 1 (2 ^ 256 + 1) 1 1
#guard checkPower 17 (by decide) 16 0 16 1
#guard checkPower 17 (by decide) 16 1 16 16
#guard checkPower 17 (by decide) 16 2 16 1
#guard checkPower 17 (by decide) 16 3 16 16
#guard checkPower 17 (by decide) 16 4 16 1
#guard checkPower 17 (by decide) 16 7 16 16
#guard checkPower 17 (by decide) 16 8 16 1
#guard checkPower 17 (by decide) 16 9 16 16
#guard checkPower 17 (by decide) 16 31 16 16
#guard checkPower 17 (by decide) 16 32 16 1
#guard checkPower 17 (by decide) 16 33 16 16
#guard checkPower 17 (by decide) 16 63 16 16
#guard checkPower 17 (by decide) 16 64 16 1
#guard checkPower 17 (by decide) 16 65 16 16
#guard checkPower 17 (by decide) 16 127 16 16
#guard checkPower 17 (by decide) 16 128 16 1
#guard checkPower 17 (by decide) 16 129 16 16
#guard checkPower 17 (by decide) 16 255 16 16
#guard checkPower 17 (by decide) 16 256 16 1
#guard checkPower 17 (by decide) 16 257 16 16
#guard checkPower 17 (by decide) 16 (2 ^ 32 - 1) 16 16
#guard checkPower 17 (by decide) 16 (2 ^ 32) 16 1
#guard checkPower 17 (by decide) 16 (2 ^ 32 + 1) 16 16
#guard checkPower 17 (by decide) 16 (2 ^ 64 - 1) 16 16
#guard checkPower 17 (by decide) 16 (2 ^ 64) 16 1
#guard checkPower 17 (by decide) 16 (2 ^ 64 + 1) 16 16
#guard checkPower 17 (by decide) 16 (2 ^ 255 - 1) 16 16
#guard checkPower 17 (by decide) 16 (2 ^ 255) 16 1
#guard checkPower 17 (by decide) 16 (2 ^ 255 + 1) 16 16
#guard checkPower 17 (by decide) 16 (2 ^ 256 + 1) 16 16
#guard checkPower 17 (by decide) 17 0 0 1
#guard checkPower 17 (by decide) 17 1 0 0
#guard checkPower 17 (by decide) 17 2 0 0
#guard checkPower 17 (by decide) 17 3 0 0
#guard checkPower 17 (by decide) 17 4 0 0
#guard checkPower 17 (by decide) 17 7 0 0
#guard checkPower 17 (by decide) 17 8 0 0
#guard checkPower 17 (by decide) 17 9 0 0
#guard checkPower 17 (by decide) 17 31 0 0
#guard checkPower 17 (by decide) 17 32 0 0
#guard checkPower 17 (by decide) 17 33 0 0
#guard checkPower 17 (by decide) 17 63 0 0
#guard checkPower 17 (by decide) 17 64 0 0
#guard checkPower 17 (by decide) 17 65 0 0
#guard checkPower 17 (by decide) 17 127 0 0
#guard checkPower 17 (by decide) 17 128 0 0
#guard checkPower 17 (by decide) 17 129 0 0
#guard checkPower 17 (by decide) 17 255 0 0
#guard checkPower 17 (by decide) 17 256 0 0
#guard checkPower 17 (by decide) 17 257 0 0
#guard checkPower 17 (by decide) 17 (2 ^ 32 - 1) 0 0
#guard checkPower 17 (by decide) 17 (2 ^ 32) 0 0
#guard checkPower 17 (by decide) 17 (2 ^ 32 + 1) 0 0
#guard checkPower 17 (by decide) 17 (2 ^ 64 - 1) 0 0
#guard checkPower 17 (by decide) 17 (2 ^ 64) 0 0
#guard checkPower 17 (by decide) 17 (2 ^ 64 + 1) 0 0
#guard checkPower 17 (by decide) 17 (2 ^ 255 - 1) 0 0
#guard checkPower 17 (by decide) 17 (2 ^ 255) 0 0
#guard checkPower 17 (by decide) 17 (2 ^ 255 + 1) 0 0
#guard checkPower 17 (by decide) 17 (2 ^ 256 + 1) 0 0
#guard checkPower 17 (by decide) 18 0 1 1
#guard checkPower 17 (by decide) 18 1 1 1
#guard checkPower 17 (by decide) 18 2 1 1
#guard checkPower 17 (by decide) 18 3 1 1
#guard checkPower 17 (by decide) 18 4 1 1
#guard checkPower 17 (by decide) 18 7 1 1
#guard checkPower 17 (by decide) 18 8 1 1
#guard checkPower 17 (by decide) 18 9 1 1
#guard checkPower 17 (by decide) 18 31 1 1
#guard checkPower 17 (by decide) 18 32 1 1
#guard checkPower 17 (by decide) 18 33 1 1
#guard checkPower 17 (by decide) 18 63 1 1
#guard checkPower 17 (by decide) 18 64 1 1
#guard checkPower 17 (by decide) 18 65 1 1
#guard checkPower 17 (by decide) 18 127 1 1
#guard checkPower 17 (by decide) 18 128 1 1
#guard checkPower 17 (by decide) 18 129 1 1
#guard checkPower 17 (by decide) 18 255 1 1
#guard checkPower 17 (by decide) 18 256 1 1
#guard checkPower 17 (by decide) 18 257 1 1
#guard checkPower 17 (by decide) 18 (2 ^ 32 - 1) 1 1
#guard checkPower 17 (by decide) 18 (2 ^ 32) 1 1
#guard checkPower 17 (by decide) 18 (2 ^ 32 + 1) 1 1
#guard checkPower 17 (by decide) 18 (2 ^ 64 - 1) 1 1
#guard checkPower 17 (by decide) 18 (2 ^ 64) 1 1
#guard checkPower 17 (by decide) 18 (2 ^ 64 + 1) 1 1
#guard checkPower 17 (by decide) 18 (2 ^ 255 - 1) 1 1
#guard checkPower 17 (by decide) 18 (2 ^ 255) 1 1
#guard checkPower 17 (by decide) 18 (2 ^ 255 + 1) 1 1
#guard checkPower 17 (by decide) 18 (2 ^ 256 + 1) 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) 0 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) 1 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) 2 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) 3 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) 4 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) 7 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) 8 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) 9 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) 31 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) 32 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) 33 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) 63 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) 64 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) 65 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) 127 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) 128 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) 129 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) 255 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) 256 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) 257 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) (2 ^ 32 - 1) 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) (2 ^ 32) 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) (2 ^ 32 + 1) 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) (2 ^ 64 - 1) 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) (2 ^ 64) 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) (2 ^ 64 + 1) 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) (2 ^ 255 - 1) 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) (2 ^ 255) 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) (2 ^ 255 + 1) 1 1
#guard checkPower 17 (by decide) (2 ^ 4096 + 17) (2 ^ 256 + 1) 1 1

-- A composite nonunit distinguishes full exponents from reduction modulo p - 1.
#guard checkPower 4 (by decide) 2 4 2 0

end STFSpec.Conformance.Field
