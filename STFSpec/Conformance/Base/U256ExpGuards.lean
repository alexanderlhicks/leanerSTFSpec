/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# Modular U256 exponentiation regression guards

Library `EthConformance`: zero/one/max bases, operand order, parity, reduction and
exponent-width boundaries.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §4.
-/

open STFSpec.Base

#guard U256.exp U256.zero U256.zero = U256.one
#guard U256.exp U256.one U256.zero = U256.one
#guard U256.exp U256.max U256.zero = U256.one
#guard U256.exp (U256.ofNat 3) U256.zero = U256.one
#guard U256.exp U256.zero U256.one = U256.zero
#guard U256.exp U256.zero (U256.ofNat 255) = U256.zero
#guard U256.exp U256.zero (U256.ofNat 256) = U256.zero
#guard U256.exp U256.zero U256.max = U256.zero
#guard U256.exp U256.one U256.one = U256.one
#guard U256.exp U256.one (U256.ofNat 255) = U256.one
#guard U256.exp U256.one (U256.ofNat 256) = U256.one
#guard U256.exp U256.one U256.max = U256.one
#guard U256.exp U256.max U256.one = U256.max
#guard U256.exp U256.max (U256.ofNat 2) = U256.one
#guard U256.exp U256.max (U256.ofNat 3) = U256.max
#guard U256.exp U256.max (U256.ofNat 254) = U256.one
#guard U256.exp U256.max (U256.ofNat 255) = U256.max
#guard U256.exp U256.max (U256.ofNat 256) = U256.one
#guard U256.exp U256.max U256.max = U256.max
#guard (U256.exp (U256.ofNat 2) (U256.ofNat 3)).toNat = 8
#guard (U256.exp (U256.ofNat 3) (U256.ofNat 2)).toNat = 9
#guard (U256.exp (U256.ofNat 2) (U256.ofNat 254)).toNat = 2 ^ 254
#guard (U256.exp (U256.ofNat 2) (U256.ofNat 255)).toNat = 2 ^ 255
#guard U256.exp (U256.ofNat 2) (U256.ofNat 256) = U256.zero
#guard U256.exp (U256.ofNat 2) U256.max = U256.zero
#guard U256.exp (U256.ofNat (2 ^ 128)) (U256.ofNat 2) = U256.zero
#guard (U256.exp (U256.ofNat (2 ^ 128 + 1)) (U256.ofNat 2)).toNat = 2 ^ 129 + 1
#guard (U256.exp (U256.ofNat 3) (U256.ofNat 255)).toNat =
  3 ^ 255 % 2 ^ 256
#guard (U256.exp (U256.ofNat 3) (U256.ofNat 256)).toNat =
  3 ^ 256 % 2 ^ 256
#guard (U256.exp (U256.ofNat 3) U256.max).toNat = (2 * 2 ^ 256 + 1) / 3
#guard U256.exp (U256.ofNat 3) (U256.ofNat (2 ^ 255)) = U256.one
#guard U256.exp (U256.ofNat 3) (U256.ofNat (2 ^ 256 - 2)) =
  U256.mul (U256.exp (U256.ofNat 3) U256.max) (U256.exp (U256.ofNat 3) U256.max)
#guard U256.exp (U256.ofNat (2 ^ 255)) (U256.ofNat 2) = U256.zero
#guard U256.exp (U256.ofNat (2 ^ 255 + 1)) (U256.ofNat 2) = U256.one
#guard U256.exp (U256.ofNat (2 ^ 256 - 2)) (U256.ofNat 256) = U256.zero
#guard U256.exp (U256.ofNat (2 ^ 256 - 2)) U256.max = U256.zero
