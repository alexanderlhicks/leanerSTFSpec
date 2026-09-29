/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# Unsigned U256 arithmetic regression guards

Library `EthConformance`: wrapping versus checked boundaries, unsigned zero divisors,
operand order and modular arithmetic with unreduced intermediates.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §4.
-/

open STFSpec.Base

#guard U256.add U256.max U256.one = U256.zero
#guard U256.add U256.zero U256.max = U256.max
#guard U256.sub U256.zero U256.one = U256.max
#guard (U256.sub (U256.ofNat 7) (U256.ofNat 3)).toNat = 4
#guard (U256.sub (U256.ofNat 3) (U256.ofNat 7)).toNat = 2 ^ 256 - 4
#guard U256.mul U256.max U256.max = U256.one
#guard U256.mul (U256.ofNat (2 ^ 128)) (U256.ofNat (2 ^ 128)) = U256.zero
#guard U256.div U256.max U256.zero = U256.zero
#guard U256.mod U256.max U256.zero = U256.zero
#guard U256.div U256.zero U256.zero = U256.zero
#guard U256.mod U256.zero U256.zero = U256.zero
#guard U256.div U256.max U256.one = U256.max
#guard U256.mod U256.max U256.one = U256.zero
#guard (U256.div (U256.ofNat 7) (U256.ofNat 3)).toNat = 2
#guard (U256.mod (U256.ofNat 7) (U256.ofNat 3)).toNat = 1
#guard (U256.div (U256.ofNat 3) (U256.ofNat 7)).toNat = 0
#guard (U256.mod (U256.ofNat 3) (U256.ofNat 7)).toNat = 3
#guard 12 * (U256.div U256.max (U256.ofNat 12)).toNat +
  (U256.mod U256.max (U256.ofNat 12)).toNat = U256.max.toNat
#guard U256.addmod U256.max U256.one U256.max = U256.one
#guard (U256.mulmod U256.max U256.max (U256.ofNat 12)).toNat = 9
#guard U256.addmod U256.max U256.max U256.zero = U256.zero
#guard U256.mulmod U256.max U256.max U256.zero = U256.zero
#guard U256.addmod U256.max U256.max U256.one = U256.zero
#guard U256.mulmod U256.max U256.max U256.one = U256.zero
#guard U256.checkedAdd U256.max U256.one = none
#guard U256.checkedAdd U256.max U256.zero = some U256.max
#guard U256.checkedAdd (U256.ofNat (2 ^ 256 - 2)) U256.one =
  some (U256.ofNat (2 ^ 256 - 1))
#guard U256.checkedSub U256.zero U256.one = none
#guard U256.checkedSub U256.zero U256.zero = some U256.zero
#guard U256.checkedSub U256.max U256.max = some U256.zero
#guard U256.checkedSub U256.max U256.zero = some U256.max
#guard U256.checkedMul U256.max U256.max = none
#guard U256.checkedMul U256.max U256.one = some U256.max
#guard U256.checkedMul U256.max U256.zero = some U256.zero
#guard U256.checkedMul (U256.ofNat (2 ^ 128)) (U256.ofNat (2 ^ 128)) = none
#guard U256.checkedMul (U256.ofNat (2 ^ 128 - 1)) (U256.ofNat (2 ^ 128 + 1)) =
  some U256.max
#guard U256.checkedDiv U256.max U256.zero = none
#guard U256.checkedMod U256.max U256.zero = none
#guard U256.checkedDiv U256.zero U256.zero = none
#guard U256.checkedMod U256.zero U256.zero = none
#guard U256.checkedDiv U256.zero U256.one = some U256.zero
#guard U256.checkedMod U256.zero U256.one = some U256.zero
#guard U256.checkedDiv U256.max U256.one = some U256.max
#guard U256.checkedMod U256.max U256.one = some U256.zero
