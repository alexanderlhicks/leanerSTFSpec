/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# U256 constructor regression guards

Library `EthConformance`: unsigned and signed endpoints, wrapping versus checked
construction, Boolean words and unsigned comparison. These tests use the public API.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §4.
-/

open STFSpec.Base

#guard U256.zero.toNat = 0
#guard U256.one.toNat = 1
#guard U256.max.toNat = 2 ^ 256 - 1
#guard U256.max.toInt = -1
#guard U256.ofNat? 0 = some U256.zero
#guard U256.ofNat? 1 = some U256.one
#guard (U256.ofNat? (2 ^ 255 - 1)).map U256.toNat = some (2 ^ 255 - 1)
#guard (U256.ofNat? (2 ^ 255)).map U256.toNat = some (2 ^ 255)
#guard (U256.ofNat? (2 ^ 255 + 1)).map U256.toNat = some (2 ^ 255 + 1)
#guard U256.ofNat? (2 ^ 256 - 1) = some U256.max
#guard U256.ofNat? (2 ^ 256) = none
#guard (U256.ofNat (2 ^ 256)).toNat = 0
#guard (U256.ofNat (2 ^ 256 + 1)).toNat = 1
#guard (U256.ofNat (2 ^ 255 - 1)).toInt = (2 : Int) ^ 255 - 1
#guard (U256.ofNat (2 ^ 255)).toInt = -(2 : Int) ^ 255
#guard (U256.ofNat (2 ^ 255 + 1)).toInt = -(2 : Int) ^ 255 + 1
#guard U256.ofInt? (-(2 : Int) ^ 255 - 1) = none
#guard U256.ofInt? (-(2 : Int) ^ 255) = some (U256.ofNat (2 ^ 255))
#guard (U256.ofInt? (-(2 : Int) ^ 255 + 1)).map U256.toInt =
  some (-(2 : Int) ^ 255 + 1)
#guard U256.ofInt? (-1) = some U256.max
#guard U256.ofInt? 0 = some U256.zero
#guard U256.ofInt? 1 = some U256.one
#guard (U256.ofInt? ((2 : Int) ^ 255 - 1)).map U256.toInt = some ((2 : Int) ^ 255 - 1)
#guard U256.ofInt? ((2 : Int) ^ 255) = none
#guard U256.ofBool false = U256.zero
#guard U256.ofBool true = U256.one
#guard compare U256.zero U256.one = .lt
#guard compare U256.max U256.zero = .gt
#guard compare (U256.ofNat (2 ^ 255)) (U256.ofNat (2 ^ 255 - 1)) = .gt
#guard compare (U256.ofNat (2 ^ 256 + 1)) U256.one = .eq
