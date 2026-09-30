/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# Signed U256 division and remainder regression guards

Library `EthConformance`: operand order, truncation versus floor division, dividend-sign
remainder, signed endpoints and the two EVM zero-divisor guards.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §4.
-/

open STFSpec.Base

-- Test inputs are constructed only through the public bit-vector constructor.
private def word (i : Int) : U256 := U256.ofBitVec (BitVec.ofInt 256 i)

#guard (U256.sdiv (word (7)) (word (2))).toInt = 3
#guard (U256.sdiv (word (-7)) (word (2))).toInt = -3
#guard (U256.sdiv (word (7)) (word (-2))).toInt = -3
#guard (U256.sdiv (word (-7)) (word (-2))).toInt = 3
#guard (U256.sdiv (word (2)) (word (7))).toInt = 0
#guard (U256.sdiv (word (-2)) (word (7))).toInt = 0
#guard (U256.sdiv (word (2)) (word (-7))).toInt = 0
#guard (U256.sdiv (word (-2)) (word (-7))).toInt = 0
#guard (U256.sdiv (word (8)) (word (3))).toInt = 2
#guard (U256.sdiv (word (-8)) (word (3))).toInt = -2
#guard (U256.sdiv (word (8)) (word (-3))).toInt = -2
#guard (U256.sdiv (word (-8)) (word (-3))).toInt = 2
#guard (U256.sdiv (word (0)) (word (0))).toInt = 0
#guard (U256.sdiv (word (7)) (word (0))).toInt = 0
#guard (U256.sdiv (word (-7)) (word (0))).toInt = 0
#guard (U256.sdiv (word (0)) (word (7))).toInt = 0
#guard (U256.sdiv (word (0)) (word (-7))).toInt = 0
#guard (U256.smod (word (7)) (word (2))).toInt = 1
#guard (U256.smod (word (-7)) (word (2))).toInt = -1
#guard (U256.smod (word (7)) (word (-2))).toInt = 1
#guard (U256.smod (word (-7)) (word (-2))).toInt = -1
#guard (U256.smod (word (2)) (word (7))).toInt = 2
#guard (U256.smod (word (-2)) (word (7))).toInt = -2
#guard (U256.smod (word (2)) (word (-7))).toInt = 2
#guard (U256.smod (word (-2)) (word (-7))).toInt = -2
#guard (U256.smod (word (8)) (word (3))).toInt = 2
#guard (U256.smod (word (-8)) (word (3))).toInt = -2
#guard (U256.smod (word (8)) (word (-3))).toInt = 2
#guard (U256.smod (word (-8)) (word (-3))).toInt = -2
#guard (U256.smod (word (6)) (word (3))).toInt = 0
#guard (U256.smod (word (-6)) (word (-3))).toInt = 0
#guard (U256.smod (word (0)) (word (0))).toInt = 0
#guard (U256.smod (word (7)) (word (0))).toInt = 0
#guard (U256.smod (word (-7)) (word (0))).toInt = 0
#guard (U256.smod (word (0)) (word (7))).toInt = 0
#guard (U256.smod (word (0)) (word (-7))).toInt = 0
#guard (U256.sdiv (word (-(2 : Int) ^ 255)) (word (-1))).toInt = -(2 : Int) ^ 255
#guard (U256.sdiv (word (-(2 : Int) ^ 255)) (word 1)).toInt = -(2 : Int) ^ 255
#guard (U256.sdiv (word (-(2 : Int) ^ 255)) (word (-(2 : Int) ^ 255))).toInt = 1
#guard (U256.sdiv (word ((2 : Int) ^ 255 - 1)) (word (-1))).toInt = -((2 : Int) ^ 255 - 1)
#guard (U256.sdiv (word (-(2 : Int) ^ 255)) (word 0)).toInt = 0
#guard (U256.sdiv (word ((2 : Int) ^ 255 - 1)) (word 0)).toInt = 0
#guard (U256.sdiv (word (-(2 : Int) ^ 255)) (word 2)).toInt = -(2 : Int) ^ 254
#guard (U256.sdiv (word (-(2 : Int) ^ 255)) (word (-2))).toInt = (2 : Int) ^ 254
#guard (U256.smod (word (-(2 : Int) ^ 255)) (word (-1))).toInt = 0
#guard (U256.smod (word (-(2 : Int) ^ 255)) (word 1)).toInt = 0
#guard (U256.smod (word (-(2 : Int) ^ 255)) (word (-(2 : Int) ^ 255))).toInt = 0
#guard (U256.smod (word ((2 : Int) ^ 255 - 1)) (word (-1))).toInt = 0
#guard (U256.smod (word (-(2 : Int) ^ 255)) (word 0)).toInt = 0
#guard (U256.smod (word ((2 : Int) ^ 255 - 1)) (word 0)).toInt = 0
#guard (U256.smod (word (-(2 : Int) ^ 255)) (word 3)).toInt = -2
#guard (U256.smod (word (-(2 : Int) ^ 255)) (word (-3))).toInt = -2
