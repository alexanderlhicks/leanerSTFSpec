/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Complete raw block-gas counter guards

Library `EthConformance`. Ten complete observations distinguish all three fields,
including swapped execution/state, maximum blob usage and unbounded Nat values.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Core.BlockGasGuards
open STFSpec.Vm.Core
open STFSpec.Base

private def observe (c : BlockGasCounters) : Nat × Nat × Nat :=
  (c.blockGasUsed, c.blockStateGasUsed, c.blobGasUsed.toNat)

#guard observe (BlockGasCounters.mk 0 0 U64.zero) == (0, 0, 0)
#guard observe (BlockGasCounters.mk 11 23 (U64.ofNat 37)) == (11, 23, 37)
#guard observe (BlockGasCounters.mk 23 11 (U64.ofNat 37)) == (23, 11, 37)
#guard observe (BlockGasCounters.mk 0 23 (U64.ofNat 37)) == (0, 23, 37)
#guard observe (BlockGasCounters.mk 11 0 (U64.ofNat 37)) == (11, 0, 37)
#guard observe (BlockGasCounters.mk 11 23 U64.zero) == (11, 23, 0)
#guard observe (BlockGasCounters.mk 5 9 U64.max) == (5, 9, 18446744073709551615)
#guard observe (BlockGasCounters.mk (2 ^ 64 + 17) 29 (U64.ofNat 43)) ==
  (18446744073709551633, 29, 43)
#guard observe (BlockGasCounters.mk 31 (2 ^ 256 + 19) (U64.ofNat 47)) ==
  (31, 115792089237316195423570985008687907853269984665640564039457584007913129639955, 47)
#guard observe (BlockGasCounters.mk (2 ^ 256 + 23) (2 ^ 256 + 41) U64.max) ==
  (115792089237316195423570985008687907853269984665640564039457584007913129639959,
   115792089237316195423570985008687907853269984665640564039457584007913129639977,
   18446744073709551615)

end STFSpec.Conformance.Vm.Core.BlockGasGuards
