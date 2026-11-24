/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Precompiles

/-!
# MODEXP pricing controls

Library `EthConformance`. Check the pricing helpers and minimum-charge law
through the Precompiles facade.
See `STFSpec/informal/modules/EthPrecompiles.md` §4.
-/

namespace STFSpec.Conformance.Precompiles.ModexpPricingControls

open STFSpec.Precompiles.Modexp

private theorem minimum (baseLength modulusLength exponentLength exponentHead : Nat) :
    500 ≤ gasCost baseLength modulusLength exponentLength exponentHead :=
  gasCost_ge_500 baseLength modulusLength exponentLength exponentHead

#guard [complexity 31 3, complexity 19 32, complexity 33 29, complexity 29 33] ==
  [16, 16, 50, 50]
#guard [complexity 7 39, complexity 40 7, complexity 41 7, complexity 65 7] ==
  [50, 50, 72, 162]
#guard [complexity 1023 1, complexity 1 1024, complexity 1025 2] ==
  [32768, 32768, 33282]

#guard [iterations 0 0, iterations 31 1, iterations 32 2, iterations 32 4,
  iterations 33 0, iterations 33 1, iterations 33 2] ==
  [1, 1, 1, 2, 16, 16, 17]
#guard [iterations 32 (2^256-1), iterations 33 (2^256-1), iterations 1024 0,
  iterations 1025 (2^256-1)] ==
  [255, 271, 15872, 16143]

#guard [gasCost 32 27 4 (2^31+3), gasCost 32 27 5 (2^32+3)] == [500, 512]
#guard [gasCost 23 33 3 (2^9+1), gasCost 33 23 3 (2^10+1), gasCost 23 33 3 (2^11+1)] ==
  [500, 500, 550]
#guard gasCost (baseLength := 33) (modulusLength := 1)
  (exponentLength := 1) (exponentHead := 2^11+1) == 550
#guard gasCost (baseLength := 1) (modulusLength := 1)
  (exponentLength := 33) (exponentHead := 2^11+1) == 500
#guard gasCost (2^270) 13 (2^271+32) 1 == 2^810
#guard iterations 33 (2^291+21) == 307

end STFSpec.Conformance.Precompiles.ModexpPricingControls
