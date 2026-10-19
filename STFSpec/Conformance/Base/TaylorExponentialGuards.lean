/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.TaylorExponential

/-!
# Full-value Taylor exponential controls

Library `EthConformance`: twenty-eight independently handwritten literal results.
The positive-denominator schedule preserves each intermediate floor, early term
growth and unbounded values; no expected recurrence produces these literals.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §3/§7.
-/

open STFSpec.Base

-- T01
#guard taylorExponential 0 7 3 (by decide) == 0
-- T02
#guard taylorExponential 5 0 3 (by decide) == 5
-- T03
#guard taylorExponential 1 0 1 (by decide) == 1
-- T04
#guard taylorExponential 1 1 1 (by decide) == 2
-- T05
#guard taylorExponential 1 2 1 (by decide) == 6
-- T06
#guard taylorExponential 2 1 2 (by decide) == 3
-- T07
#guard taylorExponential 1 3 2 (by decide) == 4
-- T08
#guard taylorExponential 3 2 3 (by decide) == 5
-- T09
#guard taylorExponential 0 0 1 (by decide) == 0
-- T10
#guard taylorExponential 0 1 11684671 (by decide) == 0
-- T11
#guard taylorExponential 1 1 2 (by decide) == 1
-- T12
#guard taylorExponential 1 2 3 (by decide) == 1
-- T13
#guard taylorExponential 7 1 3 (by decide) == 9
-- T14
#guard taylorExponential 9 4 3 (by decide) == 33
-- T15
#guard taylorExponential 1 3 1 (by decide) == 16
-- T16
#guard taylorExponential 2 5 2 (by decide) == 23
-- T17
#guard taylorExponential 1 8 3 (by decide) == 12
-- T18
#guard taylorExponential 18446744073709551615 0 1 (by decide) == 18446744073709551615
-- T19
#guard taylorExponential
  18446744073709551616
  1
  18446744073709551617
  (by decide) ==
  18446744073709551616
-- T20
#guard taylorExponential
  340282366920938463463374607431768211456
  1
  340282366920938463463374607431768211457
  (by decide) ==
  340282366920938463463374607431768211456
-- T21
#guard taylorExponential
  115792089237316195423570985008687907853269984665640564039457584007913129639935
  1
  115792089237316195423570985008687907853269984665640564039457584007913129639936
  (by decide) ==
  115792089237316195423570985008687907853269984665640564039457584007913129639935
-- T22
#guard taylorExponential 1 0 11684671 (by decide) == 1
-- T23
#guard taylorExponential 1 1 11684671 (by decide) == 1
-- T24
#guard taylorExponential 1 11684670 11684671 (by decide) == 2
-- T25
#guard taylorExponential 1 11684671 11684671 (by decide) == 2
-- T26
#guard taylorExponential 1 11684672 11684671 (by decide) == 2
-- T27
#guard taylorExponential 1 23369342 11684671 (by decide) == 7
-- T28
#guard taylorExponential 7 23369343 11684671 (by decide) == 51
