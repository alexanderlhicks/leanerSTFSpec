/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Conformance.Base.NumericCallerProofs
import STFSpec.Conformance.Base.NumericGuards
import STFSpec.Conformance.Base.U256ArithmeticCallerProofs
import STFSpec.Conformance.Base.U256ArithmeticGuards
import STFSpec.Conformance.Base.U256BitwiseCallerProofs
import STFSpec.Conformance.Base.U256BitwiseGuards
import STFSpec.Conformance.Base.U256CallerProofs
import STFSpec.Conformance.Base.U256Guards
import STFSpec.Conformance.Base.U256SignedCallerProofs
import STFSpec.Conformance.Base.U256SignedGuards

/-!
# STFSpec.Conformance

Conformance: EEST fixture runners and `core` `#guard` suites.

Library `EthConformance`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). Implementation status is owned by the
spec guidance document.
Spec guidance: `STFSpec/informal/modules/EthConformance.md`.
-/
