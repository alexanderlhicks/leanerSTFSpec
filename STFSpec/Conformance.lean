/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Conformance.Base.U256
import STFSpec.Conformance.Base.U256Client

/-!
# STFSpec.Conformance

Conformance: EEST fixture runners and `core` `#guard` suites.

Library `EthConformance`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). The U256 constructor guards and client proof
tests are implemented; guest runners remain absent.
Spec guidance: `STFSpec/informal/modules/EthConformance.md`.
-/
