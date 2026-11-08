/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless.ExecutionWitness
import STFSpec.Stateless.Output

/-!
# STFSpec.Stateless

The stateless guest: input/witness codecs, header-chain validation, `verifyStatelessNewPayload`, `runStatelessGuest`.

Library `EthStateless`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). The raw execution witness is supplied.
The concrete output record, serializer and zero sentinel have complete layout, size
and injectivity laws under the spec guidance document §§3/7. Guest execution and
input codecs remain open.
Spec guidance: `STFSpec/informal/modules/EthStateless.md`.
-/
