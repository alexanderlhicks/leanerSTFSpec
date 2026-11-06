/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless.ExecutionWitness
import STFSpec.Stateless.Output
import STFSpec.Stateless.ProtocolFork
import STFSpec.Stateless.WireLimits
import STFSpec.Stateless.SchemaIdentifiers

/-!
# STFSpec.Stateless

The stateless guest: input/witness codecs, header-chain validation, `verifyStatelessNewPayload`, `runStatelessGuest`.

Library `EthStateless`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). The raw execution witness and complete
historical `ProtocolFork` identifiers with their forward tags are supplied.
Selected schema identifiers use Fork-owned values and a private bounded nominal transport.
The concrete output record, serializer and zero sentinel have complete layout, size
and injectivity laws under the spec guidance document §§3/7. Guest execution and
input codecs remain open.
Spec guidance: `STFSpec/informal/modules/EthStateless.md`.
-/
