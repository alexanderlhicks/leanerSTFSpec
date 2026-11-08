/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless.ExecutionRequests
import STFSpec.Stateless.ExecutionWitness
import STFSpec.Stateless.ExecutionWitnessSsz
import STFSpec.Stateless.Output
import STFSpec.Stateless.ProtocolFork
import STFSpec.Stateless.RequestItems
import STFSpec.Stateless.WireLimits

/-!
# STFSpec.Stateless

The stateless guest: input/witness codecs, header-chain validation, `verifyStatelessNewPayload`, `runStatelessGuest`.

Library `EthStateless`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). The raw execution witness and complete
historical `ProtocolFork` identifiers with their forward tags are supplied.
The five raw execution-request item carriers retain all independent Base fields.
The raw `ExecutionRequests` aggregate retains all five independent ordered arrays.
The actual execution witness SSZ dictionary and three Q81 certificates are supplied
separately from serialization/root support, decoding and guest composition.
The concrete output record, serializer and zero sentinel have complete layout, size
and injectivity laws under the spec guidance document §§3/7. Guest execution and
input codecs remain open.
Spec guidance: `STFSpec/informal/modules/EthStateless.md`.
-/
