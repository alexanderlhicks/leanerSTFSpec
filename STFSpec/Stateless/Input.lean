/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.U64
import STFSpec.Stateless.ExecutionWitness
import STFSpec.Stateless.Payload

/-!
# Raw stateless input

Library `EthStateless`. The three independent fields retain complete provider values.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3–7.
-/

namespace STFSpec.Stateless

/-- Raw input fields in source order; EELS
`src/ethereum/forks/amsterdam/stateless.py:144–166` at the pin.
Construction retains all supplied values without validation or effects. -/
structure StatelessInput where
  newPayloadRequest : NewPayloadRequest
  witness : ExecutionWitness
  chainId : Base.U64

end STFSpec.Stateless
