/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import Init.Data.ByteArray.Basic

/-!
# Raw execution witness

Library `EthStateless`. The three arrays retain complete raw preimages and header bytes.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3–7.
-/

namespace STFSpec.Stateless

/-- Raw witness data in source field order; EELS
`src/ethereum/forks/amsterdam/stateless.py:41–69` at the pin.
Wire admission and header decoding are separate from this carrier. -/
structure ExecutionWitness where
  state : Array ByteArray
  codes : Array ByteArray
  headers : Array ByteArray

end STFSpec.Stateless
