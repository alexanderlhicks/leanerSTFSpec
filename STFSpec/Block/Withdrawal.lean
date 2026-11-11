/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.FixedBytes
import STFSpec.Base.U64

/-!
# Raw withdrawal

Library `EthBlock`. The four independent fields retain their supplied values.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§2.1, 3, 5 and 7.
-/

namespace STFSpec.Block

/-- Raw withdrawal in source field order; EELS
`src/ethereum/forks/amsterdam/blocks.py:38–66`. The amount is in Gwei. -/
structure Withdrawal where
  index : Base.U64
  validatorIndex : Base.U64
  address : Base.Address
  amount : Base.U64

end STFSpec.Block
