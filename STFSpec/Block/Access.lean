/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.FixedBytes

/-!
# Raw transaction access entry

Library `EthBlock`. Each entry stores an account and its ordered sequence of slots.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3, 5 and 7.
-/

namespace STFSpec.Block

/-- Raw account and slot sequence in source field order.
EELS `src/ethereum/forks/amsterdam/transactions.py:152–166`. -/
structure Access where
  account : Base.Address
  slots : Array Base.Bytes32

end STFSpec.Block
