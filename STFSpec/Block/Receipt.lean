/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.FixedBytes
import STFSpec.Vm.Core.Logs

/-!
# Raw receipts

Library `EthBlock`. The receipt and envelope carriers retain their complete inputs.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§2.1, 3 and 5.
-/

namespace STFSpec.Block

/-- Raw receipt in source field order (`src/ethereum/forks/amsterdam/blocks.py:363–391`). -/
structure Receipt where
  succeeded : Bool
  cumulativeGasUsed : Nat
  bloom : Base.Bloom
  logs : Array Vm.Core.Log

/-- The raw receipt envelope (`src/ethereum/forks/amsterdam/blocks.py:394–436`). -/
inductive EncodedReceipt where
  /-- Keep the complete legacy receipt. -/
  | legacy (r : Receipt)
  /-- Keep the complete byte array, including an empty array. -/
  | typed (b : ByteArray)

end STFSpec.Block
