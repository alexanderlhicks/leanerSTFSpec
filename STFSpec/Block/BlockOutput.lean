/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.U64
import STFSpec.Block.BlockAccessList
import STFSpec.Vm.Core.Logs

/-!
# Raw block output

Library `EthBlock`. The carrier retains the ten independent fields of its interface.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–6.
-/

namespace STFSpec.Block

/-- Raw block-body output, with encoded values in ordinal order.
EELS `src/ethereum/forks/amsterdam/vm/__init__.py:66–114`. -/
structure BlockOutput where
  /-- Block execution gas used. -/
  blockGasUsed : Nat
  /-- Block state gas used. -/
  blockStateGasUsed : Nat
  /-- Cumulative gas paid after refund and floor accounting. -/
  cumulativeGasUsed : Nat
  /-- Ordered encoded transaction values. -/
  transactionValues : Array ByteArray
  /-- Ordered encoded receipt values. -/
  receiptValues : Array ByteArray
  /-- Ordered encoded withdrawal values. -/
  withdrawalValues : Array ByteArray
  /-- Block logs stored in the Core rope. -/
  blockLogs : Vm.Core.LogRope
  /-- Total blob gas used. -/
  blobGasUsed : Base.U64
  /-- Ordered request buffers. -/
  requests : Array ByteArray
  /-- Raw block access list in supplied order. -/
  blockAccessList : BlockAccessList

end STFSpec.Block
