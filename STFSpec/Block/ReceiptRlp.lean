/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block.Receipt
import STFSpec.Codec.RlpBool

/-!
# Receipt RLP model

Library `EthBlock`. The forward model keeps all four receipt fields and each
embedded log in source order. Wire correspondence uses the assembled Q47
domain and the source conversion premises in the spec guidance.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–7.
-/

namespace STFSpec.Block

open STFSpec.Codec

private def logItem (entry : Vm.Core.Log) : RlpItem :=
  .list [.bytes entry.address.toBytes.toByteArray,
    .list (entry.topics.toList.map fun hash => .bytes hash.toBytes.toByteArray),
    .bytes entry.data.toByteArray]

/-- Complete raw receipt model in source order (EELS
`src/ethereum/forks/amsterdam/blocks.py:330–391` and locked
`ethereum_rlp/rlp.py:66–135` (0.1.6)). -/
instance Receipt.instRlpEncode : RlpEncode Receipt where
  toRlp receipt := .list [RlpEncode.toRlp receipt.succeeded,
    Rlp.ofNat receipt.cumulativeGasUsed,
    .bytes receipt.bloom.toBytes.toByteArray,
    .list (receipt.logs.toList.map logItem)]

end STFSpec.Block
