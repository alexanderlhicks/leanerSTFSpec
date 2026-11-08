/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block.Withdrawal
import STFSpec.Codec.RlpEncodeOf

/-!
# Withdrawal RLP model

Library `EthBlock`. The four fields use minimal unsigned big-endian words and
all twenty address bytes. The amount stays in Gwei.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–7.
-/

namespace STFSpec.Block

/-- Ordered withdrawal model; EELS `src/ethereum/forks/amsterdam/blocks.py:38–66`
and `fork.py:1106–1111`, with locked `ethereum_rlp/rlp.py:66–135` (0.1.6).
This public reference model admits every raw Withdrawal without amount scaling. -/
instance Withdrawal.instRlpEncode : Codec.RlpEncode Withdrawal where
  toRlp w := .list [Codec.Rlp.ofNat w.index.toNat, Codec.Rlp.ofNat w.validatorIndex.toNat,
    .bytes w.address.toBytes.toByteArray, Codec.Rlp.ofNat w.amount.toNat]

end STFSpec.Block
