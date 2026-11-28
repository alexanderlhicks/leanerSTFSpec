/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block.BlockAccessListRlp
import STFSpec.Hash.KeccakQuery

/-!
# Block access list hash

Library `EthBlock`. The typed block access list supplies the complete preimage
for one Keccak query.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§2.11, 3 and 5.
-/

namespace STFSpec.Block

open STFSpec.Base STFSpec.Codec STFSpec.Hash

/-- Query Keccak on the complete RLP encoding of `bal` in array order.
EELS `src/ethereum/forks/amsterdam/block_access_lists.py:850–856`. -/
def hashBlockAccessList {m : Type → Type} [Monad m] [KeccakQuery m]
    (bal : BlockAccessList) : m Hash32 :=
  KeccakQuery.keccak (Rlp.encodeOf bal.toList)

end STFSpec.Block
