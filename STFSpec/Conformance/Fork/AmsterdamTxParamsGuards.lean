/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block
import STFSpec.Fork

/-!
# Complete Amsterdam transaction parameter controls

Library `EthConformance`. Check the actual public value and all three projections.
Spec guidance: `STFSpec/informal/modules/EthFork.md` §§3–4.
-/

open STFSpec STFSpec.Fork.Amsterdam

private def value_type : Block.TxParams := txParams

private theorem complete_value : txParams = Block.TxParams.mk 6 80 128 := rfl

#guard txParams.blobCountLimit == 6
#guard txParams.accessListAddressFloorTokens == 80
#guard txParams.accessListStorageKeyFloorTokens == 128
#guard (txParams.blobCountLimit, txParams.accessListAddressFloorTokens,
  txParams.accessListStorageKeyFloorTokens) == (6, 80, 128)
