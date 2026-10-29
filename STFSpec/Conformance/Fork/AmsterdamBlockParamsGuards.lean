/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block
import STFSpec.Fork

/-!
# Complete Amsterdam block parameter controls

Library `EthConformance`. Check the actual public value and all three projections.
The two private source operands are checked in their owning Fork module.
Spec guidance: `STFSpec/informal/modules/EthFork.md` §§3–4.
-/

open STFSpec STFSpec.Fork.Amsterdam

private def value_type : Block.BlockParams := blockParams

private theorem complete_value : blockParams = Block.BlockParams.mk 8 2 8388608 := rfl

#guard blockParams.baseFeeMaxChangeDenominator == 8
#guard blockParams.elasticityMultiplier == 2
#guard blockParams.maxRlpBlockSize == 8388608
#guard (blockParams.baseFeeMaxChangeDenominator, blockParams.elasticityMultiplier,
  blockParams.maxRlpBlockSize) == (8, 2, 8388608)
