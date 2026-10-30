/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block.BlockParams

/-!
# Amsterdam block parameters

Library `EthFork`. Complete fixed block inputs, retaining the pinned EELS operands
of the derived RLP size limit.
Spec guidance: `STFSpec/informal/modules/EthFork.md` §§2–7.
-/

namespace STFSpec.Fork.Amsterdam

-- EELS `src/ethereum/forks/amsterdam/fork.py:144–145` at the pin.
private def MAX_BLOCK_SIZE : Nat := 10485760
private def SAFETY_MARGIN : Nat := 2097152

#guard MAX_BLOCK_SIZE == 10485760
#guard SAFETY_MARGIN == 2097152

/-- Amsterdam block parameters; EELS
`src/ethereum/forks/amsterdam/fork.py:114–115,144–146` at the pin.
The RLP limit retains the source subtraction of its two private operands. -/
def blockParams : Block.BlockParams where
  baseFeeMaxChangeDenominator := 8
  elasticityMultiplier := 2
  maxRlpBlockSize := MAX_BLOCK_SIZE - SAFETY_MARGIN

end STFSpec.Fork.Amsterdam
