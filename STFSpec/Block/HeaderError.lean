/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

/-!
# Header errors

Library `EthBlock`. Nominal tags for the R-VH header rejection sites.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§2.6/3/5.
-/

namespace STFSpec.Block

/-- Header rejection tags in the order of EELS
`src/ethereum/forks/amsterdam/fork.py:445–478`, with the gas-limit rejection
inside the base-fee helper at `:387–389`. -/
inductive HeaderError where
  /-- The header number is below one. -/
  | numberZero
  /-- The header excess blob gas differs from the calculated value. -/
  | excessBlobGas
  /-- The header gas used exceeds its gas limit. -/
  | gasUsedExceedsGasLimit
  /-- The base-fee helper rejects the gas limit. -/
  | gasLimit
  /-- The header base fee differs from the calculated value. -/
  | baseFee
  /-- The header timestamp fails to increase. -/
  | timestamp
  /-- The header number differs from its parent's number plus one. -/
  | number
  /-- The header extra data exceeds 32 bytes. -/
  | extraData
  /-- The header difficulty is nonzero. -/
  | difficulty
  /-- The header nonce is nonzero. -/
  | nonce
  /-- The header ommers hash differs from the empty ommers hash. -/
  | ommersHash
  /-- The header parent hash differs from the calculated hash. -/
  | parentHash

end STFSpec.Block
