/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

/-!
# Raw block parameters

Library `EthBlock`. Independent, unrestricted block policy inputs; the Amsterdam
values are supplied by `EthFork`.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–7.
-/

namespace STFSpec.Block

/-- Raw block policy inputs. Every triple of natural numbers is admitted. -/
structure BlockParams where
  /-- Denominator for the maximum base-fee change. -/
  baseFeeMaxChangeDenominator : Nat
  /-- Gas-target elasticity multiplier. -/
  elasticityMultiplier : Nat
  /-- Maximum RLP-encoded block size in bytes. -/
  maxRlpBlockSize : Nat

end STFSpec.Block
