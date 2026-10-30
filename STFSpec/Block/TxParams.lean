/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

/-!
# Raw transaction parameters

Library `EthBlock`. Independent, unrestricted transaction policy inputs; the
Amsterdam values are supplied by `EthFork`.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–7.
-/

namespace STFSpec.Block

/-- Raw transaction policy inputs. Floor fields count access-list tokens, whose
gas price is separate. Every triple of natural numbers is admitted. -/
structure TxParams where
  /-- Per-transaction blob count limit. -/
  blobCountLimit : Nat
  /-- Floor tokens per access-list address occurrence. -/
  accessListAddressFloorTokens : Nat
  /-- Floor tokens per access-list storage-key occurrence. -/
  accessListStorageKeyFloorTokens : Nat

end STFSpec.Block
