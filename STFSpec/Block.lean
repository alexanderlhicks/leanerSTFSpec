/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block.DepositData
import STFSpec.Block.CalldataTokens
import STFSpec.Block.TxParams

/-!
# STFSpec.Block

Transactions, headers, receipts, validation, `processTransaction`, `applyBody`, `executeBlock`, block access lists, bloom, requests, withdrawals.

Library `EthBlock`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). The calldata token and fixed deposit
extraction helpers and raw transaction parameters are supplied; the remaining pipeline
is scaffolding.
Spec guidance: `STFSpec/informal/modules/EthBlock.md`.
-/
