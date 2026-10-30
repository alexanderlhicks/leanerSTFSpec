/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block.LogsBloom
import STFSpec.Block.RequestsHash
import STFSpec.Block.DepositData
import STFSpec.Block.CalldataTokens
import STFSpec.Block.TxParams
import STFSpec.Block.SystemAddrs

/-!
# STFSpec.Block

Transactions, headers, receipts, validation, `processTransaction`, `applyBody`, `executeBlock`, block access lists, bloom, requests, withdrawals.

Library `EthBlock`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). The calldata token, fixed deposit extraction,
ordered request commitment and logs bloom helpers, raw transaction parameters and
system address/budget records are supplied; the remaining pipeline is scaffolding.
Spec guidance: `STFSpec/informal/modules/EthBlock.md`.
-/
