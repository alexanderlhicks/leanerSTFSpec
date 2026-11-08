/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block.Header
import STFSpec.Block.Withdrawal
import STFSpec.Block.WithdrawalRlp
import STFSpec.Block.WithdrawalSsz
import STFSpec.Block.LogsBloom
import STFSpec.Block.RequestsHash
import STFSpec.Block.DepositData
import STFSpec.Block.CalldataTokens
import STFSpec.Block.BlockParams
import STFSpec.Block.TxParams
import STFSpec.Block.SystemAddrs

/-!
# STFSpec.Block

Transactions, headers, receipts, validation, `processTransaction`, `applyBody`, `executeBlock`, block access lists, bloom, requests, withdrawals.

Library `EthBlock`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). The calldata token, fixed deposit extraction,
ordered request commitment and logs bloom helpers, raw block and transaction parameters
and system address/budget records, raw headers, common parent projections and the raw
withdrawal carrier with its forward RLP model and certified SSZ dictionary are supplied.
The remaining pipeline is scaffolding.
Spec guidance: `STFSpec/informal/modules/EthBlock.md`.
-/
