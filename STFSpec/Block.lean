/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block.Header
import STFSpec.Block.HeaderError
import STFSpec.Block.HeaderRlp
import STFSpec.Block.Receipt
import STFSpec.Block.ReceiptRlp
import STFSpec.Block.Withdrawal
import STFSpec.Block.WithdrawalRlp
import STFSpec.Block.WithdrawalSsz
import STFSpec.Block.WithdrawalTrieValue
import STFSpec.Block.LogsBloom
import STFSpec.Block.RequestsHash
import STFSpec.Block.DepositData
import STFSpec.Block.CalldataTokens
import STFSpec.Block.BlockParams
import STFSpec.Block.TxParams
import STFSpec.Block.SystemAddrs
import STFSpec.Block.BlockAccessList
import STFSpec.Block.BlockAccessListRlp
import STFSpec.Block.BlockAccessListHash
import STFSpec.Block.BlockOutput
import STFSpec.Block.Access

/-!
# STFSpec.Block

Transactions, headers, receipts, validation, `processTransaction`, `applyBody`, `executeBlock`, block access lists, bloom, requests, withdrawals.

Library `EthBlock`. Its allowed dependencies are listed in `scripts/boundaries.toml` (see
`STFSpec/informal/ARCHITECTURE.md` §3). The calldata token, fixed deposit extraction,
ordered request commitment and logs bloom helpers, raw block and transaction parameters and
system address/budget records, raw receipts and their envelope variants, raw headers
and common parent projections are supplied.
The raw withdrawal carrier has a forward RLP model, certified SSZ dictionary and
named trie byte dictionary.
`Receipt`, `Header`, `PrevHeader` and `ParentHeader` have forward RLP models.
The block access list carriers have six forward RLP models and a typed hash.
The raw block output carrier and transaction access entry are supplied.
The remaining pipeline is scaffolding.
Spec guidance: `STFSpec/informal/modules/EthBlock.md`.
-/
