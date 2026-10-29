/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block.TxParams
import STFSpec.Block.SystemAddrs

/-!
# STFSpec.Block

Transactions, headers, receipts, validation, `processTransaction`, `applyBody`, `executeBlock`, block access lists, bloom, requests, withdrawals.

Library `EthBlock`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). Raw transaction parameters and system address/budget records are supplied;
the remaining block semantics are open.
Spec guidance: `STFSpec/informal/modules/EthBlock.md`.
-/
