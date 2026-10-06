/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit.Storage
import STFSpec.StateCommit.Account

/-!
# STFSpec.StateCommit

Integration of state semantics with commitments: the account and storage leaf encodings, the
state root of a mathematical state (`mathStateRoot`), the root clause of the `PreState`
contract (`stateRoot d = .ok r → r = mathStateRoot (σ.apply d)`), and code-hash agreement.
`EthState` (lookup, overlay and rollback laws) and `EthCommit` (a trie generic over encoded
keys and values) do not depend on each other; this library connects them, and both state
backends build on it.

Library `EthStateCommit`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). Total storage encoding and its all-value
laws, plus contextual account encoding and its complete-domain binding law, are
implemented; other integration operations remain specified in the guidance document.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md`.
-/
