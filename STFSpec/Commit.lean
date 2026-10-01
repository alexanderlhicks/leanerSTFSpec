/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.Nibbles

/-!
# STFSpec.Commit

Merkle-Patricia commitments: the mathematical root, the partial trie with lookup/update/delete, and the incremental root.

Library `EthCommit`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). Nibbles and the three pure path
operations are implemented; node, database, root and witness operations remain open.
Spec guidance: `STFSpec/informal/modules/EthCommit.md`.
-/
