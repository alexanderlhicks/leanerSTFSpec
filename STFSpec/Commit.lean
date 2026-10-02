/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.Nibbles
import STFSpec.Commit.Compact
import STFSpec.Commit.InternalNode
import STFSpec.Commit.Root
import STFSpec.Commit.NodeDB
import STFSpec.Commit.Trie

/-!
# STFSpec.Commit

Merkle-Patricia commitments: the mathematical root, the partial trie with
lookup/update/delete, and the incremental root.

Library `EthCommit`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). Bounded paths, compact encoding/decoding,
nonrecursive internal-node encoding and raw NodeDB construction and generic typed-trie
storage/safety are implemented.
Mathematical-root domain, prefix, ordered branches, recursive construction and
the total local root are implemented. Witness trie operations remain open.
Spec guidance: `STFSpec/informal/modules/EthCommit.md`.
-/
