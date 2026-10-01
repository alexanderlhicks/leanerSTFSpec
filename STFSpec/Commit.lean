/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.Nibbles
import STFSpec.Commit.Compact
import STFSpec.Commit.InternalNode
import STFSpec.Commit.Root
import STFSpec.Commit.NodeDB

/-!
# STFSpec.Commit

Merkle-Patricia commitments: the mathematical root, the partial trie with
lookup/update/delete, and the incremental root.

Library `EthCommit`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). Bounded paths, compact encoding/decoding,
nonrecursive internal-node encoding and raw NodeDB construction are implemented.
Mathematical-root domain, prefix and bounded branch support are also implemented;
recursive root and witness trie operations remain open.
Spec guidance: `STFSpec/informal/modules/EthCommit.md`.
-/
