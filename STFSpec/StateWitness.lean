/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateWitness.CodeDB

/-!
# STFSpec.StateWitness

Witness-state backend: node and code databases, and a `PreState` over the partial trie.

Library `EthStateWitness`. Its allowed dependencies are listed in `scripts/boundaries.toml`
(see `STFSpec/informal/ARCHITECTURE.md` §3). This facade provides the code database.
Spec guidance: `STFSpec/informal/modules/EthStateWitness.md`.
-/
