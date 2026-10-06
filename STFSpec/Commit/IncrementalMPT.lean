/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.Node

/-!
# Nominal incremental-trie carrier

Library `EthCommit`. The guest projection retains the supplied secured flag and
partial root, using the existing nominal `Ref`. Remaining representation and
operation obligations are owned by EthCommit §10 and REVIEW §3.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/5/10; C21/C22/C25/C28, B3.
-/

namespace STFSpec.Commit

/-- Nominal guest incremental trie, with no admission or operation guarantee.
EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:111–123` at the pin;
the guest projection is specified by EthCommit §5. Omitted `_data` follows C21,
`default` follows C22 (`:441/452`) and `witness` follows C28/C25 (`:797/:245`);
future collapse must retain the stub failure, despite omitted recorded contents. -/
structure IncrementalMPT where
  /-- Supplied flag for the future key-hashing operations. -/
  secured : Bool
  /-- Exact optional partial root, including unresolved stubs and bare nodes.
  Semantic adoption remains conditional on B3/NEW-COMMIT-1/DISC-003 provenance,
  failure and observation sufficiency; this carrier discharges none of that gate. -/
  root : Ref

end STFSpec.Commit
