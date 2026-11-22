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
EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:114–127` at the pin.
EthCommit C21 lists the source fields and §5 specifies the guest projection.
The caller owns default comparison (C22, `:425`). C28 and C25 own witness
effects and the required collapse failure on a stub (`:790/:248`). -/
structure IncrementalMPT where
  /-- Supplied flag for the future key-hashing operations. -/
  secured : Bool
  /-- Exact optional partial root, including unresolved stubs and bare nodes.
  Semantic adoption remains conditional on B3/NEW-COMMIT-1/DISC-003 provenance,
  failure and observation sufficiency; this carrier discharges none of that gate. -/
  root : Ref

end STFSpec.Commit
