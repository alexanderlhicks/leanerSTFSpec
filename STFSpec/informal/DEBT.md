# Technical-debt register (D18)

**Status (2026-09-30):** current register under D18. No implementation debt is recorded yet. Known candidate: per-query storage-trie decoding in the witness backend, pending the memo design (DECISIONS F6).

Use one entry per local, correct and complete implementation whose data structure or algorithm is **not** performance-appropriate, justified on grounds of legibility or drastic proof-friendliness (D18). Missing semantics, proof holes required for release, unproved fuel sufficiency and protocol deviations are not performance debt. Protocol discrepancies belong in [`STFSpec/informal/DISCREPANCIES.md`](DISCREPANCIES.md).

Each entry records:

- Identifier, status, owning component and responsible maintainer.
- Preserved public contract and correctness/equivalence theorem.
- Expected workload, complexity, measured limitation (exact reproducer or benchmark, source/toolchain commits) and the reason for the exception.
- Affected consumers and why the limitation remains local.
- Replacement criterion, review/removal milestone and migration procedure.
- Decision authorizing acceptance and evidence closing the item.

Review outstanding entries when releasing, changing the owning component or updating the fork. Keep closed entries with links to their replacement evidence so that later regressions can be recognized.
