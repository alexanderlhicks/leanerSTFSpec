/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.FixedBytes

/-!
# Trie diagnostics

Library `EthCommit`. The diagnostic constructors are owned by EthCommit §5.
`compactEmpty` names the first-byte failure in the pinned compact decoder;
`pathEmpty` names the later decoded extension-path check (Q48, CONTRACT O4).
Q52 names the two-item node's path-list check before compact decoding and its
leaf-value-list check after successful leaf compact decoding. The complete generic
node decoder is supplied; WitnessError/guest adapters remain unimplemented.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§2.1/2.7/5.
-/

namespace STFSpec.Commit

/-- Enumerated malformed witness diagnostics; there is no generic catch-all. -/
inductive Malformed where
  /-- Strict RLP decoding failed. -/
  | rlp
  /-- A string-valued node is nonempty. -/
  | nonEmptyString
  /-- A two-item decoded node has a list-valued first field, before compact decoding. -/
  | compactPathList
  /-- Raw compact bytes are empty, before path decoding. -/
  | compactEmpty
  /-- After successful leaf compact decoding, the second field is list-valued. -/
  | leafValueList
  /-- A decoded extension path is empty. -/
  | pathEmpty
  /-- A node list has neither two nor seventeen fields. -/
  | badListLength (n : Nat)
  /-- A child reference has an invalid byte length. -/
  | refLength (n : Nat)
  /-- An extension child is neither a branch nor a hashed stub. -/
  | extChild
  /-- A branch has fewer than two occupied entries. -/
  | occupancy (n : Nat)
  /-- Witness traversal revisits a node on the current path. -/
  | cycle
  deriving DecidableEq

/-- Trie failures are projected through the witness channel to CONTRACT O4. -/
inductive TrieError where
  /-- The node database has no preimage for a required root. -/
  | missingRoot (h : STFSpec.Base.Hash32)
  /-- A reachable witness node has a named malformed condition. -/
  | malformed (why : Malformed)
  /-- Lookup or mutation requires an unresolved hashed node. -/
  | unresolved (h : STFSpec.Base.Hash32)
  deriving DecidableEq

end STFSpec.Commit
