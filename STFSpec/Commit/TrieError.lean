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
node decoder and pure bare lookup are supplied; WitnessError/guest adapters remain
unimplemented. Q59 branchIndex is supplied for pure lookup; Q60 also approves its
future mutation scope, reached occupancy 0 and collapseIndex after applicable witnessing.
Only the collapseIndex constructor is supplied here; mutation emission remains future.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§2.1/2.7/5.
-/

namespace STFSpec.Commit


/-- Enumerated malformed trie diagnostics; there is no generic catch-all. -/
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
  /-- Decoder occupancy is below two; Q60 additionally names future changed zero collapse. -/
  | occupancy (n : Nat)
  /-- Witness traversal revisits a node on the current path. -/
  | cycle
  /-- A reached selected slot is missing: supplied Q59 lookup, future Q60 mutation. -/
  | branchIndex (index : Nat) (arity : Nat)
  /-- Q60 sole collapse survivor has a nonnibble index, after applicable witnessing.
  Constructor supplied; mutation emission and guest projection remain future. -/
  | collapseIndex (index : Nat)
  deriving DecidableEq


/-- Trie diagnostics. Witness/guest projection, including reachability of bare
lookup bounds failures, remains separate (CONTRACT O4/O13). -/
inductive TrieError where
  /-- The node database has no preimage for a required root. -/
  | missingRoot (h : STFSpec.Base.Hash32)
  /-- A reachable witness node has a named malformed condition. -/
  | malformed (why : Malformed)
  /-- Lookup or mutation requires an unresolved hashed node. -/
  | unresolved (h : STFSpec.Base.Hash32)
  deriving DecidableEq

end STFSpec.Commit
