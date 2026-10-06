/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.Nibbles
import STFSpec.Base.FixedBytes

/-!
# Nominal partial-trie carriers

Library `EthCommit`. Type-only support for recursive partial nodes and unresolved
hashed stubs, distinct from nonrecursive `InternalNode` and generic `Trie`.
Pinned EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:48–98,287–346,892–991`
and `src/ethereum/forks/amsterdam/witness_state.py:53–100` supply field correspondence,
not a whole mutable-runtime refinement. Constructors certify no admission invariant.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§2.3/5/6/7.6; F5/F17/Q55.
-/

namespace STFSpec.Commit

open STFSpec.Base

/-- Completed raw encoding and optional cached hash; bare fields certify no coherence.
EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:48–81,287–346,932–988`.
Mutable dirty/missing-cache states are not represented (B15/Q33/D25). -/
structure Enc where
  /-- Complete raw encoding, corresponding to `_rlp` after cache completion.
  EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:56,68,80,932–988`. -/
  rlp : ByteArray
  /-- Optional complete cached hash value; acquisition/coherence are separate (Q55).
  EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:55,67,79,287–346`. -/
  hash? : Option Hash32

/-- Recursive partial-trie carrier matching the source variants.
EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:48–98`.
Bare constructors impose no branch, extension, canonicality or cache invariant. -/
inductive Node where
  /-- Source `MutableLeafNode`: `path` names its `rest_of_key`.
  EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:48–57`. -/
  | leaf (path : Nibbles) (value : ByteArray) (enc : Enc)
  /-- Source `MutableExtensionNode`: `ext` shortens its name; `path` is `key_segment`.
  EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:60–69`. -/
  | ext (path : Nibbles) (child : Node) (enc : Enc)
  /-- Source `MutableBranchNode`, with arbitrary bare Array/Option children (F5).
  EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:72–81`. -/
  | branch (children : Array (Option Node)) (value : ByteArray) (enc : Enc)
  /-- Unresolved `HashedNode` stub, retaining the full supplied digest.
  EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:84–89,892–914`. -/
  | hashed (h : Hash32)

/-- Absence or a present partial node, corresponding to the source union.
EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:92–98,892–914`.
Semantic adoption remains conditional on B3/NEW-COMMIT-1 provenance sufficiency
(DISC-003); the carrier alone does not discharge that gate (EthCommit §10). -/
abbrev Ref := Option Node

end STFSpec.Commit
