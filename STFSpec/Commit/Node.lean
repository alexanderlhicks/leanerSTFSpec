/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.Nibbles
import STFSpec.Base.FixedBytes

/-!
# Nominal partial-trie carriers

Library `EthCommit`. Type-only support for recursive partial nodes and unresolved
hashed stubs, distinct from nonrecursive `InternalNode` and generic `Trie`.
Pinned EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:53–103,290–349,885–984`
and `src/ethereum/forks/amsterdam/witness_state.py:53–100` supply field correspondence,
not a whole mutable-runtime refinement. Constructors certify no admission invariant.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§2.3/5/6/7.6; F5/F17/Q55.
-/

namespace STFSpec.Commit

open STFSpec.Base

/-- Completed raw encoding and optional cached hash; bare fields certify no coherence.
EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:53–86,290–349,925–981`.
Mutable dirty/missing-cache states are not represented (B15/Q33/D25). -/
structure Enc where
  /-- Complete raw encoding, corresponding to `_rlp` after cache completion.
  EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:61,73,85,925–981`. -/
  rlp : ByteArray
  /-- Optional complete cached hash value; acquisition/coherence are separate (Q55).
  EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:60,72,84,290–349`. -/
  hash? : Option Hash32

/-- Recursive partial-trie carrier matching the source variants.
EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:53–103`.
Bare constructors impose no branch, extension, canonicality or cache invariant. -/
inductive Node where
  /-- Source `MutableLeafNode`: `path` names its `rest_of_key`.
  EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:53–62`. -/
  | leaf (path : Nibbles) (value : ByteArray) (enc : Enc)
  /-- Source `MutableExtensionNode`: `ext` shortens its name; `path` is `key_segment`.
  EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:65–74`. -/
  | ext (path : Nibbles) (child : Node) (enc : Enc)
  /-- Source `MutableBranchNode`, with arbitrary bare Array/Option children (F5).
  EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:77–86`. -/
  | branch (children : Array (Option Node)) (value : ByteArray) (enc : Enc)
  /-- Unresolved `HashedNode` stub, retaining the full supplied digest.
  EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:89–94,885–907`. -/
  | hashed (h : Hash32)

/-- Absence or a present partial node, corresponding to the source union.
EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:97–103,885–907`.
Semantic adoption remains conditional on B3/NEW-COMMIT-1 provenance sufficiency
(DISC-003); the carrier alone does not discharge that gate (EthCommit §10). -/
abbrev Ref := Option Node

end STFSpec.Commit
