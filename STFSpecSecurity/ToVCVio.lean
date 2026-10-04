/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import ToVCVio.Oracle.QueryMorphism
import ToVCVio.Rlp.Codec
import ToVCVio.Rlp.Reference
import ToVCVio.EthCommit.NodeReference
import ToVCVio.Test.Reference
import ToVCVio.Trie.PatriciaNode
import ToVCVio.Test.PatriciaNode
import ToVCVio.Trie.PatriciaStructure
import ToVCVio.Test.PatriciaStructure
import ToVCVio.Trie.PatriciaSupport
import ToVCVio.Test.PatriciaSupport
import ToVCVio.Trie.PatriciaExtensionality
import ToVCVio.Test.PatriciaExtensionality
import ToVCVio.Trie.PatriciaRealization
import ToVCVio.Test.PatriciaRealization

/-!
# Local proved RLP reference, Patricia shell and structural support

Existing dependencies only. Faithful node injection, finite lookup, packed path
joining, one-step prefix compression, canonical support witnesses, resolved shape facts
and canonical resolved-tree observational extensionality support finite resolved
realization for actual maps satisfying `NonemptyValues`, including the empty map.
These local laws do not establish recursive map binding or a whole guest theorem.
Library `ToVCVio` in `STFSpecSecurity`.
Spec guidance: `STFSpec/informal/modules/ToVCVio.md`.
-/
