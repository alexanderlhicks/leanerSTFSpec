/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.Bytes
import STFSpec.Commit.Trie

/-!
# Withdrawal trie byte interpretation

Library `EthBlock`. The named dictionary retains already encoded withdrawal
bytes and states the stored-value preparation domain.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–5.
-/

namespace STFSpec.Block.Withdrawal

/-- Interpret pre-encoded withdrawal bytes and require nonempty stored values.
EELS `src/ethereum/forks/amsterdam/fork.py:1106–1111` and
`src/ethereum/merkle_patricia_trie.py:252–269,429–439`. -/
@[instance_reducible] def encodedTrieValue : Commit.TrieValue (Option Base.Bytes) where
  encode
    | none => ByteArray.empty
    | some bytes => bytes.toByteArray
  Valid
    | none => False
    | some bytes => bytes ≠ Base.Bytes.empty
  encode_ne_empty := by
    intro value valid empty
    cases value with
    | none => exact valid
    | some bytes =>
      apply valid
      simpa only [Base.Bytes.ofByteArray_toByteArray, Base.Bytes.empty] using
        congrArg Base.Bytes.ofByteArray empty

/-- Total encoding applies the packed-byte projection to every concrete value.
The absent case is the total mathematical extension. -/
theorem encodedTrieValue_encode (value : Option Base.Bytes) :
    encodedTrieValue.encode value =
      (match value with
       | none => ByteArray.empty
       | some bytes => bytes.toByteArray) := rfl

/-- Preparation admits exactly the concrete nonempty byte values. -/
theorem encodedTrieValue_valid (value : Option Base.Bytes) :
    encodedTrieValue.Valid value ↔
      (match value with
       | none => False
       | some bytes => bytes ≠ Base.Bytes.empty) := Iff.rfl

end STFSpec.Block.Withdrawal
