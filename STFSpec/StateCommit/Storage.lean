/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.IntegerBytes
import STFSpec.Codec.RlpCanonical
import STFSpec.Commit.Trie

/-!
# Total storage-leaf encoding

Library `EthStateCommit`. EELS `src/ethereum/merkle_patricia_trie.py:268–269`
encodes U256 through ethereum-rlp 0.1.6 and ethereum-types 0.4.1 minimal unsigned
big-endian bytes. Every word has a nonempty wire, including zero (`80`).
Trie-default deletion is a separate caller operation (Q53).
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` §§3–7.
-/

namespace STFSpec.StateCommit
open Base Codec Commit

/-- Minimal unsigned big-endian payload encoded as an RLP string (SC2).
EELS `src/ethereum/merkle_patricia_trie.py:268–269` at the pin. -/
def encodeStorage (v : U256) : ByteArray :=
  Rlp.encodeBytes v.toBeBytes.toByteArray

/-- All word payloads are inside the standard RLP domain (Q47). -/
private theorem storage_encodable (v : U256) :
    Rlp.Encodable (.bytes v.toBeBytes.toByteArray) := by
  apply (Rlp.encodable_bytes_iff _).mpr
  have h := U256.size_toBeBytes_le v
  rw [Bytes.size_toByteArray]
  exact Nat.lt_of_le_of_lt h (by decide)

/-- Every storage word has a complete, nonempty RLP wire, including zero. -/
theorem encodeStorage_ne_empty (v : U256) : encodeStorage v ≠ ByteArray.empty := by
  intro h
  have hs := Rlp.size_encodeBytes v.toBeBytes.toByteArray
  change (encodeStorage v).size = _ at hs
  rw [h] at hs
  simp only [ByteArray.size_empty] at hs
  split at hs
  · next hh => omega
  · split at hs <;> omega

/-- The complete wire preserves the complete unsigned value on every word. -/
theorem encodeStorage_inj (a b : U256) : encodeStorage a = encodeStorage b ↔ a = b := by
  constructor
  · intro h
    have he := Rlp.eq_of_encode_eq (.bytes a.toBeBytes.toByteArray)
      (.bytes b.toBeBytes.toByteArray) (storage_encodable a) (storage_encodable b) h
    have hb : a.toBeBytes = b.toBeBytes := by
      have hw := Codec.RlpItem.bytes.inj he
      have hd := congrArg Bytes.ofByteArray hw
      simpa only [Bytes.ofByteArray_toByteArray] using hd
    have hd := congrArg U256.ofBeBytes? hb
    rw [U256.ofBeBytes?_toBeBytes, U256.ofBeBytes?_toBeBytes] at hd
    exact Option.some.inj hd
  · intro h
    exact congrArg encodeStorage h

/-- All words are preparation-valid, independently of the supplied trie default. -/
instance : TrieValue U256 where
  encode := encodeStorage
  Valid := fun _ ↦ True
  encode_ne_empty := fun v _ ↦ encodeStorage_ne_empty v

end STFSpec.StateCommit
