/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit
import STFSpec.Base.Numeric

/-!
# Storage encoder public-contract clients

Library `EthConformance`. Ordinary symbolic clients use public provider laws and
Trie contracts, keeping storage encoding separate from supplied-default deletion.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` §§3–7.
-/

namespace STFSpec.Conformance.StateCommit.StorageCallerProofs
open STFSpec.Base STFSpec.Codec STFSpec.Commit STFSpec.StateCommit

private theorem wire_nonempty (v : U256) : encodeStorage v ≠ ByteArray.empty :=
  encodeStorage_ne_empty v

private theorem recover_value (a b : U256) (h : encodeStorage a = encodeStorage b) : a = b :=
  (encodeStorage_inj a b).mp h

private theorem equal_values_equal_wires (a b : U256) (h : a = b) :
    encodeStorage a = encodeStorage b := (encodeStorage_inj a b).mpr h

private theorem instance_encoding (v : U256) : TrieValue.encode v = encodeStorage v := rfl

private theorem instance_valid (v : U256) : TrieValue.Valid v := True.intro

private theorem instance_nonempty (v : U256) : TrieValue.encode v ≠ ByteArray.empty :=
  TrieValue.encode_ne_empty v (instance_valid v)

private theorem bounded_wire (v : U256) : (encodeStorage v).size ≤ 33 := by
  have hb := U256.size_toBeBytes_le v
  change (Rlp.encodeBytes v.toBeBytes.toByteArray).size ≤ 33
  rw [Rlp.size_encodeBytes]
  rw [Bytes.size_toByteArray]
  split
  · omega
  · rw [ite_eq_left (by omega)]
    omega

variable {K : Type} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

-- Even directly stored defaults are valid. NoDefault is a separate predicate.
omit [Std.LawfulEqOrd K] in
private theorem all_stored_values_safe (t : Trie K U256) : t.PrepareSafe :=
  fun _ v _ ↦ instance_valid v

private theorem all_writes_safe (t : Trie K U256) (k : K) (v : U256) :
    (trieSet t k v).PrepareSafe :=
  (trieSet_prepareSafe_iff t k v (all_stored_values_safe t)).mpr (Or.inr (instance_valid v))

omit [Std.LawfulEqOrd K] in
private theorem supplied_default_deleted (t : Trie K U256) (k : K) :
    (trieSet t k t.default).data[k]? = none ∧ encodeStorage t.default ≠ ByteArray.empty :=
  ⟨(trieSet_erases_iff t k t.default).mpr rfl, encodeStorage_ne_empty t.default⟩

private theorem zero_with_nonzero_default (t : Trie K U256) (k : K)
    (h : U256.zero ≠ t.default) :
    (trieSet t k U256.zero).data[k]? = some U256.zero := by
  rw [trieSet_lookup]
  simp [h]

private theorem no_default_preserved (t : Trie K U256) (k : K) (v : U256)
    (h : t.NoDefault) : (trieSet t k v).NoDefault := trieSet_noDefault t k v h

end STFSpec.Conformance.StateCommit.StorageCallerProofs
