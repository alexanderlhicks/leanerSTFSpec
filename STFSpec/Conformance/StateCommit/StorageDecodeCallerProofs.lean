/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit

/-!
# Storage decoder public-contract clients

Library `EthConformance`. Arbitrary-input proofs use the decoder laws in the
spec guidance and public Base/Codec contracts without access to private numeric representation.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` §§3–7.
-/

namespace STFSpec.Conformance.StateCommit.StorageDecodeCallerProofs
open STFSpec.Base STFSpec.Codec STFSpec.State STFSpec.StateCommit

private theorem parser_error (leaf : ByteArray) (e : RlpError)
    (h : Rlp.decode leaf = .error e) :
    decodeStorageLeaf leaf = .error (.malformed .leaf) :=
  decodeStorageLeaf_of_rlp_error leaf e h

private theorem parsed_list (leaf : ByteArray) (items : List RlpItem)
    (h : Rlp.decode leaf = .ok (.list items)) :
    decodeStorageLeaf leaf = .ok U256.zero :=
  decodeStorageLeaf_of_rlp_list leaf items h

private theorem parsed_bytes (leaf payload : ByteArray)
    (h : Rlp.decode leaf = .ok (.bytes payload)) :
    decodeStorageLeaf leaf =
      match U256.ofNat? (Uint.ofBeBytes (Bytes.ofByteArray payload)) with
      | some v => .ok v
      | none => .error (.malformed .leaf) :=
  decodeStorageLeaf_of_rlp_bytes leaf payload h

private theorem numeric_success_iff (leaf payload : ByteArray) (v : U256)
    (h : Rlp.decode leaf = .ok (.bytes payload)) :
    decodeStorageLeaf leaf = .ok v ↔
      Uint.ofBeBytes (Bytes.ofByteArray payload) < 2 ^ 256 ∧
      v.toNat = Uint.ofBeBytes (Bytes.ofByteArray payload) := by
  rw [decodeStorageLeaf_of_rlp_bytes leaf payload h]
  rw [← U256.ofNat?_eq_some_iff]
  cases U256.ofNat? (Uint.ofBeBytes (Bytes.ofByteArray payload)) <;> simp

private theorem numeric_overflow_iff (leaf payload : ByteArray)
    (h : Rlp.decode leaf = .ok (.bytes payload)) :
    decodeStorageLeaf leaf = .error (.malformed .leaf) ↔
      2 ^ 256 ≤ Uint.ofBeBytes (Bytes.ofByteArray payload) := by
  rw [decodeStorageLeaf_of_rlp_bytes leaf payload h, ← U256.ofNat?_eq_none_iff]
  cases U256.ofNat? (Uint.ofBeBytes (Bytes.ofByteArray payload)) <;> simp

private theorem complete_numeric_success (leaf payload : ByteArray)
    (h : Rlp.decode leaf = .ok (.bytes payload))
    (hn : Uint.ofBeBytes (Bytes.ofByteArray payload) < 2 ^ 256) :
    ∃ v, decodeStorageLeaf leaf = .ok v ∧
      v.toNat = Uint.ofBeBytes (Bytes.ofByteArray payload) := by
  cases hv : U256.ofNat? (Uint.ofBeBytes (Bytes.ofByteArray payload)) with
  | none =>
    have hg := (U256.ofNat?_eq_none_iff _).mp hv
    omega
  | some v =>
    have hs := (U256.ofNat?_eq_some_iff _ v).mp hv
    exact ⟨v, (numeric_success_iff leaf payload v h).mpr ⟨hn, hs.2⟩, hs.2⟩

private theorem canonical_nonzero_roundtrip (v : U256) (h : v ≠ U256.zero) :
    decodeStorageLeaf (encodeStorage v) = .ok v := decodeStorageLeaf_encodeStorage v h

end STFSpec.Conformance.StateCommit.StorageDecodeCallerProofs
