/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit.Storage
import STFSpec.State.WitnessError

/-!
# Strict storage-leaf decoding

Library `EthStateCommit`. Full strict RLP parsing precedes local interpretation.
The shared typed integer provider rejects lists, leading zero and excess width
before constructing the complete unsigned word.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` §§3–7/10.
-/

namespace STFSpec.StateCommit
open Base Codec State

/-- EELS `src/ethereum/forks/amsterdam/witness_state.py:127`: complete RLP,
then integer shape, leading-zero and width admission (SC6, CONTRACT O4(e)). -/
def decodeStorageLeaf (leaf : ByteArray) : Except WitnessError U256 :=
  match Rlp.decode leaf with
  | .error _ => .error (.malformed .leaf)
  | .ok item =>
    match Rlp.toNatBounded 32 item with
    | .error _ => .error (.malformed .leaf)
    | .ok n => .ok (U256.ofNat n)

/-- Complete RLP rejection precedes interpretation and maps to the coarse leaf error. -/
theorem decodeStorageLeaf_of_rlp_error (leaf : ByteArray) (e : RlpError)
    (h : Rlp.decode leaf = .error e) :
    decodeStorageLeaf leaf = .error (.malformed .leaf) := by
  simp only [decodeStorageLeaf, h]

/-- Parsed lists reject before interpreting any child as an integer. -/
theorem decodeStorageLeaf_of_rlp_list (leaf : ByteArray) (items : List RlpItem)
    (h : Rlp.decode leaf = .ok (.list items)) :
    decodeStorageLeaf leaf = .error (.malformed .leaf) := by
  have he : ∀ n, Rlp.toNatBounded 32 (.list items) ≠ .ok n := by
    intro n hn
    have hi := (Rlp.toNatBounded_eq_ok_item_iff 32 _ n).mp hn
    cases hi.1
  simp only [decodeStorageLeaf, h]
  cases ht : Rlp.toNatBounded 32 (.list items) with
  | error e => rfl
  | ok n => exact False.elim (he n ht)

/-- Canonical byte admission precedes the complete unsigned value construction. -/
theorem decodeStorageLeaf_of_rlp_bytes (leaf payload : ByteArray)
    (h : Rlp.decode leaf = .ok (.bytes payload)) :
    decodeStorageLeaf leaf =
      if payload[0]? = some 0 then .error (.malformed .leaf)
      else if payload.size ≤ 32 then
        .ok (U256.ofNat (Uint.ofBeBytes (Bytes.ofByteArray payload)))
      else .error (.malformed .leaf) := by
  simp only [decodeStorageLeaf, h]
  by_cases hz : payload[0]? = some 0
  · rw [Rlp.toNatBounded_leading_zero 32 payload hz]
    simp only [hz, ↓reduceIte]
  · simp only [hz, ↓reduceIte]
    by_cases hw : payload.size ≤ 32
    · have hn := (Rlp.toNat_eq_ok_bytes_iff payload _).mpr ⟨hz, rfl⟩
      rw [(Rlp.toNatBounded_eq_ok_iff 32 payload _).mpr ⟨hn, hw⟩]
      simp only [hw, ↓reduceIte]
    · simp only [hw, ↓reduceIte]
      cases ht : Rlp.toNatBounded 32 (.bytes payload) with
      | error e => rfl
      | ok n => exact False.elim (hw ((Rlp.toNatBounded_eq_ok_iff 32 payload n).mp ht).2)

private theorem storagePayload_encodable (v : U256) :
    Rlp.Encodable (.bytes v.toBeBytes.toByteArray) := by
  apply (Rlp.encodable_bytes_iff _).mpr
  rw [Bytes.size_toByteArray]
  exact Nat.lt_of_le_of_lt (U256.size_toBeBytes_le v) (by decide)

/-- The required nonzero SC10 storage domain reconstructs the complete word. -/
theorem decodeStorageLeaf_encodeStorage (v : U256) (h : v ≠ U256.zero) :
    decodeStorageLeaf (encodeStorage v) = .ok v := by
  have _nonzero := h
  have hd : Rlp.decode (encodeStorage v) = .ok (Rlp.ofNat v.toNat) := by
    rw [encodeStorage_eq]
    exact Rlp.decode_encode _ (by
      simpa only [Rlp.ofNat, U256.toBeBytes_eq] using storagePayload_encodable v)
  simp only [decodeStorageLeaf, hd]
  rw [(Rlp.toNatBounded_eq_ok_item_iff 32 _ v.toNat).mpr ⟨rfl, U256.toNat_lt v⟩]
  exact congrArg Except.ok (U256.ofNat_toNat v)

end STFSpec.StateCommit
