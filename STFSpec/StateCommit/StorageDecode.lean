/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit.Storage
import STFSpec.State.WitnessError

/-!
# Lenient storage-leaf decoding

Library `EthStateCommit`. Full strict RLP parsing precedes local interpretation.
Every parsed list reads as zero; byte payloads use a packed, checked unsigned
fold with unrestricted leading zeros. The ordinary reference is proof-facing.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` §§3–7/10.
-/

namespace STFSpec.StateCommit
open Base Codec State

private def storageValueReference (payload : Bytes) : Option U256 :=
  U256.ofNat? (Uint.ofBeBytes payload)

private def storageValueStep : Option U256 → UInt8 → Option U256
  | none, _ => none
  | some acc, byte => U256.ofNat? (256 * acc.toNat + byte.toNat)

private def storageValuePacked (payload : Bytes) : Option U256 :=
  payload.foldl storageValueStep (some U256.zero)

private theorem storageValueStep_commutes (n : Nat) (byte : UInt8) :
    storageValueStep (U256.ofNat? n) byte = U256.ofNat? (256 * n + byte.toNat) := by
  cases h : U256.ofNat? n with
  | none =>
    have hn := (U256.ofNat?_eq_none_iff n).mp h
    have hg : 2 ^ 256 ≤ 256 * n + byte.toNat := by omega
    rw [(U256.ofNat?_eq_none_iff _).mpr hg]
    rfl
  | some acc =>
    have hn := (U256.ofNat?_eq_some_iff n acc).mp h
    simp only [storageValueStep, hn.2]

private theorem storageValueFold_commutes (xs : List UInt8) (n : Nat) :
    xs.foldl storageValueStep (U256.ofNat? n) =
      U256.ofNat? (xs.foldl (fun acc byte ↦ 256 * acc + byte.toNat) n) := by
  induction xs generalizing n with
  | nil => rfl
  | cons byte xs ih =>
    simp only [List.foldl_cons, storageValueStep_commutes]
    exact ih _

private theorem storageValueFold_absorbing (xs : List UInt8) :
    xs.foldl storageValueStep none = none := by
  induction xs with
  | nil => rfl
  | cons byte xs ih => simpa only [List.foldl_cons, storageValueStep] using ih

private theorem storageValuePacked_absorbing (payload : Bytes) :
    payload.foldl storageValueStep none = none := by
  rw [Bytes.foldl_eq]
  exact storageValueFold_absorbing _

private theorem storageValuePacked_eq_reference (payload : Bytes) :
    storageValuePacked payload = storageValueReference payload := by
  have hz : U256.ofNat? 0 = some U256.zero := by
    simpa only [U256.toNat_zero] using U256.ofNat?_toNat U256.zero
  unfold storageValuePacked storageValueReference
  rw [Bytes.foldl_eq, ← hz, storageValueFold_commutes, Uint.ofBeBytes_eq_fold]

private theorem storageValuePrefix_invariant (xs : List UInt8) (n : Nat) :
    (∀ v, xs.foldl storageValueStep (U256.ofNat? n) = some v ↔
      xs.foldl (fun acc byte ↦ 256 * acc + byte.toNat) n < 2 ^ 256 ∧
      v.toNat = xs.foldl (fun acc byte ↦ 256 * acc + byte.toNat) n) ∧
    (xs.foldl storageValueStep (U256.ofNat? n) = none ↔
      2 ^ 256 ≤ xs.foldl (fun acc byte ↦ 256 * acc + byte.toNat) n) := by
  rw [storageValueFold_commutes]
  exact ⟨fun v ↦ U256.ofNat?_eq_some_iff _ v, U256.ofNat?_eq_none_iff _⟩

set_option exponentiation.threshold 300 in
private theorem storageValueCandidate_lt (acc : U256) (byte : UInt8) :
    256 * acc.toNat + byte.toNat < 2 ^ 264 := by
  have hb := Uint.ofBeBytes_lt (Bytes.ofList [byte])
  rw [Uint.ofBeBytes_eq_fold, Bytes.toList_ofList, Bytes.size_ofList] at hb
  simp only [List.foldl_cons, List.foldl_nil, Nat.mul_zero, Nat.zero_add,
    List.length_cons, List.length_nil] at hb
  have ha := U256.toNat_lt acc
  have hm : 2 ^ 264 = 256 * (2 ^ 256) := Nat.pow_add 2 8 256
  rw [hm]
  omega

/-- EELS `src/ethereum/forks/amsterdam/witness_state.py:198–203`: complete RLP
first, then list-to-zero or complete checked unsigned bytes (SC6, CONTRACT O4(e)). -/
def decodeStorageLeaf (leaf : ByteArray) : Except WitnessError U256 :=
  match Rlp.decode leaf with
  | .error _ => .error (.malformed .leaf)
  | .ok (.list _) => .ok U256.zero
  | .ok (.bytes payload) =>
    match storageValuePacked (Bytes.ofByteArray payload) with
    | some v => .ok v
    | none => .error (.malformed .leaf)

/-- Complete RLP rejection precedes interpretation and maps to the coarse leaf error. -/
theorem decodeStorageLeaf_of_rlp_error (leaf : ByteArray) (e : RlpError)
    (h : Rlp.decode leaf = .error e) :
    decodeStorageLeaf leaf = .error (.malformed .leaf) := by
  simp only [decodeStorageLeaf, h]

/-- Every successfully parsed list reads as zero without interpreting its children. -/
theorem decodeStorageLeaf_of_rlp_list (leaf : ByteArray) (items : List RlpItem)
    (h : Rlp.decode leaf = .ok (.list items)) :
    decodeStorageLeaf leaf = .ok U256.zero := by
  simp only [decodeStorageLeaf, h]

/-- Byte payloads use their complete unsigned value; no length or minimality premise. -/
theorem decodeStorageLeaf_of_rlp_bytes (leaf payload : ByteArray)
    (h : Rlp.decode leaf = .ok (.bytes payload)) :
    decodeStorageLeaf leaf =
      match U256.ofNat? (Uint.ofBeBytes (Bytes.ofByteArray payload)) with
      | some v => .ok v
      | none => .error (.malformed .leaf) := by
  simp only [decodeStorageLeaf, h, storageValuePacked_eq_reference, storageValueReference]

private theorem storagePayload_encodable (v : U256) :
    Rlp.Encodable (.bytes v.toBeBytes.toByteArray) := by
  apply (Rlp.encodable_bytes_iff _).mpr
  rw [Bytes.size_toByteArray]
  exact Nat.lt_of_le_of_lt (U256.size_toBeBytes_le v) (by decide)

/-- The required nonzero SC10 storage domain reconstructs the complete word. -/
theorem decodeStorageLeaf_encodeStorage (v : U256) (h : v ≠ U256.zero) :
    decodeStorageLeaf (encodeStorage v) = .ok v := by
  have _nonzero := h
  have hd : Rlp.decode (encodeStorage v) = .ok (.bytes v.toBeBytes.toByteArray) := by
    rw [encodeStorage, ← Rlp.encode_bytes]
    exact Rlp.decode_encode _ (storagePayload_encodable v)
  rw [decodeStorageLeaf_of_rlp_bytes _ _ hd, Bytes.ofByteArray_toByteArray,
    U256.toBeBytes_eq, Uint.ofBeBytes_toBeBytes, U256.ofNat?_toNat]

end STFSpec.StateCommit
