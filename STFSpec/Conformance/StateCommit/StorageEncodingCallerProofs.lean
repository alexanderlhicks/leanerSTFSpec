/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.StateCommit

/-!
# Ordinary storage-encoding callers
Library `EthConformance`. Public equations and every-word typed-trie validity
are independent of supplied defaults and storage deletion. No leaf decoder claim.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` SC2/Q53/§7.
-/
namespace STFSpec.Conformance.StateCommit.StorageEncodingCallerProofs
open STFSpec.Base STFSpec.Codec STFSpec.Commit STFSpec.StateCommit

private theorem complete_minimal (v : U256) :
    encodeStorage v = Rlp.encode (Rlp.ofNat v.toNat) := encodeStorage_eq v
private theorem nonempty (v : U256) : encodeStorage v ≠ ByteArray.empty := encodeStorage_ne_empty v
private theorem injective (v w : U256) :
    encodeStorage v = encodeStorage w ↔ v = w := encodeStorage_inj v w
private theorem instance_encode (v : U256) : TrieValue.encode v = encodeStorage v := rfl
private theorem instance_valid (v : U256) : TrieValue.Valid v ↔ True := Iff.rfl
private theorem instance_nonempty (v : U256) : TrieValue.encode v ≠ ByteArray.empty :=
  TrieValue.encode_ne_empty v True.intro
private theorem arbitrary_default_safe (t : Trie Nat U256) : t.PrepareSafe := by
  intro _ _ _
  exact True.intro
private theorem zero_bytes : (encodeStorage U256.zero).data.toList = [128] := by
  change (Rlp.encodeBytes U256.zero.toBeBytes.toByteArray).data.toList = [128]
  rw [U256.toBeBytes_zero]
  exact Rlp.encodeBytes_short ByteArray.empty (by decide) (by decide)
private theorem full_reference (v : U256) :
    (encodeStorage v).data.toList =
      Rlp.encodeModel (.bytes (Uint.toBeBytesReference v.toNat).toByteArray) := by
  rw [encodeStorage_eq, Rlp.toList_encode]
  simp only [Rlp.ofNat, Uint.toBeBytes_eq_reference]

end STFSpec.Conformance.StateCommit.StorageEncodingCallerProofs
