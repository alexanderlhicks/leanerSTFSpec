/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Commit.Set

/-!
# Encoded setter public-law clients

Library `EthConformance`. Clients retain arbitrary roots and both supplied flags
under plain Monad/KeccakQuery. Byte/path interpretation uses public provider laws;
no private setter or mutation worker is unfolded.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` C22/§7.0.10.
-/
namespace STFSpec.Conformance.Commit.SetCallerProofs
open STFSpec.Base STFSpec.Hash STFSpec.Commit

private theorem empty_encoding_action {m : Type → Type} [Monad m] [KeccakQuery m]
    (t : IncrementalMPT) (key : ByteArray) :
    mptSet (m := m) t key (some ByteArray.empty) = mptSet t key none :=
  mptSet_emptyEncoding t key

private theorem unsecured_empty_encoding {m : Type → Type} [Monad m] [KeccakQuery m]
    (root : Ref) (key : ByteArray) :
    mptSet (m := m) ⟨false,root⟩ key (some ByteArray.empty) =
      mptSet ⟨false,root⟩ key none :=
  mptSet_emptyEncoding ⟨false,root⟩ key

private theorem secured_empty_encoding {m : Type → Type} [Monad m] [KeccakQuery m]
    (root : Ref) (key : ByteArray) :
    mptSet (m := m) ⟨true,root⟩ key (some ByteArray.empty) =
      mptSet ⟨true,root⟩ key none :=
  mptSet_emptyEncoding ⟨true,root⟩ key

private theorem complete_unsecured_key (key : ByteArray) :
    (bytesToNibbleList key).toList = bytesToNibbleListModel key.data.toList :=
  toList_bytesToNibbleList key

private theorem complete_hash_key_size (h : Hash32) :
    (bytesToNibbleList h.toBytes.toByteArray).size = 64 := by
  rw [size_bytesToNibbleList, Bytes.size_toByteArray, Hash32.size_toBytes]

private theorem high_then_low (key : ByteArray) (i : Nat) (hi : i < key.size) :
    (bytesToNibbleList key).get ⟨2*i, by rw [size_bytesToNibbleList]; omega⟩ =
      highNibble key[i] ∧
    (bytesToNibbleList key).get ⟨2*i+1, by rw [size_bytesToNibbleList]; omega⟩ =
      lowNibble key[i] :=
  ⟨get_bytesToNibbleList_high key i hi,get_bytesToNibbleList_low key i hi⟩

example : True := by
  fail_if_success have _ : Monad (fun α : Type => α × Nat) := inferInstance
  trivial

end STFSpec.Conformance.Commit.SetCallerProofs
