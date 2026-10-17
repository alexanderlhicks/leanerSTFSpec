/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Commit.Delete

/-!
# Public bare-deletion law clients

Library `EthConformance`. Both approved laws retain all supplied fields under
plain Monad. Clients use public declarations only.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §7.0.10.
-/
namespace STFSpec.Conformance.Commit.DeleteCallerProofs
open STFSpec.Base STFSpec.Hash STFSpec.Commit

private theorem missing_selected_slot {m : Type → Type} [Monad m] [KeccakQuery m]
    (children : Array Ref) (value : ByteArray) (enc : Enc) (key : Nibbles)
    (hkey : 0 < key.size) (hindex : children.size ≤ (key.get ⟨0, hkey⟩).val) :
    delete (m := m) (some (.branch children value enc)) key =
      pure (.error (.malformed
        (.branchIndex (key.get ⟨0, hkey⟩).val children.size))) :=
  delete_branch_oob children value enc key hkey hindex

private theorem clear_nonempty_terminal {m : Type → Type} [Monad m] [KeccakQuery m]
    (value : ByteArray) (enc : Enc) (key : Nibbles)
    (hkey : key.size = 0) (hvalue : 0 < value.size) :
    delete (m := m) (some (.branch #[] value enc)) key =
      pure (.error (.malformed (.occupancy 0))) :=
  delete_terminal_clear_empty value enc key hkey hvalue

-- Private control instances must stay on private carriers after public import.
example : True := by
  fail_if_success have _ : Monad (fun α : Type => α × Nat) := inferInstance
  trivial

end STFSpec.Conformance.Commit.DeleteCallerProofs
