/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Commit.Update

/-!
# Public bare-insertion law clients

Library `EthConformance`. This client uses the approved full index/arity equation
under plain Monad and the public path providers; no private worker is imported.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §7.0.10.
-/
namespace STFSpec.Conformance.Commit.UpdateCallerProofs
open STFSpec.Base STFSpec.Hash STFSpec.Commit

private theorem missing_selected_slot {m : Type → Type} [Monad m] [KeccakQuery m]
    (children : Array Ref) (old newValue : ByteArray) (enc : Enc)
    (key : Nibbles) (hkey : 0 < key.size)
    (hindex : children.size ≤ (key.get ⟨0, hkey⟩).val) :
    update (m := m) (some (.branch children old enc)) key newValue =
      pure (.error (.malformed
        (.branchIndex (key.get ⟨0, hkey⟩).val children.size))) :=
  update_branch_oob children old enc key newValue hkey hindex

end STFSpec.Conformance.Commit.UpdateCallerProofs
