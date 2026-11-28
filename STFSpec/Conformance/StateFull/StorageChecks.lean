/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateFull

/-!
# Full-state storage setter checks

Library `EthConformance`. Compare complete account, storage and code fields
against the expected states after each write, and check both missing-account
failures.
Spec guidance: `STFSpec/informal/modules/EthStateFull.md` FS6 and §§3–4.
-/

namespace STFSpec.Conformance.StateFull.StorageChecks

open STFSpec.Base STFSpec.Hash STFSpec.State STFSpec.StateCommit STFSpec.StateFull

private def first : Address := Address.ofNat 1
private def other : Address := Address.ofNat 2
private def missing : Address := Address.ofNat 3
private def slot (n : Nat) : Bytes32 := FixedBytes.ofNat n
private def code : ByteArray := ⟨#[0x60, 0x01, 0x00]⟩
private def codeHash : Hash32 := Id.run (KeccakQuery.keccak (m := Id) code)

private def accounts : Std.ExtTreeMap Address Account :=
  ((∅ : Std.ExtTreeMap Address Account).insert first ⟨7, U256.ofNat 17, codeHash⟩).insert
    other (emptyAccount HashConsts.literals)

private def codes : Std.ExtTreeMap Hash32 ByteArray :=
  (∅ : Std.ExtTreeMap Hash32 ByteArray).insert codeHash code

private def initial : MathState := ⟨accounts, ∅, codes⟩

private theorem initialWf : MathState.WF initial := by
  rw [MathState.wf_iff]
  simp [initial]

private theorem initialAuthentic : CodeAuthentic initial := by
  intro key value lookup
  change codes[key]? = some value at lookup
  rw [codes, Std.ExtTreeMap.getElem?_insert] at lookup
  split at lookup
  · next same =>
    have keyEq := Std.LawfulEqCmp.eq_of_compare same
    have valueEq := Option.some.inj lookup
    subst key
    subst value
    rfl
  · simp at lookup

private def start : FullState := FullState.ofMath initial initialWf initialAuthentic

private def write (s : FullState) (a : Address) (k v : Nat) : Except StateError FullState :=
  s.setStorage a (slot k) (U256.ofNat v)

private def seeded : Except StateError FullState := do
  let firstWrite ← write start first 5 7
  let secondWrite ← write firstWrite first 11 9
  write secondWrite other 5 13

private def expectedSlots (slots : List (Nat × Nat)) : List (Bytes32 × U256) :=
  slots.map fun (k, v) ↦ (slot k, U256.ofNat v)

private def complete (result : Except StateError FullState)
    (storage : List (Address × List (Nat × Nat))) : Bool :=
  match result with
  | .error _ => false
  | .ok output =>
    let observed := output.σ.storage.toList.map fun (a, slots) ↦ (a, slots.toList)
    let expected := storage.map fun (a, slots) ↦ (a, expectedSlots slots)
    output.σ.accounts.toList == accounts.toList &&
      observed == expected &&
      output.σ.code.toList == codes.toList

private def missingError (value : Nat) : Bool :=
  match write start missing 5 value with
  | .error .storageOnMissingAccount => true
  | _ => false

#guard complete (write start first 5 7) [(first, [(5, 7)])]
#guard complete (write start other 5 13) [(other, [(5, 13)])]
#guard complete (write start first 5 0) []
#guard complete seeded [(first, [(5, 7), (11, 9)]), (other, [(5, 13)])]
#guard complete (seeded >>= fun s ↦ write s first 5 11)
  [(first, [(5, 11), (11, 9)]), (other, [(5, 13)])]
#guard complete (seeded >>= fun s ↦ write s first 5 0) [(first, [(11, 9)]), (other, [(5, 13)])]
#guard complete (do let s ← seeded; let t ← write s first 5 0; write t first 11 0)
  [(other, [(5, 13)])]
#guard missingError 0
#guard missingError 7

end STFSpec.Conformance.StateFull.StorageChecks
