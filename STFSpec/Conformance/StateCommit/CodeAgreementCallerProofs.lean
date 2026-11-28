/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit
import STFSpec.State.Apply

/-!
# Code-hash agreement proof clients

Library `EthConformance`. Ordinary proofs check the complete predicate fields,
raw diff preservation and the provider success contract at coherent constants.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` §§4, 7.3.
-/

namespace STFSpec.Conformance.StateCommit.CodeAgreementCallerProofs

open STFSpec.Base STFSpec.Hash STFSpec.State STFSpec.StateCommit

private def constsId : HashConsts := Id.run (HashConsts.query (m := Id))

example (σ : MathState) :
    CodeAuthentic σ ↔
      ∀ h code, σ.code[h]? = some code → Id.run (KeccakQuery.keccak (m := Id) code) = h :=
  Iff.rfl

example (d : BlockDiff) :
    CodeChangesAuthentic d ↔
      ∀ h code, d.codeChanges[h]? = some code → Id.run (KeccakQuery.keccak (m := Id) code) = h :=
  Iff.rfl

example (ps : PreState Id) :
    ModelsCode ps ↔
      ps.getCode constsId.emptyCodeHash = .ok ByteArray.empty ∧
      (∀ h code, ps.getCode h = .ok code → Id.run (KeccakQuery.keccak (m := Id) code) = h) :=
  Iff.rfl

example (σ : MathState) (d : BlockDiff)
    (initial : CodeAuthentic σ) (changes : CodeChangesAuthentic d) :
    CodeAuthentic (σ.apply d) := by
  intro h code found
  rw [MathState.apply_code_lookup] at found
  cases lookup : d.codeChanges[h]? with
  | none =>
    rw [lookup] at found
    exact initial h code found
  | some bytes =>
    rw [lookup] at found
    exact (Option.some.inj found) ▸ changes h bytes lookup

example (σ : MathState) (ps : PreState Id) (consts : HashConsts) (coherent : consts = constsId)
    (authentic : CodeAuthentic σ)
    (emptyAnswer : ps.getCode consts.emptyCodeHash = .ok ByteArray.empty)
    (lookup : ∀ h code, ps.getCode h = .ok code → σ.code? consts h = some code) :
    ModelsCode ps := by
  subst consts
  refine ⟨emptyAnswer, ?_⟩
  intro h code answer
  by_cases reserved : h = constsId.emptyCodeHash
  · subst h
    rw [emptyAnswer] at answer
    have digestEmpty : Id.run (KeccakQuery.keccak (m := Id) ByteArray.empty) =
        constsId.emptyCodeHash := rfl
    exact (Except.ok.inj answer) ▸ digestEmpty
  · have found := lookup h code answer
    rw [MathState.code?_of_ne σ constsId h reserved] at found
    exact authentic h code found

end STFSpec.Conformance.StateCommit.CodeAgreementCallerProofs
