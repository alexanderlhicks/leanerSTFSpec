/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit
import STFSpec.State.Apply

/-!
# Raw code and provider agreement controls

Library `EthConformance`. The controls cover stored bytes at the reserved hash,
the provider's required empty answer and success-only authentication elsewhere.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` §§3–4, 7.3.
-/

namespace STFSpec.Conformance.StateCommit.CodeAgreementGuards

open STFSpec.Base STFSpec.Hash STFSpec.State STFSpec.StateCommit

private def constsId : HashConsts := Id.run (HashConsts.query (m := Id))

private def singleton (h : Hash32) (code : ByteArray) : Std.ExtTreeMap Hash32 ByteArray :=
  (∅ : Std.ExtTreeMap Hash32 ByteArray).insert h code

example : CodeAuthentic ⟨∅, ∅, singleton constsId.emptyCodeHash ByteArray.empty⟩ := by
  intro h code found
  change (singleton constsId.emptyCodeHash ByteArray.empty)[h]? = some code at found
  rw [singleton, Std.ExtTreeMap.getElem?_insert] at found
  split at found
  · next same =>
    have hashEq := Std.LawfulEqCmp.eq_of_compare same
    have codeEq := Option.some.inj found
    subst h
    subst code
    rfl
  · simp at found

example (σ : MathState) (code : ByteArray)
    (wrongDigest : Id.run (KeccakQuery.keccak (m := Id) code) ≠ constsId.emptyCodeHash) :
    let d : BlockDiff := ⟨∅, [], ∅, [], ∅, singleton constsId.emptyCodeHash code, ∅⟩
    ¬ CodeChangesAuthentic d ∧ ¬ CodeAuthentic (σ.apply d) ∧
      (σ.apply d).code[constsId.emptyCodeHash]? = some code ∧
      (σ.apply d).code? constsId constsId.emptyCodeHash = some ByteArray.empty := by
  dsimp only
  have changed : (singleton constsId.emptyCodeHash code)[constsId.emptyCodeHash]? = some code :=
    Std.ExtTreeMap.getElem?_insert_self
  have applied :
      (σ.apply ⟨∅, [], ∅, [], ∅, singleton constsId.emptyCodeHash code, ∅⟩).code[
        constsId.emptyCodeHash]? = some code := by
    rw [MathState.apply_code_lookup, BlockDiff.codeChanges_mk, changed]
  exact ⟨fun model ↦ wrongDigest (model _ _ changed),
    fun model ↦ wrongDigest (model _ _ applied), applied, MathState.code?_empty _ _⟩

private def withCode (ps : PreState Id) (getCode : Hash32 → Id (Except WitnessError ByteArray)) :
    PreState Id :=
  PreState.mk ps.getAccount? ps.getStorage getCode ps.stateRoot

example (ps : PreState Id) (failure : WitnessError) :
    ¬ ModelsCode (withCode ps (fun _ ↦ .error failure)) := by
  intro model
  have answer := model.1
  rw [withCode, PreState.getCode_mk] at answer
  cases answer

example (ps : PreState Id) (failure : WitnessError) :
    ModelsCode (withCode ps (fun h ↦
      if h = constsId.emptyCodeHash then .ok ByteArray.empty else .error failure)) := by
  unfold ModelsCode withCode
  rw [PreState.getCode_mk]
  refine ⟨ite_eq_left rfl, ?_⟩
  intro h code answer
  split at answer
  · next reserved =>
    subst h
    have empty := Except.ok.inj answer
    subst code
    rfl
  · cases answer

example (ps : PreState Id) (h : Hash32) (code : ByteArray)
    (answer : ps.getCode h = .ok code)
    (wrongDigest : Id.run (KeccakQuery.keccak (m := Id) code) ≠ h) :
    ¬ ModelsCode ps :=
  fun model ↦ wrongDigest (model.2 h code answer)

private def firstCode : ByteArray := ⟨#[0x60, 0x01, 0x60, 0x00, 0x55]⟩
private def secondCode : ByteArray := ⟨#[0x60, 0x00, 0x60, 0x00, 0xf3]⟩
private def firstHash : Hash32 := Hash32.ofBytes32
  (FixedBytes.ofNat 0x7efcce47028dabcb0d42f3a7eda8820bf6f7f4e618398c2547d52f703cafb073)
private def secondHash : Hash32 := Hash32.ofBytes32
  (FixedBytes.ofNat 0xd003426e799329b8dca093f3bbab55a5e4e9f3c40160fc942068eef712ae88ad)

#guard Id.run (KeccakQuery.keccak (m := Id) firstCode) == firstHash
#guard Id.run (KeccakQuery.keccak (m := Id) secondCode) == secondHash
#guard secondHash != firstHash && firstHash != constsId.emptyCodeHash

end STFSpec.Conformance.StateCommit.CodeAgreementGuards
