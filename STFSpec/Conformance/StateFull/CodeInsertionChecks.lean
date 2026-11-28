/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateFull

/-!
# Full-state code insertion checks

Library `EthConformance`. Check the complete F21 result, reserved branch and
effect order through the public StateFull interface.
Spec guidance: `STFSpec/informal/modules/EthStateFull.md` FS6 and §§3–4.
-/

namespace STFSpec.Conformance.StateFull.CodeInsertionChecks

open STFSpec.Base STFSpec.Hash STFSpec.State STFSpec.StateCommit STFSpec.StateFull

private def accountAddress := Address.ofNat (2 ^ 159 + 7)
private def key : Bytes32 := FixedBytes.ofNat (2 ^ 255 + 23)
private def word := U256.ofNat (2 ^ 255 + 29)
private def oldCode : ByteArray := ⟨#[96, 17, 0]⟩
private def newCode : ByteArray := ⟨#[97, 0, 255, 0]⟩
private def previousQuery : ByteArray := ⟨#[0, 128, 7]⟩
private def oldDigest := Id.run (KeccakQuery.keccak (m := Id) oldCode)
private def emptyDigest := Id.run (KeccakQuery.keccak (m := Id) ByteArray.empty)
private def consts := HashConsts.literals

private def expectedDigest : Hash32 :=
  Hash32.ofBytes32 (FixedBytes.ofNat
    0x47c5e35235caee151b067e37fd9e1a25805d99b62e165506dca089dc75b360bb)

private def account : Account := ⟨2 ^ 70 + 31, U256.ofNat 37, oldDigest⟩

private def accounts : Std.ExtTreeMap Address Account :=
  (∅ : Std.ExtTreeMap Address Account).insert accountAddress account

private def initial : MathState :=
  ⟨accounts, ∅, (∅ : Std.ExtTreeMap Hash32 ByteArray).insert emptyDigest ByteArray.empty⟩

private theorem initialWf : MathState.WF initial := by
  rw [MathState.wf_iff]
  simp [initial]

private theorem authenticEmptyRow (digest : Hash32)
    (exactDigest : Id.run (KeccakQuery.keccak (m := Id) ByteArray.empty) = digest) :
    CodeAuthentic ⟨accounts, ∅, (∅ : Std.ExtTreeMap Hash32 ByteArray).insert digest ByteArray.empty⟩ := by
  intro h bytes stored
  rw [MathState.code_mk, Std.ExtTreeMap.getElem?_insert] at stored
  split at stored
  · next same =>
    have keyEq := Std.LawfulEqCmp.eq_of_compare same
    have bytesEq := Option.some.inj stored
    subst bytes
    exact exactDigest.trans keyEq
  · simp at stored

private theorem initialAuthentic : CodeAuthentic initial :=
  authenticEmptyRow emptyDigest rfl

private def concrete (s : FullState) (supplied : HashConsts) (code : ByteArray) :
    Hash32 × FullState :=
  let digest := Id.run (KeccakQuery.keccak (m := Id) code)
  Id.run (s.storeCode (m := Id) supplied code ⟨digest, fun _ ↦ rfl⟩ rfl)

private def seed : Except StateError FullState := do
  let start := FullState.ofMath initial initialWf initialAuthentic
  let stored ← start.setStorage accountAddress key word
  pure (concrete stored consts oldCode).2

private def storageEntries (σ : MathState) :=
  σ.storage.toList.map (fun (a, slots) ↦ (a, slots.toList))

private def matchesSeed (s : FullState) : Bool :=
  s.σ.accounts.toList == [(accountAddress, account)] &&
  storageEntries s.σ == [(accountAddress, [(key, word)])] &&
  s.σ.code[oldDigest]? == some oldCode && s.σ.code[emptyDigest]? == some ByteArray.empty &&
  s.σ.code.size == 2

private def sameRaw (s expected : MathState) : Bool :=
  s.accounts.toList == expected.accounts.toList &&
  storageEntries s == storageEntries expected &&
  s.code.toList == expected.code.toList

#guard
  match seed with
  | .error _ => false
  | .ok s =>
    let (digest, stored) := concrete s consts newCode
    let expected := { s.σ with code := s.σ.code.insert expectedDigest newCode }
    matchesSeed s && digest == expectedDigest && sameRaw stored.σ expected

#guard
  match seed with
  | .error _ => false
  | .ok s =>
    let (digest, inserted) := concrete s consts newCode
    let (again, repeated) := concrete inserted consts newCode
    digest == expectedDigest && again == digest && sameRaw repeated.σ inserted.σ

#guard
  match seed with
  | .error _ => false
  | .ok s =>
    let (digest, after) := concrete s consts ByteArray.empty
    digest == consts.emptyCodeHash && sameRaw after.σ s.σ

private abbrev Observe := _root_.StateM (List ByteArray)

@[instance_reducible] private def selectReserve (hash : Hash32) : KeccakQuery Observe :=
  ⟨fun bytes log ↦ (hash, log ++ [bytes])⟩

private def reservedAnswer (supplied : HashConsts) (code : ByteArray) :
    Observe {h : Hash32 // h ≠ supplied.emptyCodeHash →
      Id.run (KeccakQuery.keccak (m := Id) code) = h} :=
  fun log ↦
    (⟨supplied.emptyCodeHash, fun differs ↦ False.elim (differs rfl)⟩, log ++ [code])

private def runReserved (s : FullState) (supplied : HashConsts) (code : ByteArray) :
    Observe (Hash32 × FullState) :=
  @FullState.storeCode Observe _ (selectReserve supplied.emptyCodeHash)
    s supplied code (reservedAnswer supplied code) rfl

private theorem reservedWholeResult (s : FullState) (supplied : HashConsts) (code : ByteArray)
    (before : List ByteArray) :
    (runReserved s supplied code).run before =
      ((supplied.emptyCodeHash, s), before ++ [code]) := by
  simp only [runReserved, FullState.storeCode, Bind.bind, StateT.bind, StateT.run, reservedAnswer]
  split
  · rfl
  · rename_i differs
    exact False.elim (differs trivial)

private theorem projectedReserved (s : FullState) (supplied : HashConsts) (code : ByteArray) :
    (fun result : Hash32 × FullState ↦ (result.1, result.2.σ)) <$> runReserved s supplied code =
      (fun log ↦ ((supplied.emptyCodeHash, s.σ), log ++ [code])) := by
  unfold runReserved
  have projected := @FullState.storeCode_project Observe _ _ (selectReserve supplied.emptyCodeHash)
    s supplied code (reservedAnswer supplied code) rfl
  rw [projected]
  change (fun log ↦
    ((supplied.emptyCodeHash, if supplied.emptyCodeHash = supplied.emptyCodeHash then s.σ
      else { s.σ with code := s.σ.code.insert supplied.emptyCodeHash code }), log ++ [code])) = _
  simp only [ite_true, eq_self]

#guard
  match seed with
  | .error _ => false
  | .ok s =>
    let supplied := { consts with emptyCodeHash := oldDigest }
    let ((digest, after), log) := (runReserved s supplied newCode).run [previousQuery]
    oldDigest != expectedDigest && digest == oldDigest && log == [previousQuery, newCode] &&
      sameRaw after.σ s.σ && after.σ.code[oldDigest]? == some oldCode

private theorem optionFailure (s : FullState) (supplied : HashConsts) (code : ByteArray) :
    @FullState.storeCode Option _ ⟨fun _ ↦ none⟩ s supplied code none rfl = none := rfl

private abbrev Rejecting := ExceptT Nat Observe
private def rejection (code : ByteArray) : Nat := 47 + code.size

@[instance_reducible] private def rejectingQuery : KeccakQuery Rejecting :=
  ⟨fun code ↦ ExceptT.mk fun log ↦ (.error (rejection code), log ++ [code])⟩

private def rejectingAnswer (supplied : HashConsts) (code : ByteArray) :
    Rejecting {h : Hash32 // h ≠ supplied.emptyCodeHash →
      Id.run (KeccakQuery.keccak (m := Id) code) = h} :=
  ExceptT.mk fun log ↦ (.error (rejection code), log ++ [code])

#guard
  match seed with
  | .error _ => false
  | .ok s =>
    let attempt := @FullState.storeCode Rejecting _ rejectingQuery
      s consts newCode (rejectingAnswer consts newCode) rfl
    match attempt.run.run [previousQuery] with
    | (.error observed, log) => observed == rejection newCode && log == [previousQuery, newCode]
    | (.ok _, _) => false

end STFSpec.Conformance.StateFull.CodeInsertionChecks
