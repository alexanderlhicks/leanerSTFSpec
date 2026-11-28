/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateFull

/-!
# Full-state account setter checks

Library `EthConformance`. Check the raw update, its exact structural proof
boundary and complete finite states through the public StateFull interface.
Spec guidance: `STFSpec/informal/modules/EthStateFull.md` FS6 and §§3–4/7.
-/

namespace STFSpec.Conformance.StateFull.AccountChecks

open STFSpec.Base STFSpec.Hash STFSpec.State STFSpec.StateCommit STFSpec.StateFull

private theorem lookup (σ : MathState) (a b : Address) (acc : Option Account) :
    (σ.setAccount a acc).account? b = if a = b then acc else σ.account? b := by
  cases acc <;>
    simp [MathState.setAccount, MathState.account?, Std.ExtTreeMap.getElem?_insert,
      Std.ExtTreeMap.getElem?_erase]

private theorem insertedWf (σ : MathState) (a : Address) (acc : Account)
    (h : MathState.WF σ) : MathState.WF (σ.setAccount a (some acc)) := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro b slots stored
  change ((σ.setAccount a (some acc)).account? b).isSome = true
  rw [lookup]
  by_cases equal : a = b
  · simp [equal]
  · rw [ite_eq_right equal, MathState.account?_eq_lookup]
    exact h.2.2 b slots stored

private theorem erasedWf (σ : MathState) (a : Address) (h : MathState.WF σ) :
    MathState.WF (σ.setAccount a none) ↔ σ.storage[a]? = none := by
  constructor
  · intro after
    cases stored : σ.storage[a]? with
    | none => rfl
    | some slots =>
      have present := after.2.2 a slots stored
      change ((σ.setAccount a none).account? a).isSome = true at present
      simp [lookup] at present
  · intro noStorage
    refine ⟨h.1, h.2.1, ?_⟩
    intro b slots stored
    change ((σ.setAccount a none).account? b).isSome = true
    rw [lookup]
    by_cases equal : a = b
    · subst b
      change σ.storage[a]? = some slots at stored
      rw [noStorage] at stored
      contradiction
    · rw [ite_eq_right equal, MathState.account?_eq_lookup]
      exact h.2.2 b slots stored

private theorem exactCarrier (s : FullState) (a : Address) (acc : Option Account)
    (h : MathState.WF (s.σ.setAccount a acc)) :
    s.setAccount a acc h = ⟨s.σ.setAccount a acc, h, s.codeAuthentic⟩ := rfl

private theorem rawFraming (σ : MathState) (a : Address) (acc : Option Account) :
    (σ.setAccount a acc).storage = σ.storage ∧ (σ.setAccount a acc).code = σ.code :=
  ⟨rfl, rfl⟩

private def selected : Address := Address.ofNat (2 ^ 159 + 17)
private def other : Address := Address.ofNat 39
private def fresh : Address := Address.ofNat 55
private def lowSlot : Bytes32 := FixedBytes.ofNat 19
private def highSlot : Bytes32 := FixedBytes.ofNat (2 ^ 255 + 33)
private def blob : ByteArray := ⟨#[0, 17, 255, 53]⟩
private def digest := Id.run (KeccakQuery.keccak (m := Id) blob)
private def empty := emptyAccount HashConsts.literals
private def startingAccount : Account := ⟨2 ^ 75 + 7, U256.ofNat (2 ^ 255 + 11), digest⟩
private def relatedAccount : Account := ⟨13, U256.ofNat 17, HashConsts.literals.emptyCodeHash⟩
private def unavailable : Account :=
  ⟨23, U256.ofNat 29, Hash32.ofBytes32 (FixedBytes.ofNat 123)⟩

private def codeRows : Std.ExtTreeMap Hash32 ByteArray :=
  (∅ : Std.ExtTreeMap Hash32 ByteArray).insert digest blob

private def initial : MathState :=
  ⟨((∅ : Std.ExtTreeMap Address Account).insert selected startingAccount).insert other relatedAccount,
    ∅, codeRows⟩

private theorem initialWf : MathState.WF initial := by
  rw [MathState.wf_iff]
  simp [initial]

private theorem initialAuthentic : CodeAuthentic initial := by
  intro key bytes seen
  change codeRows[key]? = some bytes at seen
  simp only [codeRows, Std.ExtTreeMap.getElem?_insert,
    Std.LawfulEqOrd.compare_eq_iff_eq] at seen
  by_cases matchKey : digest = key
  · simp only [ite_eq_left matchKey] at seen
    rw [← Option.some.inj seen, ← matchKey]
    rfl
  · simp [matchKey] at seen

private def seed : FullState := .ofMath initial initialWf initialAuthentic

private def withStorage : Except StateError FullState := do
  let s ← seed.setStorage selected lowSlot (U256.ofNat 31)
  let s ← s.setStorage selected highSlot (U256.ofNat 37)
  s.setStorage other highSlot (U256.ofNat 41)

private def storageEntries (σ : MathState) :=
  σ.storage.toList.map fun (a, slots) ↦ (a, slots.toList)

private def storedRows : List (Address × List (Bytes32 × U256)) :=
  [(other, [(highSlot, U256.ofNat 41)]),
   (selected, [(lowSlot, U256.ofNat 31), (highSlot, U256.ofNat 37)])]

private def hasMaps (σ : MathState) (accounts : List (Address × Account))
    (slots : List (Address × List (Bytes32 × U256))) : Bool :=
  σ.accounts.toList == accounts && storageEntries σ == slots &&
    σ.code.toList == [(digest, blob)]

private def insertAccount (s : FullState) (a : Address) (acc : Account) : FullState :=
  s.setAccount a (some acc) (insertedWf s.σ a acc s.wf)

private def deleteStorageFree (a : Address) : FullState :=
  seed.setAccount a none ((erasedWf seed.σ a seed.wf).2 (by simp [seed, initial, FullState.ofMath]))

#guard hasMaps (insertAccount seed fresh empty).σ
  [(other, relatedAccount), (fresh, empty), (selected, startingAccount)] []
#guard hasMaps (insertAccount seed fresh unavailable).σ
  [(other, relatedAccount), (fresh, unavailable), (selected, startingAccount)] []
#guard hasMaps (deleteStorageFree selected).σ [(other, relatedAccount)] []
#guard hasMaps (deleteStorageFree fresh).σ [(other, relatedAccount), (selected, startingAccount)] []

#guard
  match withStorage with
  | .error _ => false
  | .ok state =>
    hasMaps (insertAccount state selected empty).σ
      [(other, relatedAccount), (selected, empty)] storedRows &&
    hasMaps (insertAccount state selected startingAccount).σ
      [(other, relatedAccount), (selected, startingAccount)] storedRows

#guard
  match withStorage with
  | .error _ => false
  | .ok state =>
    let rawDeletion := state.σ.setAccount selected none
    hasMaps rawDeletion [(other, relatedAccount)] storedRows &&
      rawDeletion.storageAt selected highSlot == U256.ofNat 37 &&
      hasMaps (rawDeletion.setAccount selected (some empty))
        [(other, relatedAccount), (selected, empty)] storedRows

end STFSpec.Conformance.StateFull.AccountChecks
