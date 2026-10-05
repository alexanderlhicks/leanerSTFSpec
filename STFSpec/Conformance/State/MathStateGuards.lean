/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.MathState

/-!
# Raw MathState observations and independent invariant omissions

Library `EthConformance`: finite complete-value guards and symbolic counterexamples.
No executable `WF` test enumerates the address or slot universe.
Spec guidance: `STFSpec/informal/modules/EthState.md`.
-/

namespace STFSpec.Conformance.State.MathStateGuards

open STFSpec.Base STFSpec.State

private theorem single_lookup {K V : Type} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
    [DecidableEq K]
    (key other : K) (value : V) :
    ((∅ : Std.ExtTreeMap K V).insert key value)[other]? =
      if key = other then some value else none := by
  rw [Std.ExtTreeMap.getElem?_insert]
  simp only [Std.compare_eq_iff_eq, Std.ExtTreeMap.getElem?_empty]

private theorem inner_nonempty (k : Bytes32) (v : U256) :
    ((∅ : Std.ExtTreeMap Bytes32 U256).insert k v).isEmpty = false :=
  Std.ExtTreeMap.isEmpty_eq_false_iff.mpr Std.ExtTreeMap.insert_ne_empty

/-- A stored zero violates exactly the nonzero clause; the other two clauses hold. -/
theorem zero_omission (consts : HashConsts) (a : Address) (k : Bytes32) :
    let σ : MathState := ⟨(∅ : Std.ExtTreeMap Address Account).insert a (emptyAccount consts),
      (∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert a
        ((∅ : Std.ExtTreeMap Bytes32 U256).insert k U256.zero), ∅⟩
    (¬MathState.WF σ) ∧
      (∀ (b : Address) (slots : Std.ExtTreeMap Bytes32 U256),
        σ.storage[b]? = some slots → slots.isEmpty = false) ∧
      (∀ (b : Address) (slots : Std.ExtTreeMap Bytes32 U256),
        σ.storage[b]? = some slots → σ.accounts[b]?.isSome = true) := by
  dsimp
  constructor
  · intro hw
    exact MathState.wf_storage_value_ne_zero _ a _ k U256.zero hw
      Std.ExtTreeMap.getElem?_insert_self Std.ExtTreeMap.getElem?_insert_self rfl
  · constructor
    · intro b slots hs
      rw [single_lookup] at hs
      split at hs
      · cases hs
        exact inner_nonempty k U256.zero
      · cases hs
    · intro b slots hs
      rw [single_lookup] at hs
      split at hs
      · rename_i hab
        subst b
        simp
      · cases hs

/-- A stored empty inner map violates exactly the nonempty clause. -/
theorem empty_inner_omission (consts : HashConsts) (a : Address) :
    let σ : MathState := ⟨(∅ : Std.ExtTreeMap Address Account).insert a (emptyAccount consts),
      (∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert a ∅, ∅⟩
    (¬MathState.WF σ) ∧
      (∀ (b : Address) (slots : Std.ExtTreeMap Bytes32 U256), σ.storage[b]? = some slots →
        ∀ (k : Bytes32) (v : U256), slots[k]? = some v → v ≠ U256.zero) ∧
      (∀ (b : Address) (slots : Std.ExtTreeMap Bytes32 U256),
        σ.storage[b]? = some slots → σ.accounts[b]?.isSome = true) := by
  dsimp
  constructor
  · intro hw
    have hn := MathState.wf_storage_nonempty _ a ∅ hw Std.ExtTreeMap.getElem?_insert_self
    simp at hn
  · constructor
    · intro b slots hs
      rw [single_lookup] at hs
      split at hs
      · cases hs
        simp
      · cases hs
    · intro b slots hs
      rw [single_lookup] at hs
      split at hs
      · rename_i hab
        subst b
        simp
      · cases hs

/-- Orphan nonzero storage violates exactly the account-domain clause and remains observable. -/
theorem orphan_omission (a : Address) (k : Bytes32) (v : U256) (hv : v ≠ U256.zero) :
    let σ : MathState := ⟨∅,
      (∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert a
        ((∅ : Std.ExtTreeMap Bytes32 U256).insert k v), ∅⟩
    (¬MathState.WF σ) ∧
      (∀ (b : Address) (slots : Std.ExtTreeMap Bytes32 U256), σ.storage[b]? = some slots →
        ∀ (j : Bytes32) (w : U256), slots[j]? = some w → w ≠ U256.zero) ∧
      (∀ (b : Address) (slots : Std.ExtTreeMap Bytes32 U256),
        σ.storage[b]? = some slots → slots.isEmpty = false) ∧
      σ.account? a = none ∧ σ.storageAt a k = v := by
  dsimp
  constructor
  · intro hw
    exact MathState.wf_storage_account_present _ a _ hw
      Std.ExtTreeMap.getElem?_insert_self (by simp [MathState.account?_eq_lookup])
  · constructor
    · intro b slots hs
      rw [single_lookup] at hs
      split at hs
      · cases hs
        intro j w hj
        rw [single_lookup] at hj
        split at hj
        · cases hj
          exact hv
        · cases hj
      · cases hs
    · constructor
      · intro b slots hs
        rw [single_lookup] at hs
        split at hs
        · cases hs
          exact inner_nonempty k v
        · cases hs
      · constructor
        · simp [MathState.account?_eq_lookup]
        · exact MathState.storageAt_of_slot_some _ a k _ v
            Std.ExtTreeMap.getElem?_insert_self Std.ExtTreeMap.getElem?_insert_self

/-- Fixed-constants code observations can agree on distinct raw states, even under `WF`. -/
theorem hidden_code_counterexample (consts : HashConsts) (bytes : ByteArray) :
    let σ : MathState := ⟨∅, ∅, ∅⟩
    let τ : MathState := ⟨∅, ∅,
      (∅ : Std.ExtTreeMap Hash32 ByteArray).insert consts.emptyCodeHash bytes⟩
    MathState.WF σ ∧ MathState.WF τ ∧ σ ≠ τ ∧
      (∀ a, σ.account? a = τ.account? a) ∧
      (∀ a k, σ.storageAt a k = τ.storageAt a k) ∧
      (∀ h, σ.code? consts h = τ.code? consts h) := by
  dsimp
  refine ⟨MathState.wf_empty, ?_, ?_, ?_, ?_, ?_⟩
  · simp [MathState.WF]
  · intro he
    have hc := congrArg (fun s : MathState ↦ s.code[consts.emptyCodeHash]?) he
    simp at hc
  · intro a
    rfl
  · intro a k
    rfl
  · intro h
    by_cases hh : h = consts.emptyCodeHash
    · subst h
      rw [MathState.code?_empty, MathState.code?_empty]
    · rw [MathState.code?_of_ne _ _ _ hh, MathState.code?_of_ne _ _ _ hh,
        single_lookup]
      simp [Ne.symm hh]

private def hash (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def slot (n : Nat) : Bytes32 := FixedBytes.ofNat n
private def address (n : Nat) : Address := Address.ofNat n
private def bytes (xs : List UInt8) : ByteArray := (Bytes.ofList xs).toByteArray

/-- Complete account observation without truncation. -/
def observeAccount (x : Account) : Nat × Nat × List UInt8 :=
  (x.nonce, x.balance.toNat, x.codeHash.toBytes.toList)

/-- Complete raw fields, including zero slots, empty inners and hidden code entries. -/
def observeRaw (σ : MathState) :
    List (List UInt8 × (Nat × Nat × List UInt8)) ×
    List (List UInt8 × List (List UInt8 × Nat)) × List (List UInt8 × List UInt8) :=
  (σ.accounts.toList.map (fun (a, x) ↦ (a.toBytes.toList, observeAccount x)),
    σ.storage.toList.map (fun (a, slots) ↦
      (a.toBytes.toList, slots.toList.map (fun (k, v) ↦ (k.toBytes.toList, v.toNat)))),
    σ.code.toList.map (fun (h, b) ↦ (h.toBytes.toList, b.toList)))

/-- Query keys cover every byte, leading zeros, high bytes and first/last mismatches. -/
def addresses : List Address :=
  [address 0, address 1, address (2 ^ 152), address (2 ^ 160 - 1),
    address ((List.range 20).foldl (fun n i ↦ 256 * n + i) 0)]

/-- Slot-domain keys retain every complete 32-byte value. -/
def slots : List Bytes32 :=
  [slot 0, slot 1, slot (2 ^ 248), slot (2 ^ 256 - 1),
    slot ((List.range 32).foldl (fun n i ↦ 256 * n + i) 0)]

/-- Code-hash keys use the distinct public Hash32 domain. -/
def hashes : List Hash32 := slots.map Hash32.ofBytes32

/-- An arbitrary nonliteral empty-code hash and unrelated remaining fields. -/
def constants : HashConsts := ⟨hash 1, hash (2 ^ 248), hash 0, hash (2 ^ 256 - 1)⟩

private def huge : Account := ⟨2 ^ 1024 + 17, U256.max, hash (2 ^ 248)⟩
private def accounts : Std.ExtTreeMap Address Account :=
  (∅ : Std.ExtTreeMap Address Account).insert (address 1) (emptyAccount constants) |>.insert
    (address (2 ^ 152)) huge
private def values : Std.ExtTreeMap Bytes32 U256 :=
  (∅ : Std.ExtTreeMap Bytes32 U256).insert (slot 1) U256.one |>.insert
    (slot (2 ^ 248)) U256.max
private def parent : MathState := ⟨accounts,
  (∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert (address 1) values,
  (∅ : Std.ExtTreeMap Hash32 ByteArray).insert (hash 0) ByteArray.empty |>.insert
    (hash (2 ^ 248)) (bytes [0, 128, 255, 0])⟩
private def left : MathState := ⟨parent.accounts.insert (address 0) huge,
  parent.storage.insert (address 0) ((∅ : Std.ExtTreeMap Bytes32 U256).insert (slot 0) U256.zero),
  parent.code.insert constants.emptyCodeHash (bytes [255, 128, 1])⟩
private def right : MathState := ⟨parent.accounts,
  parent.storage.insert (address (2 ^ 160 - 1)) ∅,
  parent.code.insert (hash (2 ^ 256 - 1)) (bytes (List.range 256 |>.map UInt8.ofNat))⟩

/-- Retained parents and independent siblings, plus empty/zero/orphan/hidden raw cases. -/
def samples : List MathState :=
  [⟨∅, ∅, ∅⟩, parent, left, right, parent, left, right,
    ⟨∅, ∅, (∅ : Std.ExtTreeMap Hash32 ByteArray).insert constants.emptyCodeHash ByteArray.empty⟩,
    ⟨∅, (∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert (address 1) values, ∅⟩]

/-- Complete optional account/code answers and storage words for the chosen full keys. -/
def observe (σ : MathState) (consts : HashConsts) :=
  (observeRaw σ, addresses.map (fun a ↦ (σ.account? a).map observeAccount),
    addresses.map (fun a ↦ slots.map (fun k ↦ (σ.storageAt a k).toNat)),
    hashes.map (fun h ↦ (σ.code? consts h).map ByteArray.toList))

#guard (left.code[constants.emptyCodeHash]?).map ByteArray.toList = some [255, 128, 1]
#guard left.code? constants constants.emptyCodeHash = some ByteArray.empty
#guard (parent.code? constants (hash 0)).map ByteArray.toList = some []
#guard parent.code? constants (hash (2 ^ 256 - 1)) = none
#guard parent.account? (address 0) = none
#guard parent.account? (address 1) = some (emptyAccount constants)
#guard (parent.account? (address (2 ^ 152))).map observeAccount =
  some (2 ^ 1024 + 17, 2 ^ 256 - 1, 1 :: List.replicate 31 0)
#guard (left.storage[address 0]?).isSome = true
#guard left.storageAt (address 0) (slot 0) = U256.zero
#guard (right.storage[address (2 ^ 160 - 1)]?).map Std.ExtTreeMap.isEmpty = some true
#guard ((samples.map (fun σ ↦ observe σ constants)).take 4).drop 1 ==
  ((samples.map (fun σ ↦ observe σ constants)).drop 4).take 3
#guard addresses.map (fun a ↦ Address.ofNat a.toNat) = addresses
#guard slots.map (fun k ↦ FixedBytes.ofNat k.toNat) = slots
#guard hashes.map (fun h ↦ Hash32.ofBytes32 (FixedBytes.ofNat h.toNat)) = hashes
#guard (hashes.map (fun h ↦ (parent.code? constants h).map ByteArray.toList)) =
  hashes.map (fun h ↦
    (parent.code? ⟨constants.emptyCodeHash, hash 99, hash 100, hash 101⟩ h).map ByteArray.toList)

end STFSpec.Conformance.State.MathStateGuards
