/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Account deployability controls

Private facade controls check the guided type and observe repeated calls over
transaction and block overlays and a traced provider.
Spec guidance is in `STFSpec/informal/modules/EthState.md` §§3/4/7.1.
-/

namespace STFSpec.Conformance.State.AccountDeployableGuards

open STFSpec.State STFSpec.Base

private def exactType : {m : Type → Type} → [Monad m] → Address →
    STFSpec.State.StateM m Bool := @accountDeployable

private def owner : Address := Address.ofNat (2 ^ 159 + 41)
private def other : Address := Address.ofNat 41
private def slot : Bytes32 := FixedBytes.ofNat
  0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f
private def missingHash : Hash32 := Hash32.ofBytes32
  (FixedBytes.ofNat (2 ^ 255 + 13))
private def failure : WitnessError := .missing (.node missingHash)

private abbrev Trace := StateT (List (Nat × Nat)) Id

private def provider (answer : Except WitnessError (Option Account)) : PreState Trace where
  getAccount? := fun a calls ↦ (answer, (0, a.toNat) :: calls)
  getStorage := fun a _ calls ↦ (.ok U256.zero, (1, a.toNat) :: calls)
  getCode := fun hash calls ↦ (.ok ByteArray.empty, (2, hash.toNat) :: calls)
  stateRoot := fun _ calls ↦ (.ok HashConsts.literals.emptyTrieRoot, (3, 0) :: calls)

private def balanceOnly : Account :=
  ⟨0, U256.ofNat (2 ^ 256 - 1), HashConsts.literals.emptyCodeHash⟩

private def nonceOnly : Account :=
  ⟨2 ^ 300 + 1, U256.zero, HashConsts.literals.emptyCodeHash⟩

private def codeOnly : Account :=
  ⟨0, U256.zero, Hash32.ofBytes32
    (FixedBytes.ofNat 0x45d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470)⟩

private structure Case where
  name : String
  txEntry : Option (Option Account)
  blockEntry : Option (Option Account)
  answer : Except WitnessError (Option Account)
  wanted : Option Bool

private def concreteCases : List Case :=
  let empty := emptyAccount HashConsts.literals
  let failed := Except.error failure
  [⟨"tx-tombstone", some none, some (some nonceOnly), failed, some true⟩,
   ⟨"tx-present-empty", some (some empty), some (some codeOnly), failed, some true⟩,
   ⟨"tx-balance-only", some (some balanceOnly), some (some nonceOnly), failed, some true⟩,
   ⟨"tx-nonce", some (some nonceOnly), some (some empty), failed, some false⟩,
   ⟨"tx-code", some (some codeOnly), some (some empty), failed, some false⟩,
   ⟨"block-tombstone", none, some none, failed, some true⟩,
   ⟨"block-code", none, some (some codeOnly), failed, some false⟩,
   ⟨"provider-empty", none, none, .ok none, some true⟩,
   ⟨"provider-balance", none, none, .ok (some balanceOnly), some true⟩,
   ⟨"provider-error", none, none, failed, none⟩]

private def accountWrites (entry : Option (Option Account)) : Std.ExtTreeMap Address (Option Account) :=
  match entry with
  | none => ∅
  | some value => (∅ : Std.ExtTreeMap Address (Option Account)).insert owner value

private def storageWrites (word : U256) : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256) :=
  (∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert owner
    ((∅ : Std.ExtTreeMap Bytes32 U256).insert slot word)

private def initial (consts : HashConsts) (c : Case) : TxState Trace :=
  ⟨{ BlockState.new (provider c.answer) consts with
       accountWrites := accountWrites c.blockEntry, storageWrites := storageWrites (U256.ofNat 13) },
   ⟨accountWrites c.txEntry, ⟨0, ∅, ∅⟩, storageWrites (U256.ofNat 11),
     ⟨0, ∅, ∅⟩, ∅, ∅, ∅, ∅⟩,
   ⟨(∅ : Std.HashSet Address).insert other, ∅, ∅, ∅⟩⟩

private def evaluate (t : TxState Trace) :
    Except StateError (Bool × TxState Trace) × List (Nat × Nat) :=
  (((accountDeployable owner).run t).run).run []

private def observedCall (c : Case) (calls : List (Nat × Nat)) : Bool :=
  calls == if c.txEntry.isNone && c.blockEntry.isNone then [(0, owner.toNat)] else []

private def observedResult (c : Case) (result : Except StateError (Bool × TxState Trace)) : Bool :=
  match c.wanted, result with
  | some expected, .ok (actual, next) =>
    actual == expected && next.obs.accountReads.size == 2 &&
      next.obs.accountReads.contains owner && next.obs.accountReads.contains other &&
      next.obs.storageReads.isEmpty && next.obs.codeReads.isEmpty &&
      ((next.rev.storageWrites[owner]?).bind (fun writes ↦ writes[slot]?)) == some (U256.ofNat 11) &&
      ((next.block.storageWrites[owner]?).bind (fun writes ↦ writes[slot]?)) == some (U256.ofNat 13)
  | none, .error (.witness (.missing (.node hash))) => hash == missingHash
  | _, _ => false

private def checkCase (consts : HashConsts) (c : Case) : Bool :=
  let t := initial consts c
  let (result, calls) := evaluate t
  let next := match result with
    | .ok (_, next) => next
    | .error _ => t
  let (repeated, repeatedCalls) := evaluate next
  observedCall c calls && observedResult c result &&
    observedCall c repeatedCalls && observedResult c repeated

#guard concreteCases.all (checkCase HashConsts.literals)

private def customConsts : HashConsts :=
  { HashConsts.literals with emptyCodeHash := Hash32.ofBytes32 (FixedBytes.ofNat 17) }

#guard checkCase customConsts ⟨"custom-empty", some none, none, .error failure, some true⟩
#guard checkCase customConsts
  ⟨"custom-present", some (some (emptyAccount HashConsts.literals)), none, .error failure, some false⟩

end STFSpec.Conformance.State.AccountDeployableGuards
