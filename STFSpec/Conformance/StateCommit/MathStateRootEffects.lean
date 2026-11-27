/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit

/-!
# Mathematical state root query effects

Library `EthConformance`. A synthetic oracle records complete preimages and can
fail at each reached occurrence. The controls compare the complete maps and
verify the storage-root query before the account key.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` SC4 and §7.2.
-/

namespace STFSpec.Conformance.StateCommit.MathStateRootEffects

open STFSpec.Base STFSpec.Codec STFSpec.Commit STFSpec.Hash STFSpec.State STFSpec.StateCommit

example {m : Type → Type} [Monad m] [KeccakQuery m] (consts : HashConsts) (σ : MathState)
    (code : Std.ExtTreeMap Hash32 ByteArray) :
    mathStateRoot (m := m) consts { σ with code := code } = mathStateRoot consts σ := rfl

private abbrev Observed := ExceptT Nat (StateM (List ByteArray))
private def answer : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat 77)
private def suppliedEmpty : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat 22)
private def consts : HashConsts := { HashConsts.literals with emptyTrieRoot := suppliedEmpty }
private def path : Nibbles := bytesToNibbleList answer.toBytes.toByteArray

private abbrev oracle (stop : Option Nat) : KeccakQuery Observed :=
  ⟨fun input ↦ ExceptT.mk fun seen ↦
    let result := if stop = some seen.length then Except.error seen.length else Except.ok answer
    (result, seen ++ [input])⟩

private def first : Address := Address.ofNat 17
private def second : Address := Address.ofNat 33
private def orphan : Address := Address.ofNat 49
private def slot (n : Nat) : Bytes32 := FixedBytes.ofNat n
private def slotPreimage (n : Nat) : ByteArray := (slot n).toBytes.toByteArray
private def firstAccount : Account := ⟨1, U256.ofNat 19, consts.emptyCodeHash⟩
private def secondAccount : Account := ⟨2, U256.ofNat 53, consts.emptyCodeHash⟩
private def emptyState : MathState := ⟨∅, ∅, ∅⟩

private def entries : Std.ExtTreeMap Bytes32 U256 :=
  ((∅ : Std.ExtTreeMap Bytes32 U256).insert (slot 11) (U256.ofNat 13))
    |>.insert (slot 6) U256.zero
    |>.insert (slot 5) (U256.ofNat 7)

private def state : MathState where
  accounts := ((∅ : Std.ExtTreeMap Address Account).insert second secondAccount).insert first firstAccount
  storage := ((∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert first entries).insert
    orphan ((∅ : Std.ExtTreeMap Bytes32 U256).insert (slot 19) (U256.ofNat 23))
  code := (∅ : Std.ExtTreeMap Hash32 ByteArray).insert answer ⟨#[1, 2, 3]⟩

private def leafPreimage (value : ByteArray) : ByteArray :=
  Rlp.encode (assembleInternalNode (some (.leaf path (.bytes value))))

private def slotQueries : List ByteArray := [slotPreimage 5, slotPreimage 11]
private def slotLeaf : ByteArray := encodeStorage (U256.ofNat 13)
private def accountLeaf : ByteArray := encodeAccount secondAccount suppliedEmpty
private def accountQueries : List ByteArray :=
  slotQueries ++ [leafPreimage slotLeaf, first.toBytes.toByteArray, second.toBytes.toByteArray]

private def slotsMatch : Bool :=
  letI : KeccakQuery Observed := oracle none
  let (result, seen) := (storageTrieMap (m := Observed) state first).run.run []
  match result with
  | .ok prepared => prepared.toList == [(path, slotLeaf)] && seen == slotQueries
  | .error _ => false

private def accountsMatch : Bool :=
  letI : KeccakQuery Observed := oracle none
  let (result, seen) := (accountTrieMap (m := Observed) consts state).run.run []
  match result with
  | .ok prepared => prepared.toList == [(path, accountLeaf)] && seen == accountQueries
  | .error _ => false

private def rootRun (σ : MathState) (stop : Option Nat) : Except Nat Hash32 × List ByteArray :=
  letI : KeccakQuery Observed := oracle stop
  (mathStateRoot (m := Observed) consts σ).run.run []

private def rootMatches (actual : Except Nat Hash32 × List ByteArray)
    (expected : Except Nat Hash32) (queries : List ByteArray) : Bool :=
  let answersAgree := match actual.1, expected with
    | .ok root, .ok expectedRoot => root == expectedRoot
    | .error failure, .error expectedFailure => failure == expectedFailure
    | _, _ => false
  answersAgree && actual.2 == queries

private def orphanRootMatches : Bool :=
  letI : KeccakQuery Observed := oracle none
  rootMatches ((storageRoot (m := Observed) consts state orphan).run.run []) (.ok answer)
    [slotPreimage 19, leafPreimage (encodeStorage (U256.ofNat 23))]

private def completeQueries : List ByteArray := accountQueries ++ [leafPreimage accountLeaf]

#guard slotsMatch
#guard accountsMatch
#guard orphanRootMatches
#guard rootMatches (rootRun emptyState (some 0)) (.ok suppliedEmpty) []
#guard rootMatches (rootRun state none) (.ok answer) completeQueries
#guard (List.range completeQueries.length).all (fun i ↦
  rootMatches (rootRun state (some i)) (.error i) (completeQueries.take (i + 1)))

end STFSpec.Conformance.StateCommit.MathStateRootEffects
