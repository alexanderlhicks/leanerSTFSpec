/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.PreState
import STFSpec.Conformance.State.BlockDiffGuards

/-!
# Complete raw provider callback values

Library `EthConformance`: callback carriers preserve complete values and inputs,
including nominal errors and all seven raw diff fields. No backend operation is modeled.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/7.
-/

namespace STFSpec.Conformance.State.PreStateGuards

open STFSpec.Base STFSpec.State

/-- Complete error tag, item tag and hash-byte payload; leaf has no payload. -/
private abbrev ErrorValue := Nat × Nat × List Nat

private def errorValue : WitnessError → ErrorValue
  | .missing (.node h) => (0, 0, BlockDiffGuards.hashBytes h)
  | .missing (.code h) => (0, 1, BlockDiffGuards.hashBytes h)
  | .missing .leaf => (0, 2, [])
  | .malformed (.node h) => (1, 0, BlockDiffGuards.hashBytes h)
  | .malformed (.code h) => (1, 1, BlockDiffGuards.hashBytes h)
  | .malformed .leaf => (1, 2, [])
  | .unresolved h => (2, 3, BlockDiffGuards.hashBytes h)

private def resultValue {α β : Type} (f : α → β) :
    Except WitnessError α → Option ErrorValue × Option β
  | .ok x => (none, some (f x))
  | .error e => (some (errorValue e), none)

private def payloadHash (seed : Nat) : Hash32 :=
  BlockDiffGuards.hash (BlockDiffGuards.keyNumber 32 seed)

private def suppliedError (seed : Nat) : WitnessError :=
  let h := payloadHash seed
  match seed % 7 with
  | 0 => .missing (.node h)
  | 1 => .missing (.code h)
  | 2 => .missing .leaf
  | 3 => .malformed (.node h)
  | 4 => .malformed (.code h)
  | 5 => .malformed .leaf
  | _ => .unresolved h

private def expectedError (seed : Nat) : ErrorValue :=
  let bytes := (List.range 32).map (fun i ↦ (i * 37 + seed) % 256)
  match seed % 7 with
  | 0 => (0, 0, bytes)
  | 1 => (0, 1, bytes)
  | 2 => (0, 2, [])
  | 3 => (1, 0, bytes)
  | 4 => (1, 1, bytes)
  | 5 => (1, 2, [])
  | _ => (2, 3, bytes)

private def suppliedAccount (seed : Nat) : Except WitnessError (Option Account) :=
  match seed % 4 with
  | 0 => .ok none
  | 1 => .ok (some (emptyAccount ⟨payloadHash seed, payloadHash 0,
      payloadHash 1, payloadHash 2⟩))
  | 2 => .ok (some ⟨2^1024 + seed, U256.max, payloadHash seed⟩)
  | _ => .error (suppliedError seed)

private def suppliedStorage (seed : Nat) : Except WitnessError U256 :=
  match seed % 3 with
  | 0 => .ok U256.zero
  | 1 => .ok U256.max
  | _ => .error (suppliedError seed)

private def suppliedCode (seed : Nat) : Except WitnessError ByteArray :=
  match seed % 3 with
  | 0 => .ok ByteArray.empty
  | 1 => .ok (BlockDiffGuards.bytesFor (65 + seed) seed)
  | _ => .error (suppliedError seed)

private def suppliedRoot (seed : Nat) : Except WitnessError Hash32 :=
  if seed % 2 == 0 then .ok (payloadHash seed) else .error (suppliedError seed)

/-- A type constructor carrying complete callback inputs; no Monad instance is installed. -/
private abbrev Captured (α : Type) :=
  List Nat × List Nat × Option BlockDiffGuards.Observation × α

private def callbacks (seed : Nat) : PreState Captured where
  getAccount? a := (BlockDiffGuards.addressBytes a, [], none, suppliedAccount seed)
  getStorage a k :=
    (BlockDiffGuards.addressBytes a, BlockDiffGuards.slotBytes k, none, suppliedStorage seed)
  getCode h := (BlockDiffGuards.hashBytes h, [], none, suppliedCode seed)
  stateRoot d := ([], [], some (BlockDiffGuards.observe d), suppliedRoot seed)

/-- Complete observed callback families, retaining all input and result tags. -/
private abbrev Observation :=
  List (Captured (Option ErrorValue × Option (Option (Nat × Nat × List Nat)))) ×
  List (Captured (Option ErrorValue × Option Nat)) ×
  List (Captured (Option ErrorValue × Option (List Nat))) ×
  List (Captured (Option ErrorValue × Option (List Nat)))

private def capturedValue {α β : Type} (f : α → β) (x : Captured α) : Captured β :=
  (x.1, x.2.1, x.2.2.1, f x.2.2.2)

private def addresses : List Address :=
  [Address.ofNat 0, Address.ofNat (BlockDiffGuards.keyNumber 20 255),
   Address.ofNat (BlockDiffGuards.keyNumber 20 1)]

private def slots : List Bytes32 :=
  [FixedBytes.ofNat 0, FixedBytes.ofNat (BlockDiffGuards.keyNumber 32 255),
   FixedBytes.ofNat (BlockDiffGuards.keyNumber 32 1)]

private def hashes : List Hash32 := [payloadHash 0, payloadHash 255, payloadHash 1]

private def models : List BlockDiffGuards.Model :=
  BlockDiffGuards.variations ++ (List.range 2).map BlockDiffGuards.indexedModel

private def observe (ps : PreState Captured) : Observation :=
  (addresses.map (fun a ↦ capturedValue (resultValue (Option.map BlockDiffGuards.accountValue))
      (ps.getAccount? a)),
   addresses.flatMap (fun a ↦ slots.map (fun k ↦
      capturedValue (resultValue U256.toNat) (ps.getStorage a k))),
   hashes.map (fun h ↦ capturedValue (resultValue BlockDiffGuards.codeBytes) (ps.getCode h)),
   models.map (fun model ↦ capturedValue (resultValue BlockDiffGuards.hashBytes)
      (ps.stateRoot (BlockDiffGuards.build model))))

private def expectedAccount (seed : Nat) :
    Option ErrorValue × Option (Option (Nat × Nat × List Nat)) :=
  match seed % 4 with
  | 0 => (none, some none)
  | 1 => (none, some (some (0, 0, (List.range 32).map (fun i ↦ (i * 37 + seed) % 256))))
  | 2 => (none, some (some (2^1024 + seed, 2^256 - 1,
      (List.range 32).map (fun i ↦ (i * 37 + seed) % 256))))
  | _ => (some (expectedError seed), none)

private def expectedStorage (seed : Nat) : Option ErrorValue × Option Nat :=
  match seed % 3 with
  | 0 => (none, some 0)
  | 1 => (none, some (2^256 - 1))
  | _ => (some (expectedError seed), none)

private def expectedCode (seed : Nat) : Option ErrorValue × Option (List Nat) :=
  match seed % 3 with
  | 0 => (none, some [])
  | 1 => (none, some ((List.range (65 + seed)).map (fun i ↦ (i * 37 + seed) % 256)))
  | _ => (some (expectedError seed), none)

private def expectedRoot (seed : Nat) : Option ErrorValue × Option (List Nat) :=
  if seed % 2 == 0 then (none, some ((List.range 32).map (fun i ↦ (i * 37 + seed) % 256)))
  else (some (expectedError seed), none)

private def expected (seed : Nat) : Observation :=
  (addresses.map (fun a ↦ (BlockDiffGuards.addressBytes a, [], none, expectedAccount seed)),
   addresses.flatMap (fun a ↦ slots.map (fun k ↦
      (BlockDiffGuards.addressBytes a, BlockDiffGuards.slotBytes k, none, expectedStorage seed))),
   hashes.map (fun h ↦ (BlockDiffGuards.hashBytes h, [], none, expectedCode seed)),
   models.map (fun model ↦ ([], [], some (BlockDiffGuards.expected model), expectedRoot seed)))

/-- Check every nominal error constructor with its complete payload and an independent list. -/
def nominal : Bool :=
  (List.range 21).all (fun seed ↦ errorValue (suppliedError seed) == expectedError seed)

/-- Complete parent and independently replaced sibling callbacks, observed again after sharing. -/
def cases : List (String × Observation × Observation) :=
  (List.range 21).flatMap (fun seed ↦
    let parent := callbacks seed
    let left := {parent with getCode := (callbacks (seed + 1)).getCode}
    let right := {parent with stateRoot := (callbacks (seed + 2)).stateRoot}
    let want := expected seed
    let leftWant := (want.1, want.2.1, (expected (seed + 1)).2.2.1, want.2.2.2)
    let rightWant := (want.1, want.2.1, want.2.2.1, (expected (seed + 2)).2.2.2)
    [(s!"{seed}:parent", observe parent, want),
     (s!"{seed}:left", observe left, leftWant),
     (s!"{seed}:right", observe right, rightWant),
     (s!"{seed}:parent-again", observe parent, want),
     (s!"{seed}:left-again", observe left, leftWant),
     (s!"{seed}:right-again", observe right, rightWant)])

/-- Compare complete captured inputs and results, without a backend/default interpretation. -/
private def capturedEq {α : Type} [BEq α] (a b : Captured α) : Bool :=
  a.1 == b.1 && a.2.1 == b.2.1 && a.2.2.1 == b.2.2.1 && a.2.2.2 == b.2.2.2

/-- Compare every field separately under ordinary instance-search limits. -/
def equal (a b : Observation) : Bool :=
  a.1.isEqv b.1 capturedEq && a.2.1.isEqv b.2.1 capturedEq &&
  a.2.2.1.isEqv b.2.2.1 capturedEq && a.2.2.2.isEqv b.2.2.2 capturedEq

private def capturedRepr {α : Type} [Repr α] (a : Captured α) : String :=
  s!"({reprStr a.1}, {reprStr a.2.1}, {reprStr a.2.2.1}, {reprStr a.2.2.2})"

/-- Render complete callback values with each argument and result intact. -/
def render (a : Observation) : String :=
  s!"({reprStr (a.1.map capturedRepr)}, {reprStr (a.2.1.map capturedRepr)}, " ++
  s!"{reprStr (a.2.2.1.map capturedRepr)}, {reprStr (a.2.2.2.map capturedRepr)})"

/-- Complete nominal and callback equality, without increasing elaboration limits. -/
def guards : Bool := nominal && cases.all (fun row ↦ equal row.2.1 row.2.2)

#guard cases.length == 126
#guard guards

end STFSpec.Conformance.State.PreStateGuards
