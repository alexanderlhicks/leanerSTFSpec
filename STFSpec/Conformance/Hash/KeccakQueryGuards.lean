/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash

/-!
# Keccak query observations

Library `EthConformance`. Recording oracles use four distinct arbitrary answers,
then fail at each query position. Both StateT/ExceptT orders expose their prescribed
success/error and retained/lost-state observations. The concrete equality to Base's
literal record is a compile-time guard, not a universal equality theorem.
The empty-code vector is the Keccak team's published Len=0 KAT (provenance in
`KeccakSpongeGuards.lean`); the other three constant facts are the actual pinned
EELS globals (authenticated by `keccak_query_differential.py`).
Spec guidance: `STFSpec/informal/modules/EthHash.md` §§3–4, 7.
-/

open STFSpec.Base STFSpec.Hash

namespace STFSpec.Conformance.Hash.KeccakQuery

private def preimages : List ByteArray :=
  [⟨#[]⟩, ⟨#[0x80]⟩, ⟨#[0xc0]⟩, ⟨#[
    84, 114, 97, 110, 115, 102, 101, 114, 40, 97, 100, 100, 114, 101, 115, 115, 44,
    97, 100, 100, 114, 101, 115, 115, 44, 117, 105, 110, 116, 50, 53, 54, 41]⟩]

private def answer (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat (17 + 31 * n))
private def answers : HashConsts := ⟨answer 0, answer 1, answer 2, answer 3⟩

private structure Trace where
  seen : List ByteArray := []
  failAt : Option Nat := none

private abbrev Recording := StateM Trace

private def record (b : ByteArray) : Recording Hash32 := fun s =>
  (answer s.seen.length, { s with seen := s.seen ++ [b] })

local instance : KeccakQuery Recording where
  keccak := record

private def fields (consts : HashConsts) : List Nat :=
  [consts.emptyCodeHash.toNat, consts.emptyTrieRoot.toNat,
    consts.emptyOmmerHash.toNat, consts.transferTopic.toNat]

-- A full recording run observes all four exact preimages and arbitrary return fields.
#guard fields ((HashConsts.query (m := Recording)).run {}).1 = [17, 48, 79, 110]
#guard ((HashConsts.query (m := Recording)).run {}).2.seen = preimages
#guard fields answers ≠ fields HashConsts.literals

-- One extra StateT and one extra ExceptT layer preserve oracle effects and their own state.
#guard let ((result, state), trace) :=
    ((HashConsts.query (m := ExceptT String (StateT Nat Recording))).run.run 91).run {}
  match result with
  | .ok consts => fields consts = [17, 48, 79, 110] && state == 91 && trace.seen == preimages
  | .error _ => false
#guard let (result, trace) :=
    ((HashConsts.query (m := StateT Nat (ExceptT String Recording))).run 91).run.run {}
  match result with
  | .ok (consts, state) =>
      fields consts = [17, 48, 79, 110] && state == 91 && trace.seen == preimages
  | .error _ => false

private def failRecording (b : ByteArray) : ExceptT Nat Recording Hash32 :=
  ExceptT.mk fun s =>
    let next := { s with seen := s.seen ++ [b] }
    if s.failAt = some s.seen.length then (.error s.seen.length, next)
    else (.ok (answer s.seen.length), next)

section RetainedState
local instance : KeccakQuery (ExceptT Nat Recording) where
  keccak := failRecording

-- ExceptT over StateT retains the exact prefix including the failing query;
-- no later queries execute. All four failure positions are observed.
#guard ([0, 1, 2, 3] : List Nat).all fun n =>
  let (result, trace) :=
    (HashConsts.query (m := ExceptT Nat Recording)).run.run { failAt := some n }
  (match result with | .error e => e == n | .ok _ => false) &&
    trace.seen == preimages.take (n + 1)

-- An added StateT above the failing oracle loses its result state on failure,
-- while the underlying Recording trace still records only the queried prefix.
#guard let (result, trace) :=
    (((HashConsts.query (m := StateT Nat (ExceptT Nat Recording))).run 91).run.run
      ({ failAt := some 2 } : Trace))
  (match result with | .error e => e == 2 | .ok _ => false) &&
    trace.seen == preimages.take 3
end RetainedState

private def failState (b : ByteArray) : StateT Trace (Except Nat) Hash32 := fun s =>
  if s.failAt = some s.seen.length then .error s.seen.length
  else .ok (answer s.seen.length, { s with seen := s.seen ++ [b] })

section LostState
local instance : KeccakQuery (StateT Trace (Except Nat)) where
  keccak := failState

-- StateT over Except exposes no state on failure; the exact intermediate error survives.
#guard ([0, 1, 2, 3] : List Nat).all fun n =>
  match (HashConsts.query (m := StateT Trace (Except Nat))).run { failAt := some n } with
  | .error e => e == n
  | .ok _ => false
#guard match (HashConsts.query (m := StateT Trace (Except Nat))).run {} with
  | .ok (consts, trace) => fields consts = [17, 48, 79, 110] && trace.seen == preimages
  | .error _ => false
end LostState

-- Concrete acquisition checked only after the accepted Keccak definition is executable.
#guard fields (HashConsts.query (m := Id)) = fields HashConsts.literals
#guard (HashConsts.query (m := Id)).emptyCodeHash.toBytes =
  HashConsts.literals.emptyCodeHash.toBytes
#guard (HashConsts.query (m := Id)).emptyTrieRoot.toBytes =
  HashConsts.literals.emptyTrieRoot.toBytes
#guard (HashConsts.query (m := Id)).emptyOmmerHash.toBytes =
  HashConsts.literals.emptyOmmerHash.toBytes
#guard (HashConsts.query (m := Id)).transferTopic.toBytes =
  HashConsts.literals.transferTopic.toBytes

end STFSpec.Conformance.Hash.KeccakQuery
