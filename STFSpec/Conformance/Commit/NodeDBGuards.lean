/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit

/-!
# Raw node database observations

Library `EthConformance`. Complete table values and oracle traces expose duplicate
queries, arbitrary answer collisions, failure prefixes and transformer forwarding.
These controls do not claim a collision in concrete Keccak or EEST guest execution.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` C12, §§4, 7.
-/

namespace STFSpec.Conformance.Commit.NodeDBGuards

open STFSpec.Base STFSpec.Hash STFSpec.Commit

private def key (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def entries : Array ByteArray := #[⟨#[]⟩, ⟨#[0xff]⟩, ⟨#[]⟩, ⟨#[0x80, 0x00]⟩]

private structure Trace where
  seen : List ByteArray := []
  failAt : Option Nat := none
  collide : Bool := false

private abbrev Recording := StateM Trace
private def query (b : ByteArray) : Recording Hash32 := fun s =>
  (key (if s.collide then 2^255 + 7 else 2^(64 * s.seen.length) + 7),
    { s with seen := s.seen ++ [b] })

local instance : KeccakQuery Recording where
  keccak := query

#guard let (db, trace) := (NodeDB.build (m := Recording) #[]).run {}
  db.map.size == 0 && trace.seen == []
#guard let (db, trace) := (NodeDB.build (m := Recording) entries).run {}
  db.map.size == 4 && trace.seen == entries.toList &&
    db.map[key 8]? == some ⟨#[]⟩ && db.map[key (2^64 + 7)]? == some ⟨#[0xff]⟩ &&
    db.map[key (2^128 + 7)]? == some ⟨#[]⟩ &&
    db.map[key (2^192 + 7)]? == some ⟨#[0x80, 0x00]⟩
#guard let (db, trace) := (NodeDB.build (m := Recording) entries).run { collide := true }
  db.map.size == 1 && db.map[key (2^255 + 7)]? == some ⟨#[0x80, 0x00]⟩ &&
    trace.seen == entries.toList
#guard let ((result, state), trace) :=
    ((NodeDB.build (m := ExceptT String (StateT Nat Recording)) entries).run.run 91).run {}
  match result with
  | .ok db => db.map.size == 4 && state == 91 && trace.seen == entries.toList
  | .error _ => false
#guard let (result, trace) :=
    ((NodeDB.build (m := StateT Nat (ExceptT String Recording)) entries).run 91).run.run {}
  match result with
  | .ok (db, state) => db.map.size == 4 && state == 91 && trace.seen == entries.toList
  | .error _ => false

private def failing (b : ByteArray) : ExceptT Nat Recording Hash32 :=
  ExceptT.mk fun s =>
    let next := { s with seen := s.seen ++ [b] }
    if s.failAt = some s.seen.length then (.error s.seen.length, next)
    else (.ok (key (2^(64 * s.seen.length) + 7)), next)

section Failure
local instance : KeccakQuery (ExceptT Nat Recording) where
  keccak := failing

#guard ([0, 1, 2, 3] : List Nat).all fun n =>
  let (result, trace) :=
    (NodeDB.build (m := ExceptT Nat Recording) entries).run.run { failAt := some n }
  (match result with | .error e => e == n | .ok _ => false) &&
    trace.seen == entries.toList.take (n + 1)
#guard let (result, trace) :=
    (((NodeDB.build (m := StateT Nat (ExceptT Nat Recording)) entries).run 91).run.run
      ({ failAt := some 2 } : Trace))
  (match result with | .error e => e == 2 | .ok _ => false) &&
    trace.seen == entries.toList.take 3
end Failure

private def failingState (b : ByteArray) : StateT Trace (Except Nat) Hash32 := fun s =>
  if s.failAt = some s.seen.length then .error s.seen.length
  else .ok (key s.seen.length, { s with seen := s.seen ++ [b] })

section LostState
local instance : KeccakQuery (StateT Trace (Except Nat)) where
  keccak := failingState

#guard ([0, 1, 2, 3] : List Nat).all fun n =>
  match (NodeDB.build (m := StateT Trace (Except Nat)) entries).run { failAt := some n } with
  | .error e => e == n
  | .ok _ => false
end LostState

-- Concrete construction preserves empty and malformed raw values, duplicates and misses.
#guard let raw : ByteArray := ⟨#[0xff]⟩
  let db := NodeDB.build (m := Id) #[raw, raw]
  db.map.size == 1 && db.map[keccak256 raw]? == some raw && db.map[key 0]? == none
#guard let raw : ByteArray := ⟨#[]⟩
  (NodeDB.build (m := Id) #[raw]).map[keccak256 raw]? == some raw

end STFSpec.Conformance.Commit.NodeDBGuards
