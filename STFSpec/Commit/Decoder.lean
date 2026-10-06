/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Commit.IncrementalMPT
import STFSpec.Commit.NodeDB
import STFSpec.Commit.Compact
import Std.Data.HashSet.Lemmas

/-!
# Complete eager witness decoding

Library `EthCommit`. Pinned EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:892–1040`.
Actual query answers and original raw encodings are retained. Database keys detect
current-path cycles; siblings remain independent occurrences. The two termination
measures occur only in proofs, imposing no runtime bound or admission predicate.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` C13–C17; Q55.
-/

namespace STFSpec.Commit
open STFSpec.Base STFSpec.Hash STFSpec.Codec

private theorem remaining_insert_lt (db : NodeDB) (path : Std.HashSet Hash32)
    (key : Hash32) (present : db.map.contains key = true)
    (fresh : path.contains key = false) :
    (db.map.keys.filter (fun k => !(path.insert key).contains k)).length <
      (db.map.keys.filter (fun k => !path.contains k)).length := by
  have hkeys : db.map.keys.contains key = true := by
    rw [Std.HashMap.contains_keys]
    exact present
  obtain ⟨k, hk, hbeq⟩ := List.contains_iff_exists_mem_beq.mp hkeys
  have hkfresh : path.contains k = false := by
    rw [← Std.HashSet.contains_congr hbeq]
    exact fresh
  have hkmem : k ∈ db.map.keys.filter (fun k => !path.contains k) :=
    List.mem_filter.mpr ⟨hk, by simp only [hkfresh, Bool.not_false]⟩
  have filter_eq :
      (db.map.keys.filter (fun k => !path.contains k)).filter (fun k => !(key == k)) =
        db.map.keys.filter (fun k => !(path.insert key).contains k) := by
    rw [List.filter_filter]
    congr 1
    funext k
    simp only [Std.HashSet.contains_insert, Bool.not_or]
  rw [← filter_eq]
  have hle := List.length_filter_le (fun k => !(key == k))
    (db.map.keys.filter (fun k => !path.contains k))
  have hne : ((db.map.keys.filter (fun k => !path.contains k)).filter
      (fun k => !(key == k))).length ≠
      (db.map.keys.filter (fun k => !path.contains k)).length := by
    intro heq
    have hkeep := List.length_filter_eq_length_iff.mp heq k hkmem
    simp only [hbeq, Bool.not_true, Bool.false_eq_true] at hkeep
  omega

private theorem inserted_key_on_path (onPath : Std.HashSet Hash32) (key : Hash32) :
    (onPath.insert key).contains key = true := by
  simp [Std.HashSet.contains_insert]

private theorem ancestor_stays_on_path (onPath : Std.HashSet Hash32)
    (key ancestor : Hash32) (present : onPath.contains ancestor = true) :
    (onPath.insert key).contains ancestor = true := by
  simp [Std.HashSet.contains_insert, present]

/-- Continuation form preserves the exact plain-Monad bind tree. -/
private def acquire {m : Type → Type} [Monad m] [KeccakQuery m]
    (raw : ByteArray) (next : Option Hash32 → m (Except TrieError Ref)) :
    m (Except TrieError Ref) :=
  if raw.size < 32 then next none else do
    let answer ← KeccakQuery.keccak raw
    next (some answer)

private def resolveChildren {m : Type → Type} [Monad m]
    (items : List RlpItem)
    (resolve : (item : RlpItem) → item ∈ items → m (Except TrieError Ref)) :
    m (Except TrieError (List Ref)) :=
  match items with
  | [] => pure (.ok [])
  | item :: rest => do
    let head ← resolve item List.mem_cons_self
    match head with
    | .error error => pure (.error error)
    | .ok child =>
      let tail ← resolveChildren rest (fun x hx => resolve x (List.mem_cons_of_mem item hx))
      pure (tail.map (child :: ·))

private def resolveRef {m : Type → Type} [Monad m] (db : NodeDB)
    (item : RlpItem)
    (entry : (key : Hash32) → (raw : ByteArray) → db.map[key]? = some raw →
      m (Except TrieError Ref))
    (inline : (xs : List RlpItem) → item = .list xs → m (Except TrieError Ref)) :
    m (Except TrieError Ref) :=
  match item with
  | .bytes bytes =>
    if bytes.size = 0 then pure (.ok none) else
      match Hash32.ofBytes? (Bytes.ofByteArray bytes) with
      | none => pure (.error (.malformed (.refLength bytes.size)))
      | some key =>
        match h : db.map[key]? with
        | none => pure (.ok (some (.hashed key)))
        | some raw => entry key raw h
  | .list xs => inline xs rfl

private theorem child_encodable (xs : List RlpItem) (hx : Rlp.Encodable (.list xs))
    (item : RlpItem) (hm : item ∈ xs) : Rlp.Encodable item :=
  (Rlp.encodable_list_iff xs).mp hx |>.1 item hm

private def interpret {m : Type → Type} [Monad m] [KeccakQuery m]
    (db : NodeDB)
    (entry : (key : Hash32) → (raw : ByteArray) → db.map[key]? = some raw →
      m (Except TrieError Ref))
    (item : RlpItem) (hx : Rlp.Encodable item) (enc : Enc) :
    m (Except TrieError Ref) :=
  match item with
  | .bytes bytes =>
    if bytes.size = 0 then pure (.ok none)
    else pure (.error (.malformed .nonEmptyString))
  | .list xs =>
    let resolve : (child : RlpItem) → child ∈ xs → m (Except TrieError Ref) :=
      fun child hm =>
      resolveRef db child entry fun ys heq =>
        acquire (Rlp.encode (.list ys)) fun childHash =>
          match hparse : Rlp.decode (Rlp.encode (.list ys)) with
          | .error _ => False.elim (by
              have hi := Rlp.decode_encode child (child_encodable xs hx child hm)
              rw [heq] at hi
              rw [hi] at hparse
              contradiction)
          | .ok parsed =>
            interpret db entry parsed
              (Rlp.decode_success_encodable (Rlp.encode (.list ys)) parsed hparse)
              ⟨Rlp.encode (.list ys), childHash⟩
    match hxs : xs with
    | [pathItem, valueItem] =>
      match pathItem with
      | .list _ => pure (.error (.malformed .compactPathList))
      | .bytes compact =>
        match compactToNibbles compact with
        | .error error => pure (.error error)
        | .ok (path, leaf) =>
          if leaf then
            match valueItem with
            | .list _ => pure (.error (.malformed .leafValueList))
            | .bytes value => pure (.ok (some (.leaf path value enc)))
          else if path.size = 0 then pure (.error (.malformed .pathEmpty)) else do
            let result ← resolve valueItem (by rw [hxs]; simp)
            match result with
            | .error error => pure (.error error)
            | .ok (some child@(.branch ..)) | .ok (some child@(.hashed ..)) =>
              pure (.ok (some (.ext path child enc)))
            | .ok _ => pure (.error (.malformed .extChild))
    | _ =>
      if hlen : xs.length = 17 then do
        let result ← resolveChildren (xs.take 16)
          (fun child hm => resolve child (List.mem_of_mem_take hm))
        match result with
        | .error error => pure (.error error)
        | .ok children =>
          let value : ByteArray := match xs[16]'(by omega) with
            | .bytes bytes => bytes
            | .list _ => ByteArray.empty
          let occupied : Nat := (children.filter Option.isSome).length +
            (if value.size = 0 then 0 else 1)
          if occupied < 2 then pure (.error (.malformed (.occupancy occupied)))
          else pure (.ok (some (.branch children.toArray value enc)))
      else pure (.error (.malformed (.badListLength xs.length)))
termination_by sizeOf item
decreasing_by
  have hi := Rlp.decode_encode child (child_encodable xs hx child hm)
  rw [heq] at hi
  have hmSize := List.sizeOf_lt_of_mem hm
  simp_all
  omega

private def decodeEntry {m : Type → Type} [Monad m] [KeccakQuery m]
    (db : NodeDB) (onPath : Std.HashSet Hash32) (key : Hash32)
    (raw : ByteArray) (_hlookup : db.map[key]? = some raw) :
    m (Except TrieError Ref) :=
  if _hcycle : onPath.contains key then pure (.error (.malformed .cycle)) else
    acquire raw fun hash? =>
      match hparse : Rlp.decode raw with
      | .error _ => pure (.error (.malformed .rlp))
      | .ok item => interpret db
          (fun child bytes hchild => decodeEntry db (onPath.insert key) child bytes hchild)
          item (Rlp.decode_success_encodable raw item hparse) ⟨raw, hash?⟩
termination_by (db.map.keys.filter (fun k => !onPath.contains k)).length
decreasing_by
  apply remaining_insert_lt
  · simp [Std.HashMap.contains_eq_isSome_getElem?, _hlookup]
  · simpa using _hcycle

private theorem acquire_short {m : Type → Type} [Monad m] [KeccakQuery m]
    (raw : ByteArray) (next : Option Hash32 → m (Except TrieError Ref))
    (short : raw.size < 32) : acquire raw next = next none := by
  simp only [acquire, ite_eq_left short]

private theorem acquire_long {m : Type → Type} [Monad m] [KeccakQuery m]
    (raw : ByteArray) (next : Option Hash32 → m (Except TrieError Ref))
    (long : 32 ≤ raw.size) : acquire raw next = (do
      let answer ← KeccakQuery.keccak raw
      next (some answer)) := by
  simp only [acquire, ite_eq_right (show ¬ raw.size < 32 by omega)]

private theorem resolveChildren_cons {m : Type → Type} [Monad m]
    (item : RlpItem) (rest : List RlpItem)
    (resolve : (x : RlpItem) → x ∈ item :: rest → m (Except TrieError Ref)) :
    resolveChildren (item :: rest) resolve = (do
      let head ← resolve item List.mem_cons_self
      match head with
      | .error error => pure (.error error)
      | .ok child =>
        let tail ← resolveChildren rest (fun x hx => resolve x (List.mem_cons_of_mem item hx))
        pure (tail.map (child :: ·))) := rfl

private theorem entry_cycle {m : Type → Type} [Monad m] [KeccakQuery m]
    (db : NodeDB) (onPath : Std.HashSet Hash32) (key : Hash32)
    (raw : ByteArray) (lookup : db.map[key]? = some raw)
    (cycle : onPath.contains key = true) :
    decodeEntry (m := m) db onPath key raw lookup = pure (.error (.malformed .cycle)) := by
  rw [decodeEntry]
  simp only [cycle, dite_true]

private theorem resolve_empty {m : Type → Type} [Monad m] (db : NodeDB)
    (entry : (key : Hash32) → (raw : ByteArray) → db.map[key]? = some raw →
      m (Except TrieError Ref))
    (inline : (xs : List RlpItem) → RlpItem.bytes ByteArray.empty = .list xs →
      m (Except TrieError Ref)) :
    resolveRef db (.bytes ByteArray.empty) entry inline = pure (.ok none) := rfl

private theorem entry_fresh {m : Type → Type} [Monad m] [KeccakQuery m]
    (db : NodeDB) (onPath : Std.HashSet Hash32) (key : Hash32)
    (raw : ByteArray) (lookup : db.map[key]? = some raw)
    (fresh : onPath.contains key = false) :
    decodeEntry (m := m) db onPath key raw lookup =
      acquire raw (fun hash? =>
        match hparse : Rlp.decode raw with
        | .error _ => pure (.error (.malformed .rlp))
        | .ok item => interpret db
            (fun child bytes hchild => decodeEntry db (onPath.insert key) child bytes hchild)
            item (Rlp.decode_success_encodable raw item hparse) ⟨raw, hash?⟩) := by
  rw [decodeEntry]
  simp only [fresh, Bool.false_eq_true, dite_false]

private theorem interpreted_leaf {m : Type → Type} [Monad m] [KeccakQuery m]
    (db : NodeDB)
    (entry : (key : Hash32) → (raw : ByteArray) → db.map[key]? = some raw →
      m (Except TrieError Ref))
    (compact value : ByteArray) (path : Nibbles) (enc : Enc)
    (hx : Rlp.Encodable (.list [.bytes compact, .bytes value]))
    (hcompact : compactToNibbles compact = .ok (path, true)) :
    interpret db entry (.list [.bytes compact, .bytes value]) hx enc =
      pure (.ok (some (.leaf path value enc))) := by
  rw [interpret]
  simp only [hcompact, ite_true]

private theorem interpreted_string {m : Type → Type} [Monad m] [KeccakQuery m]
    (db : NodeDB)
    (entry : (key : Hash32) → (raw : ByteArray) → db.map[key]? = some raw →
      m (Except TrieError Ref))
    (bytes : ByteArray) (hx : Rlp.Encodable (.bytes bytes)) (enc : Enc) :
    interpret db entry (.bytes bytes) hx enc =
      (if bytes.size = 0 then pure (.ok none)
       else pure (.error (.malformed .nonEmptyString))) := by
  rw [interpret]

private theorem acquisition_underlying_failure {m : Type → Type} {ε : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery (ExceptT ε m)]
    (raw : ByteArray) (next : Option Hash32 → ExceptT ε m (Except TrieError Ref))
    (long : 32 ≤ raw.size) (error : ε)
    (hquery : KeccakQuery.keccak (m := ExceptT ε m) raw =
      ExceptT.mk (pure (.error error))) :
    (acquire raw next).run = pure (.error error) := by
  rw [acquire_long raw next long, hquery]
  simp only [ExceptT.run_bind, ExceptT.run_mk, pure_bind]

private theorem children_first_error {m : Type → Type} [Monad m] [LawfulMonad m]
    (item : RlpItem) (rest : List RlpItem)
    (resolve : (x : RlpItem) → x ∈ item :: rest → m (Except TrieError Ref))
    (error : TrieError) (hhead : resolve item List.mem_cons_self = pure (.error error)) :
    resolveChildren (item :: rest) resolve = pure (.error error) := by
  rw [resolveChildren_cons, hhead]
  simp only [pure_bind]

/-- Complete eager decoding, with the caller-supplied empty root bypassing lookup/query.
EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:892–991,1024–1033` at the pin. -/
def decodeRoot {m : Type → Type} [Monad m] [KeccakQuery m]
    (emptyRoot : Hash32) (db : NodeDB) (r : Hash32) : m (Except TrieError Ref) :=
  if r = emptyRoot then pure (.ok none) else
    match h : db.map[r]? with
    | none => pure (.error (.missingRoot r))
    | some raw => decodeEntry db {} r raw h

/-- Preserve the supplied secured flag and the complete decoded partial root.
EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:994–1040` at the pin. -/
def decodeWitnessToMpt {m : Type → Type} [Monad m] [KeccakQuery m]
    (emptyRoot : Hash32) (db : NodeDB) (r : Hash32) (secured : Bool) :
    m (Except TrieError IncrementalMPT) := do
  let result ← decodeRoot emptyRoot db r
  pure (result.map (fun root => IncrementalMPT.mk secured root))

/-- The supplied empty root returns `pure (.ok none)` with no lookup or local query.
This retains the literal plain-Monad expression, without assuming laws for `pure`. -/
theorem decodeRoot_empty {m : Type → Type} [Monad m] [KeccakQuery m]
    (emptyRoot : Hash32) (db : NodeDB) :
    decodeRoot (m := m) emptyRoot db emptyRoot = pure (.ok none) := by
  simp only [decodeRoot, ite_true]

/-- A missing nonempty root fails before querying, for an arbitrary Monad. -/
theorem decodeRoot_missing {m : Type → Type} [Monad m] [KeccakQuery m]
    (emptyRoot : Hash32) (db : NodeDB) (r : Hash32)
    (hne : r ≠ emptyRoot) (hmissing : db.map[r]? = none) :
    decodeRoot (m := m) emptyRoot db r = pure (.error (.missingRoot r)) := by
  simp only [decodeRoot, ite_eq_right hne]
  split
  · rfl
  · next raw h => rw [hmissing] at h; contradiction

/-- Exact wrapper bind tree; no LawfulMonad or oracle equation is assumed. -/
theorem decodeWitnessToMpt_eq {m : Type → Type} [Monad m] [KeccakQuery m]
    (emptyRoot : Hash32) (db : NodeDB) (r : Hash32) (secured : Bool) :
    decodeWitnessToMpt (m := m) emptyRoot db r secured = (do
      let result ← decodeRoot emptyRoot db r
      pure (result.map (fun root => IncrementalMPT.mk secured root))) := rfl

end STFSpec.Commit
