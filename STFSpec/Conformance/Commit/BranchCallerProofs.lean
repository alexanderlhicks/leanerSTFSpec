/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Commit

/-!
# Reached-branch ordinary public clients

Library `EthConformance`. Only public providers and mkBranch are named. Literal
total-domain clients require Monad alone, without a public source/WF predicate.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/4/5/7 (Q60).
-/

namespace STFSpec.Conformance.Commit.BranchCallerProofs
open STFSpec.Base STFSpec.Codec STFSpec.Hash STFSpec.Commit

private def client {m : Type → Type} [Monad m] [KeccakQuery m]
    (xs : Array Ref) (v : ByteArray) : m (Except TrieError Ref) := mkBranch xs v

private theorem zero {m : Type → Type} [Monad m] [KeccakQuery m] :
    mkBranch (m := m) #[] ByteArray.empty = pure (.error (.malformed (.occupancy 0))) := rfl

private theorem stub_first {m : Type → Type} [Monad m] [KeccakQuery m] (h : Hash32) :
    mkBranch (m := m) #[some (.hashed h)] ByteArray.empty = pure (.error (.unresolved h)) := rfl

private theorem value_only {m : Type → Type} [Monad m] [KeccakQuery m]
    (v : ByteArray) (hv : v.size ≠ 0) :
    mkBranch (m := m) #[] v =
      (mkLeaf (Nibbles.ofList []) v >>= fun n => pure (.ok (some n))) := by
  change (if v.size = 0 then _ else _) = _
  rw [ite_eq_right hv]

private theorem terminal_stub {m : Type → Type} [Monad m] [KeccakQuery m]
    (h : Hash32) (v : ByteArray) (hv : v.size ≠ 0) :
    mkBranch (m := m) #[some (.hashed h)] v =
      let raw := Rlp.encode (.list [.bytes h.toBytes.toByteArray, .bytes v])
      ((if raw.size < 32 then pure (Node.branch #[some (.hashed h)] v ⟨raw, none⟩)
        else KeccakQuery.keccak raw >>= fun answer =>
          pure (Node.branch #[some (.hashed h)] v ⟨raw, some answer⟩)) >>=
        fun n => pure (.ok (some n))) := by
  change (if v.size = 0 then _ else _) = _
  rw [ite_eq_right hv]
  change
    (let raw := Rlp.encode (.list [childRef (some (.hashed h)), .bytes v])
     ((if raw.size < 32 then pure (Node.branch #[some (.hashed h)] v ⟨raw, none⟩)
       else KeccakQuery.keccak raw >>= fun answer =>
         pure (Node.branch #[some (.hashed h)] v ⟨raw, some answer⟩) : m Node) >>=
       fun n => pure (Except.ok (some n) : Except TrieError Ref))) = _
  rw [childRef_hashed]

-- Underlying transformer failures are retained by the operation's result type;
-- this client introduces no handler or source heap partial-state API.
private def exception_client {m : Type → Type} {ε : Type} [Monad m] [KeccakQuery m]
    (xs : Array Ref) (v : ByteArray) : ExceptT ε m (Except TrieError Ref) := mkBranch xs v

private def state_client {m : Type → Type} {σ : Type} [Monad m] [KeccakQuery m]
    (xs : Array Ref) (v : ByteArray) : StateT σ m (Except TrieError Ref) := mkBranch xs v

end STFSpec.Conformance.Commit.BranchCallerProofs
