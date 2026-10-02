/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.Root

/-!
# Public mathematical-root contract clients

Library `EthConformance`. These clients use authored C8/C7, node and provider
contracts; private reference/selection/storage declarations are not consumer seams.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/7.
-/

namespace STFSpec.Conformance.Commit.MathRootCallerProofs

open STFSpec.Base STFSpec.Codec STFSpec.Hash STFSpec.Commit

/-- Arbitrary supplied constants survive empty execution even with an effectful oracle. -/
theorem supplied_empty {m : Type → Type} [Monad m] [KeccakQuery m]
    (answer : Hash32) (obj : Std.ExtTreeMap Nibbles ByteArray) (empty : obj.size = 0) :
    mathRoot (m := m) answer obj = pure answer := mathRoot_empty answer obj empty

/-- Root behavior depends on the final finite map, including its empty-value lookups. -/
theorem final_map {m : Type → Type} [Monad m] [KeccakQuery m]
    (answer : Hash32) (obj other : Std.ExtTreeMap Nibbles ByteArray)
    (same : ∀ key : Nibbles, obj[key]? = other[key]?) :
    mathRoot (m := m) answer obj = mathRoot answer other := mathRoot_ext answer obj other same

/-- A singleton's full actual leaf assembly is hashed once without a root threshold. -/
theorem singleton_query {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (emptyRoot : Hash32) (obj : Std.ExtTreeMap Nibbles ByteArray)
    (single : obj.size = 1) (key : Nibbles) (member : key ∈ obj) :
    mathRoot (m := m) emptyRoot obj =
      KeccakQuery.keccak (Rlp.encode (.list [.bytes (nibbleListToCompact key true),
        .bytes (obj[key]'member)])) := by
  rw [mathRoot_nonempty emptyRoot obj (by omega),
    patricialize_singleton obj 0 (PatricializeDomain.zero obj) single key member, pure_bind,
    Nibbles.drop_zero, assembleInternalNode_leaf]

/-- Concrete roots retain caller-supplied empty constants and use actual C7 on nonempty maps. -/
theorem concrete_root (emptyRoot : Hash32) (obj : Std.ExtTreeMap Nibbles ByteArray) :
    mathRoot (m := Id) emptyRoot obj =
      if obj.size = 0 then emptyRoot else
        keccak256 (Rlp.encode (assembleInternalNode
          (patricialize (m := Id) obj 0 (PatricializeDomain.zero obj)))) :=
  mathRoot_id emptyRoot obj

/-- Descendant failures retain their diagnostic and suppress the complete-top query. -/
theorem descendant_error {m : Type → Type} {ε : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery (ExceptT ε m)]
    (emptyRoot : Hash32) (obj : Std.ExtTreeMap Nibbles ByteArray)
    (nonempty : obj.size ≠ 0) (error : ε)
    (failed : (patricialize (m := ExceptT ε m) obj 0 (PatricializeDomain.zero obj)).run =
      pure (.error error)) :
    (mathRoot (m := ExceptT ε m) emptyRoot obj).run = pure (.error error) :=
  run_mathRoot_construction_error emptyRoot obj nonempty error failed

/-- The root's own query error is retained in the original exception channel. -/
theorem final_error {m : Type → Type} {ε : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery (ExceptT ε m)]
    (emptyRoot : Hash32) (obj : Std.ExtTreeMap Nibbles ByteArray)
    (nonempty : obj.size ≠ 0) (node : Option InternalNode) (error : ε)
    (constructed : patricialize (m := ExceptT ε m) obj 0 (PatricializeDomain.zero obj) =
      pure node)
    (failed : (KeccakQuery.keccak (m := ExceptT ε m)
      (Rlp.encode (assembleInternalNode node))).run = pure (.error error)) :
    (mathRoot (m := ExceptT ε m) emptyRoot obj).run = pure (.error error) :=
  run_mathRoot_query_error emptyRoot obj nonempty node error constructed failed

/-- Exception-lift root execution consumes the authored public transformer equation. -/
example {m : Type → Type} {ε : Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (emptyRoot : Hash32) (obj : Std.ExtTreeMap Nibbles ByteArray) :
    (mathRoot (m := ExceptT ε m) emptyRoot obj).run =
      (if obj.size = 0 then pure (.ok emptyRoot) else do
        let result ← (patricialize (m := ExceptT ε m) obj 0
          (PatricializeDomain.zero obj)).run
        match result with
        | .error error => pure (.error error)
        | .ok node => do
          let answer ← KeccakQuery.keccak (Rlp.encode (assembleInternalNode node))
          pure (.ok answer) : m (Except ε Hash32)) := run_mathRoot_exceptT emptyRoot obj

/-- State-lift root execution consumes the authored public state/effect equation. -/
example {m : Type → Type} {σ : Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (emptyRoot : Hash32) (obj : Std.ExtTreeMap Nibbles ByteArray) (state : σ) :
    (mathRoot (m := StateT σ m) emptyRoot obj).run state =
      (if obj.size = 0 then pure (emptyRoot, state) else do
        let (node, next) ← (patricialize (m := StateT σ m) obj 0
          (PatricializeDomain.zero obj)).run state
        let answer ← KeccakQuery.keccak (Rlp.encode (assembleInternalNode node))
        pure (answer, next) : m (Hash32 × σ)) := run_mathRoot_stateT emptyRoot obj state

end STFSpec.Conformance.Commit.MathRootCallerProofs
