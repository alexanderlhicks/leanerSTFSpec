/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash.KeccakSponge
import STFSpec.Base.ValueRecords

/-!
# Keccak queries and hash-constant acquisition

Library `EthHash`. D5's oracle seam forwards through transformer stacks; F20's
callers acquire one record and supply it to subsequent kernels. This module does
not implement those entry points or generic interpretation coupling.
Spec guidance: `STFSpec/informal/modules/EthHash.md` §§3, 6–8.
-/

namespace STFSpec.Hash

open STFSpec.Base

/-- The single Keccak dependency of hashing kernels (D5). No concrete-answer law is assumed. -/
class KeccakQuery (m : Type → Type) where
  /-- Query the supplied oracle on the exact byte preimage. -/
  keccak : ByteArray → m Hash32

/-- Concrete execution uses the accepted Keccak-256 reference definition. -/
instance : KeccakQuery Id where
  keccak := keccak256

/-- Exception transformers forward each query to the underlying oracle. -/
instance {m : Type → Type} {ε : Type} [Monad m] [KeccakQuery m] :
    KeccakQuery (ExceptT ε m) where
  keccak b := ExceptT.lift (KeccakQuery.keccak b)

/-- State transformers forward each query without modifying their own state. -/
instance {m : Type → Type} {σ : Type} [Monad m] [KeccakQuery m] :
    KeccakQuery (StateT σ m) where
  keccak b := StateT.lift (KeccakQuery.keccak b)

namespace KeccakQuery

/-- The identity oracle is definitionally the concrete digest, for every preimage. -/
theorem keccak_id (b : ByteArray) : keccak (m := Id) b = keccak256 b := rfl

/-- The exception lift introduces no query, handler or concrete hashing. -/
theorem keccak_exceptT {m : Type → Type} {ε : Type} [Monad m] [KeccakQuery m]
    (b : ByteArray) : keccak (m := ExceptT ε m) b = ExceptT.lift (keccak (m := m) b) := rfl

/-- The state lift introduces no query or state update. -/
theorem keccak_stateT {m : Type → Type} {σ : Type} [Monad m] [KeccakQuery m]
    (b : ByteArray) : keccak (m := StateT σ m) b = StateT.lift (keccak (m := m) b) := rfl

/-- Running the exception lift wraps the underlying answer in success. -/
theorem run_keccak_exceptT {m : Type → Type} {ε : Type} [Monad m] [KeccakQuery m]
    (b : ByteArray) : (keccak (m := ExceptT ε m) b).run =
      (Except.ok <$> keccak (m := m) b : m (Except ε Hash32)) := rfl

/-- Running the state lift pairs the underlying answer with the unchanged state. -/
theorem run_keccak_stateT {m : Type → Type} {σ : Type} [Monad m] [KeccakQuery m]
    (b : ByteArray) (s : σ) : (keccak (m := StateT σ m) b).run s =
      (do let answer ← keccak (m := m) b; pure (answer, s)) := rfl

end KeccakQuery
end STFSpec.Hash

namespace STFSpec.Base.HashConsts

open STFSpec.Hash KeccakQuery

/-- Acquire exactly four oracle answers, in field order. Preimages follow pinned EELS
`src/ethereum/state.py:36`, `src/ethereum/merkle_patricia_trie.py:71`,
`src/ethereum/forks/amsterdam/fork.py:116` and `src/ethereum/forks/amsterdam/vm/__init__.py:40`.
F20 assigns acquisition timing to callers, rather than subsequent kernels. -/
def query {m : Type → Type} [Monad m] [KeccakQuery m] : m HashConsts := do
  let emptyCodeHash ← keccak ⟨#[]⟩
  let emptyTrieRoot ← keccak ⟨#[0x80]⟩
  let emptyOmmerHash ← keccak ⟨#[0xc0]⟩
  let transferTopic ← keccak "Transfer(address,address,uint256)".toUTF8
  pure (HashConsts.mk emptyCodeHash emptyTrieRoot emptyOmmerHash transferTopic)

/-- Public ordered expansion: each supplied answer occupies its matching field,
with no cache, literal substitution, or query after an earlier monadic failure. -/
theorem query_eq {m : Type → Type} [Monad m] [KeccakQuery m] :
    query (m := m) = (do
      let code ← keccak ⟨#[]⟩
      let trie ← keccak ⟨#[0x80]⟩
      let ommer ← keccak ⟨#[0xc0]⟩
      let topic ← keccak "Transfer(address,address,uint256)".toUTF8
      pure (HashConsts.mk code trie ommer topic) : m HashConsts) := rfl

/-- Identity acquisition is exactly the four concrete digest calls in field order.
This equation does not assert equality to the literal record; guards check that separately. -/
theorem query_id : query (m := Id) = HashConsts.mk
    (keccak256 ⟨#[]⟩) (keccak256 ⟨#[0x80]⟩) (keccak256 ⟨#[0xc0]⟩)
    (keccak256 "Transfer(address,address,uint256)".toUTF8) := rfl

/-- Four pure oracle answers are retained verbatim, without assuming concrete digests. -/
theorem query_of_pure_answers {m : Type → Type} [Monad m] [LawfulMonad m]
    [KeccakQuery m] (code trie ommer topic : Hash32)
    (hcode : keccak (m := m) ⟨#[]⟩ = pure code)
    (htrie : keccak (m := m) ⟨#[0x80]⟩ = pure trie)
    (hommer : keccak (m := m) ⟨#[0xc0]⟩ = pure ommer)
    (htopic : keccak (m := m) "Transfer(address,address,uint256)".toUTF8 = pure topic) :
    query (m := m) = pure (HashConsts.mk code trie ommer topic) := by
  rw [query_eq, hcode, htrie, hommer, htopic]
  simp only [pure_bind]

/-- Acquisition through the exception lift preserves the underlying computation and wraps
its result in success; underlying failures still forward through the monad. -/
theorem run_query_exceptT {m : Type → Type} {ε : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] :
    (query (m := ExceptT ε m)).run =
      (do let consts ← query (m := m); pure (.ok consts : Except ε HashConsts)) := by
  simp only [query, KeccakQuery.keccak_exceptT, ExceptT.run_bind, ExceptT.run_map,
    ExceptT.run_lift, bind_map_left, Functor.map_map, Except.map,
    map_bind, bind_pure_comp]

/-- If the second query fails, the first answer is discarded and neither later query runs.
The oracle instance on the transformer may itself fail; no concrete-answer premise is needed. -/
theorem run_query_error_emptyTrie {m : Type → Type} {ε : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery (ExceptT ε m)] (code : Hash32) (error : ε)
    (hcode : keccak (m := ExceptT ε m) ⟨#[]⟩ = pure code)
    (htrie : keccak (m := ExceptT ε m) ⟨#[0x80]⟩ = ExceptT.mk (pure (.error error))) :
    (query (m := ExceptT ε m)).run = pure (.error error) := by
  rw [query_eq, hcode, htrie]
  simp only [pure_bind, ExceptT.run_bind, ExceptT.run_mk]

/-- Acquisition through the state lift leaves the added state unchanged while preserving
all underlying oracle effects and answers. -/
theorem run_query_stateT {m : Type → Type} {σ : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] (s : σ) :
    (query (m := StateT σ m)).run s =
      (do let consts ← query (m := m); pure (consts, s)) := by
  simp [query, KeccakQuery.keccak_stateT]

end STFSpec.Base.HashConsts
