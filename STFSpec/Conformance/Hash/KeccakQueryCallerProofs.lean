/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash

/-!
# Keccak query public-law composition clients

Library `EthConformance`. These clients use public query/run equations and Base's
record projection/extensionality laws. They unfold no Base byte or hash containers.
Spec guidance: `STFSpec/informal/modules/EthHash.md` §7.
-/

open STFSpec.Base STFSpec.Hash KeccakQuery

example (b : ByteArray) : keccak (m := Id) b = keccak256 b := keccak_id b

example (consts : HashConsts)
    (h0 : consts.emptyCodeHash = keccak256 ⟨#[]⟩)
    (h1 : consts.emptyTrieRoot = keccak256 ⟨#[0x80]⟩)
    (h2 : consts.emptyOmmerHash = keccak256 ⟨#[0xc0]⟩)
    (h3 : consts.transferTopic = keccak256 "Transfer(address,address,uint256)".toUTF8) :
    consts = HashConsts.query (m := Id) := by
  rw [HashConsts.query_id]
  apply HashConsts.ext
  · rw [h0, HashConsts.emptyCodeHash_mk]
  · rw [h1, HashConsts.emptyTrieRoot_mk]
  · rw [h2, HashConsts.emptyOmmerHash_mk]
  · rw [h3, HashConsts.transferTopic_mk]

example {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (code trie ommer topic : Hash32)
    (h0 : keccak (m := m) ⟨#[]⟩ = pure code)
    (h1 : keccak (m := m) ⟨#[0x80]⟩ = pure trie)
    (h2 : keccak (m := m) ⟨#[0xc0]⟩ = pure ommer)
    (h3 : keccak (m := m) "Transfer(address,address,uint256)".toUTF8 = pure topic) :
    HashConsts.emptyTrieRoot <$> HashConsts.query (m := m) = pure trie := by
  rw [HashConsts.query_of_pure_answers code trie ommer topic h0 h1 h2 h3]
  simp only [map_pure]

example {m : Type → Type} {ε σ : Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (s : σ) : ((HashConsts.query (m := ExceptT ε (StateT σ m))).run).run s =
      (do let consts ← HashConsts.query (m := m)
          pure ((.ok consts : Except ε HashConsts), s)) := by
  rw [HashConsts.run_query_exceptT]
  simp only [StateT.run_bind, StateT.run_pure, HashConsts.run_query_stateT,
    bind_assoc, pure_bind]

example {m : Type → Type} {ε σ : Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (s : σ) : ((HashConsts.query (m := StateT σ (ExceptT ε m))).run s).run =
      (do let consts ← HashConsts.query (m := m);
          pure (.ok (consts, s) : Except ε (HashConsts × σ))) := by
  rw [HashConsts.run_query_stateT]
  simp only [ExceptT.run_bind, ExceptT.run_pure, HashConsts.run_query_exceptT,
    bind_assoc, pure_bind]

example {m : Type → Type} {ε : Type} [Monad m] [LawfulMonad m]
    [KeccakQuery (ExceptT ε m)] (code : Hash32) (error : ε)
    (h0 : keccak (m := ExceptT ε m) ⟨#[]⟩ = pure code)
    (h1 : keccak (m := ExceptT ε m) ⟨#[0x80]⟩ = ExceptT.mk (pure (.error error))) :
    (HashConsts.query (m := ExceptT ε m)).run = pure (.error error) :=
  HashConsts.run_query_error_emptyTrie code error h0 h1
