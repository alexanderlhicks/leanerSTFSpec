/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block

/-!
# Private clients of the complete logs bloom facade

Library `EthConformance`. These clients use only the four public Bloom declarations
and public Base byte laws. No packed implementation or hash internals are unfolded.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3/4/5/7.
-/

namespace STFSpec.Conformance.Block.LogsBloomCallerProofs
open STFSpec.Block STFSpec.Base STFSpec.Hash STFSpec.Vm

private theorem complete_equation {m : Type → Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] (logs : Array Core.Log) :
    logsBloom logs = (do
      let result ← (logs.toList.flatMap (fun log ↦ log.address.toBytes.toByteArray ::
        log.topics.toList.map (fun topic ↦ topic.toBytes.toByteArray))).foldlM
        (fun acc entry ↦ do
          let h ← KeccakQuery.keccak entry
          pure (acc ||| 2 ^ ((h.toNat / 2 ^ 240) % 2048) |||
            2 ^ ((h.toNat / 2 ^ 224) % 2048) ||| 2 ^ ((h.toNat / 2 ^ 208) % 2048))) 0
      pure (FixedBytes.ofNat result : Bloom) : m Bloom) := logsBloom_eq logs

private theorem empty {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m] :
    logsBloom (m := m) #[] = pure (FixedBytes.ofNat 0 : Bloom) := logsBloom_empty

private theorem sequential_append {m : Type → Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] (a b : Array Core.Log) :
    logsBloom (a ++ b) = (do
      let ba ← logsBloom a
      let bb ← logsBloom b
      pure (FixedBytes.ofNat (ba.toNat ||| bb.toNat) : Bloom) : m Bloom) :=
  logsBloom_append a b

private theorem data_irrelevant {m : Type → Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] (logs : Array Core.Log) (f : Bytes → Bytes) :
    logsBloom (m := m) (logs.map fun log ↦ { log with data := f log.data }) =
      logsBloom logs := by
  simp only [logsBloom_eq, Array.toList_map, List.flatMap_map]

private theorem singleton_address {m : Type → Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m] (address : Address) (data : Bytes) :
    logsBloom (m := m) #[⟨address, #[], data⟩] = (do
      let h ← KeccakQuery.keccak address.toBytes.toByteArray
      pure (FixedBytes.ofNat (2 ^ ((h.toNat / 2 ^ 240) % 2048) |||
        2 ^ ((h.toNat / 2 ^ 224) % 2048) ||| 2 ^ ((h.toNat / 2 ^ 208) % 2048)) : Bloom)) := by
  rw [logsBloom_eq]
  simp only [List.flatMap_cons, List.flatMap_nil,
    List.map_nil, List.append_nil, List.foldlM_cons, List.foldlM_nil,
    pure_bind, bind_assoc, Nat.zero_or]

end STFSpec.Conformance.Block.LogsBloomCallerProofs
