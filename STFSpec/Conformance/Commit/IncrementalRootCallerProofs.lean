/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Commit

/-!
# Supplied incremental-root public-law clients

Library `EthConformance`. Literal action clients use plain Monad. Derived run/bind
clients state LawfulMonad explicitly. Every input field is preserved and standard
domains cover the complete encoded item, not only a root path or ending value.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` C27/§7.
-/
namespace STFSpec.Conformance.Commit.IncrementalRootCallerProofs
open STFSpec.Base STFSpec.Codec STFSpec.Hash STFSpec.Commit

private theorem absent {m : Type → Type} [Monad m] [KeccakQuery m] (e : Hash32) :
    rootHash (m := m) e none = pure e := rootHash_none e

private theorem stub {m : Type → Type} [Monad m] [KeccakQuery m] (e h : Hash32) :
    rootHash (m := m) e (some (.hashed h)) = pure h := rootHash_hashed e h

private theorem leaf_action {m : Type → Type} [Monad m] [KeccakQuery m]
    (e : Hash32) (p : Nibbles) (v raw : ByteArray) :
    rootHash (m := m) e (some (.leaf p v ⟨raw, none⟩)) =
      KeccakQuery.keccak (Rlp.encode (.list [.bytes (nibbleListToCompact p true), .bytes v])) :=
  rootHash_leaf e p v ⟨raw, none⟩

private theorem ext_cached {m : Type → Type} [Monad m] [KeccakQuery m]
    (e h : Hash32) (p : Nibbles) (child : Node) (raw : ByteArray) :
    rootHash (m := m) e (some (.ext p child ⟨raw, some h⟩)) = pure h :=
  rootHash_ext e p child ⟨raw, some h⟩

private theorem branch_action {m : Type → Type} [Monad m] [KeccakQuery m]
    (e : Hash32) (cs : Array Ref) (v raw : ByteArray) :
    rootHash (m := m) e (some (.branch cs v ⟨raw, none⟩)) =
      KeccakQuery.keccak (Rlp.encode (.list (cs.toList.map childRef ++ [.bytes v]))) :=
  rootHash_branch e cs v ⟨raw, none⟩

private theorem secured_irrelevant {m : Type → Type} [Monad m] [KeccakQuery m]
    (e : Hash32) (root : Ref) :
    mptRoot (m := m) e ⟨true, root⟩ = mptRoot (m := m) e ⟨false, root⟩ := by
  rw [mptRoot_eq, mptRoot_eq]

private theorem leaf_raw_irrelevant {m : Type → Type} [Monad m] [KeccakQuery m]
    (e : Hash32) (p : Nibbles) (v a b : ByteArray) (h : Option Hash32) :
    rootHash (m := m) e (some (.leaf p v ⟨a, h⟩)) =
      rootHash (m := m) e (some (.leaf p v ⟨b, h⟩)) := by
  rw [rootHash_leaf, rootHash_leaf]

private theorem actual_answer {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (e answer : Hash32) (p : Nibbles) (v raw : ByteArray)
    (hq : KeccakQuery.keccak (m := m)
      (Rlp.encode (.list [.bytes (nibbleListToCompact p true), .bytes v])) = pure answer) :
    (rootHash (m := m) e (some (.leaf p v ⟨raw, none⟩)) >>= fun h => pure h.toBytes) =
      pure answer.toBytes := by
  rw [rootHash_leaf, hq]
  simp only [pure_bind]

private theorem state_lift {m : Type → Type} {σ : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m]
    (e : Hash32) (cs : Array Ref) (v : ByteArray) (enc : Enc) (s : σ) :
    (mptRoot (m := StateT σ m) e ⟨true, some (.branch cs v enc)⟩).run s =
      (do let h ← rootHash (m := m) e (some (.branch cs v enc)); pure (h, s)) := by
  rw [mptRoot_eq, rootHash_branch, rootHash_branch]
  cases enc.hash? <;> simp [KeccakQuery.run_keccak_stateT]

private theorem except_lift {m : Type → Type} {ε : Type}
    [Monad m] [LawfulMonad m] [KeccakQuery m]
    (e : Hash32) (p : Nibbles) (c : Node) (enc : Enc) :
    (rootHash (m := ExceptT ε m) e (some (.ext p c enc))).run =
      (do let h ← rootHash (m := m) e (some (.ext p c enc)); pure (.ok h : Except ε Hash32)) := by
  rw [rootHash_ext, rootHash_ext]
  cases enc.hash? <;> simp [KeccakQuery.run_keccak_exceptT]

private theorem leaf_domain (p : Nibbles) (v : ByteArray)
    (hhp : p.size / 2 + 1 < 2 ^ 64) (hv : v.size < 2 ^ 64)
    (hpayload : (Rlp.encodePayloadModel
      [.bytes (nibbleListToCompact p true), .bytes v]).length < 2 ^ 64) :
    Rlp.Encodable (.list [.bytes (nibbleListToCompact p true), .bytes v]) := by
  rw [Rlp.encodable_list_iff]
  refine ⟨?_, hpayload⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact (Rlp.encodable_bytes_iff _).mpr (by rwa [size_nibbleListToCompact])
  · exact (Rlp.encodable_bytes_iff _).mpr hv

private theorem ext_domain (p : Nibbles) (c : Node)
    (hhp : p.size / 2 + 1 < 2 ^ 64) (hc : Rlp.Encodable (childRef (some c)))
    (hpayload : (Rlp.encodePayloadModel
      [.bytes (nibbleListToCompact p false), childRef (some c)]).length < 2 ^ 64) :
    Rlp.Encodable (.list [.bytes (nibbleListToCompact p false), childRef (some c)]) := by
  rw [Rlp.encodable_list_iff]
  refine ⟨?_, hpayload⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact (Rlp.encodable_bytes_iff _).mpr (by rwa [size_nibbleListToCompact])
  · exact hc

private theorem branch_domain (cs : Array Ref) (v : ByteArray)
    (hc : ∀ child ∈ cs.toList, Rlp.Encodable (childRef child)) (hv : v.size < 2 ^ 64)
    (hpayload : (Rlp.encodePayloadModel (cs.toList.map childRef ++ [.bytes v])).length < 2 ^ 64) :
    Rlp.Encodable (.list (cs.toList.map childRef ++ [.bytes v])) := by
  rw [Rlp.encodable_list_iff]
  refine ⟨?_, hpayload⟩
  intro x hx
  rcases List.mem_append.mp hx with hchild | hvalue
  · rcases List.mem_map.mp hchild with ⟨child, hmem, rfl⟩
    exact hc child hmem
  · have he : x = .bytes v := by simpa only [List.mem_singleton] using hvalue
    subst x
    exact (Rlp.encodable_bytes_iff _).mpr hv

end STFSpec.Conformance.Commit.IncrementalRootCallerProofs
