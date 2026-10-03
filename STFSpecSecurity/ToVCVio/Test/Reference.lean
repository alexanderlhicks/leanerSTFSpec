/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import ToVCVio.EthCommit.NodeReference

/-!
# Public RLP reference clients and complete effect guards

All clients consume public codec/reference/adapter contracts. Encoded widths count
outer and inner headers; observations retain complete wires, errors and state.
Library `ToVCVio` in `STFSpecSecurity`.
Spec guidance: `STFSpec/informal/modules/ToVCVio.md` §§4/7.
-/

namespace ToVCVio.Test
open STFSpec.Base STFSpec.Codec STFSpec.Hash STFSpec.Commit
open ToVCVio.Rlp ToVCVio.Oracle ToVCVio.EthCommit

/-- A complete 31-byte node, whose one byte-string payload has 29 bytes. -/
def node31 : RlpListNode :=
  ⟨⟨.list [.bytes ⟨Array.replicate 29 (0 : UInt8)⟩], by
    simp only [STFSpec.Codec.Rlp.encodable_list_iff, List.mem_singleton, forall_eq,
      STFSpec.Codec.Rlp.encodable_bytes_iff]
    decide⟩, ⟨_, rfl⟩⟩
/-- A complete 32-byte node reaches the hashing threshold. -/
def node32 : RlpListNode :=
  ⟨⟨.list [.bytes ⟨Array.replicate 30 (0 : UInt8)⟩], by
    simp only [STFSpec.Codec.Rlp.encodable_list_iff, List.mem_singleton, forall_eq,
      STFSpec.Codec.Rlp.encodable_bytes_iff]
    decide⟩, ⟨_, rfl⟩⟩
/-- A complete 33-byte node remains hashed. -/
def node33 : RlpListNode :=
  ⟨⟨.list [.bytes ⟨Array.replicate 31 (0 : UInt8)⟩], by
    simp only [STFSpec.Codec.Rlp.encodable_list_iff, List.mem_singleton, forall_eq,
      STFSpec.Codec.Rlp.encodable_bytes_iff]
    decide⟩, ⟨_, rfl⟩⟩
/-- Empty list presence differs from empty child absence. -/
def emptyList : RlpListNode :=
  ⟨⟨.list [], by
    rw [STFSpec.Codec.Rlp.encodable_list_iff]
    constructor
    · simp
    · decide⟩, ⟨[], rfl⟩⟩
/-- Nested lists retain every joined recursive Encodable certificate. -/
def nested : ValidItem :=
  ⟨.list [.list [.bytes ByteArray.empty], .bytes ⟨Array.replicate 30 (0 : UInt8)⟩], by
    rw [STFSpec.Codec.Rlp.encodable_list_iff]
    constructor
    · intro item hi
      rcases List.mem_cons.mp hi with hi | hi
      · subst item
        rw [STFSpec.Codec.Rlp.encodable_list_iff]
        constructor
        · intro item hi
          have he := List.mem_singleton.mp hi
          subst item
          rw [STFSpec.Codec.Rlp.encodable_bytes_iff]
          decide
        · decide
      · have he := List.mem_singleton.mp hi
        subst item
        rw [STFSpec.Codec.Rlp.encodable_bytes_iff]
        decide
    · decide⟩

/-- Header-inclusive widths are the actual packed encoder's widths. -/
theorem widths : node31.encode.size = 31 ∧ node32.encode.size = 32 ∧ node33.encode.size = 33 := by
  decide
/-- Exact complete node wires, rather than payload lengths. -/
theorem complete_wires :
    node31.encode.data.toList = [0xde, 0x9d] ++ List.replicate 29 0 ∧
    node32.encode.data.toList = [0xdf, 0x9e] ++ List.replicate 30 0 ∧
    node33.encode.data.toList = [0xe0, 0x9f] ++ List.replicate 31 0 := by decide

/-- A chosen arbitrary answer with 31 leading zeros and final byte 1. -/
def answer : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat 1)
/-- Every digest byte is retained. -/
theorem answer_bytes : answer.toBytes.toList = List.replicate 31 0 ++ [1] := by decide
/-- Empty bytes, an empty list and a digest have distinct complete wires. -/
theorem reference_wires :
    (STFSpec.Codec.Rlp.encode (wireItem .empty)).data.toList = [0x80] ∧
    (STFSpec.Codec.Rlp.encode (wireItem (.inline emptyList))).data.toList = [0xc0] ∧
    (STFSpec.Codec.Rlp.encode (wireItem (.hashed answer))).data.toList =
      [0xa0] ++ List.replicate 31 0 ++ [1] := by decide
/-- The nested accepted image uses the public facade theorem. -/
theorem nested_decode : STFSpec.Codec.Rlp.decode nested.encode = .ok nested.val :=
  ValidItem.decode_encode nested

/-- State recorder preserves every occurrence, including repeated equal preimages. -/
def recordBatch (digest : Hash32) : StateM (List ByteArray) (List ChildRef) := do
  let q := fun bytes trace => (digest, trace ++ [bytes])
  let a ← childRefM q node31
  let b ← childRefM q node32
  let c ← childRefM q node33
  let d ← childRefM q node32
  pure [a, b, c, d]
/-- A nonliteral caller trace, complete answers and numeric sequencing all survive. -/
theorem recordBatch_eq (digest : Hash32) (seen : List ByteArray) :
    (recordBatch digest).run seen =
      ([.inline node31, .hashed digest, .hashed digest, .hashed digest],
        seen ++ [node32.encode, node33.encode, node32.encode]) := by
  have h31 : node31.encode.size < 32 := by rw [widths.1]; decide
  have h32 : 32 ≤ node32.encode.size := by rw [widths.2.1]; decide
  have h33 : 32 ≤ node33.encode.size := by rw [widths.2.2]; decide
  simp only [recordBatch, childRefM_inline _ _ h31,
    childRefM_hash _ _ h32, childRefM_hash _ _ h33]
  change ([ChildRef.inline node31, ChildRef.hashed digest, ChildRef.hashed digest, ChildRef.hashed digest],
      ((seen ++ [node32.encode]) ++ [node33.encode]) ++ [node32.encode]) = _
  simp [List.append_assoc]

/-- A state-changing failure exposes its complete input and original error. -/
def failureQ (bytes : ByteArray) : ExceptT String (StateM (List ByteArray × Nat)) Hash32 :=
  ExceptT.mk (fun state => (.error "oracle-error", (state.1 ++ [bytes], state.2 + 7)))
/-- Inline bypass leaves the entire underlying state unchanged. -/
theorem inline_failure_bypass (seen : List ByteArray) (counter : Nat) :
    ((childRefM failureQ node31).run).run (seen, counter) =
      (.ok (.inline node31), (seen, counter)) := by
  rw [childRefM_inline _ _ (by rw [widths.1]; decide)]
  rfl
/-- Hash failure retains the exact error, complete preimage and changed state. -/
theorem hash_failure_forward (seen : List ByteArray) (counter : Nat) :
    ((childRefM failureQ node32).run).run (seen, counter) =
      (.error "oracle-error", (seen ++ [node32.encode], counter + 7)) := by
  rw [childRefM_hash _ _ (by rw [widths.2.1]; decide)]
  rfl
/-- Empty reference bypass has no callback and preserves the underlying state. -/
theorem empty_failure_bypass (seen : List ByteArray) (counter : Nat) :
    ((emptyRefM (m := ExceptT String (StateM (List ByteArray × Nat)))).run).run (seen, counter) =
      (.ok .empty, (seen, counter)) := rfl

/-- A concrete Id-to-state map preserves pure/bind and this explicitly chosen query. -/
def idStateMorphism (h : ByteArray → Hash32) :
    QueryMorphism ByteArray Hash32 Id (StateM Nat) h (fun bytes state => (h bytes, state)) where
  map value := fun state => (value, state)
  map_pure _ := rfl
  map_bind _ _ := rfl
  map_query _ := rfl
/-- This client invokes the public kernel transport, rather than assuming parametricity. -/
theorem idState_client (h : ByteArray → Hash32) (node : RlpListNode) (state : Nat) :
    (childRefM (m := StateM Nat) (fun bytes counter => (h bytes, counter)) node).run state =
      (refWithHash h node, state) := by
  exact congrArg (fun (action : StateM Nat ChildRef) => action.run state)
    (childRefM_natural (m := Id) (n := StateM Nat) h _ (idStateMorphism h) node).symm

/-- The actual core adapter consumes one installed query capability on both sides. -/
theorem installed_adapter_client (node : InternalNode)
    (henc : STFSpec.Codec.Rlp.Encodable (assembleInternalNode (some node)))
    (digest : Hash32) (seen : List ByteArray) :
    letI : KeccakQuery (StateM (List ByteArray)) := ⟨fun bytes trace => (digest, trace ++ [bytes])⟩
    (wireItem <$> childRefM (KeccakQuery.keccak (m := StateM (List ByteArray)))
      (asListNode node henc)).run seen =
    (encodeInternalNode (m := StateM (List ByteArray)) (some node)).run seen := by
  letI : KeccakQuery (StateM (List ByteArray)) := ⟨fun bytes trace => (digest, trace ++ [bytes])⟩
  exact congrArg (fun (action : StateM (List ByteArray) RlpItem) => action.run seen)
    (keccak_adapter (m := StateM (List ByteArray)) node henc)

/-- A same-h collision yields the complete distinct input pair, with no added query. -/
theorem local_collision :
    refWithHash (fun _ => answer) node32 = refWithHash (fun _ => answer) node33 ∧
    extractCollision node32 node33 = some (node32.encode, node33.encode) := by
  constructor
  · rfl
  · decide
/-- Equal complete preimages give none. -/
theorem equal_preimage_none : extractCollision node32 node32 = none := by
  exact (extractCollision_none_iff _ _).mpr rfl
/-- The collision client uses the public conditional soundness law. -/
theorem local_collision_sound :
    node32.encode ≠ node33.encode ∧
      (fun _ : ByteArray => answer) node32.encode = (fun _ : ByteArray => answer) node33.encode := by
  have h := extractCollision_sound (fun _ => answer) node32 node33 local_collision.1
    node32.encode node33.encode local_collision.2
  exact h.2.2

/-- A supplied empty value remains present in an actual leaf assembly. -/
def emptyValueLeaf : InternalNode := .leaf (Nibbles.ofList []) (.bytes ByteArray.empty)
/-- The complete empty-value leaf satisfies every joined RLP domain premise. -/
theorem emptyValueLeaf_encodable :
    STFSpec.Codec.Rlp.Encodable (assembleInternalNode (some emptyValueLeaf)) := by
  unfold emptyValueLeaf
  rw [encodable_assembleInternalNode_leaf_iff]
  constructor
  · decide
  · constructor
    · rw [STFSpec.Codec.Rlp.encodable_bytes_iff]; decide
    · decide
/-- Present empty values have the complete wire c2 20 80, distinct from absence. -/
theorem empty_value_wire :
    (asListNode emptyValueLeaf emptyValueLeaf_encodable).encode.data.toList = [0xc2, 0x20, 0x80] := by
  decide
/-- An actual long leaf exercises the installed core adapter's hashed branch. -/
def longLeaf : InternalNode :=
  .leaf (Nibbles.ofList []) (.bytes ⟨Array.replicate 40 (0 : UInt8)⟩)
/-- The long leaf retains its HP, value and joined-payload domain certificates. -/
theorem longLeaf_encodable :
    STFSpec.Codec.Rlp.Encodable (assembleInternalNode (some longLeaf)) := by
  unfold longLeaf
  rw [encodable_assembleInternalNode_leaf_iff]
  constructor
  · decide
  · constructor
    · rw [STFSpec.Codec.Rlp.encodable_bytes_iff]; decide
    · decide
/-- The core adapter's full query and full arbitrary answer are observed together. -/
def adapterRun (digest : Hash32) (seen : List ByteArray) : RlpItem × List ByteArray :=
  letI : KeccakQuery (StateM (List ByteArray)) := ⟨fun bytes trace => (digest, trace ++ [bytes])⟩
  (wireItem <$> childRefM (KeccakQuery.keccak (m := StateM (List ByteArray)))
    (asListNode longLeaf longLeaf_encodable)).run seen
/-- This concrete long-node adapter query uses the complete assembly exactly once. -/
theorem adapterRun_eq (digest : Hash32) (seen : List ByteArray) :
    adapterRun digest seen = (.bytes digest.toBytes.toByteArray,
      seen ++ [STFSpec.Codec.Rlp.encode (assembleInternalNode (some longLeaf))]) := by
  unfold adapterRun
  rw [childRefM_hash _ _ (by decide)]
  rfl
/-- State outside an exception does not fabricate an output state after failure. -/
theorem outer_state_failure (seen : List ByteArray) (counter added : Nat) :
    (((childRefM (m := StateT Nat (ExceptT String (StateM (List ByteArray × Nat))))
      (fun bytes => StateT.lift (failureQ bytes)) node32).run added).run).run (seen, counter) =
      (.error "oracle-error", (seen ++ [node32.encode], counter + 7)) := by
  rw [run_childRefM_stateT]
  rw [childRefM_hash _ _ (by rw [widths.2.1]; decide)]
  rfl

/-- Complete native/interpreted observation data; no timed checksum. -/
structure Observation where
  label : String
  wires : List (List Nat)
  queries : List (List Nat)
  counter : Nat
  error : Option String
  deriving Repr, DecidableEq

/-- Stable full-byte observation, including every leading zero. -/
def bytes (wire : ByteArray) : List Nat := wire.data.toList.map UInt8.toNat
/-- Every returned reference is observed through its injective canonical wire. -/
def refs (items : List ChildRef) : List (List Nat) :=
  items.map (fun item => bytes (STFSpec.Codec.Rlp.encode (wireItem item)))
/-- Full batch/error/extractor values for executable conformance gates. -/
def observations : List Observation :=
  let seed := ([0x44, 0].toByteArray : ByteArray)
  let batch := (recordBatch answer).run [seed]
  let otherAnswer := Hash32.ofBytes32 (FixedBytes.ofNat 256)
  let otherBatch := (recordBatch otherAnswer).run [seed]
  let adapter := adapterRun otherAnswer [seed]
  let inlineRun := ((childRefM failureQ node31).run).run ([seed], 9)
  let hashRun := ((childRefM failureQ node32).run).run ([seed], 9)
  let emptyRun := ((emptyRefM (m := ExceptT String (StateM (List ByteArray × Nat)))).run).run ([seed], 9)
  let observe : String → (Except String ChildRef × (List ByteArray × Nat)) → Observation :=
    fun label result => match result.1 with
    | .ok item => ⟨label, refs [item], result.2.1.map bytes, result.2.2, none⟩
    | .error error => ⟨label, [], result.2.1.map bytes, result.2.2, some error⟩
  let collisionWires := match extractCollision node32 node33 with
    | none => []
    | some (a, b) => [bytes a, bytes b]
  [{label := "ordered repeated full queries", wires := refs batch.1,
      queries := batch.2.map bytes, counter := 0, error := none},
    observe "inline failing oracle bypass" inlineRun,
    observe "hash state-changing failure" hashRun,
    observe "empty bypass" emptyRun,
    {label := "complete local collision", wires := collisionWires, queries := [], counter := 0, error := none},
    {label := "empty bytes list hash", wires := refs [.empty, .inline emptyList, .hashed answer],
      queries := [], counter := 0, error := none},
    {label := "nested accepted image", wires := [bytes nested.encode], queries := [], counter := 0, error := none},
    {label := "present empty value", wires := [bytes (asListNode emptyValueLeaf emptyValueLeaf_encodable).encode],
      queries := [], counter := 0, error := none},
    {label := "other full answer", wires := refs otherBatch.1, queries := otherBatch.2.map bytes,
      counter := 0, error := none},
    {label := "actual installed core adapter", wires := [bytes (STFSpec.Codec.Rlp.encode adapter.1)],
      queries := adapter.2.map bytes, counter := 0, error := none}]

end ToVCVio.Test
