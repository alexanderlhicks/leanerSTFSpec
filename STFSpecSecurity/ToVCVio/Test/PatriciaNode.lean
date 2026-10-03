/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import ToVCVio.Trie.PatriciaNode
import ToVCVio.Test.Reference
import STFSpec.Commit.Root

/-!
# Public Patricia node clients

Library `ToVCVio` in `STFSpecSecurity`.

Complete bytes/effects, generic proof clients and the total-core empty-value counterexample.
Spec guidance: `STFSpec/informal/modules/ToVCVio.md` §§4/7.
-/

namespace ToVCVio.Test.Patricia
open STFSpec.Base STFSpec.Codec STFSpec.Commit STFSpec.Hash ToVCVio.Rlp ToVCVio.Trie

/-- An arbitrary valid nonempty encoded byte value. -/
def value : PresentValue := ⟨[0x61].toByteArray, by decide⟩
/-- No generic path cap: this has 129 digits and both nibble extremes. -/
def longPath : Nibbles := Nibbles.ofList (List.replicate 128 15 ++ [0])
/-- All-zero digest presence is independent of digest contents. -/
def zeroHash : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat 0)
/-- Sixteen distinct full digest references in numeric position order. -/
def children : Vector ChildRef 16 :=
  Vector.ofFn (fun i => .hashed (Hash32.ofBytes32 (FixedBytes.ofNat i.val)))
/-- Every constructor has a public injection client. -/
theorem shell_injection (x y : PatriciaNode) (hx : FitsRlp x) (hy : FitsRlp y)
    (equal : preimage x = preimage y) : x = y := (preimage_inj x y hx hy).mp equal
/-- All sixteen branch positions and the terminal are observed through public laws. -/
theorem every_position (cs : Vector ChildRef 16) (terminal : Terminal) :
    (∀ i : Fin 16,
      ((cs.map wireItem).toList ++ [terminalItem terminal])[i.val]'(by simp; omega) =
        wireItem cs[i.val]) ∧
    ((cs.map wireItem).toList ++ [terminalItem terminal])[16]'(by simp) =
      terminalItem terminal := ⟨branch_child cs terminal, branch_terminal cs terminal⟩
/-- Public inverse applies to every finite path and both flags. -/
theorem canonical_hp (p : Nibbles) (leaf : Bool) :
    compactToNibbles (nibbleListToCompact p leaf) = .ok (p, leaf) :=
  compactToNibbles_nibbleListToCompact p leaf
/-- Resolved canonical extensions require an actual branch, not just an admissible digest. -/
theorem extension_kind (p : Nibbles) (tree : FullTree)
    (h : Canonical (.extension p tree)) :
    0 < p.size ∧ ∃ cs terminal, tree = .branch cs terminal ∧ Canonical tree :=
  (canonical_extension_iff p tree).mp h
/-- The pure preparation client requires safety but no unsecured flag. -/
theorem safe_image {K V : Type} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
    [TrieValue V] [KeyBytes K] (t : STFSpec.Commit.Trie K V) (safe : t.PrepareSafe) :
    NonemptyValues (prepareTrieModel t) := prepareTrieModel_nonemptyValues t safe
/-- Full callback actions, including errors/state, are the accepted coupling premise. -/
theorem adapter {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (q : ByteArray → m Hash32) (n : PatriciaNode) (h : FitsRlp n)
    (hq : q (preimage n) = KeccakQuery.keccak (m := m) (preimage n)) :
    wireItem <$> childRefM q (ToVCVio.Trie.asListNode n h) =
      encodeInternalNode (m := m) (some (toInternalNode n)) :=
  ToVCVio.Trie.callback_adapter q n h hq

/-- Canonical leaf HP bytes for empty, odd, even and extreme digits. -/
theorem hp_bytes :
    (nibbleListToCompact (Nibbles.ofList []) true).data.toList = [0x20] ∧
    (nibbleListToCompact (Nibbles.ofList [0]) true).data.toList = [0x30] ∧
    (nibbleListToCompact (Nibbles.ofList [15]) false).data.toList = [0x1f] ∧
    (nibbleListToCompact (Nibbles.ofList [0, 15]) false).data.toList = [0, 15] ∧
    (nibbleListToCompact longPath true).size = 65 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  rw [size_nibbleListToCompact]
  simp only [longPath, Nibbles.size_ofList, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]
/-- Distinct raw HP aliases remain accepted without becoming canonical raw bytes. -/
theorem hp_aliases :
    compactToNibbles [0x20].toByteArray = compactToNibbles [0xaf].toByteArray ∧
    ([0x20].toByteArray : ByteArray) ≠ [0xaf].toByteArray ∧
    compactToNibbles [0x1f].toByteArray = compactToNibbles [0xdf].toByteArray := by
  have even : compactToNibbles [0xaf].toByteArray = .ok (Nibbles.ofList [], true) :=
    (compactToNibbles_ok_iff _ _ _).mpr (by
      simp only [Nibbles.toList_ofList, List.toList_data_toByteArray]
      rfl)
  have odd : compactToNibbles [0xdf].toByteArray = .ok (Nibbles.ofList [15], false) :=
    (compactToNibbles_ok_iff _ _ _).mpr (by
      simp only [Nibbles.toList_ofList, List.toList_data_toByteArray]
      rfl)
  exact ⟨(canonical_hp _ _).trans even.symm, by decide,
    (canonical_hp _ _).trans odd.symm⟩
/-- Unrestricted optional bytes cannot injectively distinguish empty presence from absence. -/
def unrestrictedTerminal (terminal : Option ByteArray) : RlpItem :=
  .bytes (terminal.getD ByteArray.empty)
/-- This is a representation ambiguity, with exactly equal preimages. -/
theorem unrestricted_empty_counterexample :
    (none : Option ByteArray) ≠ some ByteArray.empty ∧
    unrestrictedTerminal none = unrestrictedTerminal (some ByteArray.empty) := ⟨by decide, rfl⟩
/-- A small certified leaf; empty remaining path is retained. -/
def leaf : PatriciaNode := .leaf (Nibbles.ofList []) value
/-- Complete HP/value/joined-payload certificate for the leaf. -/
theorem leaf_fits : FitsRlp leaf := by
  change STFSpec.Codec.Rlp.Encodable
    (assembleInternalNode (some (.leaf (Nibbles.ofList []) (.bytes value.val))))
  rw [encodable_assembleInternalNode_leaf_iff]
  refine ⟨by decide, ?_, by decide⟩
  rw [STFSpec.Codec.Rlp.encodable_bytes_iff]
  decide
/-- A branch certificate retains the whole joined outer payload. -/
def branch : PatriciaNode := .branch children (some value)
/-- Complete sixteen-reference/value/joined-payload certificate. -/
theorem branch_fits : FitsRlp branch := by
  change STFSpec.Codec.Rlp.Encodable
    (assembleInternalNode (some (.branch (children.map wireItem) (terminalItem (some value)))))
  rw [encodable_assembleInternalNode_branch_iff]
  constructor
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have hm : x ∈ (children.toList.map wireItem) := by simpa using hx
      rcases List.mem_map.mp hm with ⟨ref, _, rfl⟩
      exact wireItem_encodable ref
    · have he := List.mem_singleton.mp hx
      subst x
      rw [terminalItem, STFSpec.Codec.Rlp.encodable_bytes_iff]
      decide
  · decide +kernel
/-- An admissible inline reference to a real leaf, without a resolved branch claim. -/
def extension : PatriciaNode := .extension (Nibbles.ofList [15])
  (.inline (ToVCVio.Trie.asListNode leaf leaf_fits))
/-- Complete certificate for a nested inline extension. -/
theorem extension_fits : FitsRlp extension := by
  change STFSpec.Codec.Rlp.Encodable
    (assembleInternalNode (some (.extension (Nibbles.ofList [15])
      (wireItem (.inline (ToVCVio.Trie.asListNode leaf leaf_fits))))))
  rw [encodable_assembleInternalNode_extension_iff]
  refine ⟨by decide, wireItem_encodable _, ?_⟩
  decide
/-- Complete 31-byte and 32-byte shell preimages include the outer list and byte headers. -/
def widthLeaf (n : Nat) : PatriciaNode := .leaf (Nibbles.ofList [])
  ⟨⟨Array.replicate (n + 1) (0 : UInt8)⟩, by
    intro h
    have hs := congrArg ByteArray.size h
    rw [ByteArray.size_empty] at hs
    simp only [ByteArray.size, Array.size_replicate] at hs
    omega⟩
/-- Complete certificates include HP, values and joined payload at both threshold edges. -/
theorem width_fits : FitsRlp (widthLeaf 27) ∧ FitsRlp (widthLeaf 28) := by
  constructor <;> change STFSpec.Codec.Rlp.Encodable (assembled _) <;>
    simp only [assembled, toInternalNode, widthLeaf, encodable_assembleInternalNode_leaf_iff,
      STFSpec.Codec.Rlp.encodable_bytes_iff] <;> decide
/-- Complete threshold edges for the actual shell. -/
theorem widths : (preimage (widthLeaf 27)).size = 31 ∧
    (preimage (widthLeaf 28)).size = 32 := by decide
/-- All three constructor wires include their full payloads and long joined headers. -/
theorem complete_wires :
    (preimage leaf).data.toList = [0xc2, 0x20, 0x61] ∧
    (preimage extension).data.toList = [0xc4, 0x1f, 0xc2, 0x20, 0x61] := by decide

#guard (preimage branch).data.toList == [0xf9, 2, 0x11] ++
      (List.range 16).flatMap (fun i => [0xa0] ++ List.replicate 31 0 ++ [UInt8.ofNat i]) ++
      [0x61]
/-- Concrete occupancy guards include zero-hash presence and one child plus terminal. -/
def oneChild : Vector ChildRef 16 := Vector.ofFn
  (fun i => if i.val = 15 then .hashed zeroHash else .empty)
/-- Complete local occupancy boundary observations. -/
theorem local_occupancy :
    countOccupied (Vector.replicate 16 .empty) = 0 ∧
    countOccupied oneChild = 1 ∧ countOccupied children = 16 ∧
    LocallyAdmissible (.branch oneChild (some value)) ∧
    ¬ LocallyAdmissible (.branch oneChild none) ∧
    ¬ LocallyAdmissible (.branch (Vector.replicate 16 .empty) none) ∧
    ¬ LocallyAdmissible (.branch (Vector.replicate 16 .empty) (some value)) ∧
    LocallyAdmissible (.branch (Vector.ofFn (fun i =>
      if i.val < 2 then .hashed zeroHash else .empty)) none) ∧
    LocallyAdmissible extension ∧
    ¬ LocallyAdmissible (.extension (Nibbles.ofList []) (.hashed zeroHash)) := by
  decide
/-- Exactly one resolved child at the last numeric position. -/
def resolvedOne : Fin 16 → Option FullTree :=
  fun i => if i.val = 15 then some (.leaf (Nibbles.ofList []) value) else none
/-- One child plus terminal is canonical; one child alone is not. -/
theorem resolved_occupancy : Canonical (.branch resolvedOne (some value)) ∧
    ¬ Canonical (.branch resolvedOne none) := by
  have ho : fullCount resolvedOne = 1 := by decide
  constructor
  · apply canonical_one_child_terminal resolvedOne value _ ho
    intro i tree h
    unfold resolvedOne at h
    split at h
    · cases h
      exact .leaf _ _
    · cases h
  · exact not_canonical_one_child_absent resolvedOne ho
/-- Two resolved children and no terminal form a canonical branch. -/
def resolvedTwo : Fin 16 → Option FullTree :=
  fun i => if i.val < 2 then some (.leaf (Nibbles.ofList []) value) else none
/-- The two-child boundary supplies canonicality without terminal presence. -/
theorem canonical_two_children : Canonical (.branch resolvedTwo none) := by
  apply Canonical.branch
  · intro i tree h
    unfold resolvedTwo at h
    split at h
    · cases h
      exact .leaf _ _
    · cases h
  · decide
/-- Empty and long leaves, empty roots and a positive resolved extension retain their shape. -/
theorem canonical_shapes :
    Canonical (.leaf (Nibbles.ofList []) value) ∧ Canonical (.leaf longPath value) ∧
    CanonicalRoot none ∧
    Canonical (.extension (Nibbles.ofList [15]) (.branch resolvedTwo none)) :=
  ⟨.leaf _ _, .leaf _ _, True.intro,
    .extension _ _ _ (by decide) canonical_two_children⟩
/-- An extension to a resolved leaf is compressible even with a positive segment. -/
theorem not_extension_leaf (p q : Nibbles) (v : PresentValue) :
    ¬ Canonical (.extension p (.leaf q v)) := by
  intro h
  rcases (canonical_extension_iff _ _).mp h with ⟨_, _, _, he, _⟩
  cases he
/-- C7's total finite-map domain retains an empty terminal. -/
def mapWithEmpty : Std.ExtTreeMap Nibbles ByteArray :=
  Std.ExtTreeMap.ofList [(Nibbles.ofList [], ByteArray.empty),
    (Nibbles.ofList [1], [0x61].toByteArray), (Nibbles.ofList [2], [0x62].toByteArray)] compare
/-- The second map lacks that terminal binding. -/
def mapWithoutEmpty : Std.ExtTreeMap Nibbles ByteArray :=
  Std.ExtTreeMap.ofList [(Nibbles.ofList [1], [0x61].toByteArray),
    (Nibbles.ofList [2], [0x62].toByteArray)] compare
/-- Genuine actual C7 assembly on each complete finite map. -/
def mapPreimage (obj : Std.ExtTreeMap Nibbles ByteArray) : ByteArray :=
  STFSpec.Codec.Rlp.encode (assembleInternalNode
    (patricialize (m := Id) obj 0 (PatricializeDomain.zero obj)))
/-- Different stored maps have exactly equal complete C7 preimages, not a hash collision. -/
theorem actual_empty_counterexample :
    mapWithEmpty[(Nibbles.ofList [])]? = some ByteArray.empty ∧
    mapWithoutEmpty[(Nibbles.ofList [])]? = none := by decide

#guard mapPreimage mapWithEmpty == mapPreimage mapWithoutEmpty
/-- Only the map with an empty stored value lies outside the faithful value domain. -/
theorem excludes_empty_map : ¬ NonemptyValues mapWithEmpty := by
  intro h
  exact h _ _ actual_empty_counterexample.1 rfl
/-- The installed capability client retains arbitrary answers and initial trace. -/
def runShell (node : PatriciaNode) (h : FitsRlp node) (digest : Hash32)
    (seen : List ByteArray) : RlpItem × List ByteArray :=
  letI : KeccakQuery (StateM (List ByteArray)) :=
    ⟨fun bytes trace => (digest, trace ++ [bytes])⟩
  (wireItem <$> childRefM (KeccakQuery.keccak (m := StateM (List ByteArray)))
    (ToVCVio.Trie.asListNode node h)).run seen
/-- This proof client invokes the actual installed adapter. -/
theorem installed_adapter {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (node : PatriciaNode) (h : FitsRlp node) :
    wireItem <$> childRefM (KeccakQuery.keccak (m := m)) (ToVCVio.Trie.asListNode node h) =
      encodeInternalNode (m := m) (some (toInternalNode node)) :=
  ToVCVio.Trie.keccak_adapter node h
/-- Complete current observations for interpreted/native comparison. -/
def observations : List (List Nat) :=
  [preimage leaf, preimage extension, preimage branch,
    preimage (widthLeaf 27), preimage (widthLeaf 28),
    mapPreimage mapWithEmpty, mapPreimage mapWithoutEmpty,
    nibbleListToCompact longPath true,
    STFSpec.Codec.Rlp.encode (wireItem (.hashed zeroHash))].map ToVCVio.Test.bytes

end ToVCVio.Test.Patricia
