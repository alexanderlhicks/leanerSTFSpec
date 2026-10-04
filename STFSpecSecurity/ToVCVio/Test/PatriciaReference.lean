/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import ToVCVio.Trie.PatriciaReference
import ToVCVio.Test.PatriciaNode

/-!
# Public conditional reference-interpretation clients

Library `ToVCVio` in `STFSpecSecurity`.

Ordinary all-finite/full-value clients, necessary-premise controls and modest certified
wire fixtures. Huge witnesses occur only in erased symbolic proofs, never runtime code.
Spec guidance: `STFSpec/informal/modules/ToVCVio.md` §§4/7.
-/

namespace ToVCVio.Test.PatriciaReference
open STFSpec.Base STFSpec.Codec STFSpec.Commit ToVCVio.Rlp ToVCVio.Trie

/-- Arbitrary fixed hash, complete paths and full values retain both reference conclusions. -/
theorem arbitrary_reference (h : ByteArray → Hash32) (resolved : Option FullTree)
    (reference : ChildRef) (d : RefInterprets h resolved reference) :
    AdmissibleRef reference ∧ occupied reference = resolved.isSome :=
  ⟨ref_interprets_admissible d, ref_interprets_occupied d⟩

/-- Every finite leaf path retains the entire supplied nonempty byte value. -/
theorem arbitrary_leaf (h : ByteArray → Hash32) (p : Nibbles) (v : PresentValue) :
    NodeInterprets h (.leaf p v) (.leaf p v) ∧ LocallyAdmissible (.leaf p v) :=
  ⟨.leaf p v, node_interprets_locally_admissible (h := h) (.leaf p v) (.leaf p v)⟩

/-- The present constructor consumes the complete shell certificate. -/
theorem certified_present (h : ByteArray → Hash32) (tree : FullTree) (node : PatriciaNode)
    (d : NodeInterprets h tree node) (fits : FitsRlp node) :
    RefInterprets h (some tree) (refWithHash h (ToVCVio.Trie.asListNode node fits)) :=
  .present tree node d fits

/-- Every natural finite length is covered without a frontend cap. -/
theorem arbitrary_length (h : ByteArray → Hash32) (n : Nat) (v : PresentValue) :
    NodeInterprets h (.leaf (Nibbles.ofList (List.replicate n 15)) v)
      (.leaf (Nibbles.ofList (List.replicate n 15)) v) := .leaf _ _

/-- Leaf derivation preserves complete fields, not only support or encoded width. -/
theorem leaf_fields (h : ByteArray → Hash32) (p : Nibbles) (v : PresentValue)
    (node : PatriciaNode) (d : NodeInterprets h (.leaf p v) node) : node = .leaf p v := by
  cases d
  rfl

/-- Positive canonical branch extensions retain the exact path and certified child. -/
theorem canonical_extension (h : ByteArray → Hash32) (p : Nibbles) (positive : 0 < p.size)
    (children : Fin 16 → Option FullTree) (references : Vector ChildRef 16)
    (terminal : Terminal) (canonical : Canonical (.branch children terminal))
    (ds : ∀ i : Fin 16, RefInterprets h (children i) references[i.val])
    (fits : FitsRlp (.branch references terminal)) :
    LocallyAdmissible (.extension p
      (refWithHash h (ToVCVio.Trie.asListNode (.branch references terminal) fits))) := by
  apply node_interprets_locally_admissible
    (tree := .extension p (.branch children terminal))
  · exact .extension p children terminal positive canonical
  · exact .extension p _ _ (.present _ _ (.branch children references terminal ds) fits)

/-- Only absent resolved children can derive the empty reference. -/
theorem absence (h : ByteArray → Hash32) (reference : ChildRef)
    (d : RefInterprets h none reference) : reference = .empty := by
  cases d
  rfl

/-- Present children cannot acquire an empty reference, even with an all-zero answer. -/
theorem presence (h : ByteArray → Hash32) (tree : FullTree) :
    ¬ RefInterprets h (some tree) .empty := by
  intro d
  have impossible := ref_interprets_occupied d
  contradiction

/-- Every original numeric branch position and the exact terminal are retained. -/
theorem branch_fields (h : ByteArray → Hash32) (children : Fin 16 → Option FullTree)
    (references : Vector ChildRef 16) (terminal : Terminal)
    (ds : ∀ i : Fin 16, RefInterprets h (children i) references[i.val]) :
    NodeInterprets h (.branch children terminal) (.branch references terminal) ∧
    (∀ i : Fin 16, occupied references[i.val] = (children i).isSome) :=
  ⟨.branch children references terminal ds, fun i ↦ ref_interprets_occupied (ds i)⟩

/-- One child plus terminal retains the canonical occupancy premise at every position. -/
theorem terminal_plus_one (h : ByteArray → Hash32) (children : Fin 16 → Option FullTree)
    (references : Vector ChildRef 16) (v : PresentValue)
    (hc : ∀ i tree, children i = some tree → Canonical tree) (count : fullCount children = 1)
    (ds : ∀ i : Fin 16, RefInterprets h (children i) references[i.val]) :
    LocallyAdmissible (.branch references (some v)) :=
  node_interprets_locally_admissible (canonical_one_child_terminal _ _ hc count)
    (.branch children references (some v) ds)

/-- Two children without a terminal retain two distinct occupied positions. -/
theorem two_without_terminal (h : ByteArray → Hash32)
    (children : Fin 16 → Option FullTree) (references : Vector ChildRef 16)
    (hc : ∀ i tree, children i = some tree → Canonical tree) (count : fullCount children = 2)
    (ds : ∀ i : Fin 16, RefInterprets h (children i) references[i.val]) :
    LocallyAdmissible (.branch references none) := by
  apply node_interprets_locally_admissible (tree := .branch children none)
  · apply Canonical.branch _ _ hc
    simp [count, terminalCount]
  · exact .branch children references none ds

/-- Identical children are sixteen occurrences, for either terminal presence. -/
theorem repeated_children (h : ByteArray → Hash32) (p : Nibbles) (v : PresentValue)
    (fits : FitsRlp (.leaf p v)) (terminal : Terminal) :
    LocallyAdmissible (.branch
      (Vector.ofFn fun _ ↦ refWithHash h (ToVCVio.Trie.asListNode (.leaf p v) fits))
      terminal) := by
  apply node_interprets_locally_admissible
    (tree := .branch (fun _ ↦ some (.leaf p v)) terminal)
  · apply Canonical.branch
    · intro i tree equality
      cases equality
      exact .leaf _ _
    · have count : fullCount (fun _ : Fin 16 ↦ some (FullTree.leaf p v)) = 16 := by
        simp [fullCount]
      rw [count]
      omega
  · apply NodeInterprets.branch
    intro i
    simpa only [Vector.getElem_ofFn] using
      (RefInterprets.present (.leaf p v) (.leaf p v) (.leaf p v) fits (h := h))

/-- A positive extension to a leaf can derive and be locally admissible, but is not canonical. -/
theorem extension_leaf_control (h : ByteArray → Hash32) (p q : Nibbles)
    (positive : 0 < p.size) (v : PresentValue) (fits : FitsRlp (.leaf q v)) :
    NodeInterprets h (.extension p (.leaf q v))
      (.extension p (refWithHash h (ToVCVio.Trie.asListNode (.leaf q v) fits))) ∧
    LocallyAdmissible
      (.extension p (refWithHash h (ToVCVio.Trie.asListNode (.leaf q v) fits))) ∧
    ¬ Canonical (.extension p (.leaf q v)) := by
  have d := RefInterprets.present (.leaf q v) (.leaf q v) (.leaf q v) fits (h := h)
  exact ⟨.extension p _ _ d,
    ⟨positive, ref_interprets_occupied d, ref_interprets_admissible d⟩,
    ToVCVio.Test.Patricia.not_extension_leaf p q v⟩

/-- Arbitrary path size is a symbolic premise; no huge packed array is evaluated. -/
theorem huge_top_missing (h : ByteArray → Hash32) (p : Nibbles) (v : PresentValue)
    (size : p.size = 2 ^ 65) :
    Canonical (.leaf p v) ∧ NodeInterprets h (.leaf p v) (.leaf p v) ∧
    ¬ FitsRlp (.leaf p v) := by
  refine ⟨.leaf p v, .leaf p v, ?_⟩
  intro fits
  change Rlp.Encodable (assembleInternalNode (some (.leaf p (.bytes v.val)))) at fits
  have bound := ((encodable_assembleInternalNode_leaf_iff p (.bytes v.val)).mp fits).1
  rw [size] at bound
  have impossible : ¬ (2 ^ 65 / 2 + 1 < (2 ^ 64 : Nat)) := by decide
  exact impossible bound

/-- The huge path is a proof-only existential witness; length is rewritten symbolically. -/
theorem huge_path_witness (h : ByteArray → Hash32) (v : PresentValue) :
    ∃ p : Nibbles, p.size = 2 ^ 65 ∧ Canonical (.leaf p v) ∧
      NodeInterprets h (.leaf p v) (.leaf p v) ∧ ¬ FitsRlp (.leaf p v) := by
  let p := Nibbles.ofList (List.replicate (2 ^ 65) (15 : Fin 16))
  have size : p.size = 2 ^ 65 := by
    simp only [p, Nibbles.size_ofList, List.length_replicate]
  exact ⟨p, size, huge_top_missing h p v size⟩

/-- Individual byte/HP bounds do not imply the joined complete shell certificate. -/
theorem joined_certificate_missing (v : PresentValue) (size : v.val.size = 2 ^ 64 - 1) :
    Rlp.Encodable (.bytes v.val) ∧
    Rlp.Encodable (.bytes (nibbleListToCompact (Nibbles.ofList []) true)) ∧
    ¬ FitsRlp (.leaf (Nibbles.ofList []) v) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Rlp.encodable_bytes_iff, size]
    decide
  · rw [Rlp.encodable_bytes_iff, size_nibbleListToCompact, Nibbles.size_ofList]
    decide
  · intro fits
    change Rlp.Encodable
      (assembleInternalNode (some (.leaf (Nibbles.ofList []) (.bytes v.val)))) at fits
    have bound := ((encodable_assembleInternalNode_leaf_iff _ _).mp fits).2.2
    rw [Rlp.length_encodePayloadModel] at bound
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at bound
    have nonsingle : ¬ (v.val.size = 1 ∧ (v.val[0]?.getD 128).toNat < 128) := by
      intro single
      have := single.1
      omega
    have wide : ¬ v.val.size < 56 := by omega
    have width : Rlp.encodedSize (.bytes v.val) =
        (1 + (Uint.toBeBytes v.val.size).size) + v.val.size := by
      rw [← Rlp.size_encode, Rlp.encode_bytes, Rlp.size_encodeBytes,
        ite_eq_right nonsingle, ite_eq_right wide]
    rw [width] at bound
    omega

/-- Complete bytes with leading/trailing zeros and 255 are preserved verbatim. -/
def value : PresentValue := ⟨[0, 255, 0].toByteArray, by decide⟩
/-- The full all-zero digest remains a present hashed reference. -/
def zeroHash : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat 0)
/-- Small concrete values yield complete preimage widths 31, 32 and 33. -/
def edgeLeaf (extra : Nat) : PatriciaNode := .leaf (Nibbles.ofList [])
  ⟨⟨Array.replicate (extra + 28) (0 : UInt8)⟩, by
    intro equality
    have sizes := congrArg ByteArray.size equality
    rw [ByteArray.size_empty] at sizes
    simp only [ByteArray.size, Array.size_replicate] at sizes
    omega⟩
/-- Each threshold fixture retains the entire HP/value/joined certificate. -/
theorem edge_fits : FitsRlp (edgeLeaf 0) ∧ FitsRlp (edgeLeaf 1) ∧ FitsRlp (edgeLeaf 2) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    change Rlp.Encodable (assembled _) <;>
    simp only [assembled, toInternalNode, edgeLeaf, encodable_assembleInternalNode_leaf_iff,
      Rlp.encodable_bytes_iff] <;> decide
/-- Full preimages include both headers, not merely the value payload. -/
theorem threshold_preimages :
    (preimage (edgeLeaf 0)).data.toList = [0xde, 0x20, 0x9c] ++ List.replicate 28 0 ∧
    (preimage (edgeLeaf 1)).data.toList = [0xdf, 0x20, 0x9d] ++ List.replicate 29 0 ∧
    (preimage (edgeLeaf 2)).data.toList = [0xe0, 0x20, 0x9e] ++ List.replicate 30 0 := by
  decide
/-- Threshold references use complete width, with all bytes of the same answer retained. -/
theorem threshold_references (h : ByteArray → Hash32) :
    refWithHash h (ToVCVio.Trie.asListNode (edgeLeaf 0) edge_fits.1) =
      .inline (ToVCVio.Trie.asListNode (edgeLeaf 0) edge_fits.1) ∧
    refWithHash h (ToVCVio.Trie.asListNode (edgeLeaf 1) edge_fits.2.1) =
      .hashed (h (preimage (edgeLeaf 1))) ∧
    refWithHash h (ToVCVio.Trie.asListNode (edgeLeaf 2) edge_fits.2.2) =
      .hashed (h (preimage (edgeLeaf 2))) := by
  simp only [refWithHash_eq]
  exact ⟨ite_eq_left (by decide), ite_eq_right (by decide), ite_eq_right (by decide)⟩
/-- Zero extensions and dead, terminal-only, compressible branches omit necessary shape. -/
theorem canonical_omissions (children : Fin 16 → Option FullTree)
    (one : fullCount children = 1) (v : PresentValue) (tree : FullTree) :
    ¬ Canonical (.extension (Nibbles.ofList []) tree) ∧
    ¬ Canonical (.branch (fun _ ↦ none) none) ∧
    ¬ Canonical (.branch (fun _ ↦ none) (some v)) ∧
    ¬ Canonical (.branch children none) := by
  refine ⟨not_canonical_zero_extension tree, ?_, ?_, not_canonical_one_child_absent _ one⟩
  · intro canonical
    have bound := ((canonical_branch_iff _ _).mp canonical).2
    simp [fullCount, terminalCount] at bound
  · intro canonical
    have bound := ((canonical_branch_iff _ _).mp canonical).2
    simp [fullCount, terminalCount] at bound

/-- An actual certified 32-byte preimage yields occupied zero-hash references. -/
theorem zero_answer :
    refWithHash (fun _ ↦ zeroHash)
      (ToVCVio.Trie.asListNode (edgeLeaf 1) edge_fits.2.1) = .hashed zeroHash ∧
    occupied (.hashed zeroHash) = true :=
  ⟨(threshold_references (fun _ ↦ zeroHash)).2.1, occupied_hashed zeroHash⟩

/-- Exact empty, odd, even and 129-digit shells for complete-byte runtime observation. -/
def paths : List Nibbles := [Nibbles.ofList [], Nibbles.ofList [0],
  Nibbles.ofList [15, 0], Nibbles.ofList (List.replicate 128 15 ++ [0])]
/-- Sixteen repeated zero digests keep all positions and the exact nonempty terminal. -/
def repeatedBranch (terminal : Terminal) : PatriciaNode :=
  .branch (Vector.ofFn fun _ ↦ .hashed zeroHash) terminal
/-- Complete joined payload bounds remain part of both branch certificates. -/
theorem repeated_branch_fits :
    FitsRlp (repeatedBranch none) ∧ FitsRlp (repeatedBranch (some value)) := by
  constructor
  all_goals
    change Rlp.Encodable (assembled _)
    simp only [assembled, toInternalNode, repeatedBranch,
      encodable_assembleInternalNode_branch_iff]
    constructor
    · intro item member
      rcases List.mem_append.mp member with child | terminal
      · have child' : item ∈ (Vector.ofFn (fun _ : Fin 16 ↦
            ChildRef.hashed zeroHash)).toList.map wireItem := by simpa using child
        rcases List.mem_map.mp child' with ⟨reference, _, rfl⟩
        exact wireItem_encodable reference
      · have equal := List.mem_singleton.mp terminal
        subst item
        rw [terminalItem, Rlp.encodable_bytes_iff]
        decide
    · decide +kernel
/-- Full repeated branches retain the long outer header and all sixteen 32-byte answers. -/
theorem repeated_branch_bytes :
    (preimage (repeatedBranch none)).data.toList = [0xf9, 2, 0x11] ++
      (List.replicate 16 ([0xa0] ++ List.replicate 32 0)).flatten ++ [0x80] ∧
    (preimage (repeatedBranch (some value))).data.toList = [0xf9, 2, 0x14] ++
      (List.replicate 16 ([0xa0] ++ List.replicate 32 0)).flatten ++ [0x83, 0, 255, 0] := by
  decide +kernel
/-- Complete modest public shell/reference observations; no Prop witness is extracted. -/
def observations : List (List Nat) :=
  ((paths.map fun p ↦ preimage (.leaf p value)) ++
    [preimage (edgeLeaf 0), preimage (edgeLeaf 1), preimage (edgeLeaf 2),
      preimage (repeatedBranch none), preimage (repeatedBranch (some value)),
      Rlp.encode (wireItem (refWithHash (fun _ ↦ zeroHash)
        (ToVCVio.Trie.asListNode (edgeLeaf 0) edge_fits.1))),
      Rlp.encode (wireItem (refWithHash (fun _ ↦ zeroHash)
        (ToVCVio.Trie.asListNode (edgeLeaf 1) edge_fits.2.1))),
      Rlp.encode (wireItem (refWithHash (fun _ ↦ zeroHash)
        (ToVCVio.Trie.asListNode (edgeLeaf 2) edge_fits.2.2)))]).map
      (fun bytes ↦ bytes.data.toList.map UInt8.toNat)
end ToVCVio.Test.PatriciaReference
