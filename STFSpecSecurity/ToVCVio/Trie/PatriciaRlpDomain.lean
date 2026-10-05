/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import ToVCVio.Trie.PatriciaReference

/-! Logical RLP-domain support for the finite resolved Patricia model.

The total noncomputable logical definitions are proof support, with no executable
width extraction or witness-construction contract. CompleteRlpDomain certifies
every present descendant and the shell's raw/joined RLP bounds; DescendantRlpDomain
deliberately omits the current shell's bounds. HP expressions remain separate by
flag. The interpretation laws hold for every fixed pure hash, without canonicality.
Pinned source context: `ethereum_rlp/rlp.py:92–109` (`encode_bytes`) and
`ethereum_rlp/rlp.py:112–128` (`encode_sequence`), locked ethereum-rlp 0.1.6; EELS
`src/ethereum/merkle_patricia_trie.py:213–249` supplies the child threshold.
These local logical models consume public provider laws, with no new source-operation refinement.
Library `ToVCVio` in `STFSpecSecurity`.
Spec guidance: `STFSpec/informal/modules/ToVCVio.md` §§4/5/7; Q56.
-/
namespace ToVCVio.Trie
open STFSpec.Base STFSpec.Codec STFSpec.Commit ToVCVio.Rlp
noncomputable section

private def lengthBound : Nat := 2 ^ 64

private def prefixWidth (n : Nat) : Nat :=
  if n < 56 then 1 else 1 + (Uint.toBeBytes n).size

private def byteWidth (b : ByteArray) : Nat :=
  if b.size = 1 ∧ (b[0]?.getD 128).toNat < 128 then b.size
  else prefixWidth b.size + b.size

private def hpLeafWidth (p : Nibbles) : Nat :=
  STFSpec.Codec.Rlp.encodedSize (.bytes (nibbleListToCompact p true))

private def hpExtensionWidth (p : Nibbles) : Nat :=
  STFSpec.Codec.Rlp.encodedSize (.bytes (nibbleListToCompact p false))

private def listWidth (payload : Nat) : Nat := prefixWidth payload + payload

private def wireWidthFromNodeWidth (width : Nat) : Nat :=
  if width < 32 then width else 33

private def terminalWidth : Terminal → Nat
  | none => 1
  | some v => byteWidth v.val

/-- Total logical joined payload width, counting every original numeric child occurrence. -/
noncomputable def rlpPayloadWidth (tree : FullTree) : Nat :=
  @FullTree.rec (fun _ => Nat) (fun _ => Nat)
    (fun p v => hpLeafWidth p + byteWidth v.val)
    (fun p _ childPayload => hpExtensionWidth p + wireWidthFromNodeWidth (listWidth childPayload))
    (fun _ terminal childWidths => (List.ofFn childWidths).sum + terminalWidth terminal)
    1 (fun _ childPayload => wireWidthFromNodeWidth (listWidth childPayload)) tree

/-- Total logical optional wire width: absence is one; present nodes use complete size. -/
noncomputable def rlpReferenceWidth (root : Option FullTree) : Nat :=
  @FullTree.rec_1 (fun _ => Nat) (fun _ => Nat)
    (fun p v => hpLeafWidth p + byteWidth v.val)
    (fun p _ childPayload => hpExtensionWidth p + wireWidthFromNodeWidth (listWidth childPayload))
    (fun _ terminal childWidths => (List.ofFn childWidths).sum + terminalWidth terminal)
    1 (fun _ childPayload => wireWidthFromNodeWidth (listWidth childPayload)) root

/-- Total logical complete list width, including the unconditional outer list header. -/
noncomputable def rlpNodeWidth (tree : FullTree) : Nat := listWidth (rlpPayloadWidth tree)

private def terminalBound : Terminal → Prop
  | none => True
  | some v => v.val.size < lengthBound

/-- Every present descendant and the current raw/joined shell fit the standard RLP domain.
This bounds each joined payload, not the complete encoded extent. -/
noncomputable def CompleteRlpDomain (tree : FullTree) : Prop :=
  @FullTree.rec (fun _ => Prop) (fun _ => Prop)
    (fun p v => p.size / 2 + 1 < lengthBound ∧ v.val.size < lengthBound ∧
      rlpPayloadWidth (.leaf p v) < lengthBound)
    (fun p child childCertificate => childCertificate ∧ p.size / 2 + 1 < lengthBound ∧
      rlpPayloadWidth (.extension p child) < lengthBound)
    (fun children terminal childCertificates => (∀ i : Fin 16, childCertificates i) ∧
      terminalBound terminal ∧ rlpPayloadWidth (.branch children terminal) < lengthBound)
    True (fun _ childCertificate => childCertificate) tree

private def rootCertificate (root : Option FullTree) : Prop :=
  @FullTree.rec_1 (fun _ => Prop) (fun _ => Prop)
    (fun p v => p.size / 2 + 1 < lengthBound ∧ v.val.size < lengthBound ∧
      rlpPayloadWidth (.leaf p v) < lengthBound)
    (fun p child childCertificate => childCertificate ∧ p.size / 2 + 1 < lengthBound ∧
      rlpPayloadWidth (.extension p child) < lengthBound)
    (fun children terminal childCertificates => (∀ i : Fin 16, childCertificates i) ∧
      terminalBound terminal ∧ rlpPayloadWidth (.branch children terminal) < lengthBound)
    True (fun _ childCertificate => childCertificate) root

/-- Complete certificates for strict descendants only; no own raw/joined shell bound. -/
noncomputable def DescendantRlpDomain : FullTree → Prop
  | .leaf _ _ => True
  | .extension _ child => CompleteRlpDomain child
  | .branch children _ => ∀ i : Fin 16, rootCertificate (children i)

private def actualPayloadWidth (node : PatriciaNode) : Nat :=
  match assembled node with
  | .bytes _ => 0
  | .list xs => (STFSpec.Codec.Rlp.encodePayloadModel xs).length
private theorem encodedSize_bytes (b : ByteArray) :
    STFSpec.Codec.Rlp.encodedSize (.bytes b) = byteWidth b := by
  rw [← STFSpec.Codec.Rlp.size_encode, STFSpec.Codec.Rlp.encode_bytes]
  simpa only [byteWidth, prefixWidth] using STFSpec.Codec.Rlp.size_encodeBytes b

private theorem encodedSize_list (xs : List RlpItem) :
    STFSpec.Codec.Rlp.encodedSize (.list xs) =
      listWidth (STFSpec.Codec.Rlp.encodePayloadModel xs).length := by
  rw [← STFSpec.Codec.Rlp.size_encode, STFSpec.Codec.Rlp.size_encode_list]
  rfl

private theorem encodedSize_wire_empty :
    STFSpec.Codec.Rlp.encodedSize (wireItem .empty) = 1 := by
  rw [wireItem, encodedSize_bytes]
  simp [byteWidth, prefixWidth]

private theorem encodedSize_wire_hashed (digest : Hash32) :
    STFSpec.Codec.Rlp.encodedSize (wireItem (.hashed digest)) = 33 := by
  rw [wireItem, encodedSize_bytes]
  simp [byteWidth, prefixWidth, Bytes.size_toByteArray, Hash32.size_toBytes]

private theorem facade_size (node : RlpListNode) :
    node.encode.size = STFSpec.Codec.Rlp.encodedSize node.val.val := by
  change (STFSpec.Codec.Rlp.encode node.val.val).size = _
  exact STFSpec.Codec.Rlp.size_encode _

private theorem encodedSize_ref (h : ByteArray → Hash32) (node : RlpListNode) :
    STFSpec.Codec.Rlp.encodedSize (wireItem (refWithHash h node)) =
      wireWidthFromNodeWidth (STFSpec.Codec.Rlp.encodedSize node.val.val) := by
  rw [refWithHash_eq, facade_size]
  by_cases small : STFSpec.Codec.Rlp.encodedSize node.val.val < 32
  · rw [ite_eq_left small, wireItem, wireWidthFromNodeWidth, ite_eq_left small]
  · rw [ite_eq_right small, wireWidthFromNodeWidth, ite_eq_right small]
    exact encodedSize_wire_hashed _

private theorem encodedSize_terminal (terminal : Terminal) :
    STFSpec.Codec.Rlp.encodedSize (terminalItem terminal) = terminalWidth terminal := by
  cases terminal with
  | none => simpa only [terminalItem, terminalWidth, wireItem] using encodedSize_wire_empty
  | some v => simpa only [terminalItem, terminalWidth] using encodedSize_bytes v.val

private theorem vector_toList (v : Vector ChildRef 16) :
    v.toList = List.ofFn (fun i : Fin 16 => v[i.val]) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [Vector.getElem_toList, List.getElem_ofFn]

private theorem encodedSize_node (node : PatriciaNode) :
    STFSpec.Codec.Rlp.encodedSize (assembled node) = listWidth (actualPayloadWidth node) := by
  obtain ⟨xs, hx⟩ := assembled_list node
  rw [hx, encodedSize_list]
  simp only [actualPayloadWidth, hx]

private theorem interpreted_payload {h : ByteArray → Hash32} {tree : FullTree}
      {node : PatriciaNode} (derivation : NodeInterprets h tree node) :
      actualPayloadWidth node = rlpPayloadWidth tree := by
    induction derivation using NodeInterprets.rec
      (motive_2 := fun root reference _ =>
        STFSpec.Codec.Rlp.encodedSize (wireItem reference) = rlpReferenceWidth root) with
    | leaf p v =>
      simp only [rlpPayloadWidth]
      change (STFSpec.Codec.Rlp.encodePayloadModel
        [.bytes (nibbleListToCompact p true), .bytes v.val]).length = _
      rw [STFSpec.Codec.Rlp.length_encodePayloadModel]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        encodedSize_bytes, hpLeafWidth]
    | extension p child reference childDerivation ih =>
      simp only [rlpPayloadWidth]
      change (STFSpec.Codec.Rlp.encodePayloadModel
        [.bytes (nibbleListToCompact p false), wireItem reference]).length = _
      rw [STFSpec.Codec.Rlp.length_encodePayloadModel]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      rw [ih]
      rfl
    | branch children references terminal childDerivations ih =>
      simp only [rlpPayloadWidth]
      change (STFSpec.Codec.Rlp.encodePayloadModel
        ((references.map wireItem).toList ++ [terminalItem terminal])).length = _
      rw [STFSpec.Codec.Rlp.length_encodePayloadModel, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      rw [Vector.toList_map, List.map_map, vector_toList, List.map_ofFn]
      have equality :
          (fun i : Fin 16 => STFSpec.Codec.Rlp.encodedSize (wireItem references[i.val])) =
            (fun i : Fin 16 => rlpReferenceWidth (children i)) := by
        funext i
        exact ih i
      change (List.ofFn (fun i : Fin 16 =>
        STFSpec.Codec.Rlp.encodedSize (wireItem references[i.val]))).sum +
          STFSpec.Codec.Rlp.encodedSize (terminalItem terminal) = _
      rw [equality, encodedSize_terminal]
      rfl
    | empty => exact encodedSize_wire_empty
    | present tree node nodeDerivation fits ih =>
      rw [encodedSize_ref, asListNode_item, encodedSize_node, ih]
      rfl

private theorem interpreted_reference {h : ByteArray → Hash32} {root : Option FullTree}
      {reference : ChildRef} (derivation : RefInterprets h root reference) :
      STFSpec.Codec.Rlp.encodedSize (wireItem reference) = rlpReferenceWidth root := by
    cases derivation with
    | empty => exact encodedSize_wire_empty
    | present tree node nodeDerivation fits =>
      rw [encodedSize_ref, asListNode_item, encodedSize_node,
        interpreted_payload nodeDerivation]
      rfl

private theorem interpreted_encodedWidth {h : ByteArray → Hash32} {tree : FullTree}
    {node : PatriciaNode} (derivation : NodeInterprets h tree node) :
    STFSpec.Codec.Rlp.encodedSize (assembled node) = rlpNodeWidth tree := by
  rw [encodedSize_node, interpreted_payload derivation]
  rfl

private def topCertificate : FullTree → Prop
  | .leaf p v =>
      p.size / 2 + 1 < lengthBound ∧ v.val.size < lengthBound ∧
        rlpPayloadWidth (.leaf p v) < lengthBound
  | .extension p child =>
      p.size / 2 + 1 < lengthBound ∧ rlpPayloadWidth (.extension p child) < lengthBound
  | .branch children terminal =>
      terminalBound terminal ∧ rlpPayloadWidth (.branch children terminal) < lengthBound

private theorem complete_iff_descendants_top (tree : FullTree) :
    CompleteRlpDomain tree ↔ DescendantRlpDomain tree ∧ topCertificate tree := by
  cases tree with
  | leaf p v => simp only [CompleteRlpDomain, DescendantRlpDomain, topCertificate, true_and]
  | extension p child => rfl
  | branch children terminal => rfl

private theorem terminal_encodable (terminal : Terminal) :
    STFSpec.Codec.Rlp.Encodable (terminalItem terminal) ↔ terminalBound terminal := by
  cases terminal with
  | none =>
    simp only [terminalItem, terminalBound, STFSpec.Codec.Rlp.encodable_bytes_iff]
    decide
  | some v => exact STFSpec.Codec.Rlp.encodable_bytes_iff v.val

private theorem fits_leaf (p : Nibbles) (v : PresentValue) :
    FitsRlp (.leaf p v) ↔ p.size / 2 + 1 < lengthBound ∧
      v.val.size < lengthBound ∧ actualPayloadWidth (.leaf p v) < lengthBound := by
  change STFSpec.Codec.Rlp.Encodable
    (assembleInternalNode (some (.leaf p (.bytes v.val)))) ↔ _
  rw [encodable_assembleInternalNode_leaf_iff, STFSpec.Codec.Rlp.encodable_bytes_iff]
  rfl

private theorem fits_extension (p : Nibbles) (reference : ChildRef) :
    FitsRlp (.extension p reference) ↔ p.size / 2 + 1 < lengthBound ∧
      actualPayloadWidth (.extension p reference) < lengthBound := by
  change STFSpec.Codec.Rlp.Encodable
    (assembleInternalNode (some (.extension p (wireItem reference)))) ↔ _
  rw [encodable_assembleInternalNode_extension_iff]
  simp only [wireItem_encodable, true_and]
  rfl

private theorem fits_branch (references : Vector ChildRef 16) (terminal : Terminal) :
    FitsRlp (.branch references terminal) ↔ terminalBound terminal ∧
      actualPayloadWidth (.branch references terminal) < lengthBound := by
  change STFSpec.Codec.Rlp.Encodable
    (assembleInternalNode (some (.branch (references.map wireItem) (terminalItem terminal)))) ↔ _
  rw [encodable_assembleInternalNode_branch_iff]
  have children_valid : ∀ x ∈ (references.map wireItem).toList,
      STFSpec.Codec.Rlp.Encodable x := by
    intro x hx
    rw [Vector.toList_map] at hx
    obtain ⟨reference, _, rfl⟩ := List.mem_map.mp hx
    exact wireItem_encodable reference
  constructor
  · intro cert
    have ht := cert.1 (terminalItem terminal) (List.mem_append.mpr (Or.inr (by simp)))
    exact ⟨(terminal_encodable terminal).mp ht, cert.2⟩
  · intro cert
    refine ⟨?_, cert.2⟩
    intro x hx
    rcases List.mem_append.mp hx with hc | ht
    · exact children_valid x hc
    · have equality : x = terminalItem terminal := by simpa using ht
      subst x
      exact (terminal_encodable terminal).mpr cert.1

private theorem fits_iff_top {h : ByteArray → Hash32} {tree : FullTree}
    {node : PatriciaNode} (derivation : NodeInterprets h tree node) :
    FitsRlp node ↔ topCertificate tree := by
  have width := interpreted_payload derivation
  cases derivation with
  | leaf p v =>
    rw [fits_leaf, width]
    rfl
  | extension p child reference childDerivation =>
    rw [fits_extension, width]
    rfl
  | branch children references terminal childDerivations =>
    rw [fits_branch, width]
    rfl

private theorem interpreted_descendants {h : ByteArray → Hash32} {tree : FullTree}
    {node : PatriciaNode} (derivation : NodeInterprets h tree node) :
    DescendantRlpDomain tree := by
  induction derivation using NodeInterprets.rec
    (motive_2 := fun root _ _ => rootCertificate root) with
  | leaf p v => trivial
  | extension p child reference childDerivation ih => exact ih
  | branch children references terminal childDerivations ih => exact ih
  | empty => trivial
  | present tree node nodeDerivation fits ih =>
    exact (complete_iff_descendants_top tree).mpr ⟨ih, (fits_iff_top nodeDerivation).mp fits⟩

private theorem complete_of_interpreted_node {h : ByteArray → Hash32} {tree : FullTree}
    {node : PatriciaNode} (derivation : NodeInterprets h tree node) (fits : FitsRlp node) :
    CompleteRlpDomain tree :=
  (complete_iff_descendants_top tree).mpr
    ⟨interpreted_descendants derivation, (fits_iff_top derivation).mp fits⟩

private theorem complete_of_interpreted_reference {h : ByteArray → Hash32}
    {root : Option FullTree} {reference : ChildRef}
    (derivation : RefInterprets h root reference) : rootCertificate root := by
  cases derivation with
  | empty => trivial
  | present tree node nodeDerivation fits =>
    exact complete_of_interpreted_node nodeDerivation fits

private theorem construct_certified_node (tree : FullTree) :
    ∀ h : ByteArray → Hash32, CompleteRlpDomain tree →
      ∃ node, NodeInterprets h tree node ∧ FitsRlp node := by
  induction tree using FullTree.rec
    (motive_2 := fun root => ∀ h : ByteArray → Hash32, rootCertificate root →
      ∃ reference, RefInterprets h root reference) with
  | leaf p v =>
    intro h cert
    have derivation : NodeInterprets h (.leaf p v) (.leaf p v) := .leaf p v
    exact ⟨.leaf p v, derivation,
      (fits_iff_top derivation).mpr ((complete_iff_descendants_top _).mp cert).2⟩
  | extension p child ih =>
    intro h cert
    obtain ⟨childNode, childDerivation, childFits⟩ := ih h cert.1
    let reference := refWithHash h (asListNode childNode childFits)
    have childReference : RefInterprets h (some child) reference :=
      .present child childNode childDerivation childFits
    have derivation : NodeInterprets h (.extension p child) (.extension p reference) :=
      .extension p child reference childReference
    exact ⟨.extension p reference, derivation,
      (fits_iff_top derivation).mpr ((complete_iff_descendants_top _).mp cert).2⟩
  | branch children terminal ih =>
    intro h cert
    classical
    let references : Vector ChildRef 16 :=
      Vector.ofFn (fun i : Fin 16 => Classical.choose (ih i h (cert.1 i)))
    have derivations : ∀ i : Fin 16, RefInterprets h (children i) references[i.val] := by
      intro i
      simpa [references] using Classical.choose_spec (ih i h (cert.1 i))
    have derivation : NodeInterprets h (.branch children terminal)
        (.branch references terminal) := .branch children references terminal derivations
    exact ⟨.branch references terminal, derivation,
      (fits_iff_top derivation).mpr ((complete_iff_descendants_top _).mp cert).2⟩
  | none =>
    exact ⟨.empty, .empty⟩
  | some tree ih =>
    rename_i h cert
    obtain ⟨node, derivation, fits⟩ := ih h cert
    exact ⟨refWithHash h (asListNode node fits), .present tree node derivation fits⟩

private theorem construct_reference (root : Option FullTree) (h : ByteArray → Hash32)
    (cert : rootCertificate root) : ∃ reference, RefInterprets h root reference := by
  cases root with
  | none => exact ⟨.empty, .empty⟩
  | some tree =>
    obtain ⟨node, derivation, fits⟩ := construct_certified_node tree h cert
    exact ⟨refWithHash h (asListNode node fits), .present tree node derivation fits⟩

private theorem construct_node (tree : FullTree) (h : ByteArray → Hash32)
    (cert : DescendantRlpDomain tree) : ∃ node, NodeInterprets h tree node := by
  cases tree with
  | leaf p v => exact ⟨.leaf p v, .leaf p v⟩
  | extension p child =>
    obtain ⟨reference, derivation⟩ := construct_reference (some child) h cert
    exact ⟨.extension p reference, .extension p child reference derivation⟩
  | branch children terminal =>
    classical
    let references : Vector ChildRef 16 :=
      Vector.ofFn (fun i : Fin 16 =>
        Classical.choose (construct_reference (children i) h (cert i)))
    have derivations : ∀ i : Fin 16, RefInterprets h (children i) references[i.val] := by
      intro i
      simpa [references] using
        Classical.choose_spec (construct_reference (children i) h (cert i))
    exact ⟨.branch references terminal, .branch children references terminal derivations⟩

private theorem DescendantRlpDomain_iff_node (h : ByteArray → Hash32) (tree : FullTree) :
    DescendantRlpDomain tree ↔ ∃ node, NodeInterprets h tree node := by
  constructor
  · exact construct_node tree h
  · rintro ⟨node, derivation⟩
    exact interpreted_descendants derivation

private theorem CompleteRlpDomain_iff_node_fits (h : ByteArray → Hash32) (tree : FullTree) :
    CompleteRlpDomain tree ↔ ∃ node, NodeInterprets h tree node ∧ FitsRlp node := by
  constructor
  · exact construct_certified_node tree h
  · rintro ⟨node, derivation, fits⟩
    exact complete_of_interpreted_node derivation fits

private theorem CompleteRlpDomain_iff_reference (h : ByteArray → Hash32) (tree : FullTree) :
    CompleteRlpDomain tree ↔ ∃ reference, RefInterprets h (some tree) reference := by
  constructor
  · exact construct_reference (some tree) h
  · rintro ⟨reference, derivation⟩
    exact complete_of_interpreted_reference derivation


/-- Exact joined payload width of any actual structural node interpretation. -/
theorem node_interprets_payload_width
    {h : ByteArray → Hash32} {tree : FullTree} {node : PatriciaNode}
    (derivation : NodeInterprets h tree node) :
    (match assembled node with
     | .bytes _ => 0
     | .list xs => (STFSpec.Codec.Rlp.encodePayloadModel xs).length) =
      rlpPayloadWidth tree := interpreted_payload derivation

/-- Exact complete encoded width; this is not a payload-domain bound. -/
theorem node_interprets_encoded_width
    {h : ByteArray → Hash32} {tree : FullTree} {node : PatriciaNode}
    (derivation : NodeInterprets h tree node) :
    STFSpec.Codec.Rlp.encodedSize (assembled node) = rlpNodeWidth tree :=
  interpreted_encodedWidth derivation

/-- Wire width uses the complete node threshold, including the 32-byte case. -/
theorem ref_interprets_wire_width
    {h : ByteArray → Hash32} {root : Option FullTree} {reference : ChildRef}
    (derivation : RefInterprets h root reference) :
    STFSpec.Codec.Rlp.encodedSize (wireItem reference) = rlpReferenceWidth root :=
  interpreted_reference derivation

/-- Bare node inhabitation requires exactly the strict descendants' certificates. -/
theorem descendantRlpDomain_iff_nodeInterprets
    (h : ByteArray → Hash32) (tree : FullTree) :
    DescendantRlpDomain tree ↔ ∃ node, NodeInterprets h tree node :=
  DescendantRlpDomain_iff_node h tree

/-- Whole-node Fits adds precisely the current raw/joined bounds. -/
theorem completeRlpDomain_iff_nodeInterprets_fits
    (h : ByteArray → Hash32) (tree : FullTree) :
    CompleteRlpDomain tree ↔ ∃ node, NodeInterprets h tree node ∧ FitsRlp node :=
  CompleteRlpDomain_iff_node_fits h tree

/-- Complete recursive certificates are exactly present-reference inhabitation. -/
theorem completeRlpDomain_iff_refInterprets
    (h : ByteArray → Hash32) (tree : FullTree) :
    CompleteRlpDomain tree ↔ ∃ reference, RefInterprets h (some tree) reference :=
  CompleteRlpDomain_iff_reference h tree

end
end ToVCVio.Trie
