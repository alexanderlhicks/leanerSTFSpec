/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import ToVCVio.Trie.PatriciaRlpDomain

/-! Logical domain clients and complete modest executable observations.
Clients apply public laws and unfold public logical definitions; those reductions
also depend on the definitions' private scalar and recursor implementations.
Private scalar mirrors support these proofs, not an independent model comparison.
Huge paths/abstract values appear only in erased symbolic proofs. Runtime rows
use existing executable codec/HP/shell/wire providers, never logical width folds
or a Prop witness selector. All support is private except observations.
Library `ToVCVio` in `STFSpecSecurity`.
Spec guidance: `STFSpec/informal/modules/ToVCVio.md` §§4/7; Q56. -/
namespace ToVCVio.Test.PatriciaRlpDomain
open STFSpec.Base STFSpec.Codec STFSpec.Commit ToVCVio.Rlp ToVCVio.Trie
noncomputable section
private def lengthBound : Nat := 2 ^ 64

private def prefixWidth (n : Nat) : Nat :=
  if n < 56 then 1 else 1 + (Uint.toBeBytes n).size

private def byteWidth (b : ByteArray) : Nat :=
  if b.size = 1 ∧ (b[0]?.getD 128).toNat < 128 then b.size
  else prefixWidth b.size + b.size

private def hpWidth (p : Nibbles) (isLeaf : Bool) : Nat :=
  STFSpec.Codec.Rlp.encodedSize (.bytes (nibbleListToCompact p isLeaf))

private def listWidth (payload : Nat) : Nat := prefixWidth payload + payload

private def wireWidthFromNodeWidth (width : Nat) : Nat :=
  if width < 32 then width else 33

private def terminalWidth : Terminal → Nat
  | none => 1
  | some v => byteWidth v.val

private def terminalBound : Terminal → Prop
  | none => True
  | some v => v.val.size < lengthBound

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
  | leaf p v =>
    simp only [CompleteRlpDomain, DescendantRlpDomain, topCertificate, true_and]
    rfl
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
  have width : actualPayloadWidth node = rlpPayloadWidth tree :=
    node_interprets_payload_width derivation
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


private theorem complete_of_interpreted_reference {h : ByteArray → Hash32}
    {tree : FullTree} {reference : ChildRef}
    (derivation : RefInterprets h (some tree) reference) : CompleteRlpDomain tree :=
  (completeRlpDomain_iff_refInterprets h tree).mpr ⟨reference, derivation⟩

private theorem interpreted_descendants {h : ByteArray → Hash32} {tree : FullTree}
    {node : PatriciaNode} (derivation : NodeInterprets h tree node) : DescendantRlpDomain tree :=
  (descendantRlpDomain_iff_nodeInterprets h tree).mpr ⟨node, derivation⟩
private def emptyPath : Nibbles := Nibbles.ofList []
private def zeroValue : PresentValue := ⟨⟨#[0]⟩, by decide⟩
private def highValue : PresentValue := ⟨⟨#[128]⟩, by decide⟩
private def fullValue : PresentValue := ⟨⟨#[0, 255, 0]⟩, by decide⟩

private theorem empty_hp_width (flag : Bool) : hpWidth emptyPath flag = 1 := by
  cases flag <;> decide

private theorem byteWidth_ge_size (b : ByteArray) : b.size ≤ byteWidth b := by
  unfold byteWidth
  split <;> omega

private theorem leafWidth_ge_hp (p : Nibbles) (v : PresentValue) :
    p.size / 2 + 1 ≤ rlpNodeWidth (.leaf p v) := by
  have hp := byteWidth_ge_size (nibbleListToCompact p true)
  rw [size_nibbleListToCompact] at hp
  have hpWidth_eq : hpWidth p true = byteWidth (nibbleListToCompact p true) :=
    encodedSize_bytes _
  change p.size / 2 + 1 ≤ listWidth (rlpPayloadWidth (.leaf p v))
  unfold listWidth
  change p.size / 2 + 1 ≤ prefixWidth (hpWidth p true + byteWidth v.val) +
    (hpWidth p true + byteWidth v.val)
  rw [hpWidth_eq]
  omega

private theorem huge_leaf_control (h : ByteArray → Hash32) (p : Nibbles)
    (v : PresentValue) (size : p.size = 2 ^ 65) :
    Canonical (.leaf p v) ∧ DescendantRlpDomain (.leaf p v) ∧
      NodeInterprets h (.leaf p v) (.leaf p v) ∧
      ¬CompleteRlpDomain (.leaf p v) ∧ ¬FitsRlp (.leaf p v) ∧
      ¬∃ reference, RefInterprets h (some (.leaf p v)) reference := by
  have bad : ¬p.size / 2 + 1 < lengthBound := by
    rw [size]
    decide
  have noComplete : ¬CompleteRlpDomain (.leaf p v) := fun cert => bad cert.1
  refine ⟨.leaf p v, True.intro, .leaf p v, noComplete, ?_, ?_⟩
  · intro fits
    exact bad ((fits_leaf p v).mp fits).1
  · rintro ⟨reference, derivation⟩
    exact noComplete (complete_of_interpreted_reference derivation)

private theorem huge_finite_path (h : ByteArray → Hash32) (v : PresentValue) :
    ∃ p : Nibbles, p.size = 2 ^ 65 ∧ Canonical (.leaf p v) ∧
      DescendantRlpDomain (.leaf p v) ∧ NodeInterprets h (.leaf p v) (.leaf p v) ∧
      ¬CompleteRlpDomain (.leaf p v) ∧ ¬FitsRlp (.leaf p v) ∧
      ¬∃ reference, RefInterprets h (some (.leaf p v)) reference := by
  let p := Nibbles.generate (2 ^ 65) (fun _ => (0 : Fin 16))
  have size : p.size = 2 ^ 65 := Nibbles.size_generate _ _
  exact ⟨p, size, huge_leaf_control h p v size⟩

private theorem byteWidth_large (v : PresentValue) (n : Nat) (size : v.val.size = n)
    (notSingleton : n ≠ 1) (headerWidth : prefixWidth n = 9) : byteWidth v.val = 9 + n := by
  have notSingle : ¬(v.val.size = 1 ∧ (v.val[0]?.getD 128).toNat < 128) := by
    intro single
    exact notSingleton (size.symm.trans single.1)
  rw [byteWidth, ite_eq_right notSingle, size, headerWidth]

private theorem joined_payload_failure (h : ByteArray → Hash32) (v : PresentValue)
    (size : v.val.size = 2 ^ 64 - 1) :
    emptyPath.size / 2 + 1 < lengthBound ∧ v.val.size < lengthBound ∧
      rlpPayloadWidth (.leaf emptyPath v) = 2 ^ 64 + 9 ∧ ¬FitsRlp (.leaf emptyPath v) := by
  have vb : byteWidth v.val = 9 + (2 ^ 64 - 1) :=
    byteWidth_large v _ size (by decide) (by decide)
  have payload : rlpPayloadWidth (.leaf emptyPath v) = 2 ^ 64 + 9 := by
    change hpWidth emptyPath true + byteWidth v.val = _
    rw [empty_hp_width, vb]
  refine ⟨by decide, ?_, payload, ?_⟩
  · rw [size]
    decide
  · intro fits
    have joined := ((fits_iff_top (NodeInterprets.leaf emptyPath v (h := h))).mp fits).2.2
    rw [payload] at joined
    exact (by decide : ¬(2 ^ 64 + 9 < lengthBound)) joined

private theorem whole_extent_overstrong (h : ByteArray → Hash32) (v : PresentValue)
    (size : v.val.size = 2 ^ 64 - 11) :
    CompleteRlpDomain (.leaf emptyPath v) ∧ FitsRlp (.leaf emptyPath v) ∧
      rlpNodeWidth (.leaf emptyPath v) = 2 ^ 64 + 8 ∧
      2 ^ 64 ≤ STFSpec.Codec.Rlp.encodedSize (assembled (.leaf emptyPath v)) := by
  have vb : byteWidth v.val = 9 + (2 ^ 64 - 11) :=
    byteWidth_large v _ size (by decide) (by decide)
  have payload : rlpPayloadWidth (.leaf emptyPath v) = 2 ^ 64 - 1 := by
    change hpWidth emptyPath true + byteWidth v.val = _
    rw [empty_hp_width, vb]
  have cert : CompleteRlpDomain (.leaf emptyPath v) := by
    refine ⟨by decide, ?_, ?_⟩
    · rw [size]
      decide
    · rw [payload]
      decide
  have width : rlpNodeWidth (.leaf emptyPath v) = 2 ^ 64 + 8 := by
    rw [rlpNodeWidth, payload]
    decide
  have derivation : NodeInterprets h (.leaf emptyPath v) (.leaf emptyPath v) := .leaf _ _
  refine ⟨cert, (fits_iff_top derivation).mpr ((complete_iff_descendants_top _).mp cert).2,
    width, ?_⟩
  rw [node_interprets_encoded_width derivation, width]
  decide

private theorem repeated_hashed_payload (tree : FullTree) (terminal : Terminal)
    (large : 32 ≤ rlpNodeWidth tree) :
    rlpPayloadWidth (.branch (fun _ => some tree) terminal) = 528 + terminalWidth terminal := by
  have wire : rlpReferenceWidth (some tree) = 33 := by
    change (if rlpNodeWidth tree < 32 then rlpNodeWidth tree else 33) = 33
    rw [ite_eq_right (by omega)]
  rw [rlpPayloadWidth]
  change (List.ofFn (fun _ : Fin 16 => rlpReferenceWidth (some tree))).sum + _ = _
  rw [wire, show (List.ofFn (fun _ : Fin 16 => (33 : Nat))).sum = 528 by decide]
  rfl

private theorem huge_descendant_parent_control (h : ByteArray → Hash32) (p : Nibbles)
    (v : PresentValue) (size : p.size = 2 ^ 65) :
    rlpPayloadWidth (.branch (fun _ => some (.leaf p v)) none) = 529 ∧
      rlpPayloadWidth (.branch (fun _ => some (.leaf p v)) none) < lengthBound ∧
      ¬DescendantRlpDomain (.branch (fun _ => some (.leaf p v)) none) ∧
      ¬∃ node, NodeInterprets h (.branch (fun _ => some (.leaf p v)) none) node := by
  have hp := leafWidth_ge_hp p v
  rw [size] at hp
  have large : 32 ≤ rlpNodeWidth (.leaf p v) := by omega
  have payload : rlpPayloadWidth (.branch (fun _ => some (.leaf p v)) none) = 529 :=
    repeated_hashed_payload (.leaf p v) none large
  have noDescendants : ¬DescendantRlpDomain (.branch (fun _ => some (.leaf p v)) none) := by
    intro cert
    exact (huge_leaf_control h p v size).2.2.2.1 (cert (0 : Fin 16))
  refine ⟨payload, ?_, noDescendants, ?_⟩
  · rw [payload]
    decide
  · rintro ⟨node, derivation⟩
    exact noDescendants (interpreted_descendants derivation)

private theorem singleton_value_widths :
    rlpNodeWidth (.leaf emptyPath zeroValue) = 3 ∧
      rlpNodeWidth (.leaf emptyPath highValue) = 4 := by
  decide

private theorem singleton_hp_widths :
    hpWidth emptyPath true = 1 ∧ hpWidth emptyPath false = 1 ∧
      hpWidth (Nibbles.ofList [(15 : Fin 16)]) true = 1 ∧
      hpWidth (Nibbles.ofList [(15 : Fin 16)]) false = 1 := by
  decide

private theorem list_prefix_separate :
    STFSpec.Codec.Rlp.encodedSize (.list [.bytes zeroValue.val]) = 2 ∧
      byteWidth zeroValue.val = 1 := by decide

private theorem terminal_tags_same_width :
    terminalWidth none = 1 ∧ terminalWidth (some zeroValue) = 1 ∧
      terminalWidth (some fullValue) = 4 ∧ (none : Terminal) ≠ some zeroValue := by decide

private theorem repeated_full_terminal_payload (tree : FullTree) (large : 32 ≤ rlpNodeWidth tree) :
    rlpPayloadWidth (.branch (fun _ => some tree) none) = 529 ∧
      rlpPayloadWidth (.branch (fun _ => some tree) (some fullValue)) = 532 := by
  exact ⟨repeated_hashed_payload tree none large,
    repeated_hashed_payload tree (some fullValue) large⟩

private theorem complete_threshold_widths :
    wireWidthFromNodeWidth 31 = 31 ∧ wireWidthFromNodeWidth 32 = 33 ∧
      wireWidthFromNodeWidth 33 = 33 ∧ wireWidthFromNodeWidth 32 ≠ min 32 33 := by decide

private def thresholdValue (n : Nat) : PresentValue :=
  ⟨⟨Array.replicate (n + 1) 128⟩, by
    intro empty
    have size := congrArg ByteArray.size empty
    rw [ByteArray.size_empty] at size
    change (Array.replicate (n + 1) (128 : UInt8)).size = 0 at size
    rw [Array.size_replicate] at size
    omega⟩

private theorem threshold_leaf_certificates :
    CompleteRlpDomain (.leaf emptyPath (thresholdValue 27)) ∧
      CompleteRlpDomain (.leaf emptyPath (thresholdValue 28)) ∧
      CompleteRlpDomain (.leaf emptyPath (thresholdValue 29)) := by
  unfold CompleteRlpDomain
  decide

private theorem threshold_leaf_widths :
    rlpNodeWidth (.leaf emptyPath (thresholdValue 27)) = 31 ∧
      rlpNodeWidth (.leaf emptyPath (thresholdValue 28)) = 32 ∧
      rlpNodeWidth (.leaf emptyPath (thresholdValue 29)) = 33 := by decide

private theorem threshold_actual_reference_widths (h : ByteArray → Hash32) :
    ∃ r31 r32 r33,
      RefInterprets h (some (.leaf emptyPath (thresholdValue 27))) r31 ∧
      RefInterprets h (some (.leaf emptyPath (thresholdValue 28))) r32 ∧
      RefInterprets h (some (.leaf emptyPath (thresholdValue 29))) r33 ∧
      STFSpec.Codec.Rlp.encodedSize (wireItem r31) = 31 ∧
      STFSpec.Codec.Rlp.encodedSize (wireItem r32) = 33 ∧
      STFSpec.Codec.Rlp.encodedSize (wireItem r33) = 33 := by
  obtain ⟨r31, d31⟩ := (completeRlpDomain_iff_refInterprets h _).mp threshold_leaf_certificates.1
  obtain ⟨r32, d32⟩ := (completeRlpDomain_iff_refInterprets h _).mp threshold_leaf_certificates.2.1
  obtain ⟨r33, d33⟩ := (completeRlpDomain_iff_refInterprets h _).mp threshold_leaf_certificates.2.2
  refine ⟨r31, r32, r33, d31, d32, d33, ?_, ?_, ?_⟩
  · rw [ref_interprets_wire_width d31]
    decide
  · rw [ref_interprets_wire_width d32]
    decide
  · rw [ref_interprets_wire_width d33]
    decide

private theorem certified_noncanonical_empty_branch (h : ByteArray → Hash32) :
    CompleteRlpDomain (.branch (fun _ => none) none) ∧
      ¬Canonical (.branch (fun _ => none) none) ∧
      (∃ node, NodeInterprets h (.branch (fun _ => none) none) node ∧ FitsRlp node) ∧
      (∃ reference, RefInterprets h (some (.branch (fun _ => none) none)) reference) := by
  have cert : CompleteRlpDomain (.branch (fun _ => none) none) := by
    refine ⟨fun _ => True.intro, True.intro, ?_⟩
    decide
  refine ⟨cert, ?_, (completeRlpDomain_iff_nodeInterprets_fits h _).mp cert,
    (completeRlpDomain_iff_refInterprets h _).mp cert⟩
  intro canonical
  cases canonical with
  | branch _ _ _ occupancy =>
    have count : fullCount (fun _ => none) + terminalCount none = 0 := by decide
    rw [count] at occupancy
    omega

private theorem repeated_full_terminal_complete_widths (tree : FullTree)
    (large : 32 ≤ rlpNodeWidth tree) :
    rlpNodeWidth (.branch (fun _ => some tree) none) = 532 ∧
      rlpNodeWidth (.branch (fun _ => some tree) (some fullValue)) = 535 := by
  have widths := repeated_full_terminal_payload tree large
  constructor
  · rw [rlpNodeWidth, widths.1]
    decide
  · rw [rlpNodeWidth, widths.2]
    decide


private theorem arbitrary_width_laws {h : ByteArray → Hash32} {tree : FullTree}
    {node : PatriciaNode} (derivation : NodeInterprets h tree node) :
    actualPayloadWidth node = rlpPayloadWidth tree ∧
      STFSpec.Codec.Rlp.encodedSize (assembled node) = rlpNodeWidth tree :=
  ⟨node_interprets_payload_width derivation, node_interprets_encoded_width derivation⟩

private theorem arbitrary_reference_width {h : ByteArray → Hash32}
    {root : Option FullTree} {reference : ChildRef} (derivation : RefInterprets h root reference) :
    STFSpec.Codec.Rlp.encodedSize (wireItem reference) = rlpReferenceWidth root :=
  ref_interprets_wire_width derivation

private theorem arbitrary_domain_directions (h : ByteArray → Hash32) (tree : FullTree) :
    (DescendantRlpDomain tree → ∃ node, NodeInterprets h tree node) ∧
    ((∃ node, NodeInterprets h tree node) → DescendantRlpDomain tree) ∧
    (CompleteRlpDomain tree → ∃ node, NodeInterprets h tree node ∧ FitsRlp node) ∧
    ((∃ node, NodeInterprets h tree node ∧ FitsRlp node) → CompleteRlpDomain tree) ∧
    (CompleteRlpDomain tree → ∃ reference, RefInterprets h (some tree) reference) ∧
    ((∃ reference, RefInterprets h (some tree) reference) → CompleteRlpDomain tree) :=
  ⟨(descendantRlpDomain_iff_nodeInterprets h tree).mp,
   (descendantRlpDomain_iff_nodeInterprets h tree).mpr,
   (completeRlpDomain_iff_nodeInterprets_fits h tree).mp,
   (completeRlpDomain_iff_nodeInterprets_fits h tree).mpr,
   (completeRlpDomain_iff_refInterprets h tree).mp,
   (completeRlpDomain_iff_refInterprets h tree).mpr⟩

private theorem absent_width : rlpReferenceWidth none = 1 := rfl

private theorem arbitrary_nat_leaf (h : ByteArray → Hash32) (n : Nat) (v : PresentValue) :
    DescendantRlpDomain (.leaf (Nibbles.generate n (fun _ ↦ (15 : Fin 16))) v) ∧
      (∃ node, NodeInterprets h (.leaf (Nibbles.generate n (fun _ ↦ (15 : Fin 16))) v) node) :=
  ⟨True.intro, (descendantRlpDomain_iff_nodeInterprets h _).mp True.intro⟩

private theorem every_original_slot (h : ByteArray → Hash32)
    (children : Fin 16 → Option FullTree) (references : Vector ChildRef 16)
    (terminal : Terminal)
    (ds : ∀ i : Fin 16, RefInterprets h (children i) references[i.val]) :
    DescendantRlpDomain (.branch children terminal) ∧
      (∀ i : Fin 16, STFSpec.Codec.Rlp.encodedSize (wireItem references[i.val]) =
        rlpReferenceWidth (children i)) :=
  ⟨(descendantRlpDomain_iff_nodeInterprets h _).mpr
      ⟨.branch references terminal, .branch children references terminal ds⟩,
    fun i ↦ ref_interprets_wire_width (ds i)⟩

private def lowValue : PresentValue := ⟨⟨#[127]⟩, by decide⟩
private def maxValue : PresentValue := ⟨⟨#[255]⟩, by decide⟩

private theorem equal_width_distinct_full_bytes :
    rlpNodeWidth (.leaf emptyPath zeroValue) = rlpNodeWidth (.leaf emptyPath lowValue) ∧
      preimage (.leaf emptyPath zeroValue) ≠ preimage (.leaf emptyPath lowValue) := by
  decide

private theorem singleton_all_values :
    rlpNodeWidth (.leaf emptyPath zeroValue) = 3 ∧
    rlpNodeWidth (.leaf emptyPath lowValue) = 3 ∧
    rlpNodeWidth (.leaf emptyPath highValue) = 4 ∧
    rlpNodeWidth (.leaf emptyPath maxValue) = 4 := by decide

private theorem noncanonical_extensions_certified (h : ByteArray → Hash32) :
    CompleteRlpDomain (.extension emptyPath (.leaf emptyPath zeroValue)) ∧
    ¬Canonical (.extension emptyPath (.leaf emptyPath zeroValue)) ∧
    (∃ reference, RefInterprets h
      (some (.extension emptyPath (.leaf emptyPath zeroValue))) reference) ∧
    CompleteRlpDomain (.extension (Nibbles.ofList [15]) (.leaf emptyPath zeroValue)) ∧
    ¬Canonical (.extension (Nibbles.ofList [15]) (.leaf emptyPath zeroValue)) := by
  have zeroCert : CompleteRlpDomain (.extension emptyPath (.leaf emptyPath zeroValue)) := by
    unfold CompleteRlpDomain
    decide
  have positiveCert :
      CompleteRlpDomain (.extension (Nibbles.ofList [15]) (.leaf emptyPath zeroValue)) := by
    unfold CompleteRlpDomain
    decide
  refine ⟨zeroCert, not_canonical_zero_extension _,
    (completeRlpDomain_iff_refInterprets h _).mp zeroCert, positiveCert, ?_⟩
  intro canonical
  cases canonical

private theorem hp_odd_even_separate_flags :
    hpWidth (Nibbles.ofList [0, 15]) true = 3 ∧
    hpWidth (Nibbles.ofList [0, 15]) false = 3 ∧
    hpWidth (Nibbles.ofList [0, 15, 0]) true = 3 ∧
    hpWidth (Nibbles.ofList [0, 15, 0]) false = 3 := by decide

private theorem prefix_boundaries :
    prefixWidth 55 = 1 ∧ prefixWidth 56 = 2 ∧
    prefixWidth 255 = 2 ∧ prefixWidth 256 = 3 := by decide

end

/-! ### Modest complete executable codec/HP/shell/reference observations -/

private def runtimeEmptyPath : Nibbles := Nibbles.ofList []
private def runtimeZero : PresentValue := ⟨⟨#[0]⟩, by decide⟩
private def runtimeLow : PresentValue := ⟨⟨#[127]⟩, by decide⟩
private def runtimeHigh : PresentValue := ⟨⟨#[128]⟩, by decide⟩
private def runtimeMax : PresentValue := ⟨⟨#[255]⟩, by decide⟩
private def runtimeFull : PresentValue := ⟨⟨#[0, 255, 0]⟩, by decide⟩
private def runtimeZeroHash : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat 0)
private def runtimeDigest (i : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat (i + 1))
private def runtimeThresholdValue (n : Nat) : PresentValue :=
  ⟨⟨Array.replicate (n + 1) 128⟩, by
    intro empty
    have size := congrArg ByteArray.size empty
    rw [ByteArray.size_empty] at size
    change (Array.replicate (n + 1) (128 : UInt8)).size = 0 at size
    rw [Array.size_replicate] at size
    omega⟩
private def runtimeEdge (n : Nat) : PatriciaNode :=
  .leaf runtimeEmptyPath (runtimeThresholdValue (n + 27))
private theorem runtime_edge_fits :
    FitsRlp (runtimeEdge 0) ∧ FitsRlp (runtimeEdge 1) ∧ FitsRlp (runtimeEdge 2) := by
  constructor
  · unfold runtimeEdge
    rw [fits_leaf]
    decide
  constructor
  all_goals
    unfold runtimeEdge
    rw [fits_leaf]
    decide
private def runtimePaths : List Nibbles :=
  [runtimeEmptyPath, Nibbles.ofList [0], Nibbles.ofList [15, 0],
    Nibbles.ofList [0, 15, 0], Nibbles.ofList (List.replicate 128 15 ++ [0]),
    Nibbles.ofList (List.replicate 136 0 ++ [15])]
private def frame (tag index : Nat) (b : ByteArray) : List Nat :=
  [tag, index, b.size] ++ b.data.toList.map UInt8.toNat
private def branchFixture (distinct : Bool) (terminal : Terminal) : PatriciaNode :=
  .branch (Vector.ofFn fun i ↦ .hashed
    (if distinct then runtimeDigest i.val else runtimeZeroHash)) terminal
private def nestedFixture : PatriciaNode :=
  .extension (Nibbles.ofList [15, 0])
    (.inline (ToVCVio.Trie.asListNode (runtimeEdge 0) runtime_edge_fits.1))

/-- Complete tagged modest codec, HP, shell, wire and numeric-slot outputs.
Rows do not execute logical widths or choose any interpretation witness. -/
def observations : List (List Nat) :=
  let values := [runtimeZero, runtimeLow, runtimeHigh, runtimeMax, runtimeFull]
  let byteRows := (values.zipIdx).map fun (v, i) ↦
    frame 10 i (STFSpec.Codec.Rlp.encode (.bytes v.val))
  let prefixRows := ([55, 56, 255, 256].zipIdx).map fun (n, i) ↦
    frame 11 i (STFSpec.Codec.Rlp.encode (.list (List.replicate n (.bytes ByteArray.empty))))
  let hpRows := (runtimePaths.zipIdx).flatMap fun (p, i) ↦
    [frame 12 (2 * i) (nibbleListToCompact p false),
     frame 12 (2 * i + 1) (nibbleListToCompact p true),
     frame 13 (2 * i) (STFSpec.Codec.Rlp.encode (.bytes (nibbleListToCompact p false))),
     frame 13 (2 * i + 1) (STFSpec.Codec.Rlp.encode (.bytes (nibbleListToCompact p true)))]
  let leafRows := (runtimePaths.zipIdx).flatMap fun (p, i) ↦
    (values.zipIdx).map fun (v, j) ↦ frame 14 (5 * i + j) (preimage (.leaf p v))
  let edgeRows := [frame 15 0 (preimage (runtimeEdge 0)), frame 15 1 (preimage (runtimeEdge 1)),
    frame 15 2 (preimage (runtimeEdge 2))]
  let wireRows := [frame 16 0 (STFSpec.Codec.Rlp.encode (wireItem .empty)),
    frame 16 1 (STFSpec.Codec.Rlp.encode (wireItem (refWithHash (fun _ ↦ runtimeZeroHash)
      (ToVCVio.Trie.asListNode (runtimeEdge 0) runtime_edge_fits.1)))),
    frame 16 2 (STFSpec.Codec.Rlp.encode (wireItem (refWithHash (fun _ ↦ runtimeZeroHash)
      (ToVCVio.Trie.asListNode (runtimeEdge 1) runtime_edge_fits.2.1)))),
    frame 16 3 (STFSpec.Codec.Rlp.encode (wireItem (refWithHash (fun _ ↦ runtimeZeroHash)
      (ToVCVio.Trie.asListNode (runtimeEdge 2) runtime_edge_fits.2.2))))]
  let branchRows := [frame 17 0 (preimage (branchFixture false none)),
    frame 17 1 (preimage (branchFixture false (some runtimeZero))),
    frame 17 2 (preimage (branchFixture false (some runtimeFull))),
    frame 17 3 (preimage (branchFixture true none)),
    frame 17 4 (preimage (branchFixture true (some runtimeFull)))]
  let slotRows := (List.ofFn fun i : Fin 16 ↦
    frame 18 i.val (STFSpec.Codec.Rlp.encode (wireItem (.hashed (runtimeDigest i.val)))))
  let terminalRows := [frame 19 0 (STFSpec.Codec.Rlp.encode (terminalItem none)),
    frame 19 1 (STFSpec.Codec.Rlp.encode (terminalItem (some runtimeZero))),
    frame 19 2 (STFSpec.Codec.Rlp.encode (terminalItem (some runtimeFull)))]
  byteRows ++ prefixRows ++ hpRows ++ leafRows ++ edgeRows ++ wireRows ++ branchRows ++ slotRows ++
    terminalRows ++ [frame 20 0 (preimage nestedFixture)]

end ToVCVio.Test.PatriciaRlpDomain
