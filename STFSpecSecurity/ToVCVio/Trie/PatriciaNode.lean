/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import ToVCVio.EthCommit.NodeReference
import STFSpec.Commit.Compact
import STFSpec.Commit.Preparation

/-!
# Faithful Patricia node shells and finite resolved shapes

Library `ToVCVio` in `STFSpecSecurity`.

Security-local support. Wire injection binds the actual child-reference representation;
the separate resolved grammar contains no hashes, stubs, caches or sharing.
Spec guidance: `STFSpec/informal/modules/ToVCVio.md` §§5/7.
-/

namespace ToVCVio.Trie
open STFSpec.Base STFSpec.Codec STFSpec.Commit STFSpec.Hash ToVCVio.Rlp

private theorem congrArg2 {α β γ : Type} (f : α → β → γ) {a a' : α} {b b' : β}
    (ha : a = a') (hb : b = b') : f a b = f a' b' := by
  cases ha
  cases hb
  rfl

/-- Present encoded bytes exclude the branch absence sentinel. -/
abbrev PresentValue := {b : ByteArray // b ≠ ByteArray.empty}
/-- A branch has either no terminal or a present nonempty encoded value. -/
abbrev Terminal := Option PresentValue

/-- The branch terminal wire, preserving nonempty presence. -/
def terminalItem : Terminal → RlpItem
  | none => .bytes ByteArray.empty
  | some value => .bytes value.val

/-- Nonempty presence makes the terminal wire injective. -/
theorem terminalItem_inj (x y : Terminal) : terminalItem x = terminalItem y ↔ x = y := by
  constructor
  · intro h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some v => exact False.elim (v.property (RlpItem.bytes.inj h).symm)
    | some v =>
      cases y with
      | none => exact False.elim (v.property (RlpItem.bytes.inj h))
      | some w => exact congrArg some (Subtype.ext (RlpItem.bytes.inj h))
  · exact congrArg terminalItem

/-- A single nonrecursive node, using the accepted actual reference type. -/
inductive PatriciaNode where
  | leaf (remaining : Nibbles) (value : PresentValue)
  | extension (segment : Nibbles) (child : ChildRef)
  | branch (children : Vector ChildRef 16) (terminal : Terminal)

/-- Pure embedding into the broader total core node domain. -/
def toInternalNode : PatriciaNode → InternalNode
  | .leaf p v => .leaf p (.bytes v.val)
  | .extension p child => .extension p (wireItem child)
  | .branch children terminal => .branch (children.map wireItem) (terminalItem terminal)

/-- The embedded branch preserves every numeric child wire. -/
theorem branch_child (children : Vector ChildRef 16) (terminal : Terminal) (i : Fin 16) :
    ((children.map wireItem).toList ++ [terminalItem terminal])[i.val]'(by simp; omega) =
      wireItem children[i.val] := by
  rw [branch_items_get]
  erw [Vector.getElem_map]
/-- Position sixteen is exactly the faithful terminal wire. -/
theorem branch_terminal (children : Vector ChildRef 16) (terminal : Terminal) :
    ((children.map wireItem).toList ++ [terminalItem terminal])[16]'(by simp) =
      terminalItem terminal := branch_items_value _ _

/-- Mapping actual child wires retains every numeric vector position. -/
theorem wireVector_inj (x y : Vector ChildRef 16) :
    x.map wireItem = y.map wireItem ↔ x = y := by
  constructor
  · intro h
    apply Vector.ext
    intro i hi
    apply (wireItem_inj _ _).mp
    simpa only [Vector.getElem_map] using congrArg (fun v => v[i]) h
  · exact congrArg (Vector.map wireItem)

/-- The pure embedding preserves all constructor fields. -/
theorem toInternalNode_inj (x y : PatriciaNode) : toInternalNode x = toInternalNode y ↔ x = y := by
  constructor
  · intro h
    cases x <;> cases y <;> simp only [toInternalNode] at h
    all_goals try { exact False.elim (InternalNode.noConfusion h) }
    · rcases InternalNode.leaf.inj h with ⟨hp, hv⟩
      exact congrArg2 PatriciaNode.leaf hp (Subtype.ext (RlpItem.bytes.inj hv))
    · rcases InternalNode.extension.inj h with ⟨hp, hc⟩
      exact congrArg2 PatriciaNode.extension hp ((wireItem_inj _ _).mp hc)
    · rcases InternalNode.branch.inj h with ⟨hc, ht⟩
      exact congrArg2 PatriciaNode.branch ((wireVector_inj _ _).mp hc)
        ((terminalItem_inj _ _).mp ht)
  · exact congrArg toInternalNode

/-- Complete core assembly is injective even on its unrestricted arbitrary RLP fields. -/
theorem assembleInternalNode_inj (x y : Option InternalNode) :
    assembleInternalNode x = assembleInternalNode y ↔ x = y := by
  constructor
  · intro h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y => cases y <;> simp only [assembleInternalNode_none, assembleInternalNode_leaf,
          assembleInternalNode_extension, assembleInternalNode_branch] at h <;> cases h
    | some x =>
      cases y with
      | none => cases x <;> simp only [assembleInternalNode_none, assembleInternalNode_leaf,
          assembleInternalNode_extension, assembleInternalNode_branch] at h <;> cases h
      | some y =>
        cases x <;> cases y
        all_goals simp only [assembleInternalNode_leaf, assembleInternalNode_extension,
          assembleInternalNode_branch, RlpItem.list.injEq] at h
        · rcases List.cons.inj h with ⟨hp, ht⟩
          have hp := (nibbleListToCompact_inj _ _ true true).mp (RlpItem.bytes.inj hp)
          exact congrArg some (congrArg2 InternalNode.leaf hp.1 (List.cons.inj ht).1)
        · have hp := (List.cons.inj h).1
          have hp := (nibbleListToCompact_inj _ _ true false).mp (RlpItem.bytes.inj hp)
          cases hp.2
        · have hl := congrArg List.length h
          simp only [List.length_cons, List.length_nil, branch_items_length] at hl
          contradiction
        · have hp := (List.cons.inj h).1
          have hp := (nibbleListToCompact_inj _ _ false true).mp (RlpItem.bytes.inj hp)
          cases hp.2
        · rcases List.cons.inj h with ⟨hp, ht⟩
          have hp := (nibbleListToCompact_inj _ _ false false).mp (RlpItem.bytes.inj hp)
          exact congrArg some (congrArg2 InternalNode.extension hp.1 (List.cons.inj ht).1)
        · have hl := congrArg List.length h
          simp only [List.length_cons, List.length_nil, branch_items_length] at hl
          contradiction
        · have hl := congrArg List.length h
          simp only [List.length_cons, List.length_nil, branch_items_length] at hl
          contradiction
        · have hl := congrArg List.length h
          simp only [List.length_cons, List.length_nil, branch_items_length] at hl
          contradiction
        · rename_i cs v ds w
          have hc : cs = ds := by
            apply Vector.ext
            intro i hi
            have he := congrArg (fun xs => xs[i]?) h
            rw [List.getElem?_eq_getElem (by rw [branch_items_length]; omega),
              List.getElem?_eq_getElem (by rw [branch_items_length]; omega)] at he
            rw [branch_items_get cs v ⟨i, hi⟩, branch_items_get ds w ⟨i, hi⟩] at he
            exact Option.some.inj he
          have ht : v = w := by
            have he := congrArg (fun xs => xs[16]?) h
            simpa using he
          exact congrArg some (congrArg2 InternalNode.branch hc ht)
  · exact congrArg assembleInternalNode

/-- The complete unencoded node; no query is performed. -/
def assembled (node : PatriciaNode) : RlpItem :=
  assembleInternalNode (some (toInternalNode node))
/-- The actual complete packed preimage, including all headers. -/
def preimage (node : PatriciaNode) : ByteArray := STFSpec.Codec.Rlp.encode (assembled node)
/-- The entire recursive standard RLP certificate, including joined outer payload. -/
def FitsRlp (node : PatriciaNode) : Prop := STFSpec.Codec.Rlp.Encodable (assembled node)

/-- Every shell assembles to a list. -/
theorem assembled_list (node : PatriciaNode) : ∃ xs, assembled node = .list xs := by
  cases node <;> exact ⟨_, rfl⟩
/-- One assembled list determines the entire typed node. -/
theorem assembled_inj (x y : PatriciaNode) : assembled x = assembled y ↔ x = y := by
  rw [assembled, assembled, assembleInternalNode_inj, Option.some.injEq, toInternalNode_inj]
/-- Standard preimage injection requires both complete RLP certificates. -/
theorem preimage_inj (x y : PatriciaNode) (hx : FitsRlp x) (hy : FitsRlp y) :
    preimage x = preimage y ↔ x = y := by
  rw [preimage, preimage, STFSpec.Codec.Rlp.encode_inj _ _ hx hy, assembled_inj]
/-- Reuse the accepted assembly facade with the full certificate. -/
def asListNode (node : PatriciaNode) (h : FitsRlp node) : RlpListNode :=
  ToVCVio.EthCommit.asListNode (toInternalNode node) h
/-- The facade retains exactly the shell's complete assembly. -/
theorem asListNode_item (node : PatriciaNode) (h : FitsRlp node) :
    (asListNode node h).val.val = assembled node := rfl
/-- Callback comparison requires equality of full query actions at the exact preimage. -/
theorem callback_adapter {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (q : ByteArray → m Hash32) (node : PatriciaNode) (h : FitsRlp node)
    (hq : q (preimage node) = KeccakQuery.keccak (m := m) (preimage node)) :
    wireItem <$> childRefM q (asListNode node h) =
      encodeInternalNode (m := m) (some (toInternalNode node)) :=
  ToVCVio.EthCommit.callback_adapter q _ _ rfl hq
/-- The installed capability supplies both sides of the accepted lawful adapter. -/
theorem keccak_adapter {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (node : PatriciaNode) (h : FitsRlp node) :
    wireItem <$> childRefM (KeccakQuery.keccak (m := m)) (asListNode node h) =
      encodeInternalNode (m := m) (some (toInternalNode node)) :=
  callback_adapter _ node h rfl

/-- Occupancy depends on the reference constructor, never on digest contents. -/
def occupied : ChildRef → Bool
  | .empty => false
  | _ => true
/-- Count all sixteen occupied numeric child positions. -/
def countOccupied (children : Vector ChildRef 16) : Nat :=
  (children.toList.filter occupied).length
/-- Count terminal presence separately from its encoded bytes. -/
def terminalCount (terminal : Terminal) : Nat := if terminal.isSome then 1 else 0
/-- Local reference admissibility supplies no resolved child-kind claim. -/
def LocallyAdmissible : PatriciaNode → Prop
  | .leaf _ _ => True
  | .extension p child => 0 < p.size ∧ occupied child = true ∧ AdmissibleRef child
  | .branch children terminal =>
      (∀ i : Fin 16, AdmissibleRef children[i.val]) ∧
        2 ≤ countOccupied children + terminalCount terminal
/-- Local finite reference and width premises are decidable. -/
instance (node : PatriciaNode) : Decidable (LocallyAdmissible node) := by
  cases node <;> unfold LocallyAdmissible <;> infer_instance
/-- All leaf paths, including empty, are locally admissible. -/
theorem locallyAdmissible_leaf (p : Nibbles) (v : PresentValue) :
    LocallyAdmissible (.leaf p v) := True.intro
/-- Zero digests still occupy a child position. -/
theorem occupied_hashed (digest : Hash32) : occupied (.hashed digest) = true := rfl
/-- An admissible extension has exactly the positive/occupied/reference premises. -/
theorem locallyAdmissible_extension_iff (p : Nibbles) (child : ChildRef) :
    LocallyAdmissible (.extension p child) ↔
      0 < p.size ∧ occupied child = true ∧ AdmissibleRef child := Iff.rfl
/-- A local branch exposes all sixteen reference premises and terminal-inclusive count. -/
theorem locallyAdmissible_branch_iff (children : Vector ChildRef 16) (terminal : Terminal) :
    LocallyAdmissible (.branch children terminal) ↔
      (∀ i : Fin 16, AdmissibleRef children[i.val]) ∧
        2 ≤ countOccupied children + terminalCount terminal := Iff.rfl

/-- A finite resolved tree, with no reference or cache representation. -/
inductive FullTree where
  | leaf (remaining : Nibbles) (value : PresentValue)
  | extension (segment : Nibbles) (child : FullTree)
  | branch (children : Fin 16 → Option FullTree) (terminal : Terminal)
/-- Count resolved present children in numeric nibble order. -/
def fullCount (children : Fin 16 → Option FullTree) : Nat :=
  ((List.ofFn children).filter Option.isSome).length
/-- Ordinary finite canonical grammar; extensions resolve specifically to branches. -/
inductive Canonical : FullTree → Prop where
  | leaf (p : Nibbles) (v : PresentValue) : Canonical (.leaf p v)
  | extension (p : Nibbles) (children : Fin 16 → Option FullTree) (terminal : Terminal)
      (positive : 0 < p.size) (child : Canonical (.branch children terminal)) :
      Canonical (.extension p (.branch children terminal))
  | branch (children : Fin 16 → Option FullTree) (terminal : Terminal)
      (childrenCanonical : ∀ i tree, children i = some tree → Canonical tree)
      (occupancy : 2 ≤ fullCount children + terminalCount terminal) :
      Canonical (.branch children terminal)
/-- Empty maps have no resolved tree; present roots have the finite grammar. -/
def CanonicalRoot : Option FullTree → Prop
  | none => True
  | some tree => Canonical tree
/-- Canonical extensions have a positive segment and a canonical resolved branch. -/
theorem canonical_extension_iff (p : Nibbles) (child : FullTree) :
    Canonical (.extension p child) ↔
      0 < p.size ∧ ∃ children terminal,
        child = .branch children terminal ∧ Canonical child := by
  constructor
  · intro h
    cases h with
    | extension _ children terminal hp hc => exact ⟨hp, children, terminal, rfl, hc⟩
  · rintro ⟨hp, children, terminal, rfl, hc⟩
    exact .extension p children terminal hp hc
/-- Canonical branches expose canonical present children and the exact occupancy bound. -/
theorem canonical_branch_iff (children : Fin 16 → Option FullTree) (terminal : Terminal) :
    Canonical (.branch children terminal) ↔
      (∀ i tree, children i = some tree → Canonical tree) ∧
        2 ≤ fullCount children + terminalCount terminal := by
  constructor
  · intro h
    cases h with
    | branch _ _ hc ho => exact ⟨hc, ho⟩
  · rintro ⟨hc, ho⟩
    exact .branch children terminal hc ho
/-- A zero extension cannot be canonical. -/
theorem not_canonical_zero_extension (child : FullTree) :
    ¬ Canonical (.extension (Nibbles.ofList []) child) := by
  intro h
  have hp := (canonical_extension_iff _ _).mp h
  have hz : (Nibbles.ofList []).size = 0 := by rw [Nibbles.size_ofList]; rfl
  rw [hz] at hp
  omega
/-- One canonical child and a present terminal form a canonical branch. -/
theorem canonical_one_child_terminal (children : Fin 16 → Option FullTree)
    (value : PresentValue) (hc : ∀ i tree, children i = some tree → Canonical tree)
    (ho : fullCount children = 1) : Canonical (.branch children (some value)) := by
  apply Canonical.branch _ _ hc
  simp only [ho, terminalCount, Option.isSome_some, ite_true]
  decide
/-- One child without a terminal is compressible and not canonical. -/
theorem not_canonical_one_child_absent (children : Fin 16 → Option FullTree)
    (ho : fullCount children = 1) : ¬ Canonical (.branch children none) := by
  intro h
  have hb := ((canonical_branch_iff _ _).mp h).2
  simp only [ho, terminalCount, Option.isSome_none, Bool.false_eq_true, ite_false] at hb
  omega
/-- Faithful finite-map values exclude empty encoded bytes at every stored binding. -/
def NonemptyValues (obj : Std.ExtTreeMap Nibbles ByteArray) : Prop :=
  ∀ (k : Nibbles) (b : ByteArray), obj[k]? = some b → b ≠ ByteArray.empty
/-- Safe pure preparation has faithful nonempty values without an unsecured premise. -/
theorem prepareTrieModel_nonemptyValues {K V : Type} [Ord K] [Std.TransOrd K]
    [Std.LawfulEqOrd K] [TrieValue V] [KeyBytes K] (t : STFSpec.Commit.Trie K V)
    (safe : t.PrepareSafe) : NonemptyValues (prepareTrieModel t) :=
  prepareTrieModel_image_nonempty t safe

end ToVCVio.Trie
