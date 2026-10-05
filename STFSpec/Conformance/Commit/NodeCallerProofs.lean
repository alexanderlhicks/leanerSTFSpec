/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit

/-!
# Partial-node public-import clients

Library `EthConformance`. Private typing and structural consumers retain complete
fields and recursive Array/Option children. Non-admitted cache/shape controls establish
bare expressibility only, with no decoding or cache API or acceptance claim.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/5/6/10.
-/

namespace STFSpec.Conformance.Commit.NodeCallerProofs

open STFSpec.Base STFSpec.Commit

private def variant : Ref → Nat
  | none => 0
  | some (.leaf _ _ _) => 1
  | some (.ext _ _ _) => 2
  | some (.branch _ _ _) => 3
  | some (.hashed _) => 4

private theorem enc_fields (raw : ByteArray) (cached : Option Hash32) :
    (Enc.mk raw cached).rlp = raw ∧ (Enc.mk raw cached).hash? = cached := ⟨rfl, rfl⟩

private theorem leaf_fields (path : Nibbles) (value raw : ByteArray) (cached : Option Hash32) :
    match Node.leaf path value ⟨raw, cached⟩ with
    | .leaf p v e => p = path ∧ v = value ∧ e.rlp = raw ∧ e.hash? = cached
    | _ => False := ⟨rfl, rfl, rfl, rfl⟩

private theorem extension_fields (path : Nibbles) (child : Node)
    (raw : ByteArray) (cached : Option Hash32) :
    match Node.ext path child ⟨raw, cached⟩ with
    | .ext p c e => p = path ∧ c = child ∧ e.rlp = raw ∧ e.hash? = cached
    | _ => False := ⟨rfl, rfl, rfl, rfl⟩

private theorem branch_fields (children : Array (Option Node)) (value raw : ByteArray)
    (cached : Option Hash32) :
    match Node.branch children value ⟨raw, cached⟩ with
    | .branch cs v e => cs = children ∧ v = value ∧ e.rlp = raw ∧ e.hash? = cached
    | _ => False := ⟨rfl, rfl, rfl, rfl⟩

private theorem stub_field (h : Hash32) :
    match Node.hashed h with
    | .hashed actual => actual = h
    | _ => False := rfl

private theorem absence_stub_empty_leaf (h : Hash32) (enc : Enc) :
    variant none = 0 ∧ variant (some (.hashed h)) = 4 ∧
      variant (some (.leaf (Nibbles.ofList []) ByteArray.empty enc)) = 1 ∧
      (none : Ref) ≠ some (.hashed h) ∧
      some (Node.hashed h) ≠ some (Node.leaf (Nibbles.ofList []) ByteArray.empty enc) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro equality
    cases equality
  · intro equality
    cases equality

private theorem resolved_variants (p : Nibbles) (n : Node) (cs : Array Ref)
    (v : ByteArray) (e : Enc) :
    variant (some (.ext p n e)) = 2 ∧ variant (some (.branch cs v e)) = 3 := ⟨rfl, rfl⟩

-- These arities include values outside future size-16 admission.
private theorem arbitrary_branch_arity (arity : Nat) (child : Ref) (value : ByteArray)
    (enc : Enc) :
    match Node.branch (Array.replicate arity child) value enc with
    | .branch cs v e => cs.size = arity ∧ cs.toList = List.replicate arity child ∧
        v = value ∧ e = enc
    | _ => False := by
  simp

private theorem branch_arity_controls (child : Ref) (value : ByteArray) (enc : Enc) :
    ∀ arity ∈ [0, 15, 16, 17],
      match Node.branch (Array.replicate arity child) value enc with
      | .branch cs v e => cs.size = arity ∧ cs.toList = List.replicate arity child ∧
          v = value ∧ e = enc
      | _ => False := by
  intro arity _
  exact arbitrary_branch_arity arity child value enc

-- Both cache-presence choices at all widths deliberately include incoherent caches.
private theorem cache_width_controls (byte : UInt8) (h : Hash32) :
    ∀ width ∈ [31, 32, 33], ∀ cached ∈ [none, some h],
      let raw := (List.replicate width byte).toByteArray
      (Enc.mk raw cached).rlp = raw ∧ (Enc.mk raw cached).rlp.size = width ∧
        (Enc.mk raw cached).hash? = cached := by
  intro width _ cached _
  exact ⟨rfl, by simp, rfl⟩

-- Empty labels and ext-to-leaf/ext are expressible without choosing Node.WF.
private theorem nested_extension_fields (p q : Nibbles) (v : ByteArray) (a b c : Enc) :
    match Node.ext p (.ext q (.leaf (Nibbles.ofList []) v c) b) a with
    | .ext actualP (.ext actualQ (.leaf actualLeaf actualV actualC) actualB) actualA =>
        actualP = p ∧ actualQ = q ∧ actualLeaf.toList = [] ∧ actualV = v ∧
          actualC = c ∧ actualB = b ∧ actualA = a
    | _ => False := by
  exact ⟨rfl, rfl, Nibbles.toList_ofList [], rfl, rfl, rfl, rfl⟩

-- Pattern matching traverses two literal array levels and retains every full payload.
private theorem recursive_array_fields (p : Nibbles) (value outerValue innerValue : ByteArray)
    (outerEnc innerEnc leafEnc : Enc) (h : Hash32) :
    match Node.branch
      #[none, some (Node.branch #[some (.leaf p value leafEnc), some (.hashed h)]
        innerValue innerEnc)] outerValue outerEnc with
    | .branch outer actualOuterValue actualOuterEnc =>
        outer[0]? = some none ∧ actualOuterValue = outerValue ∧
          actualOuterEnc = outerEnc ∧
          (match outer[1]? with
          | some (some (Node.branch inner actualInnerValue actualInnerEnc)) =>
              actualInnerValue = innerValue ∧ actualInnerEnc = innerEnc ∧
                inner[1]? = some (some (.hashed h)) ∧
                (match inner[0]? with
                | some (some (Node.leaf actualP actualValue actualEnc)) =>
                    actualP = p ∧ actualValue = value ∧ actualEnc = leafEnc
                | _ => False)
          | _ => False)
    | _ => False := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end STFSpec.Conformance.Commit.NodeCallerProofs
