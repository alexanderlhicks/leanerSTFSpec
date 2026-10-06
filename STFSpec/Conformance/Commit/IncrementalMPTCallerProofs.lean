/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit

/-!
# Incremental-trie public-import clients

Library `EthConformance`. Private ordinary proofs observe the complete supplied
flag and nominal root, including nested raw/cache fields and non-admitted shapes.
These clients certify field retention, not decoding or any trie operation.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/5/10.
-/

namespace STFSpec.Conformance.Commit.IncrementalMPTCallerProofs

open STFSpec.Base STFSpec.Commit

private theorem constructor_fields (secured : Bool) (root : Ref) :
    (IncrementalMPT.mk secured root).secured = secured ∧
      (IncrementalMPT.mk secured root).root = root := ⟨rfl, rfl⟩

private theorem reconstruct (trie : IncrementalMPT) :
    IncrementalMPT.mk trie.secured trie.root = trie := by
  cases trie
  rfl

private theorem secured_controls (root : Ref) :
    (IncrementalMPT.mk false root).secured = false ∧
      (IncrementalMPT.mk true root).secured = true ∧
      (IncrementalMPT.mk false root).root = root ∧
      (IncrementalMPT.mk true root).root = root := ⟨rfl, rfl, rfl, rfl⟩

private theorem absence_stub (secured : Bool) (hash : Hash32) :
    (IncrementalMPT.mk secured none).root = none ∧
      (IncrementalMPT.mk secured (some (.hashed hash))).root = some (.hashed hash) ∧
      IncrementalMPT.mk secured none ≠ IncrementalMPT.mk secured (some (.hashed hash)) := by
  refine ⟨rfl, rfl, ?_⟩
  intro equality
  have roots := congrArg IncrementalMPT.root equality
  cases roots

private theorem leaf_fields (secured : Bool) (path : Nibbles) (value raw : ByteArray)
    (cached : Option Hash32) :
    match (IncrementalMPT.mk secured (some (.leaf path value ⟨raw, cached⟩))).root with
    | some (.leaf p v enc) => p = path ∧ v = value ∧ enc.rlp = raw ∧ enc.hash? = cached
    | _ => False := ⟨rfl, rfl, rfl, rfl⟩

private theorem extension_fields (secured : Bool) (path : Nibbles) (child : Node)
    (raw : ByteArray) (cached : Option Hash32) :
    match (IncrementalMPT.mk secured (some (.ext path child ⟨raw, cached⟩))).root with
    | some (.ext p c enc) => p = path ∧ c = child ∧ enc.rlp = raw ∧ enc.hash? = cached
    | _ => False := ⟨rfl, rfl, rfl, rfl⟩

private theorem branch_fields (secured : Bool) (children : Array Ref)
    (value raw : ByteArray) (cached : Option Hash32) :
    match (IncrementalMPT.mk secured (some (.branch children value ⟨raw, cached⟩))).root with
    | some (.branch cs v enc) =>
        cs = children ∧ v = value ∧ enc.rlp = raw ∧ enc.hash? = cached
    | _ => False := ⟨rfl, rfl, rfl, rfl⟩

-- Arbitrary arity, raw width and cache presence remain representable, without admission.
private theorem bare_shape_controls (secured : Bool) (child : Ref) (value : ByteArray)
    (byte : UInt8) :
    ∀ (arity width : Nat) (cached : Option Hash32),
      let raw := (List.replicate width byte).toByteArray
      match (IncrementalMPT.mk secured
        (some (.branch (Array.replicate arity child) value ⟨raw, cached⟩))).root with
      | some (.branch cs v enc) =>
          cs.size = arity ∧ cs.toList = List.replicate arity child ∧
            v = value ∧ enc.rlp = raw ∧ enc.rlp.size = width ∧ enc.hash? = cached
      | _ => False := by
  intro arity width cached
  exact ⟨by simp, by simp, rfl, rfl, by simp, rfl⟩

-- Two array levels retain every raw/cache payload, including an ext-to-leaf bare shape.
private theorem nested_fields (secured : Bool) (p q : Nibbles) (hash : Hash32)
    (outerValue innerValue leafValue outerRaw innerRaw extRaw leafRaw : ByteArray)
    (outerCache innerCache extCache leafCache : Option Hash32) :
    match (IncrementalMPT.mk secured (some (.branch
      #[none, some (.branch
        #[some (.ext p (.leaf q leafValue ⟨leafRaw, leafCache⟩) ⟨extRaw, extCache⟩),
          some (.hashed hash)] innerValue ⟨innerRaw, innerCache⟩)]
      outerValue ⟨outerRaw, outerCache⟩))).root with
    | some (.branch outer ov oe) =>
        outer[0]? = some none ∧ ov = outerValue ∧ oe.rlp = outerRaw ∧
          oe.hash? = outerCache ∧
          (match outer[1]? with
          | some (some (Node.branch inner iv ie)) =>
              iv = innerValue ∧ ie.rlp = innerRaw ∧ ie.hash? = innerCache ∧
                inner[1]? = some (some (.hashed hash)) ∧
                (match inner[0]? with
                | some (some (Node.ext ep (Node.leaf lp lv le) ee)) =>
                    ep = p ∧ lp = q ∧ lv = leafValue ∧ le.rlp = leafRaw ∧
                      le.hash? = leafCache ∧ ee.rlp = extRaw ∧ ee.hash? = extCache
                | _ => False)
          | _ => False)
    | _ => False := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end STFSpec.Conformance.Commit.IncrementalMPTCallerProofs
