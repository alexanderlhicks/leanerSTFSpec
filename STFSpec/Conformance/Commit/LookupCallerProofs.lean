/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Commit

/-!
# Pure lookup public clients

Library `EthConformance`. Only public constructor equations and flat diagnostic
injectivity are consumed; no private traversal or storage is unfolded.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` C20/Q59/§7.0.5.
-/
namespace STFSpec.Conformance.Commit.LookupCallerProofs
open STFSpec.Base STFSpec.Commit

/-- An absent root is successful absence. -/
private theorem client_lookup_none (key : Nibbles) : lookup none key = .ok none := by
  exact lookup_none key

/-- A reached unresolved stub fails before key exhaustion. -/
private theorem client_lookup_hashed (h : Hash32) (key : Nibbles) :
    lookup (some (.hashed h)) key = .error (.unresolved h) := by
  exact lookup_hashed h key

/-- A leaf matches the complete remaining key and preserves even an empty value. -/
private theorem client_lookup_leaf (path : Nibbles) (value : ByteArray) (enc : Enc)
    (key : Nibbles) :
    lookup (some (.leaf path value enc)) key = .ok (if path = key then some value else none) := by
  exact lookup_leaf path value enc key

/-- An extension descends only after its whole clipped-prefix match. -/
private theorem client_lookup_ext (path : Nibbles) (child : Node) (enc : Enc)
    (key : Nibbles) :
    lookup (some (.ext path child enc)) key =
      if path = key.take path.size then lookup (some child) (key.drop path.size)
      else .ok none := by
  exact lookup_ext path child enc key

/-- Terminal branch value dispatch precedes all selected-slot bounds. -/
private theorem client_lookup_branch_emptyKey (children : Array Ref) (value : ByteArray)
    (enc : Enc) (key : Nibbles) (hkey : key.size = 0) :
    lookup (some (.branch children value enc)) key =
      .ok (if value.size = 0 then none else some value) := by
  exact lookup_branch_emptyKey children value enc key hkey

/-- A nonterminal in-bounds branch follows exactly its selected child. -/
private theorem client_lookup_branch_index (children : Array Ref) (value : ByteArray)
    (enc : Enc) (key : Nibbles) (hkey : 0 < key.size)
    (hindex : (key.get ⟨0, hkey⟩).val < children.size) :
    lookup (some (.branch children value enc)) key =
      lookup (children[(key.get ⟨0, hkey⟩).val]'hindex) (key.drop 1) := by
  exact lookup_branch_index children value enc key hkey hindex

/-- A missing selected slot retains the actual nibble and actual array arity. -/
private theorem client_lookup_branch_oob (children : Array Ref) (value : ByteArray)
    (enc : Enc) (key : Nibbles) (hkey : 0 < key.size)
    (hindex : children.size ≤ (key.get ⟨0, hkey⟩).val) :
    lookup (some (.branch children value enc)) key =
      .error (.malformed (.branchIndex (key.get ⟨0, hkey⟩).val children.size)) := by
  exact lookup_branch_oob children value enc key hkey hindex

private theorem index_injective (i j a b : Nat)
    (h : Malformed.branchIndex i a = .branchIndex j b) : i = j ∧ a = b := by
  cases h
  exact ⟨rfl, rfl⟩
private theorem index_wrapper (i j a b : Nat)
    (h : TrieError.malformed (.branchIndex i a) = .malformed (.branchIndex j b)) :
    i = j ∧ a = b := index_injective i j a b (TrieError.malformed.inj h)
private theorem index_not_cycle (i a : Nat) : Malformed.branchIndex i a ≠ .cycle := by
  intro h
  cases h
end STFSpec.Conformance.Commit.LookupCallerProofs
