/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpCanonical
import STFSpec.Commit.Compact

/-!
# Public clients of decoder diagnostics and codec/compact contracts

Library `EthConformance`. Symbolic clients preserve exact error identity and
compose public codec and compact laws without unfolding provider storage.
No whole node decoder or witness/outcome adapter is implemented here.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/5/7 (Q52/Q60).
-/

namespace STFSpec.Conformance.Commit.DecoderDiagnosticCallerProofs

open STFSpec.Codec STFSpec.Commit

/-- Diagnostic wrapping preserves and reflects every exact malformed condition. -/
theorem malformed_inj (a b : Malformed) :
    TrieError.malformed a = TrieError.malformed b ↔ a = b := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    cases h
    rfl

/-- Both new conditions are distinct from every error the compact seam can return. -/
theorem compact_error_distinct (wire : ByteArray) (e : TrieError)
    (h : compactToNibbles wire = .error e) :
    e ≠ .malformed .compactPathList ∧ e ≠ .malformed .leafValueList ∧
      e ≠ .malformed .pathEmpty := by
  have he := (compactToNibbles_error_iff wire e).mp h
  rcases he with ⟨_, rfl⟩
  exact ⟨by decide, by decide, by decide⟩

/-- Nonempty raw compact input produces a complete path and flag before C14 dispatch. -/
theorem nonempty_compact (wire : ByteArray) (h : 0 < wire.size) :
    ∃ path leaf, compactToNibbles wire = .ok (path, leaf) :=
  (compactToNibbles_success_iff wire).mpr h

/-- Whole-input RLP success fixes the complete bytes for the later node consumer. -/
theorem node_wire_bound (wire : ByteArray) (item : RlpItem)
    (h : Rlp.decode wire = .ok item) :
    Rlp.Encodable item ∧ Rlp.encode item = wire :=
  ⟨Rlp.decode_success_encodable wire item h, Rlp.encode_eq_of_decode_eq_ok wire item h⟩

/-- A failed whole-input codec parse cannot also supply a decoded semantic node. -/
theorem failed_rlp_no_item (wire : ByteArray) (e : RlpError)
    (h : Rlp.decode wire = .error e) : ∀ item, Rlp.decode wire ≠ .ok item := by
  intro item hi
  rw [h] at hi
  cases hi

/- Q60 constructor-only clients: no mutation emission or public helper/law. -/
private theorem collapseIndex_inj (i j : Nat) :
    Malformed.collapseIndex i = .collapseIndex j ↔ i = j := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    cases h
    rfl

private theorem collapseIndex_wrapped_inj (i j : Nat) :
    TrieError.malformed (.collapseIndex i) = .malformed (.collapseIndex j) ↔ i = j := by
  rw [malformed_inj, collapseIndex_inj]

private theorem collapseIndex_not_branchIndex (i j arity : Nat) :
    Malformed.collapseIndex i ≠ .branchIndex j arity := by
  intro h
  cases h

private theorem collapseIndex_not_occupancy (i n : Nat) :
    Malformed.collapseIndex i ≠ .occupancy n := by
  intro h
  cases h

end STFSpec.Conformance.Commit.DecoderDiagnosticCallerProofs
