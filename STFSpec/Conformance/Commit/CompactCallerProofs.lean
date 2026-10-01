/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit

/-!
# Compact decoder public-law callers

Library `EthConformance`. Consumers use the bounded path model and ordinary
public equations; no provider representation is unfolded.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/7/8.
-/

namespace STFSpec.Conformance.Commit.CompactCallerProofs

open STFSpec.Commit

example (b : ByteArray) :
    (compactToNibbles b).map (fun p ↦ (p.1.toList, p.2)) =
      compactToNibblesModel b.data.toList := compactToNibbles_eq_model b
example : compactToNibbles ByteArray.empty = .error (.malformed .compactEmpty) :=
  compactToNibbles_empty
example (b : ByteArray) (e : TrieError) : compactToNibbles b = .error e ↔
    b.size = 0 ∧ e = .malformed .compactEmpty := compactToNibbles_error_iff b e
example (b : ByteArray) (p : Nibbles) (leaf : Bool) :
    compactToNibbles b = .ok (p, leaf) ↔
      compactToNibblesModel b.data.toList = .ok (p.toList, leaf) :=
  compactToNibbles_ok_iff b p leaf
example (b : ByteArray) :
    (∃ p l, compactToNibbles b = .ok (p, l)) ↔ 0 < b.size := compactToNibbles_success_iff b
example (b : ByteArray) (p : Nibbles) (leaf : Bool)
    (h : compactToNibbles b = .ok (p, leaf)) (hb : 0 < b.size) :
    leaf = compactIsLeaf b[0] := compactToNibbles_leaf b p leaf h hb
example (b : ByteArray) (p : Nibbles) (leaf : Bool)
    (h : compactToNibbles b = .ok (p, leaf)) (hb : 0 < b.size) :
    p.size = 2 * (b.size - 1) + if compactIsOdd b[0] then 1 else 0 :=
  compactToNibbles_size b p leaf h hb
example (x : Nibbles) (leaf : Bool) :
    compactToNibbles (nibbleListToCompact x leaf) = .ok (x, leaf) :=
  compactToNibbles_nibbleListToCompact x leaf
example (x y : Nibbles) (leaf other : Bool) :
    nibbleListToCompact x leaf = nibbleListToCompact y other ↔ x = y ∧ leaf = other :=
  nibbleListToCompact_inj x y leaf other
example (b : ByteArray) (p : Nibbles) (leaf : Bool) (h : compactToNibbles b = .ok (p, leaf)) :
    compactToNibbles (nibbleListToCompact p leaf) = compactToNibbles b :=
  compactToNibbles_normalization b p leaf h
example (b : ByteArray) (p : Nibbles) (leaf : Bool) (h : compactToNibbles b = .ok (p, leaf)) :
    nibbleListToCompact p leaf = b ↔ ∃ x l, b = nibbleListToCompact x l :=
  nibbleListToCompact_decode_eq_iff b p leaf h

example (b : ByteArray) (path : Nibbles) (leaf : Bool)
    (h : compactToNibbles b = .ok (path, leaf)) (hb : 0 < b.size)
    (i : Nat) (hi : i < path.size) :
    (i + (if compactIsOdd b[0] then 1 else 2)) / 2 < b.size :=
  compactToNibbles_index_lt b path leaf h hb i hi

example (b : ByteArray) (path : Nibbles) (leaf : Bool)
    (h : compactToNibbles b = .ok (path, leaf)) (hb : 0 < b.size)
    (i : Nat) (hi : i < path.size) :
    let skip := if compactIsOdd b[0] then 1 else 2
    path.get ⟨i, hi⟩ =
      if (i + skip) % 2 = 0 then
        highNibble (b[(i + skip) / 2]'(compactToNibbles_index_lt b path leaf h hb i hi))
      else lowNibble (b[(i + skip) / 2]'(compactToNibbles_index_lt b path leaf h hb i hi)) :=
  compactToNibbles_get b path leaf h hb i hi

end STFSpec.Conformance.Commit.CompactCallerProofs
