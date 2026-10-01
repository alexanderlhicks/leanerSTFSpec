/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit
import Std.Data.ExtTreeMap.Lemmas

/-!
# Public nibble copying, ordering and map clients

Library `EthConformance`. Symbolic clients use public List/observer laws only.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/7/8.
-/

namespace STFSpec.Conformance.Commit.NibblesOperationsCallerProofs

open STFSpec.Commit

/-- Actual map insertion uses actual path equality, with no comparator aliasing. -/
theorem map_insert_get (t : Std.ExtTreeMap Nibbles Nat) (k a : Nibbles) (v : Nat) :
    (t.insert k v)[a]? = if k = a then some v else t[a]? := by
  simp only [Std.ExtTreeMap.getElem?_insert, Nibbles.compare_eq_eq_iff]

/-- Equal public key lookups give actual map equality. -/
theorem map_ext (t u : Std.ExtTreeMap Nibbles Nat)
    (h : ∀ k : Nibbles, t[k]? = u[k]?) : t = u := Std.ExtTreeMap.ext_getElem? h

/-- Clipped windows compose using prefix and suffix public equations. -/
theorem clipped_window (x : Nibbles) (start stop : Nat) :
    (x.take stop).drop start = x.extract start stop := Nibbles.drop_take x stop start

/-- A copied prefix of a suffix is the corresponding absolute window. -/
theorem suffix_prefix (x : Nibbles) (start n : Nat) :
    (x.drop start).take n = x.extract start (start + n) := Nibbles.take_drop x start n

/-- Repeated suffix copies preserve their complete model. -/
theorem suffix_composition (x : Nibbles) (a b : Nat) :
    (x.drop a).drop b = x.drop (a + b) := Nibbles.drop_drop x a b

/-- The returned maximal prefix is an equal bounded path. -/
theorem prefix_paths (a b : Nibbles) :
    a.take (commonPrefixLength a b) = b.take (commonPrefixLength a b) :=
  Nibbles.take_commonPrefixLength a b

/-- Strict measure support retains both essential caller hypotheses. -/
theorem remaining_length (x : Nibbles) (level n : Nat)
    (hlevel : level < x.size) (hn : 0 < n) :
    (x.drop (level + n)).size < (x.drop level).size :=
  Nibbles.size_drop_add_lt x level n hlevel hn

example (n : Nat) (f : Nat → Fin 16) : (Nibbles.generate n f).size = n :=
  Nibbles.size_generate n f
example (n : Nat) (f : Nat → Fin 16) :
    (Nibbles.generate n f).toList = (List.range n).map f := Nibbles.toList_generate n f
example (n : Nat) (f : Nat → Fin 16) (i : Nat) (hi : i < n) :
    (Nibbles.generate n f).get ⟨i, by rw [Nibbles.size_generate]; exact hi⟩ = f i :=
  Nibbles.get_generate n f i hi
example (n : Nat) (f g : Nat → Fin 16) (h : ∀ i, i < n → f i = g i) :
    Nibbles.generate n f = Nibbles.generate n g := Nibbles.generate_congr n f g h
example (x : Nibbles) (start stop : Nat) :
    (x.extract start stop).size = min stop x.size - start := Nibbles.size_extract x start stop
example (x : Nibbles) (start stop : Nat) :
    (x.extract start stop).toList = (x.toList.drop start).take (stop - start) :=
  Nibbles.toList_extract x start stop
example (x : Nibbles) (start stop i : Nat) (hi : i < (x.extract start stop).size) :
    (x.extract start stop).get ⟨i, hi⟩ =
      x.get ⟨start + i, by rw [Nibbles.size_extract] at hi; omega⟩ :=
  Nibbles.get_extract x start stop i hi
example (x : Nibbles) (n : Nat) : (x.take n).toList = x.toList.take n := Nibbles.toList_take x n
example (x : Nibbles) (n : Nat) : (x.drop n).toList = x.toList.drop n := Nibbles.toList_drop x n
example (x : Nibbles) (n i : Nat) (hi : i < (x.take n).size) :
    (x.take n).get ⟨i, hi⟩ = x.get ⟨i, by rw [Nibbles.size_take] at hi; omega⟩ :=
  Nibbles.get_take x n i hi
example (x : Nibbles) (n i : Nat) (hi : i < (x.drop n).size) :
    (x.drop n).get ⟨i, hi⟩ = x.get ⟨n + i, by rw [Nibbles.size_drop] at hi; omega⟩ :=
  Nibbles.get_drop x n i hi
example (x : Nibbles) (n : Nat) : (x.take n).size = min n x.size := Nibbles.size_take x n
example (x : Nibbles) (n : Nat) : (x.drop n).size = x.size - n := Nibbles.size_drop x n
example (x : Nibbles) (n : Nat) : (x.take n).size ≤ x.size := Nibbles.size_take_le x n
example (x : Nibbles) (n : Nat) : (x.drop n).size ≤ x.size := Nibbles.size_drop_le x n
example (x : Nibbles) : x.take 0 = Nibbles.ofList [] := Nibbles.take_zero x
example (x : Nibbles) : x.drop 0 = x := Nibbles.drop_zero x
example (x : Nibbles) : x.take x.size = x := Nibbles.take_size x
example (x : Nibbles) : x.drop x.size = Nibbles.ofList [] := Nibbles.drop_size x
example (f : Nat → Fin 16) : Nibbles.generate 0 f = Nibbles.ofList [] := Nibbles.generate_zero f
example (x : Nibbles) (n : Nat) (h : x.size ≤ n) : x.take n = x := Nibbles.take_of_size_le x n h
example (x : Nibbles) (n : Nat) (h : x.size ≤ n) :
    x.drop n = Nibbles.ofList [] := Nibbles.drop_of_size_le x n h
example (x : Nibbles) (a b : Nat) (h : b ≤ a) :
    x.extract a b = Nibbles.ofList [] := Nibbles.extract_of_stop_le_start x a b h
example (x : Nibbles) (a b : Nat) (h : x.size ≤ a) :
    x.extract a b = Nibbles.ofList [] := Nibbles.extract_of_size_le_start x a b h
example (x : Nibbles) (a b : Nat) : (x.take a).take b = x.take (min b a) :=
  Nibbles.take_take x a b
example (a b : Nibbles) : compare a b = compare a.toList b.toList := Nibbles.compare_toList a b
example (a b : Nibbles) : compare a b = .eq ↔ a = b := Nibbles.compare_eq_eq_iff a b
example (a a' b b' : Nibbles) (ha : a.toList = a'.toList) (hb : b.toList = b'.toList) :
    compare a b = compare a' b' := Nibbles.compare_of_toList_eq a a' b b' ha hb
example (x : Nibbles) (level : Nat) (h : level < x.size) :
    (x.drop (level+1)).size < (x.drop level).size := Nibbles.size_drop_succ_lt x level h
example (a b : Nibbles) (k : Nat) (ha : k ≤ a.size) (hb : k ≤ b.size) :
    a.take k = b.take k ↔ k ≤ commonPrefixLength a b :=
  Nibbles.take_eq_iff_le_commonPrefixLength a b k ha hb

end STFSpec.Conformance.Commit.NibblesOperationsCallerProofs
