/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.Root

/-!
# Complete-value root-domain support guards

Library `EthConformance`. Ordered-map filters observe the expression in the public
`PatricializeDomain.child` statement. The remaining-key sum is a local copy of the
owner's measure expression. No root or node is fabricated.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/4/7.1.
-/

namespace STFSpec.Conformance.Commit.RootDomainGuards

open STFSpec.Commit

/-- Finite executable check of exactly the public domain. -/
def domainCheck (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat) : Bool :=
  obj.keys.all fun k ↦ decide (level ≤ k.size) &&
    obj.keys.all (fun j ↦ decide (k.take level = j.take level))

/-- The finite guard checks the complete domain rather than only the depth bound. -/
theorem domainCheck_iff (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat) :
    domainCheck obj level = true ↔ PatricializeDomain obj level := by
  simp only [domainCheck, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    constructor
    · intro k hk
      exact (h k (Std.ExtTreeMap.mem_keys.mpr hk)).1
    · intro k hk j hj
      exact (h k (Std.ExtTreeMap.mem_keys.mpr hk)).2 j (Std.ExtTreeMap.mem_keys.mpr hj)
  · intro h k hk
    exact ⟨h.depth k (Std.ExtTreeMap.mem_keys.mp hk),
      fun j hj ↦ h.consumedPrefix k (Std.ExtTreeMap.mem_keys.mp hk)
        j (Std.ExtTreeMap.mem_keys.mp hj)⟩

/-- Guarded full-key filter appearing in the public `PatricializeDomain.child` statement. -/
def partition (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (digit : Fin 16) : Std.ExtTreeMap Nibbles ByteArray :=
  obj.filter fun k _ ↦
    if h : level < k.size then decide (k.get ⟨level, h⟩ = digit) else false

/-- Complete remaining-key sum using a local copy of the owner's measure expression. -/
def remaining (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat) : Nat :=
  (obj.keys.map fun k ↦ k.size - level).sum

/-- Observe complete full keys and complete byte values, in the map's numeric order. -/
def entries (obj : Std.ExtTreeMap Nibbles ByteArray) : List (List Nat × List UInt8) :=
  obj.toList.map fun (k, v) ↦ (k.toList.map Fin.val, v.data.toList)

/-- Model input adapter; all digits are bounded in these finite test inputs. -/
def key (xs : List (Fin 16)) : Nibbles := Nibbles.ofList xs

/-- Empty values remain present independently of the absence sentinel. -/
def ending : Std.ExtTreeMap Nibbles ByteArray :=
  (∅ : Std.ExtTreeMap Nibbles ByteArray).insert (key [0]) ByteArray.empty
    |>.insert (key [0, 1]) ⟨#[42, 43]⟩

/-- Same complete map from reversed insertion. -/
def endingReverse : Std.ExtTreeMap Nibbles ByteArray :=
  (∅ : Std.ExtTreeMap Nibbles ByteArray).insert (key [0, 1]) ⟨#[42, 43]⟩
    |>.insert (key [0]) ByteArray.empty

/-- Prefix relationship starting with the empty key. -/
def emptyPrefix : Std.ExtTreeMap Nibbles ByteArray :=
  (∅ : Std.ExtTreeMap Nibbles ByteArray).insert (key []) ⟨#[99]⟩
    |>.insert (key [15]) ByteArray.empty

/-- Every numeric child, with distinguishable values and an empty ending key. -/
def allDigits : Std.ExtTreeMap Nibbles ByteArray :=
  (List.finRange 16).foldl
    (fun obj digit ↦ obj.insert (key [digit]) ⟨#[UInt8.ofNat digit.val]⟩)
    ((∅ : Std.ExtTreeMap Nibbles ByteArray).insert (key []) ByteArray.empty)

/-- Odd, unbounded finite paths; no secured-key width cap. -/
def longOdd : Std.ExtTreeMap Nibbles ByteArray :=
  (∅ : Std.ExtTreeMap Nibbles ByteArray)
    |>.insert (key (List.replicate 257 3)) ByteArray.empty
    |>.insert (key (List.replicate 257 3 ++ [4, 5])) ⟨#[7]⟩

/-- Equal depths alone do not give a reachable domain. -/
def inconsistent : Std.ExtTreeMap Nibbles ByteArray :=
  (∅ : Std.ExtTreeMap Nibbles ByteArray).insert (key [0]) ⟨#[1]⟩
    |>.insert (key [1]) ⟨#[2]⟩

/-- Complete values compared by committed guards; local native checks are separate evidence. -/
inductive Observation where
  | bool (value : Bool)
  | nat (value : Nat)
  | counts (values : List Nat)
  | entries (values : List (List Nat × List UInt8))
  | branches (values : List (List (List Nat × List UInt8)))
  | lookup (value : Option (List UInt8))
  deriving BEq, DecidableEq, Repr

/-- Named complete-value cases, with actual and independently written expected values. -/
def cases : List (String × Observation × Observation) := [
  ("empty domain at arbitrary depth", .bool (domainCheck ∅ 999), .bool true),
  ("empty remaining", .nat (remaining ∅ 0), .nat 0),
  ("empty children", .branches ((List.finRange 16).map fun d ↦ entries (partition ∅ 0 d)),
    .branches (List.replicate 16 [])),
  ("singleton empty key/value", .entries (entries ((∅ : Std.ExtTreeMap Nibbles ByteArray)
    |>.insert (key []) ByteArray.empty)), .entries [([], [])]),
  ("ending singleton zero sum", .nat (remaining ((∅ : Std.ExtTreeMap Nibbles ByteArray)
    |>.insert (key [0, 1, 2]) ByteArray.empty) 3), .nat 0),
  ("prefix-related map", .entries (entries ending), .entries [([0], []), ([0, 1], [42, 43])]),
  ("insertion permutation", .entries (entries endingReverse),
    .entries [([0], []), ([0, 1], [42, 43])]),
  ("domain zero", .bool (domainCheck ending 0), .bool true),
  ("shared extension domain", .bool (domainCheck ending 1), .bool true),
  ("short key domain counterexample", .bool (domainCheck ending 2), .bool false),
  ("inconsistent consumed prefixes", .bool (domainCheck inconsistent 1), .bool false),
  ("past ending singleton", .bool (domainCheck ((∅ : Std.ExtTreeMap Nibbles ByteArray)
    |>.insert (key []) ByteArray.empty) 1), .bool false),
  ("extension sum", .counts [remaining ending 0, remaining ending 1], .counts [3, 1]),
  ("all child sums including empty", .counts ((List.finRange 16).map fun d ↦
    remaining (partition ending 1 d) 2), .counts (List.replicate 16 0)),
  ("ending exclusion and complete child values", .branches ((List.finRange 16).map fun d ↦
    entries (partition ending 1 d)),
    .branches ([[], [([0, 1], [42, 43])]] ++ List.replicate 14 [])),
  ("child domains", .bool ((List.finRange 16).all fun d ↦
    domainCheck (partition ending 1 d) 2), .bool true),
  ("every ending child strictly descends", .bool ((List.finRange 16).all fun d ↦
    decide (remaining (partition ending 1 d) 2 < remaining ending 1)), .bool true),
  ("ending representative empty present value", .lookup ((ending[(key [0]).take 1]?).map
    (fun v ↦ v.data.toList)), .lookup (some [])),
  ("continuing representative same empty present value",
    .lookup ((ending[(key [0, 1]).take 1]?).map (fun v ↦ v.data.toList)), .lookup (some [])),
  ("empty key with continuation", .entries (entries emptyPrefix),
    .entries [([], [99]), ([15], [])]),
  ("empty prefix positive multikey sum", .nat (remaining emptyPrefix 0), .nat 1),
  ("all sixteen numeric groups", .branches ((List.finRange 16).map fun d ↦
    entries (partition allDigits 0 d)),
    .branches ((List.range 16).map fun d ↦ [([d], [UInt8.ofNat d])])),
  ("all digits positivity", .nat (remaining allDigits 0), .nat 16),
  ("all numeric children zero remaining", .counts ((List.finRange 16).map fun d ↦
    remaining (partition allDigits 0 d) 1), .counts (List.replicate 16 0)),
  ("all numeric child domains", .bool ((List.finRange 16).all fun d ↦
    domainCheck (partition allDigits 0 d) 1), .bool true),
  ("all numeric children strictly descend", .bool ((List.finRange 16).all fun d ↦
    decide (remaining (partition allDigits 0 d) 1 < remaining allDigits 0)), .bool true),
  ("odd long complete paths", .entries (entries longOdd),
    .entries [(List.replicate 257 3, []), (List.replicate 257 3 ++ [4, 5], [7])]),
  ("positive long extension domain", .bool (domainCheck longOdd 257), .bool true),
  ("positive long extension sums", .counts [remaining longOdd 0, remaining longOdd 257],
    .counts [516, 2]),
  ("long extension child retains full path", .entries (entries (partition longOdd 257 4)),
    .entries [(List.replicate 257 3 ++ [4, 5], [7])]),
  ("long child strict sum", .nat (remaining (partition longOdd 257 4) 258), .nat 1),
  ("all long children strictly descend including empty", .bool ((List.finRange 16).all fun d ↦
    decide (remaining (partition longOdd 257 d) 258 < remaining longOdd 257)), .bool true),
  ("zero advancement is not strict", .bool (decide (remaining ending 1 < remaining ending 1)),
    .bool false),
  ("empty extension is not strict", .bool (decide (remaining ∅ 1 < remaining ∅ 0)), .bool false),
  ("singleton zero sum is not positive", .bool (decide (0 < remaining
    ((∅ : Std.ExtTreeMap Nibbles ByteArray).insert (key []) ByteArray.empty) 0)), .bool false)
]

/-- Each comparison uses its complete structured result, with no checksum. -/
def allCases : Bool := cases.all fun (_, actual, expected) ↦ actual == expected

#guard allCases

end STFSpec.Conformance.Commit.RootDomainGuards
