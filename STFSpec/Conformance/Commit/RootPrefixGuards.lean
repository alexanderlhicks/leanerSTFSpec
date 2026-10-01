/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Conformance.Commit.RootDomainGuards

/-!
# Complete reference observations of longest shared-prefix support

Library `EthConformance`. Complete List/drop reference observations are linked
to the private packed scanner by the ordinary all-input equalities in Root. These
guards use public path/map contracts; they do not directly execute private Root
definitions. The production API remains `PatricializeDomain`; no recursive trie
or root is constructed here.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/4/7.1.
-/

namespace STFSpec.Conformance.Commit.RootPrefixGuards

open STFSpec.Commit RootDomainGuards

/-- Capped suffix reference; Root proves its all-input equality to the packed pair scan. -/
def pair (a b : Nibbles) (level cap : Nat) : Nat :=
  min cap (commonPrefixLength (a.drop level) (b.drop level))

private def prefixFold (representative : List (Fin 16)) (level : Nat) :
    List (List (Fin 16)) → Nat → Nat
  | [], cap => cap
  | key :: keys, cap => prefixFold representative level keys
      (min cap (commonPrefixLengthModel (representative.drop level) (key.drop level)))

/-- List/drop reference for any specified member; owner laws retain membership premises. -/
def prefixFrom (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat) (a : Nibbles) : Nat :=
  prefixFold a.toList level (obj.keys.map Nibbles.toList) (a.size - level)

/-- Complete selected-member reference, or an explicit empty result. Root proves
all-input selector equality to this head/fold expression. -/
def selection (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat) :
    Option (List Nat × Nat × List Nat) :=
  obj.keys.head?.map fun a ↦
    let amount := prefixFrom obj level a
    (a.toList.map Fin.val, amount, (a.extract level (level + amount)).toList.map Fin.val)

/-- The empty value does not suppress a key or change the selected path. -/
def singleton : Std.ExtTreeMap Nibbles ByteArray :=
  (∅ : Std.ExtTreeMap Nibbles ByteArray).insert (key [1, 2, 3, 4, 5]) ByteArray.empty

/-- Unequal lengths with a mismatch after an odd shared prefix. -/
def oddShared : Std.ExtTreeMap Nibbles ByteArray :=
  (∅ : Std.ExtTreeMap Nibbles ByteArray)
    |>.insert (key [1, 2, 3, 4]) ⟨#[7, 8]⟩
    |>.insert (key [1, 2, 3, 5, 6, 7]) ByteArray.empty

/-- Same map, independent insertion order. -/
def oddSharedReverse : Std.ExtTreeMap Nibbles ByteArray :=
  (∅ : Std.ExtTreeMap Nibbles ByteArray)
    |>.insert (key [1, 2, 3, 5, 6, 7]) ByteArray.empty
    |>.insert (key [1, 2, 3, 4]) ⟨#[7, 8]⟩

/-- All numeric next digits after a consumed prefix; none can extend it. -/
def prefixedDigits : Std.ExtTreeMap Nibbles ByteArray :=
  (List.finRange 16).foldl
    (fun obj digit ↦ obj.insert (key [7, 8, digit]) ⟨#[UInt8.ofNat digit.val]⟩) ∅

/-- Long packed paths, whose common portion has odd length beyond secured widths. -/
def longShared : Std.ExtTreeMap Nibbles ByteArray :=
  (∅ : Std.ExtTreeMap Nibbles ByteArray)
    |>.insert (Nibbles.generate 4098 (fun _ ↦ 3)) ByteArray.empty
    |>.insert (Nibbles.generate 4100 (fun i ↦ if i < 4097 then 3 else 4)) ⟨#[9, 10]⟩

/-- Finite domain-negative test: equal remaining suffixes do not repair consumed disagreement. -/
def wrongPrefix : Std.ExtTreeMap Nibbles ByteArray :=
  (∅ : Std.ExtTreeMap Nibbles ByteArray)
    |>.insert (key [0, 2, 3]) ByteArray.empty
    |>.insert (key [1, 2, 3]) ⟨#[1]⟩

/-- Complete selected-prefix observations from actual finite maps. -/
def selections : List (String × Option (List Nat × Nat × List Nat) ×
    Option (List Nat × Nat × List Nat)) := [
  ("empty zero", selection ∅ 0, none),
  ("empty arbitrary depth", selection ∅ 999, none),
  ("singleton complete", selection singleton 0, some ([1, 2, 3, 4, 5], 5, [1, 2, 3, 4, 5])),
  ("singleton arbitrary ending depth", selection singleton 5,
    some ([1, 2, 3, 4, 5], 0, [])),
  ("singleton remaining suffix", selection singleton 2, some ([1, 2, 3, 4, 5], 3, [3, 4, 5])),
  ("empty key and value", selection ((∅ : Std.ExtTreeMap Nibbles ByteArray)
    |>.insert (key []) ByteArray.empty) 0, some ([], 0, [])),
  ("prefix ending", selection ending 0, some ([0], 1, [0])),
  ("ending at consumed depth", selection ending 1, some ([0], 0, [])),
  ("ending reversed insertion", selection endingReverse 0, some ([0], 1, [0])),
  ("empty key prefix", selection emptyPrefix 0, some ([], 0, [])),
  ("all sixteen root digits", selection allDigits 0, some ([], 0, [])),
  ("all sixteen next digits", selection prefixedDigits 2, some ([7, 8, 0], 0, [])),
  ("odd shared unequal keys", selection oddShared 0, some ([1, 2, 3, 4], 3, [1, 2, 3])),
  ("odd shared at depth", selection oddShared 2, some ([1, 2, 3, 4], 1, [3])),
  ("odd insertion permutation", selection oddSharedReverse 0,
    some ([1, 2, 3, 4], 3, [1, 2, 3])),
  ("long odd prefix related", selection longOdd 0,
    some (List.replicate 257 3, 257, List.replicate 257 3)),
  ("long odd prefix ending", selection longOdd 257, some (List.replicate 257 3, 0, [])),
  ("long shared complete", selection longShared 0,
    some (List.replicate 4098 3, 4097, List.replicate 4097 3)),
  ("long shared advanced", selection longShared 4096,
    some (List.replicate 4098 3, 1, [3]))
]

/-- Complete scalar and domain-premise observations, including invalid domains. -/
def cases : List (String × Observation × Observation) := [
  ("alternative member odd", .counts (oddShared.keys.map (prefixFrom oddShared 0)),
    .counts [3, 3]),
  ("alternative member long", .counts (longShared.keys.map (prefixFrom longShared 4096)),
    .counts [1, 1]),
  ("alternative member ending", .counts (ending.keys.map (prefixFrom ending 1)), .counts [0, 0]),
  ("bounded cap", .counts ((List.range 6).map (pair (key [1, 2, 3, 4])
    (key [1, 2, 3, 5, 6, 7]) 0)), .counts [0, 1, 2, 3, 3, 3]),
  ("pair starts after consumed prefix", .nat (pair (key [0, 2, 3]) (key [1, 2, 3]) 1 99),
    .nat 2),
  ("wrong consumed prefix premise", .bool (domainCheck wrongPrefix 1), .bool false),
  ("wrong prefix result cannot imply advanced domain",
    .bool (domainCheck wrongPrefix (1 + prefixFrom wrongPrefix 1 (key [0, 2, 3]))), .bool false),
  ("wrong depth premise", .bool (domainCheck ending 2), .bool false),
  ("wrong depth scan safely exhausted", .nat (prefixFrom ending 2 (key [0, 1])), .nat 0),
  ("huge level bounded before digit read", .nat (pair (key [1]) (key [1]) (2 ^ 80) (2 ^ 80)),
    .nat 0),
  ("unequal ending bounds", .nat (pair (key [1, 2]) (key [1, 2, 3]) 1 99), .nat 1),
  ("long advanced domain", .bool (domainCheck longShared 4097), .bool true),
  ("long one more digit fails", .bool (domainCheck longShared 4098), .bool false),
  ("long full retained keys/values", .entries (entries longShared),
    .entries [(List.replicate 4098 3, []),
      (List.replicate 4097 3 ++ List.replicate 3 4, [9, 10])]),
  ("positive selected sum descent", .counts [remaining longShared 0, remaining longShared 4097],
    .counts [8198, 4]),
  ("zero shared next domain fails", .bool (domainCheck prefixedDigits 3), .bool false),
  ("empty map still has every next domain", .bool (domainCheck ∅ 1), .bool true)
]

/-- Exact complete values, rather than a checksum or sampled long path. -/
def allCases : Bool :=
  selections.all (fun (_, actual, expected) ↦ actual == expected) &&
    cases.all (fun (_, actual, expected) ↦ actual == expected)

#guard allCases

end STFSpec.Conformance.Commit.RootPrefixGuards
