/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Conformance.Commit.RootBranchGuards
import STFSpec.Conformance.Commit.RootPrefixGuards

/-!
# Complete recursive construction observations

Library `EthConformance`. Observations retain the node variant, full path, every
nested child field, value and ordered full query preimages/answers. Private selector
instrumentation tests actual recursive construction, never a copied algorithm.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/4/7.1/7.3.
-/

namespace STFSpec.Conformance.Commit.RootConstructionGuards

open STFSpec.Commit STFSpec.Codec STFSpec.Base STFSpec.Hash

/-- Exact private Root declarations for narrowly scoped test instrumentation. -/
macro "rootConstructionOwner% " helper:ident : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.STFSpec.Commit.Root 0).str "STFSpec" |>.str "Commit"
    |>.append helper.getId))

mutual
  /-- Explicit structural token stream, including list/byte tags and lengths. -/
  def itemTokens : RlpItem → List Nat
    | .bytes bytes => [0, bytes.size] ++ bytes.data.toList.map UInt8.toNat
    | .list items => [1, items.length] ++ itemsTokens items
  def itemsTokens : List RlpItem → List Nat
    | [] => []
    | item :: items => itemTokens item ++ itemsTokens items
end

/-- Variant, path, complete child structures and original value. -/
abbrev NodeView := Option (Nat × List Nat × List Nat × List Nat)

def nodeView : Option InternalNode → NodeView
  | none => none
  | some (.leaf path value) => some (0, path.toList.map Fin.val, [], itemTokens value)
  | some (.extension path child) => some (1, path.toList.map Fin.val, itemTokens child, [])
  | some (.branch children value) =>
      some (2, [], itemTokens (.list children.toList), itemTokens value)

def key (digits : List (Fin 16)) : Nibbles := Nibbles.ofList digits

def bytes (digits : List UInt8) : ByteArray := digits.toByteArray

def mapOf (entries : List (Nibbles × ByteArray)) : Std.ExtTreeMap Nibbles ByteArray :=
  entries.foldl (fun obj (key, value) ↦ obj.insert key value) ∅

/-- Complete concrete C7 return; the returned node is not itself C6-encoded. -/
def concrete (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (domain : PatricializeDomain obj level) : NodeView :=
  nodeView (patricialize (m := Id) obj level domain)

/-- Complete concrete query trace, independent of hash summaries. -/
def concreteTrace (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (domain : PatricializeDomain obj level) : NodeView × List (List UInt8 × List UInt8) :=
  letI : KeccakQuery (StateM (List (List UInt8 × List UInt8))) :=
    ⟨fun preimage state ↦
      let answer := keccak256 preimage
      (answer, state ++ [(preimage.data.toList, answer.toBytes.toByteArray.data.toList)])⟩
  let (node, trace) := (patricialize (m := StateM (List (List UInt8 × List UInt8))) obj level domain).run []
  (nodeView node, trace)

/-- A different valid member is selected afresh at every nonempty recursive map. -/
def alternate (obj : Std.ExtTreeMap Nibbles ByteArray) (level index : Nat)
    (domain : PatricializeDomain obj level) : NodeView :=
  let select : rootConstructionOwner% RepresentativeSelector := fun child depth hn ↦
    let selected := child.keys[(index + depth) % child.keys.length]'(by
      have h := Std.ExtTreeMap.length_keys (t := child)
      exact Nat.mod_lt _ (by omega))
    ⟨selected, Std.ExtTreeMap.mem_keys.mp (List.getElem_mem _)⟩
  let node : Id (Option InternalNode) :=
    (rootConstructionOwner% patricializeWith) select obj level domain
  nodeView node

/-- Every-node alternative construction equality is an ordinary recursive theorem. -/
theorem alternate_eq (obj : Std.ExtTreeMap Nibbles ByteArray) (level index : Nat)
    (domain : PatricializeDomain obj level) : alternate obj level index domain =
      concrete obj level domain := by
  dsimp only [alternate, concrete, patricialize]
  exact congrArg nodeView ((rootConstructionOwner% patricializeWith_independent) _ _ obj level domain)

/-- Complete observations under arbitrary answers and original ExceptT errors. -/
def recorded (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (domain : PatricializeDomain obj level) : NodeView × RootBranchGuards.Trace :=
  let (node, trace) := (patricialize (m := RootBranchGuards.TestState) obj level domain).run {}
  (nodeView node, trace)

def failed (obj : Std.ExtTreeMap Nibbles ByteArray) (level : Nat)
    (domain : PatricializeDomain obj level) (index : Nat) :
    Except RootBranchGuards.Failure NodeView × RootBranchGuards.Trace :=
  let (node, trace) := ((patricialize (m := RootBranchGuards.TestFailure)
    obj level domain).run).run {failQueryAt := some index}
  (node.map nodeView, trace)

def empty : Std.ExtTreeMap Nibbles ByteArray := ∅

theorem emptyDomain (level : Nat) : PatricializeDomain empty level :=
  (RootDomainGuards.domainCheck_iff empty level).mp (by rfl)

def singleton := mapOf [(key [2, 4, 6], bytes [0, 255])]
def emptySingleton := mapOf [(key [], ByteArray.empty)]
def ending := mapOf [(key [], ByteArray.empty), (key [0], ByteArray.empty)]
def prefixed := mapOf [(key [1, 2, 3], ByteArray.empty), (key [1, 2, 3, 4], bytes [9])]
def thresholds := mapOf ((List.finRange 16).map fun digit ↦
  (key [digit], bytes (List.replicate (28 + digit.val % 3) (UInt8.ofNat digit.val))))
def nested := mapOf ((List.finRange 16).map fun digit ↦
  (key [7, 8, digit], bytes (List.replicate (28 + digit.val % 3) (UInt8.ofNat digit.val))))

def expectedThresholdNode : Option InternalNode :=
  some (.branch (Vector.ofFn RootBranchGuards.expectedReference) (.bytes ByteArray.empty))

def expectedNestedNode : Option InternalNode :=
  let answer := Hash32.ofBytes32 (FixedBytes.ofNat 1010)
  some (.extension (key [7, 8]) (.bytes answer.toBytes.toByteArray))

def thresholdExpected : NodeView × RootBranchGuards.Trace :=
  (nodeView expectedThresholdNode,
    {events := (List.range 16).flatMap fun digit ↦
      if RootBranchGuards.payloadSize digit = 28 then [] else
        [.query (RootBranchGuards.queryIndexBefore digit)
          (RootBranchGuards.expectedPreimage digit)
          (Hash32.ofBytes32 (FixedBytes.ofNat
            (1000 + RootBranchGuards.queryIndexBefore digit))).toBytes.toByteArray.data.toList],
      queries := 10})

def nestedExpected : NodeView × RootBranchGuards.Trace :=
  (nodeView expectedNestedNode,
    {events := thresholdExpected.2.events ++
      [.query 10 (Rlp.encode (assembleInternalNode expectedThresholdNode)).data.toList
        (Hash32.ofBytes32 (FixedBytes.ofNat 1010)).toBytes.toByteArray.data.toList], queries := 11})

/-- Original oracle failure and only the earlier complete query prefix. -/
def errorExpected (healthy : NodeView × RootBranchGuards.Trace) (index : Nat) :
    Except RootBranchGuards.Failure NodeView × RootBranchGuards.Trace :=
  match healthy.2.events[index]? with
  | some (.query _ preimage _) =>
      (.error (.oracle index preimage),
        {events := healthy.2.events.take index ++ [.queryError index preimage],
          queries := index, failQueryAt := some index})
  | _ => (.ok healthy.1, {healthy.2 with failQueryAt := some index})

def cases : List (String × Bool) := [
  ("empty at zero", concrete empty 0 (PatricializeDomain.zero _) == none),
  ("empty at arbitrary depth", concrete empty 927 (emptyDomain _) == none),
  ("empty key and value", concrete emptySingleton 0 (PatricializeDomain.zero _) ==
    nodeView (some (.leaf (key []) (.bytes ByteArray.empty)))),
  ("singleton zero", concrete singleton 0 (PatricializeDomain.zero _) ==
    nodeView (some (.leaf (key [2, 4, 6]) (.bytes (bytes [0, 255]))))),
  ("singleton ending", concrete singleton 3
    ((RootDomainGuards.domainCheck_iff _ _).mp (by decide)) ==
      nodeView (some (.leaf (key []) (.bytes (bytes [0, 255]))))),
  ("empty-valued ending plus child", concrete ending 0 (PatricializeDomain.zero _) ==
    nodeView (some (.branch (Vector.ofFn fun digit ↦
      if digit = 0 then .list [.bytes (bytes [32]), .bytes ByteArray.empty]
      else .bytes ByteArray.empty) (.bytes ByteArray.empty)))),
  ("odd positive prefix and ending", concrete prefixed 0 (PatricializeDomain.zero _) ==
    nodeView (some (.extension (key [1, 2, 3]) (.list
      ((Vector.ofFn fun digit : Fin 16 ↦ if digit = 4 then
        RlpItem.list [.bytes (bytes [32]), .bytes (bytes [9])] else
          RlpItem.bytes ByteArray.empty).toList ++ [RlpItem.bytes ByteArray.empty]))))),
  ("actual C6 leaf31/32/33 full values and ordered arbitrary answers",
    recorded thresholds 0 (PatricializeDomain.zero _) == thresholdExpected),
  ("extension child encoded once and no parent hash",
    recorded nested 0 (PatricializeDomain.zero _) == nestedExpected),
  ("all ten first errors in ordered branch", (List.range 10).all fun index ↦
    failed thresholds 0 (PatricializeDomain.zero _) index == errorExpected thresholdExpected index),
  ("all eleven first errors through extension", (List.range 11).all fun index ↦
    failed nested 0 (PatricializeDomain.zero _) index == errorExpected nestedExpected index),
  ("every member selector across recursive maps", (List.range 16).all fun index ↦
    alternate nested 0 index (PatricializeDomain.zero _) == concrete nested 0 (PatricializeDomain.zero _)),
  ("wrong depth demonstrates domain premise", !RootDomainGuards.domainCheck singleton 4),
  ("inconsistent consumed prefix demonstrates domain premise",
    !RootDomainGuards.domainCheck RootBranchGuards.allDigits 1)]

#guard cases.all Prod.snd

/-- Native output prints actual complete values and full trace, then each finite guard. -/
def printComplete : IO UInt32 := do
  IO.println s!"threshold actual={reprStr (recorded thresholds 0 (PatricializeDomain.zero _))}; expected={reprStr thresholdExpected}"
  IO.println s!"nested actual={reprStr (recorded nested 0 (PatricializeDomain.zero _))}; expected={reprStr nestedExpected}"
  let mut failures := 0
  for (name, result) in cases do
    IO.println s!"construction {name}: {result}"
    if !result then failures := failures + 1
  return failures

end STFSpec.Conformance.Commit.RootConstructionGuards
