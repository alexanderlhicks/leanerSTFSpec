/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.FixedBytes
import Std

/-!
# Chronological logs and immutable log ropes

Library `EthVmCore`. Raw logs retain every ordered topic and payload byte. Public
rope constructors expose raw shapes; the List observation gives chronological
semantics. A private ordinary refinement connects the explicit work-stack traversal
to the legible recursive reference. Append allocates one concat node.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/6/7.
-/

namespace STFSpec.Vm.Core
open STFSpec.Base

/-- Complete raw log value, EELS `src/ethereum/forks/amsterdam/blocks.py:327–356`.
Topic-count restrictions belong to producers, not this all-finite data carrier. -/
structure Log where
  /-- Emitter's complete nominal address. -/
  address : Address
  /-- Complete ordered topics, retaining arbitrary lengths and duplicates. -/
  topics : Array Hash32
  /-- Complete immutable data bytes. -/
  data : Bytes

/-- Equality of all three complete stored fields determines a Log. -/
theorem Log.ext (a b : Log)
    (h_address : a.address = b.address)
    (h_topics : a.topics = b.topics)
    (h_data : a.data = b.data) : a = b := by
  cases a
  cases b
  congr 1 <;> assumption

/-- Reconstruct every field in source order, without a topic-count premise. -/
theorem Log.eta (l : Log) : Log.mk l.address l.topics l.data = l := by
  cases l
  rfl

/-- Strict immutable rope. All finite raw empty/leaf/concat shapes are public.
Its List model represents EELS's ordered log tuples at
`src/ethereum/forks/amsterdam/vm/__init__.py:169,247`. -/
inductive LogRope where
  /-- No log occurrences. -/
  | empty
  /-- A complete ordered leaf, including an empty list. -/
  | leaf (logs : List Log)
  /-- The left child's occurrences precede the right child's occurrences. -/
  | concat (left right : LogRope)

namespace LogRope

private def reference : LogRope → List Log
  | .empty => []
  | .leaf logs => logs
  | .concat left right => reference left ++ reference right

-- Expanded occurrences, including repeated shared subtrees; proof support only.
private def nodeCount : LogRope → Nat
  | .empty => 1
  | .leaf _ => 1
  | .concat left right => 1 + nodeCount left + nodeCount right

private def pendingWeight : List LogRope → Nat
  | [] => 0
  | tree :: rest => nodeCount tree + pendingWeight rest

private def pendingModel : List LogRope → List Log
  | [] => []
  | tree :: rest => reference tree ++ pendingModel rest

private def scan (pending : List LogRope) (acc : List Log) : List Log :=
  match pending with
  | [] => acc.reverse
  | .empty :: rest => scan rest acc
  | .leaf logs :: rest => scan rest (logs.foldl (fun out entry ↦ entry :: out) acc)
  | .concat left right :: rest => scan (left :: right :: rest) acc
termination_by pendingWeight pending
decreasing_by
  all_goals simp_all only [pendingWeight, nodeCount]
  all_goals omega

private theorem scan_refines (pending : List LogRope) (acc : List Log) :
    scan pending acc = acc.reverse ++ pendingModel pending := by
  cases pending with
  | nil => simp only [scan, pendingModel, List.append_nil]
  | cons tree rest =>
    cases tree with
    | empty =>
      rw [scan, scan_refines rest acc]
      simp only [pendingModel, reference, List.nil_append]
    | leaf logs =>
      rw [scan, scan_refines rest (logs.foldl (fun out entry ↦ entry :: out) acc)]
      simp only [List.foldl_flip_cons_eq_append', List.reverse_append, List.reverse_reverse,
        pendingModel, reference, List.append_assoc]
    | concat left right =>
      rw [scan, scan_refines (left :: right :: rest) acc]
      simp only [pendingModel, reference, List.append_assoc]
termination_by pendingWeight pending
decreasing_by
  all_goals simp_all only [pendingWeight, nodeCount]
  all_goals omega

/-- Flatten every finite raw rope in chronological order using an explicit
left-first work stack and one reversed output accumulator; no prefix copying.
This is the List model of the ordered tuples in pinned EELS
`src/ethereum/forks/amsterdam/vm/__init__.py:169,247`;
actual frame/receipt integration and compiled resource obligations are separate. -/
def toList (tree : LogRope) : List Log := scan [tree] []

private theorem toList_eq_reference (tree : LogRope) : toList tree = reference tree := by
  simp only [toList, scan_refines, List.reverse_nil, pendingModel, List.nil_append,
    List.append_nil]

/-- Constant-time chronological concatenation; EELS tuple concatenation's model
at `src/ethereum/forks/amsterdam/vm/__init__.py:247`. No structural law is exported. -/
def append (left right : LogRope) : LogRope := .concat left right

/-- Empty rope observes exactly the empty chronological list. -/
theorem toList_empty : LogRope.toList .empty = [] := by
  simp only [toList_eq_reference, reference]

/-- Every entry in a raw leaf is retained, including duplicates and full payloads. -/
theorem toList_leaf (ls : List Log) : LogRope.toList (.leaf ls) = ls := by
  simp only [toList_eq_reference, reference]

/-- All left occurrences precede all right occurrences, including shared subtrees. -/
theorem toList_concat (left right : LogRope) :
    LogRope.toList (.concat left right) = LogRope.toList left ++ LogRope.toList right := by
  simp only [toList_eq_reference, reference]

/-- Append's complete chronological observation, without a structural-tree claim. -/
theorem toList_append (left right : LogRope) :
    LogRope.toList (LogRope.append left right) =
      LogRope.toList left ++ LogRope.toList right := by
  exact toList_concat left right

end LogRope
end STFSpec.Vm.Core
