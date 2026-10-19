/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Public-only chronological-log clients

Library `EthConformance`. Private symbolic clients consume all six public laws and
existing Base observers. Conditional selection is List-model algebra, not an EVM
child incorporation or gas/state/receipt implementation.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/7.
-/

namespace STFSpec.Conformance.Vm.Core.LogsCallerProofs
open STFSpec.Vm.Core STFSpec.Base

private def view (entry : Log) : List UInt8 × List (List UInt8) × List UInt8 :=
  (entry.address.toBytes.toList,
    entry.topics.toList.map (fun topic ↦ topic.toBytes.toList), entry.data.toList)

private theorem topic_lists_inj (xs ys : List Hash32)
    (h : xs.map (fun x ↦ x.toBytes.toList) = ys.map (fun x ↦ x.toBytes.toList)) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => cases h
  | cons x xs ih =>
    cases ys with
    | nil => cases h
    | cons y ys =>
      have parts := List.cons.inj h
      have same : x = y := Hash32.toBytes_inj.mp (Bytes.toList_inj.mp parts.1)
      rw [same, ih ys parts.2]

private theorem view_injective (a b : Log) (h : view a = view b) : a = b := by
  unfold view at h
  obtain ⟨ha, rest⟩ := Prod.mk.inj h
  obtain ⟨ht, hd⟩ := Prod.mk.inj rest
  exact Log.ext a b (Address.toBytes_inj.mp (Bytes.toList_inj.mp ha))
    (Array.toList_inj.mp (topic_lists_inj _ _ ht)) (Bytes.toList_inj.mp hd)

private theorem reconstruct (entry : Log) :
    Log.mk entry.address entry.topics entry.data = entry := Log.eta entry

private theorem full_field_congruence (a b : Log)
    (ha : a.address = b.address) (ht : a.topics = b.topics) (hd : a.data = b.data) :
    a = b := Log.ext a b ha ht hd

private theorem empty_model : LogRope.toList .empty = [] := LogRope.toList_empty

private theorem complete_leaf (entries : List Log) :
    LogRope.toList (.leaf entries) = entries := LogRope.toList_leaf entries

private theorem append_empty_left (r : LogRope) :
    (LogRope.append .empty r).toList = r.toList := by
  rw [LogRope.toList_append, LogRope.toList_empty, List.nil_append]

private theorem append_empty_right (r : LogRope) :
    (LogRope.append r .empty).toList = r.toList := by
  rw [LogRope.toList_append, LogRope.toList_empty, List.append_nil]

private theorem append_associative_model (a b c : LogRope) :
    (LogRope.append (LogRope.append a b) c).toList =
      (LogRope.append a (LogRope.append b c)).toList := by
  simp only [LogRope.toList_append, List.append_assoc]

private theorem concat_associative_model (a b c : LogRope) :
    (LogRope.concat (LogRope.concat a b) c).toList =
      (LogRope.concat a (LogRope.concat b c)).toList := by
  simp only [LogRope.toList_concat, List.append_assoc]

private theorem duplicate_occurrences (r : LogRope) :
    (LogRope.concat r r).toList = r.toList ++ r.toList := LogRope.toList_concat r r

private theorem singleton_emission (r : LogRope) (entry : Log) :
    (LogRope.append r (.leaf [entry])).toList = r.toList ++ [entry] := by
  rw [LogRope.toList_append, LogRope.toList_leaf]

private theorem append_length (a b : LogRope) :
    (LogRope.append a b).toList.length = a.toList.length + b.toList.length := by
  rw [LogRope.toList_append, List.length_append]

private theorem model_congruence (a b c d : LogRope)
    (hab : a.toList = b.toList) (hcd : c.toList = d.toList) :
    (LogRope.append a c).toList = (LogRope.append b d).toList := by
  rw [LogRope.toList_append, LogRope.toList_append, hab, hcd]

private theorem retained_inputs (p q : LogRope) :
    let savedP := p.toList
    let savedQ := q.toList
    (LogRope.append p q).toList = savedP ++ savedQ ∧
      p.toList = savedP ∧ q.toList = savedQ := by
  exact ⟨LogRope.toList_append p q, rfl, rfl⟩

private def select (success : Bool) (parent child : LogRope) : LogRope :=
  if success then LogRope.append parent child else parent

private theorem selection_suffix (success : Bool) (p c : LogRope) (suffix : List Log) :
    (LogRope.append (select success p c) (.leaf suffix)).toList =
      p.toList ++ (if success then c.toList else []) ++ suffix := by
  cases success <;>
    simp [select, LogRope.toList_append, LogRope.toList_leaf, List.append_assoc]

private theorem inner_success (c grandchild : LogRope) :
    (select true c grandchild).toList = c.toList ++ grandchild.toList := by
  exact LogRope.toList_append c grandchild

private theorem outer_discard (p c grandchild : LogRope) :
    (select false p (select true c grandchild)).toList = p.toList := rfl

private theorem failed_output_preserves_stored (stored : LogRope) :
    (if false then stored.toList else []) = ([] : List Log) ∧
      stored.toList = stored.toList := ⟨rfl, rfl⟩

private theorem equal_models_do_not_hide_shapes :
    (LogRope.concat .empty .empty).toList = LogRope.empty.toList ∧
      LogRope.concat .empty .empty ≠ LogRope.empty := by
  constructor
  · rw [LogRope.toList_concat, LogRope.toList_empty, List.nil_append]
  · intro impossible
    cases impossible

end STFSpec.Conformance.Vm.Core.LogsCallerProofs
