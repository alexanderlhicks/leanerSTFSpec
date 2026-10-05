/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.WriteOrder
import STFSpec.Base.FixedBytes

/-!
# WriteOrder component tests

Library `EthConformance`: public-law clients and complete finite observations of
internal State support. Nested containers are test models of paired saved roots.
Spec guidance: `STFSpec/informal/modules/EthState.md`.
-/

namespace STFSpec.Conformance.State.WriteOrderCallerProofs

open STFSpec.State STFSpec.State.WriteOrder

private theorem symbolic_raw_empty {K : Type} [Ord K] [Std.TransOrd K] :
    toList (empty : WriteOrder K) = [] ∧ WF (empty : WriteOrder K) :=
  ⟨toList_empty, wf_empty⟩
private theorem symbolic_raw_noops {K : Type} [Ord K] [Std.TransOrd K]
    (r : WriteOrder K) (k : K) (p : Nat) :
    (r.positions[k]? = some p → record r k = r) ∧
    (r.positions[k]? = none → erase r k = r) :=
  ⟨record_of_present r k p, erase_of_absent r k⟩
private theorem symbolic_raw_counters {K : Type} [Ord K] [Std.TransOrd K]
    (r : WriteOrder K) (k : K) :
    (record r k).next = (if r.positions[k]?.isSome then r.next else r.next + 1) ∧
    (erase r k).next = r.next := ⟨next_record r k, next_erase r k⟩
private theorem symbolic_all_lawful {K V : Type} [Ord K] [Std.TransOrd K]
    [Std.LawfulEqOrd K] (r : WriteOrder K) (writes : Std.ExtTreeMap K V)
    (k : K) (v : V) (hw : WF r) (ha : Agrees r writes) :
    WF (record r k) ∧ WF (erase r k) ∧
    (k ∈ toList r ↔ r.positions[k]?.isSome = true) ∧ (toList r).Nodup ∧
    (toList (record r k) =
      if r.positions[k]?.isSome then toList r else toList r ++ [k]) ∧
    (toList (erase r k) = (toList r).filter (fun a => compare k a != .eq)) ∧
    Agrees (record r k) (writes.insert k v) ∧
    Agrees (erase r k) (writes.erase k) :=
  ⟨wf_record r k hw, wf_erase r k hw, mem_toList_iff r k hw,
    toList_nodup r hw, toList_record r k hw, toList_erase r k hw,
    agrees_record_insert r writes k v ha, agrees_erase_erase r writes k ha⟩
private theorem symbolic_both_inverse {K : Type} [Ord K] [Std.TransOrd K]
    (r : WriteOrder K) (hw : WF r) (k : K) (p : Nat) :
    (r.positions[k]? = some p → r.keysByPosition[p]? = some k) ∧
    (r.keysByPosition[p]? = some k → r.positions[k]? = some p) :=
  ⟨(hw.1 k p).mp, (hw.1 k p).mpr⟩
private theorem symbolic_record_domain_no_WF {K V : Type} [Ord K] [Std.TransOrd K]
    [Std.LawfulEqOrd K] (r : WriteOrder K) (w : Std.ExtTreeMap K V)
    (k : K) (v : V) (h : Agrees r w) : Agrees (record r k) (w.insert k v) :=
  agrees_record_insert r w k v h
private theorem symbolic_erase_domain_no_WF {K V : Type} [Ord K] [Std.TransOrd K]
    [Std.LawfulEqOrd K] (r : WriteOrder K) (w : Std.ExtTreeMap K V)
    (k : K) (h : Agrees r w) : Agrees (erase r k) (w.erase k) :=
  agrees_erase_erase r w k h
private theorem symbolic_address (r : WriteOrder STFSpec.Base.Address)
    (k : STFSpec.Base.Address) (h : WF r) : WF (record r k) := wf_record r k h
private theorem symbolic_slot (r : WriteOrder STFSpec.Base.Bytes32)
    (k : STFSpec.Base.Bytes32) (h : WF r) : WF (erase r k) := wf_erase r k h

example {K : Type} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
    (r : WriteOrder K) (k a : K) (h : WF r) (p : Nat)
    (hp : (record r k).positions[a]? = some p) :
    (record r k).keysByPosition[p]? = some a :=
  ((wf_record r k h).1 a p).mp hp

example (a : STFSpec.Base.Address) :
    STFSpec.Base.Address.ofBytes? a.toBytes = some a :=
  STFSpec.Base.Address.ofBytes?_toBytes a

example (k : STFSpec.Base.Bytes32) :
    STFSpec.Base.FixedBytes.ofBytes? k.toBytes = some k :=
  STFSpec.Base.FixedBytes.ofBytes?_toBytes k

end STFSpec.Conformance.State.WriteOrderCallerProofs
