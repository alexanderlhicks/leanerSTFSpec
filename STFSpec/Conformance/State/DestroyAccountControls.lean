/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Transaction account destruction controls

Library `EthConformance`. The clients check the State facade and its complete
transaction result. See `STFSpec/informal/modules/EthState.md` §§4/7.5.
-/

namespace STFSpec.Conformance.State.DestroyAccountControls

open STFSpec.Base STFSpec.State

private theorem run_ordered {m : Type → Type} [Monad m] (t : TxState m) (a : Address) :
    ((destroyAccount a).run t).run = (do
      match ← ((destroyStorage a).run t).run with
      | .error e => pure (.error e)
      | .ok cleared => ((setAccount a none).run cleared.2).run) := by
  change (((destroyStorage a).run t).run >>=
    ExceptT.bindCont (fun pair : Unit × TxState m ↦
      match pair with | (_, cleared) => (setAccount a none).run cleared)) = _
  congr 1
  funext result
  cases result with
  | error => rfl
  | ok value => cases value; rfl

private def clearedReads (t : TxState Id) (a : Address) :
    Std.HashSet (Address × Bytes32) :=
  match t.rev.storageWrites[a]? with
  | none => t.obs.storageReads
  | some patch => patch.foldl (fun reads key _ ↦ reads.insert (a, key)) t.obs.storageReads

private def destroyed (t : TxState Id) (a : Address) : TxState Id :=
  { t with
    rev := { t.rev with
      accountWrites := t.rev.accountWrites.insert a none
      accountOrder := t.rev.accountOrder.record a
      storageWrites := t.rev.storageWrites.erase a
      storageAddressOrder := t.rev.storageAddressOrder.erase a
      storageSlotOrder := t.rev.storageSlotOrder.erase a
      storageClears := t.rev.storageClears.insert a }
    obs.storageReads := clearedReads t a }

private theorem id_result (t : TxState Id) (a : Address) :
    ((destroyAccount a).run t).run = .ok ((), destroyed t a) := rfl

private theorem target_entries (t : TxState Id) (a : Address) :
    (destroyed t a).rev.accountWrites[a]? = some none ∧
      (destroyed t a).rev.storageWrites[a]? = none ∧
      (destroyed t a).rev.storageSlotOrder[a]? = none ∧ a ∈ (destroyed t a).rev.storageClears := by
  simp [destroyed]

private theorem slot_reads (t : TxState Id) (a b : Address) (k : Bytes32) :
    (b, k) ∈ (destroyed t a).obs.storageReads ↔
      (b, k) ∈ t.obs.storageReads ∨ b = a ∧
        (∃ patch, t.rev.storageWrites[a]? = some patch ∧ k ∈ patch) := by
  cases pending : t.rev.storageWrites[a]? with
  | none => simp [destroyed, clearedReads, pending]
  | some patch =>
    have foldKeys (keys : List Bytes32) (reads : Std.HashSet (Address × Bytes32)) :
        (b, k) ∈ keys.foldl (fun seen key ↦ seen.insert (a, key)) reads ↔
          (b, k) ∈ reads ∨ b = a ∧ k ∈ keys := by
      induction keys generalizing reads with
      | nil => simp
      | cons key rest ih =>
        rw [List.foldl_cons, ih, Std.HashSet.mem_insert]
        simp only [beq_iff_eq, Prod.mk.injEq, List.mem_cons]
        grind
    change (b, k) ∈ clearedReads t a ↔ _
    simp only [clearedReads, pending]
    rw [Std.ExtTreeMap.foldl_eq_foldl_keys, foldKeys]
    simp

private theorem retained_fields (t : TxState Id) (a : Address) :
    (destroyed t a).block = t.block ∧
      (destroyed t a).obs.accountReads = t.obs.accountReads ∧
      (destroyed t a).obs.codeReads = t.obs.codeReads ∧
      (destroyed t a).obs.createdAccounts = t.obs.createdAccounts ∧
      (destroyed t a).rev.codeWrites = t.rev.codeWrites ∧
      (destroyed t a).rev.transient = t.rev.transient :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem order_invariants (t : TxState Id) (a : Address)
    (accountsWF : t.rev.accountOrder.WF) (accountsAgree : t.rev.accountOrder.Agrees t.rev.accountWrites)
    (storageWF : t.rev.storageAddressOrder.WF)
    (storageAgree : t.rev.storageAddressOrder.Agrees t.rev.storageWrites) :
    let r := (destroyed t a).rev
    r.accountOrder.WF ∧ r.accountOrder.Agrees r.accountWrites ∧
      r.storageAddressOrder.WF ∧ r.storageAddressOrder.Agrees r.storageWrites :=
  ⟨t.rev.accountOrder.wf_record a accountsWF,
    t.rev.accountOrder.agrees_record_insert t.rev.accountWrites a none accountsAgree,
    t.rev.storageAddressOrder.wf_erase a storageWF,
    t.rev.storageAddressOrder.agrees_erase_erase t.rev.storageWrites a storageAgree⟩

private theorem restore_keeps_observations (t : TxState Id) (a : Address) :
    (((do destroyAccount a; restoreTxState (copyTxState t)) : StateM Id Unit).run t).run =
      .ok ((), { t with obs.storageReads := clearedReads t a }) := rfl

private structure Trace (α : Type) where
  value : α
  events : List Nat

private instance : Monad Trace where
  pure value := ⟨value, [17]⟩
  bind x f :=
    let y := f x.value
    ⟨y.value, x.events ++ [29] ++ y.events⟩

private theorem trace_steps (t : TxState Trace) (a : Address) :
    (((destroyAccount a).run t).run).events = [17, 29, 17] := rfl

private def target := Address.ofNat 17
private def other := Address.ofNat 19
private def first : Bytes32 := FixedBytes.ofNat 23
private def second : Bytes32 := FixedBytes.ofNat 29
private def emptyHash := Hash32.ofBytes32 (FixedBytes.ofNat 31)
private def account : Account := ⟨37, U256.ofNat 41, emptyHash⟩

private def provider : PreState Id :=
  ⟨fun _ ↦ .error (.missing (.code emptyHash)), fun _ _ ↦ .error (.missing (.code emptyHash)),
    fun _ ↦ .error (.missing (.code emptyHash)), fun _ ↦ .error (.missing (.code emptyHash))⟩

private abbrev SlotMap := Std.ExtTreeMap Bytes32 U256

private def entry (patch : Option SlotMap) (prior : Option (Option Account)) : TxState Id :=
  let block := BlockState.new provider ⟨emptyHash, emptyHash, emptyHash, emptyHash⟩
  let t := TxState.new block
  { t with
    rev := { t.rev with
      accountWrites := prior.elim (t.rev.accountWrites.insert other (some account))
        (fun value ↦ (t.rev.accountWrites.insert other (some account)).insert target value)
      accountOrder := prior.elim (t.rev.accountOrder.record other)
        (fun _ ↦ (t.rev.accountOrder.record other).record target)
      storageWrites := patch.elim (t.rev.storageWrites.insert other (∅ : SlotMap))
        (fun values ↦ (t.rev.storageWrites.insert other (∅ : SlotMap)).insert target values)
      storageAddressOrder := patch.elim (t.rev.storageAddressOrder.record other)
        (fun _ ↦ (t.rev.storageAddressOrder.record other).record target)
      storageSlotOrder := patch.elim t.rev.storageSlotOrder (fun values ↦
        t.rev.storageSlotOrder.insert target (values.toList.foldl
          (fun order pair ↦ order.record pair.1) WriteOrder.empty))
      transient := t.rev.transient.insert (target, second) (U256.ofNat 43) }
    obs := { t.obs with
      accountReads := t.obs.accountReads.insert other
      storageReads := t.obs.storageReads.insert (other, first)
      codeReads := t.obs.codeReads.insert emptyHash
      createdAccounts := t.obs.createdAccounts.insert other } }

private def control (patch : Option SlotMap) (prior : Option (Option Account)) : Bool :=
  let before := entry patch prior
  let run := fun t ↦ ((destroyAccount target).run t).run
  let restored := fun t ↦ ((restoreTxState (copyTxState before)).run t).run
  match run before with
  | .error _ => false
  | .ok (_, next) =>
    let repeated := run next
    let snapshot := restored next
    (next.rev.accountWrites[target]?.map (·.isNone) == some true) &&
      next.rev.accountOrder.toList.map Address.toNat == [19, 17] &&
      next.rev.storageWrites[target]?.isNone && next.rev.storageSlotOrder[target]?.isNone &&
      next.rev.storageAddressOrder.toList.map Address.toNat == [19] &&
      next.rev.storageClears.contains target && next.obs.storageReads.contains (other, first) &&
      next.obs.storageReads.contains (target, first) == (patch.any (·.contains first)) &&
      next.obs.storageReads.contains (target, second) == (patch.any (·.contains second)) &&
      (next.rev.transient[(target, second)]?.map U256.toNat == some 43) &&
      repeated.toOption.any (fun (_, twice) ↦
        twice.rev.accountOrder.next == next.rev.accountOrder.next &&
        twice.obs.storageReads.size == next.obs.storageReads.size) &&
      snapshot.toOption.any (fun (_, rolled) ↦
        rolled.rev.accountOrder.toList.map Address.toNat == before.rev.accountOrder.toList.map Address.toNat &&
        rolled.rev.storageWrites[target]?.isSome == patch.isSome &&
        rolled.obs.storageReads.size == next.obs.storageReads.size)

private def explicit : SlotMap :=
  (∅ : SlotMap).insert first (U256.ofNat 0) |>.insert second (U256.ofNat 47)

#guard control none none
#guard control (some ∅) none
#guard control (some explicit) (some (some account))
#guard control (some explicit) (some none)

end STFSpec.Conformance.State.DestroyAccountControls
