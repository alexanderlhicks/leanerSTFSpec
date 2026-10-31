/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Shared precompile carrier clients and logical controls

Library `EthConformance`. Private clients use the public Core facade, raw record
reduction, Base observations, Std set laws and the existing exact Id law. The
generic empty and arbitrary-address Id singleton examples are local inhabitants,
not an installed Ethereum table or a generic constructor for actual precompiles.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/5/7.
-/

namespace STFSpec.Conformance.Vm.Core.PrecompileCallerProofs
open STFSpec.Vm.Core STFSpec.Base

private def okSignature : GasMeter → Bytes → PrecompileResult := PrecompileResult.ok
private def haltSignature : ExceptionalHalt → PrecompileResult := PrecompileResult.halt
private def functionSignature (m : Type → Type) :
    (Bytes → GasMeter → m PrecompileResult) → PrecompileFn m := fun p ↦ p

private theorem success_payload (g : GasMeter) (output : Bytes) :
    (match PrecompileResult.ok g output with
      | .ok g' output' => some (g', output')
      | .halt _ => none) = some (g, output) := rfl

private theorem halt_payload (e : ExceptionalHalt) :
    (match PrecompileResult.halt e with
      | .ok _ _ => none
      | .halt e' => some e') = some e := rfl

private theorem success_definition (g g' : GasMeter) (output : Bytes) :
    MeterOk g (.ok g' output) ↔
      g'.gasLeft ≤ g.gasLeft ∧ { g' with gasLeft := g.gasLeft } = g := Iff.rfl

private theorem success_fields (g g' : GasMeter) (output : Bytes)
    (h : MeterOk g (.ok g' output)) :
    g'.gasLeft ≤ g.gasLeft ∧ g'.stateGasLeft = g.stateGasLeft ∧
      g'.stateGasBaseline = g.stateGasBaseline ∧ g'.refundCounter = g.refundCounter ∧
      g'.stateGasSpilled = g.stateGasSpilled ∧
      g'.stateGasCommittedSpill = g.stateGasCommittedSpill := by
  have hState := congrArg GasMeter.stateGasLeft h.2
  have hBaseline := congrArg GasMeter.stateGasBaseline h.2
  have hRefund := congrArg GasMeter.refundCounter h.2
  have hSpill := congrArg GasMeter.stateGasSpilled h.2
  have hCommitted := congrArg GasMeter.stateGasCommittedSpill h.2
  exact ⟨h.1, hState, hBaseline, hRefund, hSpill, hCommitted⟩

private theorem arbitrary_output (g : GasMeter) (cost : Nat) (output : Bytes) :
    MeterOk g (.ok { g with gasLeft := g.gasLeft - cost } output) :=
  ⟨Nat.sub_le _ _, rfl⟩

private theorem unchanged_meter (g : GasMeter) (output : Bytes) :
    MeterOk g (.ok g output) := ⟨Nat.le_refl _, rfl⟩

private theorem unconstrained_halt (g : GasMeter) (e : ExceptionalHalt) :
    MeterOk g (.halt e) ↔ True := Iff.rfl

private theorem gas_increase_rejected (g : GasMeter) (output : Bytes) :
    ¬ MeterOk g (.ok { g with gasLeft := g.gasLeft + 1 } output) := by
  intro h
  have hle := h.1
  change g.gasLeft + 1 ≤ g.gasLeft at hle
  omega

private theorem supplied_table {m : Type → Type} [Monad m]
    (lookup : Address → Option (PrecompileFn m)) (addresses : AddrSet)
    (lookup_iff : ∀ a, (lookup a).isSome ↔ a ∈ addresses)
    (meter_law : ∀ a p i g, lookup a = some p → SatisfiesM (MeterOk g) (p i g)) :
    let t := PrecompileTable.mk lookup addresses lookup_iff meter_law
    t.lookup = lookup ∧ t.addresses = addresses ∧
      t.lookup_iff = lookup_iff ∧ t.meter_law = meter_law := ⟨rfl, rfl, rfl, rfl⟩

private theorem reconstruct {m : Type → Type} [Monad m] (t : PrecompileTable m) :
    PrecompileTable.mk t.lookup t.addresses t.lookup_iff t.meter_law = t := rfl

private theorem supplied_lookup_domain {m : Type → Type} [Monad m]
    (t : PrecompileTable m) (a : Address) :
    (t.lookup a).isSome ↔ a ∈ t.addresses := t.lookup_iff a

private theorem supplied_factorization {m : Type → Type} [Monad m]
    (t : PrecompileTable m) (a : Address) (p : PrecompileFn m) (i : Bytes) (g : GasMeter)
    (h : t.lookup a = some p) :
    ∃ y : m {r : PrecompileResult // MeterOk g r}, Subtype.val <$> y = p i g :=
  t.meter_law a p i g h

private theorem id_success {t : PrecompileTable Id} {a : Address} {p : PrecompileFn Id}
    (i : Bytes) (g g' : GasMeter) (output : Bytes)
    (hLookup : t.lookup a = some p) (hResult : p i g = .ok g' output) :
    g'.gasLeft ≤ g.gasLeft ∧ { g' with gasLeft := g.gasLeft } = g := by
  have h := (satisfiesM_id_iff _ _).mp (t.meter_law a p i g hLookup)
  rw [hResult] at h
  exact h

private def emptyTable (m : Type → Type) [Monad m] : PrecompileTable m where
  lookup _ := none
  addresses := ∅
  lookup_iff _ := by simp only [Option.isSome_none, Bool.false_eq_true,
    Std.ExtTreeSet.not_mem_empty]
  meter_law _ _ _ _ h := by contradiction

private def echo : PrecompileFn Id := fun i g ↦ .ok g i

private def singleton (a : Address) : PrecompileTable Id where
  lookup b := if b = a then some echo else none
  addresses := (∅ : AddrSet).insert a
  lookup_iff b := by
    simp only [Std.ExtTreeSet.mem_insert, Std.ExtTreeSet.not_mem_empty, or_false,
      Std.LawfulEqOrd.compare_eq_iff_eq]
    by_cases h : b = a
    · simp only [h, ↓reduceIte, Option.isSome_some]
    · simp only [h, ↓reduceIte, Option.isSome_none, Bool.false_eq_true, Ne.symm h]
  meter_law b p i g h := by
    split at h
    · cases h
      exact (satisfiesM_id_iff _ _).mpr (unchanged_meter g i)
    · contradiction

private theorem singleton_result (a : Address) (i : Bytes) (g : GasMeter) :
    (singleton a).lookup a = some echo ∧ echo i g = .ok g i := by
  exact ⟨by simp only [singleton, ↓reduceIte], rfl⟩

-- Deliberately unrestricted raw meter: negative refund and reservoir above baseline.
private def meter : GasMeter := ⟨13, 101, 2, -17, 5, 11⟩
private def bytes : Bytes := Bytes.ofList [0, 255, 128, 0, 1]

private theorem every_nonexecution_change_rejected :
    ¬ MeterOk meter (.ok { meter with stateGasLeft := 102 } bytes) ∧
    ¬ MeterOk meter (.ok { meter with stateGasBaseline := 3 } bytes) ∧
    ¬ MeterOk meter (.ok { meter with refundCounter := 17 } bytes) ∧
    ¬ MeterOk meter (.ok { meter with stateGasSpilled := 6 } bytes) ∧
    ¬ MeterOk meter (.ok { meter with stateGasCommittedSpill := 12 } bytes) := by
  simp only [MeterOk, meter, GasMeter.mk.injEq]
  decide

private theorem zero_execution_accepted :
    MeterOk meter (.ok ⟨0, 101, 2, -17, 5, 11⟩ bytes) := by
  exact ⟨by decide, rfl⟩

private theorem nominal_halts_preserved (reason : String) (opcode : UInt8) :
    MeterOk meter (.halt (.precompileHalt reason)) ∧
      MeterOk meter (.halt (.invalidOpcode opcode)) := ⟨True.intro, True.intro⟩

#guard bytes.toList == [0, 255, 128, 0, 1]
#guard ((singleton (Address.ofNat 256)).addresses.toList.map Address.toNat) == [256]
#guard ((singleton (Address.ofNat 256)).lookup (Address.ofNat 1)).isSome == false
#guard ((singleton (Address.ofNat 256)).lookup (Address.ofNat 256)).isSome == true

end STFSpec.Conformance.Vm.Core.PrecompileCallerProofs
