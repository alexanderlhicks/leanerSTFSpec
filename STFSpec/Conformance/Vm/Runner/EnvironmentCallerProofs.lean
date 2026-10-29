/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Runner

/-!
# Public runner-environment clients

Library `EthConformance`. Private clients use only the Runner facade and public
Core, Base and Std contracts. Complete supplied records and actual proof fields
are retained. The local singleton is an Id inhabitant, not an installed table.
Spec guidance: `STFSpec/informal/modules/EthVmRunner.md` §§3/4/5/7.
-/

namespace STFSpec.Conformance.Vm.Runner.EnvironmentCallerProofs
open STFSpec.Base STFSpec.Vm.Core STFSpec.Vm.Runner

private def typeSignature (m : Type → Type) [Monad m] : Type := RunnerEnv m
private def constructorSignature {m : Type → Type} [Monad m] :
    PrecompileTable m → VmConfig → Address → RunnerEnv m := RunnerEnv.mk
private def tableSignature {m : Type → Type} [Monad m] :
    RunnerEnv m → PrecompileTable m := RunnerEnv.precompiles
private def configSignature {m : Type → Type} [Monad m] :
    RunnerEnv m → VmConfig := RunnerEnv.vm
private def addressSignature {m : Type → Type} [Monad m] :
    RunnerEnv m → Address := RunnerEnv.systemAddress

private theorem complete_construction {m : Type → Type} [Monad m]
    (table : PrecompileTable m) (cfg : VmConfig) (address : Address) :
    let env := RunnerEnv.mk table cfg address
    env.precompiles = table ∧ env.vm = cfg ∧ env.systemAddress = address :=
  ⟨rfl, rfl, rfl⟩

private theorem reconstruction {m : Type → Type} [Monad m] (env : RunnerEnv m) :
    RunnerEnv.mk env.precompiles env.vm env.systemAddress = env := rfl

private theorem update_table {m : Type → Type} [Monad m]
    (env : RunnerEnv m) (table : PrecompileTable m) :
    let changed := { env with precompiles := table }
    changed.precompiles = table ∧ changed.vm = env.vm ∧
      changed.systemAddress = env.systemAddress := ⟨rfl, rfl, rfl⟩

private theorem update_config {m : Type → Type} [Monad m]
    (env : RunnerEnv m) (cfg : VmConfig) :
    let changed := { env with vm := cfg }
    changed.precompiles = env.precompiles ∧ changed.vm = cfg ∧
      changed.systemAddress = env.systemAddress := ⟨rfl, rfl, rfl⟩

private theorem update_address {m : Type → Type} [Monad m]
    (env : RunnerEnv m) (address : Address) :
    let changed := { env with systemAddress := address }
    changed.precompiles = env.precompiles ∧ changed.vm = env.vm ∧
      changed.systemAddress = address := ⟨rfl, rfl, rfl⟩

private theorem supplied_certificates {m : Type → Type} [Monad m]
    (lookup : Address → Option (PrecompileFn m)) (addresses : AddrSet)
    (domain : ∀ a, (lookup a).isSome ↔ a ∈ addresses)
    (certified : ∀ a p i g, lookup a = some p → SatisfiesM (MeterOk g) (p i g))
    (cfg : VmConfig) (address : Address) :
    let env := RunnerEnv.mk (PrecompileTable.mk lookup addresses domain certified) cfg address
    env.precompiles = PrecompileTable.mk lookup addresses domain certified ∧
      env.precompiles.lookup = lookup ∧ env.precompiles.addresses = addresses ∧
      env.precompiles.lookup_iff = domain ∧ env.precompiles.meter_law = certified ∧
      env.vm = cfg ∧ env.systemAddress = address := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem stored_domain {m : Type → Type} [Monad m]
    (env : RunnerEnv m) (a : Address) :
    (env.precompiles.lookup a).isSome ↔ a ∈ env.precompiles.addresses :=
  env.precompiles.lookup_iff a

private theorem stored_factorization {m : Type → Type} [Monad m]
    (env : RunnerEnv m) (a : Address) (p : PrecompileFn m) (i : Bytes) (g : GasMeter)
    (h : env.precompiles.lookup a = some p) :
    ∃ y : m {r : PrecompileResult // MeterOk g r}, Subtype.val <$> y = p i g :=
  env.precompiles.meter_law a p i g h

private theorem stored_id_success (env : RunnerEnv Id) (a : Address)
    (p : PrecompileFn Id) (i : Bytes) (g g' : GasMeter) (output : Bytes)
    (hLookup : env.precompiles.lookup a = some p) (hResult : p i g = .ok g' output) :
    g'.gasLeft ≤ g.gasLeft ∧ { g' with gasLeft := g.gasLeft } = g := by
  have h := (satisfiesM_id_iff _ _).mp (env.precompiles.meter_law a p i g hLookup)
  rw [hResult] at h
  exact h

private def debit (cost : Nat) (output : Bytes) : PrecompileFn Id := fun _ g ↦
  .ok { g with gasLeft := g.gasLeft - cost } output

private def singleton (address : Address) (cost : Nat) (output : Bytes) :
    PrecompileTable Id where
  lookup a := if a = address then some (debit cost output) else none
  addresses := (∅ : AddrSet).insert address
  lookup_iff a := by
    simp only [Std.ExtTreeSet.mem_insert, Std.ExtTreeSet.not_mem_empty, or_false,
      Std.LawfulEqOrd.compare_eq_iff_eq]
    by_cases h : a = address
    · simp [h]
    · simp [h, Ne.symm h]
  meter_law a p i g h := by
    split at h
    · cases h
      exact (satisfiesM_id_iff _ _).mpr ⟨Nat.sub_le _ _, rfl⟩
    · contradiction

-- Full arbitrary GasCosts are retained, including arrays, signed refunds and U64 values.
-- Raw state prices and independent limits admit zero and values beyond word width.
private theorem varied_full_records (costs replacement : GasCosts) (output : Bytes) :
    let table := singleton (Address.ofNat 0x010203) 7 output
    let cfg := VmConfig.mk costs ⟨0, 2 ^ 300, 3, 11⟩ ⟨0, 2 ^ 280, 1⟩
    let env := RunnerEnv.mk table cfg (Address.ofNat 0x020100)
    let next := { env with vm := VmConfig.mk replacement ⟨13, 0, 17, 19⟩ ⟨9, 0, 2 ^ 290⟩ }
    env.precompiles = table ∧ env.vm = cfg ∧
      next.precompiles = table ∧ next.vm.costs = replacement ∧
      next.vm.stateCosts = StateGasCosts.mk 13 0 17 19 ∧
      next.vm.limits = VmLimits.mk 9 0 (2 ^ 290) ∧
      next.systemAddress = Address.ofNat 0x020100 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem singleton_stored (cfg : VmConfig) (address system : Address)
    (cost : Nat) (input output : Bytes) (g : GasMeter) :
    let env := RunnerEnv.mk (singleton address cost output) cfg system
    env.precompiles.lookup address = some (debit cost output) ∧
      address ∈ env.precompiles.addresses ∧
      debit cost output input g = .ok { g with gasLeft := g.gasLeft - cost } output ∧
      env.vm = cfg ∧ env.systemAddress = system := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · simp only [singleton, ↓reduceIte]
  · exact (stored_domain _ address).mp (by simp only [singleton, ↓reduceIte,
      Option.isSome_some])

private def output : Bytes := Bytes.ofList [0, 255, 1, 128, 0]
private def meter : GasMeter := ⟨13, 101, 2, -17, 5, 11⟩

private theorem complete_debit_result :
    debit 7 output Bytes.empty meter = .ok ⟨6, 101, 2, -17, 5, 11⟩ output := rfl

#guard ((singleton (Address.ofNat 0x010203) 7 output).addresses.toList.map
  Address.toNat) == [0x010203]
#guard ((singleton (Address.ofNat 0x010203) 7 output).lookup
  (Address.ofNat 0x030201)).isSome == false
private theorem stored_address_byte_order {m : Type → Type} [Monad m]
    (table : PrecompileTable m) (cfg : VmConfig) :
    let env := RunnerEnv.mk table cfg (Address.ofNat 0x020100)
    let changed := { env with systemAddress := Address.ofNat 0x000102 }
    env.systemAddress.toBytes.toList =
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0] ∧
      changed.systemAddress.toBytes.toList =
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2] ∧
      changed.precompiles = table ∧ changed.vm = cfg := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · change (Address.ofNat 0x020100).toBytes.toList = _
    decide
  · change (Address.ofNat 0x000102).toBytes.toList = _
    decide

#guard output.toList == [0, 255, 1, 128, 0]

end STFSpec.Conformance.Vm.Runner.EnvironmentCallerProofs
