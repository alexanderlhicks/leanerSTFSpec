/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State.ModelsLookups

/-!
# Supplied-record lookup proof clients

Library `EthConformance`: ordinary symbolic clients consume exactly the three
success implications. Only this owned predicate unfolds; providers use public laws.
Spec guidance: `STFSpec/informal/modules/EthState.md` R8/§4/§5.
-/

namespace STFSpec.Conformance.State.ModelsLookupsCallerProofs

open STFSpec.Base STFSpec.State

example (consts : HashConsts) (ps : PreState Id) (σ : MathState)
    (hm : ModelsLookups consts ps σ) (a : Address) (o : Option Account)
    (ha : ps.getAccount? a = .ok o) : σ.account? a = o := by
  unfold ModelsLookups at hm
  exact hm.1 a o ha

example (consts : HashConsts) (ps : PreState Id) (σ : MathState)
    (hm : ModelsLookups consts ps σ) (a : Address) (k : Bytes32) (v : U256)
    (hs : ps.getStorage a k = .ok v) : σ.storageAt a k = v := by
  unfold ModelsLookups at hm
  exact hm.2.1 a k v hs

example (consts : HashConsts) (ps : PreState Id) (σ : MathState)
    (hm : ModelsLookups consts ps σ) (h : Hash32) (code : ByteArray)
    (hc : ps.getCode h = .ok code) : σ.code? consts h = some code := by
  unfold ModelsLookups at hm
  exact hm.2.2 h code hc

example (consts : HashConsts) (ps : PreState Id) (σ : MathState)
    (hm : ModelsLookups consts ps σ) (a : Address)
    (ha : ps.getAccount? a = .ok none) : σ.accounts[a]? = none := by
  rw [← MathState.account?_eq_lookup]
  exact hm.1 a none ha

example (consts : HashConsts) (ps : PreState Id) (σ : MathState)
    (hm : ModelsLookups consts ps σ) (a : Address) (x : Account)
    (ha : ps.getAccount? a = .ok (some x)) : σ.accounts[a]? = some x := by
  rw [← MathState.account?_eq_lookup]
  exact hm.1 a (some x) ha

example (consts : HashConsts) (ps : PreState Id) (σ : MathState)
    (hm : ModelsLookups consts ps σ) (a : Address) (k : Bytes32) (v : U256)
    (hs : ps.getStorage a k = .ok v) (hn : σ.storage[a]? = none) : v = U256.zero :=
  (hm.2.1 a k v hs).symm.trans (MathState.storageAt_of_storage_none σ a k hn)

example (consts : HashConsts) (ps : PreState Id) (σ : MathState)
    (hm : ModelsLookups consts ps σ) (a : Address) (k : Bytes32) (v : U256)
    (slots : Std.ExtTreeMap Bytes32 U256) (hs : ps.getStorage a k = .ok v)
    (hmaps : σ.storage[a]? = some slots) (hn : slots[k]? = none) : v = U256.zero :=
  (hm.2.1 a k v hs).symm.trans (MathState.storageAt_of_slot_none σ a k slots hmaps hn)

example (consts : HashConsts) (ps : PreState Id) (σ : MathState)
    (hm : ModelsLookups consts ps σ) (code : ByteArray)
    (hc : ps.getCode consts.emptyCodeHash = .ok code) : code = ByteArray.empty := by
  have he := (MathState.code?_empty σ consts).symm.trans (hm.2.2 _ code hc)
  exact (Option.some.inj he).symm

example (consts other : HashConsts) (ps : PreState Id) (σ : MathState)
    (he : consts.emptyCodeHash = other.emptyCodeHash)
    (hm : ModelsLookups consts ps σ) : ModelsLookups other ps σ := by
  refine ⟨hm.1, hm.2.1, ?_⟩
  intro h code hc
  rw [← MathState.code?_congr_consts σ consts h other he]
  exact hm.2.2 h code hc

example (consts : HashConsts) (ps : PreState Id) (σ : MathState)
    (root : BlockDiff → Id (Except WitnessError Hash32))
    (hm : ModelsLookups consts ps σ) :
    ModelsLookups consts (PreState.mk ps.getAccount? ps.getStorage ps.getCode root) σ := by
  unfold ModelsLookups
  rw [PreState.getAccount?_mk, PreState.getStorage_mk, PreState.getCode_mk]
  exact hm

end STFSpec.Conformance.State.ModelsLookupsCallerProofs
