/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# Primitive record client proofs

Library `EthConformance`: fixed clients use public record projections and model laws,
without unpacking the replaceable word, address or hash representations.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §§3–4.
-/

open STFSpec.Base

example (k : HashConsts) :
    HashConsts.mk k.emptyCodeHash k.emptyTrieRoot k.emptyOmmerHash k.transferTopic = k :=
  HashConsts.mk_projections k

example (a b c d : Hash32) : (HashConsts.mk a b c d).emptyCodeHash = a :=
  HashConsts.emptyCodeHash_mk a b c d
example (a b c d : Hash32) : (HashConsts.mk a b c d).emptyTrieRoot = b :=
  HashConsts.emptyTrieRoot_mk a b c d
example (a b c d : Hash32) : (HashConsts.mk a b c d).emptyOmmerHash = c :=
  HashConsts.emptyOmmerHash_mk a b c d
example (a b c d : Hash32) : (HashConsts.mk a b c d).transferTopic = d :=
  HashConsts.transferTopic_mk a b c d

example (x y : HashConsts) (ha : x.emptyCodeHash.toBytes = y.emptyCodeHash.toBytes)
    (hb : x.emptyTrieRoot.toBytes = y.emptyTrieRoot.toBytes)
    (hc : x.emptyOmmerHash.toBytes = y.emptyOmmerHash.toBytes)
    (hd : x.transferTopic.toBytes = y.transferTopic.toBytes) : x = y :=
  HashConsts.ext (Hash32.toBytes_inj.mp ha) (Hash32.toBytes_inj.mp hb)
    (Hash32.toBytes_inj.mp hc) (Hash32.toBytes_inj.mp hd)

example (a : Authorization) :
    Authorization.mk a.chainId a.address a.nonce a.yParity a.r a.s = a :=
  Authorization.mk_projections a

example (x y : Authorization) (hc : x.chainId.toNat = y.chainId.toNat)
    (ha : x.address.toBytes = y.address.toBytes) (hn : x.nonce.toNat = y.nonce.toNat)
    (hy : x.yParity.toNat = y.yParity.toNat) (hr : x.r.toNat = y.r.toNat)
    (hs : x.s.toNat = y.s.toNat) : x = y :=
  Authorization.ext (U256.toNat_inj.mp hc) (Address.toBytes_inj.mp ha)
    (U64.toNat_inj.mp hn) (U8.toNat_inj.mp hy) (U256.toNat_inj.mp hr) (U256.toNat_inj.mp hs)

example (g : StateGasPerByte) : StateGasPerByte.mk g.rate = g :=
  StateGasPerByte.mk_projections g
example (x y : StateGasPerByte) (h : x.rate = y.rate) : x = y := StateGasPerByte.ext h
example (n : Nat) : (StateGasPerByte.mk n).rate = n := StateGasPerByte.rate_mk n
example (g : StateGasPerByte) (n : Nat) : g.charge n = g.rate * n :=
  StateGasPerByte.charge_eq g n
example (g : StateGasPerByte) (n : Nat) : g.charge n = n * g.rate :=
  StateGasPerByte.charge_eq_mul_rate g n
example (g : StateGasPerByte) : g.charge 0 = 0 := StateGasPerByte.charge_zero g
example (n : Nat) : (StateGasPerByte.mk 0).charge n = 0 := StateGasPerByte.zero_rate_charge n
example (g : StateGasPerByte) (a b : Nat) : g.charge (a + b) = g.charge a + g.charge b := by
  rw [StateGasPerByte.charge_eq, StateGasPerByte.charge_eq, StateGasPerByte.charge_eq]
  exact Nat.mul_add _ _ _
