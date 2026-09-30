/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# Integer byte conversion caller proofs

Library `EthConformance`: public observation, inverse, canonicality and exact failure laws.
Every proof uses the model contract; no stored fields or provider internals are unfolded.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §7.
-/

open STFSpec.Base

example (n : Nat) : Uint.ofBeBytes (Uint.toBeBytes n) = n :=
  Uint.ofBeBytes_toBeBytes n

example (n k : Nat) : (Uint.toBeBytes n).size ≤ k ↔ n < 2 ^ (8 * k) :=
  Uint.size_toBeBytes_le_iff n k

example (n : Nat) (h : n ≠ 0) : (Bytes.toList (Uint.toBeBytes n)).head? ≠ some 0 :=
  Uint.toList_toBeBytes_head_ne_zero n h

example (n : Nat) : Uint.toBeBytes n = Bytes.empty ↔ n = 0 :=
  Uint.toBeBytes_eq_empty_iff n

example (n : Nat) : Uint.toBeBytes32? n = none ↔ 2 ^ 256 ≤ n :=
  Uint.toBeBytes32?_eq_none_iff n

example (n : Nat) (b : Bytes32) (h : Uint.toBeBytes32? n = some b) : b.toNat = n :=
  ((Uint.toBeBytes32?_eq_some_iff n b).mp h).2

example (b : Bytes) : Uint.ofBeBytes b < 2 ^ (8 * b.size) := Uint.ofBeBytes_lt b

example (b : Bytes) : Uint.ofLeBytes b < 2 ^ (8 * b.size) := Uint.ofLeBytes_lt b

example (b : Bytes) : Uint.ofLeBytes b = Uint.ofBeBytes (Bytes.ofList (Bytes.toList b).reverse) :=
  Uint.ofLeBytes_eq_reverse b

example (x : U256) : U256.ofBeBytes32 (U256.toBeBytes32 x) = x :=
  U256.ofBeBytes32_toBeBytes32 x

example (b : Bytes32) : U256.toBeBytes32 (U256.ofBeBytes32 b) = b :=
  U256.toBeBytes32_ofBeBytes32 b

example (x : U256) : U256.ofBeBytes? (U256.toBeBytes x) = some x :=
  U256.ofBeBytes?_toBeBytes x

example (b : Bytes) : U256.ofBeBytes? b = none ↔ 32 < b.size :=
  U256.ofBeBytes?_eq_none_iff b

example (b : Bytes) (x : U256) (h : U256.ofBeBytes? b = some x) :
    b.size ≤ 32 ∧ x.toNat = Uint.ofBeBytes b :=
  (U256.ofBeBytes?_eq_some_iff b x).mp h

example (x : U256) : Uint.ofLeBytes (U256.toLeBytes32 x).toBytes = x.toNat :=
  U256.ofLeBytes_toLeBytes32 x

example (x : U256) : (U256.toBeBytes x).size ≤ 32 := U256.size_toBeBytes_le x

example (x : U64) : U64.ofBeBytes? (U64.toBeBytes8 x).toBytes = some x :=
  U64.ofBeBytes?_toBeBytes8 x

example (x : U64) : U64.ofLeBytes? (U64.toLeBytes8 x).toBytes = some x :=
  U64.ofLeBytes?_toLeBytes8 x

example (b : Bytes) : U64.ofLeBytes? b = none ↔ 8 < b.size :=
  U64.ofLeBytes?_eq_none_iff b

example (b : Bytes) (x : U64) (h : U64.ofLeBytes? b = some x) :
    x.toNat = Uint.ofLeBytes b := ((U64.ofLeBytes?_eq_some_iff b x).mp h).2

example (x : U64) : U64.ofBeBytes? (U64.toBeBytes x) = some x :=
  U64.ofBeBytes?_toBeBytes x

example (x : U64) : (U64.toBeBytes x).size ≤ 8 := U64.size_toBeBytes_le x

example (x : U64) (h : x.toNat ≠ 0) : (Bytes.toList (U64.toBeBytes x)).head? ≠ some 0 :=
  U64.toList_toBeBytes_head_ne_zero x h

example (x : U256) : (Address.ofU256Masked x).toNat = x.toNat % 2 ^ 160 :=
  Address.toNat_ofU256Masked x

example (x : U256) : (Address.ofU256Masked x).toBytes =
    Bytes.ofList ((Bytes.toList (U256.toBeBytes32 x).toBytes).drop 12) :=
  Address.toBytes_ofU256Masked x

example (a : Address) : a.toU256.toNat = a.toNat := Address.toNat_toU256 a

example (a : Address) : Address.ofU256Masked a.toU256 = a :=
  Address.ofU256Masked_toU256 a

example (x : U256) : (Address.ofU256Masked x).toU256.toNat = x.toNat % 2 ^ 160 :=
  Address.toNat_toU256_ofU256Masked x

example (x : U256) (k : Nat) : (U256.toBeBytes x).size ≤ k ↔ x.toNat < 2 ^ (8 * k) :=
  U256.size_toBeBytes_le_iff x k

example (x : U64) (k : Nat) : (U64.toBeBytes x).size ≤ k ↔ x.toNat < 2 ^ (8 * k) :=
  U64.size_toBeBytes_le_iff x k

example (x : U256) : U256.toBeBytes x = Bytes.empty ↔ x = U256.zero :=
  U256.toBeBytes_eq_empty_iff x

example (x : U64) : U64.toBeBytes x = Bytes.empty ↔ x = U64.zero :=
  U64.toBeBytes_eq_empty_iff x


example {α : Type} (f : UInt8 → α → α) (b : Bytes) (init : α) :
    b.foldr f init = b.toList.foldr f init := Bytes.foldr_eq f init b

example {n : Nat} (v : Nat) :
    (FixedBytes.ofNat v : FixedBytes n).toNat = v % 2 ^ (8 * n) :=
  FixedBytes.toNat_ofNat v

example {n : Nat} (x : FixedBytes n) : FixedBytes.ofNat x.toNat = x :=
  FixedBytes.ofNat_toNat x

example {n : Nat} (v : Nat) :
    (FixedBytes.ofLeNat v : FixedBytes n).toBytes =
      Bytes.ofList (FixedBytes.ofNat v : FixedBytes n).toBytes.toList.reverse :=
  FixedBytes.toBytes_ofLeNat_eq_reverse v

example (v : Nat) : (Address.ofNat v).toNat = v % 2 ^ 160 :=
  Address.toNat_ofNat v

example (a : Address) : Address.ofNat a.toNat = a := Address.ofNat_toNat a

example (v : Nat) : Uint.toBeBytes v = Uint.toBeBytesReference v :=
  Uint.toBeBytes_eq_reference v
