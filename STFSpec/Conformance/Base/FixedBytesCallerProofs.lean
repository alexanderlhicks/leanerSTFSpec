/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.FixedBytes

/-!
# Fixed-byte public-law clients

Library `EthConformance`: callers use only public byte/numeric observations and laws.
The generic clients include width zero; pair clients check the supplied lexical instance.

Spec guidance: `STFSpec/informal/modules/EthBase.md`.
-/

namespace STFSpec.Conformance.Base.FixedBytesCallerProofs

open STFSpec.Base

example {n : Nat} (x : FixedBytes n) : FixedBytes.ofBytes? x.toBytes = some x :=
  FixedBytes.ofBytes?_toBytes x

example {n : Nat} (x : FixedBytes n) : x.toBytes.size = n := FixedBytes.size_toBytes x

example {n : Nat} (x : FixedBytes n) : x.toNat < 2 ^ (8 * n) := FixedBytes.toNat_lt x

example {n : Nat} {x y : FixedBytes n} (h : x.toBytes = y.toBytes) : x = y :=
  FixedBytes.toBytes_inj.mp h

example {n : Nat} {x y : FixedBytes n} (h : x.toNat = y.toNat) : x = y :=
  FixedBytes.toNat_inj.mp h

example {n : Nat} {x : FixedBytes n} {b : Bytes} (h : FixedBytes.ofBytes? b = some x) :
    x.toBytes = b := (FixedBytes.ofBytes?_eq_some_iff.mp h).2

example {n : Nat} {x : FixedBytes n} {b : Bytes} (h : FixedBytes.ofBytes? b = some x) :
    b.size = n := (FixedBytes.ofBytes?_eq_some_iff.mp h).1

example {n : Nat} {b : Bytes} (h : b.size ≠ n) :
    (FixedBytes.ofBytes? b : Option (FixedBytes n)) = none :=
  FixedBytes.ofBytes?_eq_none_iff.mpr h

example {n : Nat} (x y : FixedBytes n) :
    compare x y = compare (Bytes.toList x.toBytes) (Bytes.toList y.toBytes) :=
  FixedBytes.compare_toBytes x y

example {n : Nat} (x : FixedBytes n) :
    x.toNat = (Bytes.toList x.toBytes).foldl (fun acc b ↦ 256 * acc + b.toNat) 0 :=
  FixedBytes.toNat_eq_fold x

example (x : FixedBytes 0) : x.toNat = 0 := by
  have h := FixedBytes.toNat_lt x
  simp only [Nat.mul_zero, Nat.pow_zero] at h
  omega

example (x y : FixedBytes 0) : x = y := by
  apply FixedBytes.toNat_inj.mp
  have hx := FixedBytes.toNat_lt x
  have hy := FixedBytes.toNat_lt y
  simp only [Nat.mul_zero, Nat.pow_zero] at hx hy
  omega

example (x : Address) : Address.ofBytes? x.toBytes = some x := Address.ofBytes?_toBytes x
example (x : Address) : x.toBytes.size = 20 := Address.size_toBytes x
example (x : Address) : x.toNat < 2 ^ 160 := Address.toNat_lt x
example {x y : Address} (h : x.toBytes = y.toBytes) : x = y := Address.toBytes_inj.mp h
example {x y : Address} (h : x.toNat = y.toNat) : x = y := Address.toNat_inj.mp h
example {b : Bytes} (h : b.size ≠ 20) : Address.ofBytes? b = none :=
  Address.ofBytes?_eq_none_iff.mpr h
example {x : Address} {b : Bytes} (h : Address.ofBytes? b = some x) : x.toBytes = b :=
  (Address.ofBytes?_eq_some_iff.mp h).2
example (x y : Address) :
    compare x y = compare (Bytes.toList x.toBytes) (Bytes.toList y.toBytes) :=
  Address.compare_toBytes x y

example (x : Hash32) : Hash32.ofBytes? x.toBytes = some x := Hash32.ofBytes?_toBytes x
example (x : Hash32) : x.toBytes.size = 32 := Hash32.size_toBytes x
example (x : Hash32) : x.toNat < 2 ^ 256 := Hash32.toNat_lt x
example {x y : Hash32} (h : x.toBytes = y.toBytes) : x = y := Hash32.toBytes_inj.mp h
example {x y : Hash32} (h : x.toNat = y.toNat) : x = y := Hash32.toNat_inj.mp h
example {b : Bytes} (h : b.size ≠ 32) : Hash32.ofBytes? b = none :=
  Hash32.ofBytes?_eq_none_iff.mpr h
example {x : Hash32} {b : Bytes} (h : Hash32.ofBytes? b = some x) : x.toBytes = b :=
  (Hash32.ofBytes?_eq_some_iff.mp h).2
example (x y : Hash32) :
    compare x y = compare (Bytes.toList x.toBytes) (Bytes.toList y.toBytes) :=
  Hash32.compare_toBytes x y

example (x : Bytes32) : (Hash32.ofBytes32 x).toBytes32 = x := Hash32.toBytes32_ofBytes32 x
example (x : Hash32) : Hash32.ofBytes32 x.toBytes32 = x := Hash32.ofBytes32_toBytes32 x
example (x : Hash32) : x.toBytes32.toBytes = x.toBytes := Hash32.toBytes_toBytes32 x
example (x : Bytes32) : (Hash32.ofBytes32 x).toNat = x.toNat := Hash32.toNat_ofBytes32 x

example {x y : Hash32} (h : x.toBytes32.toBytes = y.toBytes) : x = y := by
  apply Hash32.toBytes_inj.mp
  simpa only [Hash32.toBytes_toBytes32] using h

example (x y : Address × Bytes32) :
    compare x y = (compare x.1 y.1).then (compare x.2 y.2) := compare_address_slot_eq_then x y

example (x y : Address × Bytes32) :
    compare x y =
      (compare (Bytes.toList x.1.toBytes) (Bytes.toList y.1.toBytes)).then
        (compare (Bytes.toList x.2.toBytes) (Bytes.toList y.2.toBytes)) :=
  compare_address_slot_toBytes x y

example {x y : Address × Bytes32} (h : compare x y = .eq) : x = y :=
  Std.LawfulEqOrd.eq_of_compare h

example {x y z : Address × Bytes32}
    (hxy : (compare x y).isLE) (hyz : (compare y z).isLE) : (compare x z).isLE :=
  Std.TransOrd.isLE_trans hxy hyz

example {n : Nat} : Std.TransOrd (FixedBytes n) := inferInstance
example {n : Nat} : Std.LawfulEqOrd (FixedBytes n) := inferInstance
example : Std.TransOrd Address := inferInstance
example : Std.LawfulEqOrd Address := inferInstance
example : Std.TransOrd Hash32 := inferInstance
example : Std.LawfulEqOrd Hash32 := inferInstance
example : Std.TransOrd (Address × Bytes32) := inferInstance
example : Std.LawfulEqOrd (Address × Bytes32) := inferInstance

end STFSpec.Conformance.Base.FixedBytesCallerProofs
