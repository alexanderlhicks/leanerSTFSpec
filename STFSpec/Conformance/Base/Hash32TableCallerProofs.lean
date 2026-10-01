/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.FixedBytes
import Std.Data.HashMap.Lemmas

/-!
# Hash32 public hash-table clients

Library `EthConformance`: complete observers determine actual equality and the
nonprotocol support hash. Std's public lookup laws preserve collisions and last writes.
No proof unfolds fixed-byte representation or hash-map storage.

Spec guidance: `STFSpec/informal/modules/EthBase.md` (DECISIONS Q51).
-/

namespace STFSpec.Conformance.Base.Hash32TableCallerProofs

open STFSpec.Base

/-- Boolean Hash32 equality is equivalent to actual key equality. -/
theorem hash32_beq_iff_eq (x y : Hash32) : (x == y) = true ↔ x = y := by simp

/-- The generic lawful hash class is compatible with actual equality. -/
theorem hash_compatible (x y : Hash32) (h : x == y) : hash x = hash y := hash_eq h

/-- Equal complete numeric observations preserve the support model. -/
theorem hash_eq_of_toNat_eq (x y : Hash32) (h : x.toNat = y.toNat) :
    hash x = hash y := congrArg hash (Hash32.toNat_inj.mp h)

/-- Equal byte observations preserve the support model. -/
theorem hash_eq_of_toBytes_eq (x y : Hash32) (h : x.toBytes = y.toBytes) :
    hash x = hash y := congrArg hash (Hash32.toBytes_inj.mp h)

/-- The Hashable instance exposes the ordinary executable/reference theorem. -/
theorem hash_model (x : Hash32) : hash x = Hash32.tableHashReference x :=
  Hash32.hash_eq_reference x

/-- Insertion tests actual key equality, independently of hash or bucket collisions. -/
theorem lookup_insert {β : Type} (db : Std.HashMap Hash32 β)
    (key query : Hash32) (value : β) :
    (db.insert key value)[query]? = if key = query then some value else db[query]? := by
  simpa only [hash32_beq_iff_eq] using
    (Std.HashMap.getElem?_insert (m := db) (k := key) (a := query) (v := value))

/-- Equal-key overwrite returns the newest payload. -/
theorem lookup_overwrite {β : Type} (db : Std.HashMap Hash32 β)
    (key : Hash32) (value latest : β) :
    ((db.insert key value).insert key latest)[key]? = some latest :=
  Std.HashMap.getElem?_insert_self

/-- Different keys preserve lookup without a distinct-hash premise. -/
theorem lookup_other {β : Type} (db : Std.HashMap Hash32 β)
    (key query : Hash32) (value : β) (h : key ≠ query) :
    (db.insert key value)[query]? = db[query]? := by
  rw [lookup_insert, ite_eq_right h]

/-- Independently constructed keys with equal numeric models retrieve the inserted value. -/
theorem lookup_equal_toNat {β : Type} (db : Std.HashMap Hash32 β)
    (key query : Hash32) (value : β) (h : key.toNat = query.toNat) :
    (db.insert key value)[query]? = some value := by
  rw [Hash32.toNat_inj.mp h]
  exact Std.HashMap.getElem?_insert_self

/-- Independently constructed keys with equal byte contents retrieve the inserted value. -/
theorem lookup_equal_toBytes {β : Type} (db : Std.HashMap Hash32 β)
    (key query : Hash32) (value : β) (h : key.toBytes = query.toBytes) :
    (db.insert key value)[query]? = some value := by
  rw [Hash32.toBytes_inj.mp h]
  exact Std.HashMap.getElem?_insert_self

end STFSpec.Conformance.Base.Hash32TableCallerProofs
