/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.FixedBytes
import Std.Data.HashMap.Lemmas

/-!
# Hash32 table-support regression guards

Library `EthConformance`: actual Hash32 instance and public Std map observations.
Vector constants are independent Python xor/multiply arithmetic, not EELS hashing.
Compiled whole-value tests live in `STFSpec/Conformance/Base/hash32_table_support.py`.

Spec guidance: `STFSpec/informal/modules/EthBase.md` (DECISIONS Q51).
-/

namespace STFSpec.Conformance.Base.Hash32TableGuards

open STFSpec.Base

private def key (value : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat value)

#synth BEq Hash32
#synth LawfulBEq Hash32
#synth EquivBEq Hash32
#synth LawfulHashable Hash32
#synth Hashable Root
#synth Hashable VersionedHash
#check_failure (inferInstance : Hashable Address)
#check_failure (inferInstance : Hashable Bytes32)

#guard hash (key 0) == (901300984310592933 : UInt64)
#guard hash (key 1) == (901299884798964722 : UInt64)
#guard hash (key (2 ^ 64)) == (8725648526499905426 : UInt64)
#guard hash (key (2 ^ 128)) == (13666960868811915058 : UInt64)
#guard hash (key (2 ^ 192)) == (17560413411585667794 : UInt64)
#guard hash (key (2 ^ 256 - 1)) == (11152567584539099013 : UInt64)
#guard hash (key (3 + 2 ^ 256)) == hash (key 3)

private def mapGuards : Bool := Id.run do
  let db : Std.HashMap Hash32 Nat := ∅
  let db := db.insert (key 3) 11
  let db := db.insert (key 8) 22
  let db := db.insert (key (3 + 2 ^ 256)) 33
  return db[key 3]? == some 33 && db[key 8]? == some 22 &&
    db[key 999]? == none && db.size == 2

#guard mapGuards

end STFSpec.Conformance.Base.Hash32TableGuards
