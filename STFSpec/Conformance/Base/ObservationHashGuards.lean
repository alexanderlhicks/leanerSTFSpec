/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base
import Std.Data.HashSet.Lemmas
import Std.Data.HashMap.Lemmas

/-!
# Observation-key support guards

Library `EthConformance`: complete UInt64 literals computed independently with
integer xor/multiply arithmetic; actual Std observations retain duplicate keys.
These are functional cases, not distribution or cost measurements.

Spec guidance: `STFSpec/informal/modules/EthBase.md` (DECISIONS Q84).
-/

namespace STFSpec.Conformance.Base.ObservationHashGuards

open STFSpec.Base

private abbrev SlotAlias := FixedBytes 32
#synth Hashable Address
#synth Hashable Bytes32
#synth Hashable SlotAlias
#synth LawfulBEq Address
#synth LawfulHashable Address
#synth LawfulBEq Bytes32
#synth LawfulHashable Bytes32
#synth LawfulBEq (Address × Bytes32)
#synth LawfulHashable (Address × Bytes32)
#synth LawfulBEq (Address × Hash32)
#synth LawfulHashable (Address × Hash32)
#check_failure (inferInstance : Hashable (FixedBytes 0))
#check_failure (inferInstance : Hashable (FixedBytes 20))
#check_failure (inferInstance : Hashable Bytes)
#check_failure (inferInstance : Hashable Hash64)
section
variable (n : Nat)
#check_failure (inferInstance : Hashable (FixedBytes n))
end

private def addressVector (n : Nat) (expected : UInt64) : Bool :=
  let x := Address.ofNat n
  Address.tableHash x == expected && Address.tableHashReference x == expected &&
    hash x == expected && Address.ofBytes? x.toBytes == some x

private def slotVector (n : Nat) (expected : UInt64) : Bool :=
  let x : Bytes32 := FixedBytes.ofNat n
  Bytes32.tableHash x == expected && Bytes32.tableHashReference x == expected &&
    hash x == expected && FixedBytes.ofBytes? x.toBytes == some x

#guard addressVector 0 17187419518357145909
#guard addressVector 1 17187418418845517698
#guard addressVector 3 17187416219822261276
#guard addressVector 255 17187438210054825496
#guard addressVector 256 17186462943240791564
#guard addressVector 257 17186464042752419775
#guard addressVector 1461501637330902918203684832716283019655932542975 6853414789623893377
#guard addressVector 1461501637330902918203684832716283019655932542979 17187416219822261276
#guard addressVector 2147483648 16995458167421358517
#guard addressVector 4294967296 16273501972323868370
#guard addressVector 9223372036854775808 8152208532148975797
#guard addressVector 18446744073709551616 6565022986836906786
#guard addressVector 39614081257132168796771975168 5531593314323574965
#guard addressVector 79228162514264337593543950336 6815248620231636082
#guard addressVector 170141183460469231731687303715884105728 8033039596142913717
#guard addressVector 340282366920938463463374607431768211456 11506335329148916418
#guard addressVector 730750818665451459101842416358141509827966271488 352384754983072181
#guard addressVector 22475995960490625424124334220934763854762515 14740984644555640673
#guard addressVector 108873724432616589554458274966207996112469623040 15386978571825638713

#guard slotVector 0 901300984310592933
#guard slotVector 1 901299884798964722
#guard slotVector 3 901297685775708300
#guard slotVector 255 901425229124580776
#guard slotVector 256 900344409194238588
#guard slotVector 257 900345508705866799
#guard slotVector 115792089237316195423570985008687907853269984665640564039457584007913129639935 11152567584539099013
#guard slotVector 115792089237316195423570985008687907853269984665640564039457584007913129639939 901297685775708300
#guard slotVector 2147483648 1093262335246380325
#guard slotVector 4294967296 18434127511986867010
#guard slotVector 9223372036854775808 9936511970518763045
#guard slotVector 18446744073709551616 8725648526499905426
#guard slotVector 39614081257132168796771975168 12557127188344163877
#guard slotVector 79228162514264337593543950336 8975874159894634722
#guard slotVector 170141183460469231731687303715884105728 10055680906524825125
#guard slotVector 340282366920938463463374607431768211456 13666960868811915058
#guard slotVector 57896044618658097711785492504343953926634992332820282019728792003956564819968 13320385225556702757
#guard slotVector 1780731860627700044960722568376592200742329637303199754547598369979440671 16630484232385628869
#guard slotVector 14074904626401341155369551180448584754667373453244490859944217516317499064576 1843852397005901797

private def tables {α : Type} [BEq α] [Hashable α]
    (first second equalFirst absent : α) : Bool := Id.run do
  let left : Std.HashSet α := (∅ : Std.HashSet α).insert first
  let right : Std.HashSet α := ((∅ : Std.HashSet α).insert second).insert equalFirst
  let merged := left ∪ right
  let repeated := merged.insert first
  let db : Std.HashMap α Nat := ∅
  let db := ((db.insert first 11).insert second 22).insert equalFirst 33
  return merged.contains first && merged.contains second && !merged.contains absent &&
    merged.size == 2 && repeated.size == 2 && repeated.contains equalFirst &&
    left.size == 1 && !left.contains second && db[first]? == some 33 &&
    db[second]? == some 22 && db[absent]? == none && db.size == 2

private def a (n : Nat) : Address := Address.ofNat n
private def b (n : Nat) : Bytes32 := FixedBytes.ofNat n
private def h (n : Nat) : Hash32 := Hash32.ofBytes32 (b n)

#guard tables (a 3) (a 8) (a (3 + 2 ^ 160)) (a 999)
#guard tables (b 3) (b 8) (b (3 + 2 ^ 256)) (b 999)
#guard tables (a 3, b 5) (a 3, b 8) (a (3 + 2 ^ 160), b (5 + 2 ^ 256)) (a 3, b 999)
#guard tables (a 3, b 5) (a 8, b 5) (a 3, b 5) (a 999, b 5)
#guard tables (a 3, h 5) (a 3, h 8) (a (3 + 2 ^ 160), h (5 + 2 ^ 256)) (a 3, h 999)
#guard tables (a 3, h 5) (a 8, h 5) (a 3, h 5) (a 999, h 5)

end STFSpec.Conformance.Base.ObservationHashGuards
