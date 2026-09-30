/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# Narrow unsigned regression guards

Library `EthConformance`: width boundaries, huge natural constructors, checked
failures and unsigned order. Only the public narrow API is used.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §§3–4.
-/

open STFSpec.Base

-- U8: endpoints and constructor reduction.
#guard U8.zero.toNat = 0
#guard U8.one.toNat = 1
#guard U8.max.toNat = 2 ^ 8 - 1
#guard U8.ofNat? 0 = some U8.zero
#guard U8.ofNat? 1 = some U8.one
#guard U8.ofNat? (2 ^ 8 - 1) = some U8.max
#guard U8.ofNat? (2 ^ 8) = none
#guard U8.ofNat? (2 ^ 8 + 1) = none
#guard U8.ofNat? (2 ^ 4096 + 17) = none
#guard (U8.ofNat (2 ^ 8)).toNat = 0
#guard (U8.ofNat (2 ^ 8 + 1)).toNat = 1
#guard (U8.ofNat (2 ^ 4096 + 17)).toNat = 17
#guard (U8.ofNat (2 ^ 8 - 1)).toBitVec = BitVec.ofNat 8 (2 ^ 8 - 1)
#guard U8.wrappingAdd U8.max U8.one = U8.zero
#guard U8.wrappingAdd U8.max U8.max = U8.ofNat (2 ^ 8 - 2)
#guard U8.wrappingSub U8.zero U8.one = U8.max
#guard U8.wrappingSub U8.one U8.one = U8.zero
#guard U8.wrappingMul U8.max U8.max = U8.one
#guard U8.wrappingMul U8.max U8.zero = U8.zero
#guard U8.checkedAdd U8.max U8.one = none
#guard U8.checkedAdd U8.max U8.zero = some U8.max
#guard U8.checkedAdd (U8.ofNat (2 ^ 8 - 2)) U8.one = some U8.max
#guard U8.checkedAdd (U8.ofNat (2 ^ (8 - 1)))
  (U8.ofNat (2 ^ (8 - 1))) = none
#guard U8.checkedSub U8.zero U8.one = none
#guard U8.checkedSub U8.max U8.max = some U8.zero
#guard U8.checkedSub U8.max U8.one = some (U8.ofNat (2 ^ 8 - 2))
#guard U8.checkedSub U8.zero U8.zero = some U8.zero
#guard U8.checkedMul U8.max U8.max = none
#guard U8.checkedMul U8.max U8.one = some U8.max
#guard U8.checkedMul U8.max U8.zero = some U8.zero
#guard U8.checkedMul (U8.ofNat (2 ^ (8 - 1))) (U8.ofNat 2) = none
#guard U8.checkedMul (U8.ofNat (2 ^ (8 - 1) - 1)) (U8.ofNat 2) =
  some (U8.ofNat (2 ^ 8 - 2))
#guard compare U8.zero U8.one = .lt
#guard compare U8.max U8.zero = .gt
#guard compare (U8.ofNat (2 ^ (8 - 1)))
  (U8.ofNat (2 ^ (8 - 1) - 1)) = .gt
#guard compare (U8.ofNat (2 ^ 8 + 1)) U8.one = .eq
#guard U8.ofNat 1 = U8.ofNat (2 ^ 8 + 1)

-- Inherited arithmetic, literals, coercions and storage are unavailable.
#check_failure (inferInstance : Add U8)
#check_failure (inferInstance : Sub U8)
#check_failure (inferInstance : Mul U8)
#check_failure (inferInstance : OfNat U8 0)
#check_failure (inferInstance : Coe U8 UInt8)
#check_failure (inferInstance : Coe UInt8 U8)
#check_failure U8.val
#check_failure U8.ofUIntRaw

-- U16: endpoints and constructor reduction.
#guard U16.zero.toNat = 0
#guard U16.one.toNat = 1
#guard U16.max.toNat = 2 ^ 16 - 1
#guard U16.ofNat? 0 = some U16.zero
#guard U16.ofNat? 1 = some U16.one
#guard U16.ofNat? (2 ^ 16 - 1) = some U16.max
#guard U16.ofNat? (2 ^ 16) = none
#guard U16.ofNat? (2 ^ 16 + 1) = none
#guard U16.ofNat? (2 ^ 4096 + 17) = none
#guard (U16.ofNat (2 ^ 16)).toNat = 0
#guard (U16.ofNat (2 ^ 16 + 1)).toNat = 1
#guard (U16.ofNat (2 ^ 4096 + 17)).toNat = 17
#guard (U16.ofNat (2 ^ 16 - 1)).toBitVec = BitVec.ofNat 16 (2 ^ 16 - 1)
#guard U16.wrappingAdd U16.max U16.one = U16.zero
#guard U16.wrappingAdd U16.max U16.max = U16.ofNat (2 ^ 16 - 2)
#guard U16.wrappingSub U16.zero U16.one = U16.max
#guard U16.wrappingSub U16.one U16.one = U16.zero
#guard U16.wrappingMul U16.max U16.max = U16.one
#guard U16.wrappingMul U16.max U16.zero = U16.zero
#guard U16.checkedAdd U16.max U16.one = none
#guard U16.checkedAdd U16.max U16.zero = some U16.max
#guard U16.checkedAdd (U16.ofNat (2 ^ 16 - 2)) U16.one = some U16.max
#guard U16.checkedAdd (U16.ofNat (2 ^ (16 - 1)))
  (U16.ofNat (2 ^ (16 - 1))) = none
#guard U16.checkedSub U16.zero U16.one = none
#guard U16.checkedSub U16.max U16.max = some U16.zero
#guard U16.checkedSub U16.max U16.one = some (U16.ofNat (2 ^ 16 - 2))
#guard U16.checkedSub U16.zero U16.zero = some U16.zero
#guard U16.checkedMul U16.max U16.max = none
#guard U16.checkedMul U16.max U16.one = some U16.max
#guard U16.checkedMul U16.max U16.zero = some U16.zero
#guard U16.checkedMul (U16.ofNat (2 ^ (16 - 1))) (U16.ofNat 2) = none
#guard U16.checkedMul (U16.ofNat (2 ^ (16 - 1) - 1)) (U16.ofNat 2) =
  some (U16.ofNat (2 ^ 16 - 2))
#guard compare U16.zero U16.one = .lt
#guard compare U16.max U16.zero = .gt
#guard compare (U16.ofNat (2 ^ (16 - 1)))
  (U16.ofNat (2 ^ (16 - 1) - 1)) = .gt
#guard compare (U16.ofNat (2 ^ 16 + 1)) U16.one = .eq
#guard U16.ofNat 1 = U16.ofNat (2 ^ 16 + 1)

-- Inherited arithmetic, literals, coercions and storage are unavailable.
#check_failure (inferInstance : Add U16)
#check_failure (inferInstance : Sub U16)
#check_failure (inferInstance : Mul U16)
#check_failure (inferInstance : OfNat U16 0)
#check_failure (inferInstance : Coe U16 UInt16)
#check_failure (inferInstance : Coe UInt16 U16)
#check_failure U16.val
#check_failure U16.ofUIntRaw

-- U32: endpoints and constructor reduction.
#guard U32.zero.toNat = 0
#guard U32.one.toNat = 1
#guard U32.max.toNat = 2 ^ 32 - 1
#guard U32.ofNat? 0 = some U32.zero
#guard U32.ofNat? 1 = some U32.one
#guard U32.ofNat? (2 ^ 32 - 1) = some U32.max
#guard U32.ofNat? (2 ^ 32) = none
#guard U32.ofNat? (2 ^ 32 + 1) = none
#guard U32.ofNat? (2 ^ 4096 + 17) = none
#guard (U32.ofNat (2 ^ 32)).toNat = 0
#guard (U32.ofNat (2 ^ 32 + 1)).toNat = 1
#guard (U32.ofNat (2 ^ 4096 + 17)).toNat = 17
#guard (U32.ofNat (2 ^ 32 - 1)).toBitVec = BitVec.ofNat 32 (2 ^ 32 - 1)
#guard U32.wrappingAdd U32.max U32.one = U32.zero
#guard U32.wrappingAdd U32.max U32.max = U32.ofNat (2 ^ 32 - 2)
#guard U32.wrappingSub U32.zero U32.one = U32.max
#guard U32.wrappingSub U32.one U32.one = U32.zero
#guard U32.wrappingMul U32.max U32.max = U32.one
#guard U32.wrappingMul U32.max U32.zero = U32.zero
#guard U32.checkedAdd U32.max U32.one = none
#guard U32.checkedAdd U32.max U32.zero = some U32.max
#guard U32.checkedAdd (U32.ofNat (2 ^ 32 - 2)) U32.one = some U32.max
#guard U32.checkedAdd (U32.ofNat (2 ^ (32 - 1)))
  (U32.ofNat (2 ^ (32 - 1))) = none
#guard U32.checkedSub U32.zero U32.one = none
#guard U32.checkedSub U32.max U32.max = some U32.zero
#guard U32.checkedSub U32.max U32.one = some (U32.ofNat (2 ^ 32 - 2))
#guard U32.checkedSub U32.zero U32.zero = some U32.zero
#guard U32.checkedMul U32.max U32.max = none
#guard U32.checkedMul U32.max U32.one = some U32.max
#guard U32.checkedMul U32.max U32.zero = some U32.zero
#guard U32.checkedMul (U32.ofNat (2 ^ (32 - 1))) (U32.ofNat 2) = none
#guard U32.checkedMul (U32.ofNat (2 ^ (32 - 1) - 1)) (U32.ofNat 2) =
  some (U32.ofNat (2 ^ 32 - 2))
#guard compare U32.zero U32.one = .lt
#guard compare U32.max U32.zero = .gt
#guard compare (U32.ofNat (2 ^ (32 - 1)))
  (U32.ofNat (2 ^ (32 - 1) - 1)) = .gt
#guard compare (U32.ofNat (2 ^ 32 + 1)) U32.one = .eq
#guard U32.ofNat 1 = U32.ofNat (2 ^ 32 + 1)

-- Inherited arithmetic, literals, coercions and storage are unavailable.
#check_failure (inferInstance : Add U32)
#check_failure (inferInstance : Sub U32)
#check_failure (inferInstance : Mul U32)
#check_failure (inferInstance : OfNat U32 0)
#check_failure (inferInstance : Coe U32 UInt32)
#check_failure (inferInstance : Coe UInt32 U32)
#check_failure U32.val
#check_failure U32.ofUIntRaw

-- U64: endpoints and constructor reduction.
#guard U64.zero.toNat = 0
#guard U64.one.toNat = 1
#guard U64.max.toNat = 2 ^ 64 - 1
#guard U64.ofNat? 0 = some U64.zero
#guard U64.ofNat? 1 = some U64.one
#guard U64.ofNat? (2 ^ 64 - 1) = some U64.max
#guard U64.ofNat? (2 ^ 64) = none
#guard U64.ofNat? (2 ^ 64 + 1) = none
#guard U64.ofNat? (2 ^ 4096 + 17) = none
#guard (U64.ofNat (2 ^ 64)).toNat = 0
#guard (U64.ofNat (2 ^ 64 + 1)).toNat = 1
#guard (U64.ofNat (2 ^ 4096 + 17)).toNat = 17
#guard (U64.ofNat (2 ^ 64 - 1)).toBitVec = BitVec.ofNat 64 (2 ^ 64 - 1)
#guard U64.wrappingAdd U64.max U64.one = U64.zero
#guard U64.wrappingAdd U64.max U64.max = U64.ofNat (2 ^ 64 - 2)
#guard U64.wrappingSub U64.zero U64.one = U64.max
#guard U64.wrappingSub U64.one U64.one = U64.zero
#guard U64.wrappingMul U64.max U64.max = U64.one
#guard U64.wrappingMul U64.max U64.zero = U64.zero
#guard U64.checkedAdd U64.max U64.one = none
#guard U64.checkedAdd U64.max U64.zero = some U64.max
#guard U64.checkedAdd (U64.ofNat (2 ^ 64 - 2)) U64.one = some U64.max
#guard U64.checkedAdd (U64.ofNat (2 ^ (64 - 1)))
  (U64.ofNat (2 ^ (64 - 1))) = none
#guard U64.checkedSub U64.zero U64.one = none
#guard U64.checkedSub U64.max U64.max = some U64.zero
#guard U64.checkedSub U64.max U64.one = some (U64.ofNat (2 ^ 64 - 2))
#guard U64.checkedSub U64.zero U64.zero = some U64.zero
#guard U64.checkedMul U64.max U64.max = none
#guard U64.checkedMul U64.max U64.one = some U64.max
#guard U64.checkedMul U64.max U64.zero = some U64.zero
#guard U64.checkedMul (U64.ofNat (2 ^ (64 - 1))) (U64.ofNat 2) = none
#guard U64.checkedMul (U64.ofNat (2 ^ (64 - 1) - 1)) (U64.ofNat 2) =
  some (U64.ofNat (2 ^ 64 - 2))
#guard compare U64.zero U64.one = .lt
#guard compare U64.max U64.zero = .gt
#guard compare (U64.ofNat (2 ^ (64 - 1)))
  (U64.ofNat (2 ^ (64 - 1) - 1)) = .gt
#guard compare (U64.ofNat (2 ^ 64 + 1)) U64.one = .eq
#guard U64.ofNat 1 = U64.ofNat (2 ^ 64 + 1)

-- Inherited arithmetic, literals, coercions and storage are unavailable.
#check_failure (inferInstance : Add U64)
#check_failure (inferInstance : Sub U64)
#check_failure (inferInstance : Mul U64)
#check_failure (inferInstance : OfNat U64 0)
#check_failure (inferInstance : Coe U64 UInt64)
#check_failure (inferInstance : Coe UInt64 U64)
#check_failure U64.val
#check_failure U64.ofUIntRaw

#check_failure fun (x : U8) ↦ x.1
#check_failure (⟨0⟩ : U8)
#check_failure ({ val := 0 } : U8)

#check_failure fun (x : U16) ↦ x.1
#check_failure (⟨0⟩ : U16)
#check_failure ({ val := 0 } : U16)

#check_failure fun (x : U32) ↦ x.1
#check_failure (⟨0⟩ : U32)
#check_failure ({ val := 0 } : U32)

#check_failure fun (x : U64) ↦ x.1
#check_failure (⟨0⟩ : U64)
#check_failure ({ val := 0 } : U64)
