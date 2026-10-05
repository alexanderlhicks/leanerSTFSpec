/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit
import STFSpec.Base.Numeric

/-!
# Complete storage wire regressions

Library `EthConformance`. Expected payloads are explicit unsigned radix-256
patterns; expected headers use the RLP short-string rules independently of the
production encoder. No decoder or assembled state-root coverage is claimed.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` §§3–4.
-/

open STFSpec.Base STFSpec.Commit STFSpec.StateCommit

private def wire (n : Nat) : List UInt8 := (encodeStorage (U256.ofNat n)).data.toList
private def stringWire (payload : List UInt8) : List UInt8 :=
  match payload with
  | [b] => if b.toNat < 128 then [b] else [129, b]
  | _ => UInt8.ofNat (128 + payload.length) :: payload

#guard wire 0 = [128]
#guard wire 1 = [1]
#guard wire 127 = [127]
#guard wire 128 = [129, 128]
#guard wire 255 = [129, 255]
#guard wire 256 = [130, 1, 0]
-- Exact zero/byte/list tags remain distinct.
#guard wire 0 ≠ ([] : List UInt8) ∧ wire 0 ≠ [0] ∧ wire 0 ≠ [192]

-- Every unsigned byte boundary, on both sides and at the boundary.
#guard (List.range 31).all fun j ↦
  let k := j + 1
  wire (2 ^ (8 * k) - 1) == stringWire (List.replicate k 255) &&
  wire (2 ^ (8 * k)) == stringWire (1 :: List.replicate k 0) &&
  wire (2 ^ (8 * k) + 1) == stringWire (1 :: List.replicate (k - 1) 0 ++ [1])

-- Every bit, including the high bit of each byte and bit255.
#guard (List.range 256).all fun i ↦
  wire (2 ^ i) == stringWire (UInt8.ofNat (2 ^ (i % 8)) :: List.replicate (i / 8) 0)
#guard wire (2 ^ 255) = 160 :: 128 :: List.replicate 31 0
#guard wire (2 ^ 256 - 1) = 160 :: List.replicate 32 255

#guard wire 0x010002000300 = [134, 1, 0, 2, 0, 3, 0]
#guard wire 0x800100ff000200 = [135, 128, 1, 0, 255, 0, 2, 0]
#guard wire 0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20 =
  160 :: [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
    17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]
#guard wire 0x80000100020003000400050006000700080009000a000b000c000d000e000f00 =
  160 :: [128, 0, 1, 0, 2, 0, 3, 0, 4, 0, 5, 0, 6, 0, 7, 0,
    8, 0, 9, 0, 10, 0, 11, 0, 12, 0, 13, 0, 14, 0, 15, 0]

private def suppliedDefaultTrie : Trie Nat U256 := ⟨false, U256.ofNat 128, ∅⟩
#guard (trieSet suppliedDefaultTrie 3 (U256.ofNat 128)).data[3]? = none
#guard (trieSet suppliedDefaultTrie 3 U256.zero).data[3]? = some U256.zero
#guard (TrieValue.encode (U256.ofNat 128)).data.toList = [129, 128]
#guard (TrieValue.encode U256.zero).data.toList = [128]
-- Directly stored defaults are valid and are retained by storage itself.
private def directlyStoredDefault : Trie Nat U256 :=
  ⟨false, U256.ofNat 128, (∅ : Std.ExtTreeMap Nat U256).insert 3 (U256.ofNat 128)⟩
#guard directlyStoredDefault.data[3]? = some (U256.ofNat 128)
private theorem direct_default_safe : directlyStoredDefault.PrepareSafe := fun _ _ _ ↦ True.intro
private theorem direct_default_not_noDefault : ¬directlyStoredDefault.NoDefault := by
  intro h
  have hv := h 3 (U256.ofNat 128) (by decide)
  exact hv rfl
