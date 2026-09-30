/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# Byte-sequence client proof tests

Library `EthConformance`: these callers use only stable byte observations and public
laws, without unfolding a padding/read definition or inspecting stored array data.
Spec guidance: `STFSpec/informal/modules/EthBase.md` §7.
-/

open STFSpec.Base

example (a b : Bytes) (h : Bytes.toList a = Bytes.toList b) : a = b := Bytes.ext h

example (b : Bytes) : (Bytes.toList b).toByteArray = b := Bytes.toByteArray_toList b

example (xs : List UInt8) : Bytes.toList xs.toByteArray = xs := Bytes.toList_toByteArray xs

example (b : Bytes) (n : Nat) : b.size ≤ (Bytes.leftPadZero b n).size := by
  rw [Bytes.size_leftPadZero]
  exact Nat.le_max_left _ _

example (b : Bytes) (n : Nat) : n ≤ (Bytes.rightPadZero b n).size := by
  rw [Bytes.size_rightPadZero]
  exact Nat.le_max_right _ _

example (b : Bytes) (n : Nat) (h : n ≤ b.size) : Bytes.leftPadZero b n = b :=
  Bytes.leftPadZero_of_le b n h

example (b : Bytes) (n : Nat) :
    Bytes.rightPadZero (Bytes.rightPadZero b n) n = Bytes.rightPadZero b n :=
  Bytes.rightPadZero_idempotent b n

example (b : Bytes) (n : Nat) :
    Bytes.toList (Bytes.leftPadZero b n) = List.replicate (n - b.size) 0 ++ Bytes.toList b :=
  Bytes.toList_leftPadZero b n

example (b : Bytes) (n i : Nat) (hi : i < b.size) :
    (Bytes.toList (Bytes.rightPadZero b n))[i]? = (Bytes.toList b)[i]? := by
  rw [Bytes.getElem?_toList_rightPadZero, ite_eq_left hi]

example (b : Bytes) (start len : Nat) :
    (Bytes.toList (Bytes.extractPadded b start len)).length = len := by
  rw [Bytes.length_toList, Bytes.size_extractPadded]

example (b : Bytes) (start : Nat) : Bytes.extractPadded b start 0 = ByteArray.empty :=
  Bytes.extractPadded_zero b start

example (b : Bytes) (start len : Nat) (h : b.size ≤ start) :
    Bytes.toList (Bytes.extractPadded b start len) = List.replicate len 0 :=
  Bytes.toList_extractPadded_of_size_le b start len h

example (b : Bytes) (start len : Nat) :
    Bytes.toList (Bytes.extractPadded b start len) =
      ((Bytes.toList b).drop start).take len ++
        List.replicate (len - min len (b.size - start)) 0 :=
  Bytes.toList_extractPadded_window b start len

example (b : Bytes) (start len i : Nat) (hi : i < len) (hb : ¬ start + i < b.size) :
    (Bytes.extractPadded b start len)[i]'(by rw [Bytes.size_extractPadded]; exact hi) = 0 := by
  rw [Bytes.getElem_extractPadded b start len i hi, dite_eq_right hb]

example (b : Bytes) (n start len : Nat) (h : start + len ≤ max b.size n) :
    Bytes.extractPadded (Bytes.rightPadZero b n) start len = Bytes.extractPadded b start len :=
  Bytes.extractPadded_rightPadZero b n start len h
