/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Typed RLP public contract callers

Library `EthConformance`. Clients use exported observations and accept-set laws,
including converse minimality, bounded range, list order and exactly-one union.
These are model composition proofs, without wire codecs or schema instances.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §7.
-/

open STFSpec.Codec STFSpec.Codec.Rlp STFSpec.Base

example (n : Nat) : toNat (ofNat n) = .ok n := toNat_ofNat n

example (b : ByteArray) (n : Nat) (h : toNat (.bytes b) = .ok n) :
    b = (Uint.toBeBytes n).toByteArray := (toNat_canonical_iff b n).mp h

example (b : ByteArray) (n : Nat) (h : b = (Uint.toBeBytes n).toByteArray) :
    toNat (.bytes b) = .ok n := (toNat_canonical_iff b n).mpr h

example (x : RlpItem) (n m : Nat) (hn : toNat x = .ok n) (hm : toNat x = .ok m) :
    n = m := Except.ok.inj (hn.symm.trans hm)

example (w n : Nat) (h : n < 2 ^ (8 * w)) :
    toNatBounded w (ofNat n) = .ok n :=
  (toNatBounded_eq_ok_item_iff w (ofNat n) n).mpr ⟨rfl, h⟩

example (w : Nat) (x : RlpItem) (n : Nat) (h : toNatBounded w x = .ok n) :
    toNat x = .ok n ∧ n < 2 ^ (8 * w) := by
  obtain ⟨hx, hn⟩ := (toNatBounded_eq_ok_item_iff w x n).mp h
  exact ⟨(toNat_eq_ok_iff x n).mpr hx, hn⟩

example (w₁ w₂ : Nat) (x : RlpItem) (n : Nat)
    (hw : w₁ ≤ w₂) (h : toNatBounded w₁ x = .ok n) :
    toNatBounded w₂ x = .ok n := by
  obtain ⟨hx, hn⟩ := (toNatBounded_eq_ok_item_iff w₁ x n).mp h
  subst x
  apply (toNatBounded_eq_ok_item_iff w₂ (ofNat n) n).mpr
  exact ⟨rfl, (Uint.size_toBeBytes_le_iff n w₂).mp
    (Nat.le_trans ((Uint.size_toBeBytes_le_iff n w₁).mpr hn) hw)⟩

example (x : RlpItem) (n : Nat) (h : toNatBounded 0 x = .ok n) :
    x = ofNat 0 ∧ n = 0 := (toNatBounded_zero_iff x n).mp h

example (w : Nat) (b : ByteArray) (h : b[0]? = some 0) :
    toNatBounded w (.bytes b) = .error (.nonCanonical "integer leading zero") :=
  toNatBounded_leading_zero w b h

example (x : RlpItem) (v : Bool) (h : toBool x = .ok v) :
    (x = .bytes ByteArray.empty ∧ v = false) ∨
      (x = .bytes ⟨#[1]⟩ ∧ v = true) := (toBool_eq_ok_iff x v).mp h

example (x : RlpItem) (b : ByteArray) (h : toBytes x = .ok b) :
    x = .bytes b := (toBytes_eq_ok_iff x b).mp h

example (n : Nat) (b : ByteArray) (v : FixedBytes n) (h : toFixed n (.bytes b) = .ok v) :
    b.size = n ∧ v.toBytes.toByteArray = b := (toFixed_eq_ok_iff n b v).mp h

example (n : Nat) (v : FixedBytes n) :
    toFixed n (.bytes v.toBytes.toByteArray) = .ok v :=
  (toFixed_eq_ok_iff n _ v).mpr ⟨by rw [Bytes.size_toByteArray, FixedBytes.size_toBytes], rfl⟩

example (x : RlpItem) (xs : List RlpItem) (h : toList x = .ok xs) :
    x = .list xs := (toList_eq_ok_iff x xs).mp h

example (n : Nat) (x : RlpItem) (v : Vector RlpItem n) (h : toFields n x = .ok v) :
    x = .list v.toList ∧ v.toList.length = n :=
  ⟨(toFields_eq_ok_iff n x v).mp h, Vector.length_toList⟩

example (n : Nat) (v : Vector RlpItem n) :
    toFields n (.list v.toList) = .ok v := (toFields_eq_ok_iff n _ v).mpr rfl

example {α : Type} (f g : RlpItem → Except RlpError α) (x : RlpItem) (a : α)
    (h : union2 f g x = .ok a) :
    (f x = .ok a ∧ ∃ e, g x = .error e) ∨
      (g x = .ok a ∧ ∃ e, f x = .error e) := (union2_eq_ok_iff f g x a).mp h

example {α : Type} (f g : RlpItem → Except RlpError α) (x : RlpItem) (a : α)
    (hf : f x = .ok a) (hg : g x = .ok a) : union2 f g x ≠ .ok a := by
  intro h
  rcases (union2_eq_ok_iff f g x a).mp h with ⟨_, e, he⟩ | ⟨_, e, he⟩
  · rw [hg] at he
    cases he
  · rw [hf] at he
    cases he

example (n : Nat) (x : RlpItem) (v : FixedBytes n) (h : toFixed n x = .ok v) :
    x = .bytes v.toBytes.toByteArray := (toFixed_eq_ok_item_iff n x v).mp h
