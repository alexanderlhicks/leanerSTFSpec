/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpItem

/-!
# Typed RLP leaf adapters

Library `EthCodec`. Operates on model items, without wire decoding or schema
instances. Follows locked ethereum-rlp 0.1.6 `ethereum_rlp/rlp.py:162–384` and
ethereum-types 0.4.1 byte/integer constructors. Integer failure order is shape,
leading zero, then fixed width, before numeric construction. Union alternatives
both contribute to the exactly-one-success count, even if values are equal.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§2–7.
-/

namespace STFSpec.Codec.Rlp

open STFSpec.Base

/-- Minimal integer model item; `ethereum_rlp/rlp.py:77–78` (0.1.6).
The Base encoder uses empty bytes for zero. -/
def ofNat (n : Nat) : RlpItem := .bytes (Uint.toBeBytes n).toByteArray

/-- Shared source-ordered integer guards; optional width bounds byte count.
`ethereum_rlp/rlp.py:263–277`; `ethereum_types/numeric.py:566–577`. -/
private def integer (width : Option Nat) : RlpItem → Except RlpError Nat
  | .list _ => .error (.shape "integer")
  | .bytes b =>
    if b[0]? = some 0 then .error (.nonCanonical "integer leading zero")
    else
      match width with
      | some w =>
        if b.size ≤ w then .ok (Uint.ofBeBytes (Bytes.ofByteArray b))
        else .error (.shape "integer width")
      | none => .ok (Uint.ofBeBytes (Bytes.ofByteArray b))

/-- Unbounded unsigned leaf; rejects lists and leading zero before decoding.
Pinned dependency `ethereum_rlp/rlp.py:263–277` (0.1.6). -/
def toNat : RlpItem → Except RlpError Nat := integer none

/-- Fixed-width unsigned leaf; leading zero precedes width rejection, and both
checks precede numeric construction. `ethereum_types/numeric.py:566–577` (0.4.1). -/
def toNatBounded (widthBytes : Nat) : RlpItem → Except RlpError Nat := integer (some widthBytes)

/-- Boolean leaf accepts exactly empty or singleton 0x01; lists reject.
Pinned dependency `ethereum_rlp/rlp.py:245–251` (0.1.6). -/
def toBool : RlpItem → Except RlpError Bool
  | .list _ => .error (.shape "boolean")
  | .bytes b =>
    if b = ByteArray.empty then .ok false
    else if b = ⟨#[1]⟩ then .ok true
    else .error (.shape "boolean")

/-- Byte leaf observes exactly the supplied bytes; `ethereum_rlp/rlp.py:254–260`. -/
def toBytes : RlpItem → Except RlpError ByteArray
  | .bytes b => .ok b
  | .list _ => .error (.shape "bytes")

/-- Exact-width byte leaf via the public checked Base constructor, including n=0.
`ethereum_rlp/rlp.py:254–260`; `ethereum_types/bytes.py:27–36`. -/
def toFixed (n : Nat) : RlpItem → Except RlpError (FixedBytes n)
  | .list _ => .error (.shape "bytes")
  | .bytes b =>
    match FixedBytes.ofBytes? (Bytes.ofByteArray b) with
    | some x => .ok x
    | none => .error (.shape "fixed bytes length")

/-- Raw list-shape observation, before element deserialization.
Pinned dependency `ethereum_rlp/rlp.py:374–379` (0.1.6). -/
def toList : RlpItem → Except RlpError (List RlpItem)
  | .bytes _ => .error (.shape "list")
  | .list xs => .ok xs

/-- Dataclass raw field-shape and arity step; child typing belongs to the schema.
Pinned dependency `ethereum_rlp/rlp.py:217–229` (0.1.6). -/
def toFields (n : Nat) : RlpItem → Except RlpError (Vector RlpItem n)
  | .bytes _ => .error (.shape "fields")
  | .list xs =>
    if h : xs.length = n then .ok ⟨xs.toArray, by simpa using h⟩
    else .error (.shape "field count")

/-- Exactly one successful variant; two successes reject even equal results.
Pinned dependency `ethereum_rlp/rlp.py:325–343` (0.1.6). Both alternatives are
observed; the future wrapper erases the no-match/multiple-match diagnostics. -/
def union2 {α : Type} (f g : RlpItem → Except RlpError α)
    (x : RlpItem) : Except RlpError α :=
  match f x, g x with
  | .ok a, .error _ => .ok a
  | .error _, .ok a => .ok a
  | .ok _, .ok _ => .error (.shape "multiple union variants")
  | .error _, .error _ => .error (.shape "no union variant")

private theorem first_byte (b : ByteArray) :
    b[0]? = (Bytes.ofByteArray b).toList.head? := by
  rw [Bytes.toList_ofByteArray, List.head?_eq_getElem?, Array.getElem?_toList]
  rfl

private theorem fold_lower (bs : List UInt8) (acc : Nat) :
    acc * 256 ^ bs.length ≤ bs.foldl (fun a b ↦ 256 * a + b.toNat) acc := by
  induction bs generalizing acc with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons, List.length_cons, Nat.pow_succ]
    have h := ih (256 * acc + b.toNat)
    apply Nat.le_trans _ h
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_right (256 ^ bs.length) (Nat.le_add_right (256 * acc) b.toNat)

private theorem canonical_size (b : Bytes) (h : b.toList.head? ≠ some 0) :
    (Uint.toBeBytes (Uint.ofBeBytes b)).size = b.size := by
  have upper := (Uint.size_toBeBytes_le_iff (Uint.ofBeBytes b) b.size).mpr
    (Uint.ofBeBytes_lt b)
  cases hb : b.toList with
  | nil =>
    have hs : b.size = 0 := by rw [← Bytes.length_toList, hb]; rfl
    omega
  | cons x xs =>
    have hx : x ≠ 0 := by simpa only [hb, List.head?_cons, ne_eq, Option.some.injEq] using h
    have hxn : 1 ≤ x.toNat := by
      have : x.toNat ≠ 0 := by
        intro he
        apply hx
        exact UInt8.toNat_inj.mp he
      omega
    have lower := fold_lower xs x.toNat
    have hp : 256 ^ xs.length ≤ x.toNat * 256 ^ xs.length :=
      by simpa using Nat.mul_le_mul_right (256 ^ xs.length) hxn
    have hv : 256 ^ xs.length ≤ Uint.ofBeBytes b := by
      rw [Uint.ofBeBytes_eq_fold, hb, List.foldl_cons]
      simpa using Nat.le_trans hp lower
    have hs : b.size = xs.length + 1 := by rw [← Bytes.length_toList, hb]; rfl
    by_cases he : (Uint.toBeBytes (Uint.ofBeBytes b)).size = b.size
    · exact he
    have hl : (Uint.toBeBytes (Uint.ofBeBytes b)).size ≤ xs.length := by omega
    have hv' := (Uint.size_toBeBytes_le_iff (Uint.ofBeBytes b) xs.length).mp hl
    have radix : 2 ^ (8 * xs.length) = 256 ^ xs.length := by rw [Nat.pow_mul]
    rw [radix] at hv'
    omega

private theorem canonical_bytes (b : Bytes) (h : b.toList.head? ≠ some 0) :
    b = Uint.toBeBytes (Uint.ofBeBytes b) := by
  have hs := canonical_size b h
  have obtain_fixed (z : Bytes) (hz : z.size = b.size) :
      ∃ v : FixedBytes b.size, v.toBytes = z := by
    cases he : (FixedBytes.ofBytes? z : Option (FixedBytes b.size)) with
    | none => exact False.elim ((FixedBytes.ofBytes?_eq_none_iff.mp he) hz)
    | some v => exact ⟨v, (FixedBytes.ofBytes?_eq_some_iff.mp he).2⟩
  obtain ⟨v, hv⟩ := obtain_fixed b rfl
  obtain ⟨u, hu⟩ := obtain_fixed (Uint.toBeBytes (Uint.ofBeBytes b)) hs
  have he : v.toNat = u.toNat := by
    rw [FixedBytes.toNat_eq_fold, FixedBytes.toNat_eq_fold, hv, hu,
      ← Uint.ofBeBytes_eq_fold, ← Uint.ofBeBytes_eq_fold, Uint.ofBeBytes_toBeBytes]
  have := congrArg FixedBytes.toBytes (FixedBytes.toNat_inj.mp he)
  simpa only [hv, hu] using this

private theorem encoded_first (n : Nat) : (Uint.toBeBytes n).toByteArray[0]? ≠ some 0 := by
  rw [first_byte, Bytes.ofByteArray_toByteArray]
  by_cases hn : n = 0
  · subst n
    simp only [Uint.toBeBytes_zero, Bytes.toList_empty, List.head?_nil, ne_eq]
    decide
  · exact Uint.toList_toBeBytes_head_ne_zero n hn

/-- Unbounded acceptance is exactly a byte leaf without leading zero and its value. -/
theorem toNat_eq_ok_bytes_iff (b : ByteArray) (n : Nat) :
    toNat (.bytes b) = .ok n ↔
      b[0]? ≠ some 0 ∧ Uint.ofBeBytes (Bytes.ofByteArray b) = n := by
  simp only [toNat, integer]
  split <;> simp_all

/-- Successful integer decoding is equivalent to the unique minimal bytes. -/
theorem toNat_canonical_iff (b : ByteArray) (n : Nat) :
    toNat (.bytes b) = .ok n ↔ b = (Uint.toBeBytes n).toByteArray := by
  constructor
  · intro h
    obtain ⟨hz, hv⟩ := (toNat_eq_ok_bytes_iff b n).mp h
    rw [first_byte] at hz
    have he := canonical_bytes (Bytes.ofByteArray b) hz
    rw [hv] at he
    simpa only [Bytes.toByteArray_ofByteArray] using congrArg Bytes.toByteArray he
  · intro h
    subst b
    apply (toNat_eq_ok_bytes_iff _ _).mpr
    exact ⟨encoded_first n, by rw [Bytes.ofByteArray_toByteArray, Uint.ofBeBytes_toBeBytes]⟩

/-- The integer item encoder and typed decoder roundtrip for every natural. -/
theorem toNat_ofNat (n : Nat) : toNat (ofNat n) = .ok n :=
  (toNat_canonical_iff _ n).mpr rfl

/-- Item-level integer acceptance identifies both shape and minimal contents. -/
theorem toNat_eq_ok_iff (x : RlpItem) (n : Nat) :
    toNat x = .ok n ↔ x = ofNat n := by
  cases x with
  | bytes b => simpa only [ofNat, RlpItem.bytes.injEq] using toNat_canonical_iff b n
  | list xs => simp [toNat, integer, ofNat]

/-- Fixed-width acceptance adds a byte-count check to unbounded acceptance. -/
theorem toNatBounded_eq_ok_iff (w : Nat) (b : ByteArray) (n : Nat) :
    toNatBounded w (.bytes b) = .ok n ↔ toNat (.bytes b) = .ok n ∧ b.size ≤ w := by
  simp only [toNatBounded, toNat, integer]
  split <;> simp_all
  split <;> simp_all

/-- Fixed-width success is minimal canonical output fitting the byte width. -/
theorem toNatBounded_canonical_iff (w : Nat) (b : ByteArray) (n : Nat) :
    toNatBounded w (.bytes b) = .ok n ↔
      b = (Uint.toBeBytes n).toByteArray ∧ b.size ≤ w := by
  rw [toNatBounded_eq_ok_iff, toNat_canonical_iff]

/-- Item-level bounded acceptance is canonicality plus the complete numeric range. -/
theorem toNatBounded_eq_ok_item_iff (w : Nat) (x : RlpItem) (n : Nat) :
    toNatBounded w x = .ok n ↔ x = ofNat n ∧ n < 2 ^ (8 * w) := by
  cases x with
  | list xs => simp [toNatBounded, integer, ofNat]
  | bytes b =>
    rw [toNatBounded_canonical_iff]
    constructor
    · rintro ⟨hb, hw⟩
      exact ⟨congrArg RlpItem.bytes hb,
        (Uint.size_toBeBytes_le_iff n w).mp (by simpa only [hb, Bytes.size_toByteArray] using hw)⟩
    · rintro ⟨hb, hw⟩
      have he : b = (Uint.toBeBytes n).toByteArray := RlpItem.bytes.inj hb
      exact ⟨he, by simpa only [he, Bytes.size_toByteArray] using
        (Uint.size_toBeBytes_le_iff n w).mpr hw⟩

/-- Zero-byte integers accept exactly the empty representation of zero. -/
theorem toNatBounded_zero_iff (x : RlpItem) (n : Nat) :
    toNatBounded 0 x = .ok n ↔ x = ofNat 0 ∧ n = 0 := by
  rw [toNatBounded_eq_ok_item_iff]
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.lt_one_iff]
  constructor <;> rintro ⟨hx, hn⟩ <;> subst n <;> exact ⟨hx, rfl⟩

/-- Boolean success is precisely the two source-canonical byte leaves. -/
theorem toBool_eq_ok_iff (x : RlpItem) (v : Bool) :
    toBool x = .ok v ↔
      (x = .bytes ByteArray.empty ∧ v = false) ∨
      (x = .bytes ⟨#[1]⟩ ∧ v = true) := by
  cases x with
  | list xs => simp [toBool]
  | bytes b =>
    simp only [toBool, RlpItem.bytes.injEq]
    have he : ByteArray.empty ≠ (⟨#[1]⟩ : ByteArray) := by decide
    by_cases hb : b = ByteArray.empty
    · simp [hb, he]
    · by_cases h1 : b = (⟨#[1]⟩ : ByteArray)
      · simp [h1, Ne.symm he]
      · simp [hb, h1]

/-- A leading zero always wins over an invalid width. -/
theorem toNatBounded_leading_zero (w : Nat) (b : ByteArray) (h : b[0]? = some 0) :
    toNatBounded w (.bytes b) = .error (.nonCanonical "integer leading zero") := by
  simp only [toNatBounded, integer, h, ↓reduceIte]

/-- Byte leaf success preserves the constructor and every byte. -/
theorem toBytes_eq_ok_iff (x : RlpItem) (b : ByteArray) :
    toBytes x = .ok b ↔ x = .bytes b := by
  cases x <;> simp [toBytes]

/-- List-shape success preserves every ordered child without decoding it. -/
theorem toList_eq_ok_iff (x : RlpItem) (xs : List RlpItem) :
    toList x = .ok xs ↔ x = .list xs := by
  cases x <;> simp [toList]

/-- Exact fixed length and byte observation characterize successful construction. -/
theorem toFixed_eq_ok_iff (n : Nat) (b : ByteArray) (v : FixedBytes n) :
    toFixed n (.bytes b) = .ok v ↔ b.size = n ∧ v.toBytes.toByteArray = b := by
  unfold toFixed
  cases h : (FixedBytes.ofBytes? (Bytes.ofByteArray b) : Option (FixedBytes n)) with
  | none =>
    have hn := FixedBytes.ofBytes?_eq_none_iff.mp h
    simp only [Bytes.size_ofByteArray] at hn
    simp [h, hn]
  | some u =>
    have hu := FixedBytes.ofBytes?_eq_some_iff.mp h
    simp only [Bytes.size_ofByteArray] at hu
    have hb : u.toBytes.toByteArray = b := by
      rw [hu.2, Bytes.toByteArray_ofByteArray]
    simp only [h, Except.ok.injEq]
    constructor
    · intro huv
      subst v
      exact ⟨hu.1, hb⟩
    · rintro ⟨_, hv⟩
      apply (FixedBytes.toBytes_inj).mp
      rw [← Bytes.ofByteArray_toByteArray u.toBytes,
        ← Bytes.ofByteArray_toByteArray v.toBytes, hb, hv]

/-- Item-level fixed-byte success pins shape as well as all byte observations. -/
theorem toFixed_eq_ok_item_iff (n : Nat) (x : RlpItem) (v : FixedBytes n) :
    toFixed n x = .ok v ↔ x = .bytes v.toBytes.toByteArray := by
  cases x with
  | list xs => simp [toFixed]
  | bytes b =>
    rw [toFixed_eq_ok_iff]
    simp only [RlpItem.bytes.injEq]
    constructor
    · intro h
      exact h.2.symm
    · intro h
      subst b
      exact ⟨by rw [Bytes.size_toByteArray, FixedBytes.size_toBytes], rfl⟩

/-- Fields accept precisely a list of the requested arity and preserve child order. -/
theorem toFields_eq_ok_iff (n : Nat) (x : RlpItem) (v : Vector RlpItem n) :
    toFields n x = .ok v ↔ x = .list v.toList := by
  cases x with
  | bytes b => simp [toFields]
  | list xs =>
    simp only [toFields, RlpItem.list.injEq]
    split
    · next h =>
      simp only [Except.ok.injEq]
      constructor
      · intro he
        subst v
        simp
      · intro he
        apply Vector.toList_inj.mp
        simpa using he
    · next h =>
      simp only [reduceCtorEq, false_iff]
      intro he
      apply h
      rw [he, Vector.length_toList]

/-- Wrong list arity rejects before any child is interpreted. -/
theorem toFields_wrong_arity (n : Nat) (xs : List RlpItem) (h : xs.length ≠ n) :
    toFields n (.list xs) = .error (.shape "field count") := by
  simp [toFields, h]

/-- Union success identifies one successful alternative and one failure exactly. -/
theorem union2_eq_ok_iff {α : Type} (f g : RlpItem → Except RlpError α)
    (x : RlpItem) (a : α) :
    union2 f g x = .ok a ↔
      (f x = .ok a ∧ ∃ e, g x = .error e) ∨
      (g x = .ok a ∧ ∃ e, f x = .error e) := by
  unfold union2
  cases hf : f x <;> cases hg : g x <;> simp

end STFSpec.Codec.Rlp
