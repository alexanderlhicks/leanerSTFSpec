/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.FixedBytes
import STFSpec.Base.U256
import STFSpec.Base.U64

/-!
# Integer byte conversions

Library `EthBase`: checked bounded decoding, exact-width endian output, minimal
big-endian unsigned output and masked addresses. All consumers use public models.
Spec guidance: `STFSpec/informal/modules/EthBase.md`.
Reference: locked `ethereum-types` 0.4.1; complete source mappings are in the spec guidance.
-/

namespace STFSpec.Base

namespace Uint

/-- Unbounded big-endian decoding; `ethereum_types/numeric.py:523`.
Every byte length is accepted, including leading zero bytes. -/
def ofBeBytes (b : Bytes) : Nat := b.foldl (fun acc byte ↦ 256 * acc + byte.toNat) 0

/-- Unbounded little-endian decoding; `ethereum_types/numeric.py:531`. -/
def ofLeBytes (b : Bytes) : Nat := b.foldr (fun byte acc ↦ 256 * acc + byte.toNat) 0

/-- Big-endian decoding is the positional Horner fold over the public byte model. -/
theorem ofBeBytes_eq_fold (b : Bytes) :
    ofBeBytes b = (Bytes.toList b).foldl (fun acc b ↦ 256 * acc + b.toNat) 0 :=
  Bytes.foldl_eq _ _ _

/-- Little-endian decoding is big-endian decoding of reversed byte observations. -/
theorem ofLeBytes_eq_reverse (b : Bytes) :
    ofLeBytes b = ofBeBytes (Bytes.ofList (Bytes.toList b).reverse) := by
  rw [ofLeBytes, Bytes.foldr_eq, ofBeBytes_eq_fold, Bytes.toList_ofList,
    List.foldl_reverse]

end Uint

private theorem fold_acc (bs : List UInt8) (acc : Nat) :
    bs.foldl (fun acc b ↦ 256 * acc + b.toNat) acc =
      acc * 256 ^ bs.length + bs.foldl (fun acc b ↦ 256 * acc + b.toNat) 0 := by
  induction bs generalizing acc with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons, List.length_cons, Nat.pow_succ, Nat.mul_zero, Nat.zero_add]
    rw [ih (256 * acc + b.toNat), ih b.toNat]
    simp only [Nat.add_mul]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.add_assoc]

private theorem radix_eq (n : Nat) : 256 ^ n = 2 ^ (8 * n) := by
  rw [Nat.pow_mul]

private def decodeLeReference : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decodeLeReference bs

private theorem decode_append (xs ys : List UInt8) :
    Uint.ofBeBytes (Bytes.ofList (xs ++ ys)) =
      Uint.ofBeBytes (Bytes.ofList xs) * 256 ^ ys.length +
        Uint.ofBeBytes (Bytes.ofList ys) := by
  simp only [Uint.ofBeBytes_eq_fold, Bytes.toList_ofList]
  rw [List.foldl_append, fold_acc]

private theorem decode_reverse (bs : List UInt8) :
    Uint.ofBeBytes (Bytes.ofList bs.reverse) = decodeLeReference bs := by
  have hr : bs.foldr (fun byte acc ↦ 256 * acc + byte.toNat) 0 =
      decodeLeReference bs := by
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      simp only [List.foldr_cons, decodeLeReference, ih]
      exact Nat.add_comm _ _
  have h := Uint.ofLeBytes_eq_reverse (Bytes.ofList bs)
  rw [Bytes.toList_ofList] at h
  rw [← h, Uint.ofLeBytes, Bytes.foldr_eq, Bytes.toList_ofList, hr]

private def minimalLe (n : Nat) : List UInt8 :=
  if n = 0 then [] else UInt8.ofNat (n % 256) :: minimalLe (n / 256)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

private theorem decode_minimalLe (n : Nat) : decodeLeReference (minimalLe n) = n := by
  rw [minimalLe]
  split
  · next h => simp [h, decodeLeReference]
  · next h =>
    simp only [decodeLeReference]
    rw [UInt8.toNat_ofNat_of_lt' (Nat.mod_lt _ (by decide)), decode_minimalLe]
    change n % 256 + 256 * (n / 256) = n
    have := Nat.div_add_mod n 256
    omega
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

private theorem minimalLe_eq_nil_iff (n : Nat) : minimalLe n = [] ↔ n = 0 := by
  rw [minimalLe]
  split <;> simp_all

private theorem minimalLe_reverse_head (n : Nat) (h : n ≠ 0) :
    (minimalLe n).reverse.head? ≠ some 0 := by
  rw [minimalLe, ite_eq_right h, List.reverse_cons]
  by_cases hd : n / 256 = 0
  · rw [minimalLe, ite_eq_left hd]
    simp only [List.reverse_nil, List.nil_append, List.head?_cons, ne_eq,
      Option.some.injEq]
    intro hz
    have hr : n < 256 := (Nat.div_eq_zero_iff_lt (by decide)).mp hd
    have hn := UInt8.toNat_ofNat_of_lt' hr
    rw [Nat.mod_eq_of_lt hr] at hz
    have he := congrArg UInt8.toNat hz
    simp only [hn] at he
    exact h he
  · have ih := minimalLe_reverse_head (n / 256) hd
    have hn : (minimalLe (n / 256)).reverse ≠ [] := by
      intro he
      apply hd
      exact (minimalLe_eq_nil_iff _).mp (List.reverse_eq_nil_iff.mp he)
    cases he : (minimalLe (n / 256)).reverse with
    | nil => exact False.elim (hn he)
    | cons b bs => simpa only [he, List.cons_append, List.head?_cons] using ih
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

private theorem minimalLe_length_le_iff (n k : Nat) :
    (minimalLe n).length ≤ k ↔ n < 256 ^ k := by
  induction k generalizing n with
  | zero =>
    rw [Nat.pow_zero]
    have := minimalLe_eq_nil_iff n
    simpa only [Nat.le_zero, List.length_eq_zero_iff, Nat.lt_one_iff] using this
  | succ k ih =>
    rw [minimalLe]
    split
    · next h => simp [h, Nat.pow_pos (by decide : 0 < 256)]
    · simp only [List.length_cons, Nat.add_le_add_iff_right, ih, Nat.pow_succ]
      exact Nat.div_lt_iff_lt_mul (by decide : 0 < 256)

private def byteLength (n : Nat) : Nat :=
  if n = 0 then 0 else n.log2 / 8 + 1

private theorem byteLength_le_iff (n k : Nat) :
    byteLength n ≤ k ↔ n < 2 ^ (8 * k) := by
  by_cases h : n = 0
  · simp [byteLength, h, Nat.pow_pos (by decide : 0 < 2)]
  · simp only [byteLength, ite_eq_right h]
    rw [← Nat.log2_lt h]
    have hd : n.log2 / 8 < k ↔ n.log2 < 8 * k := by
      simpa only [Nat.mul_comm] using
        (Nat.div_lt_iff_lt_mul (by decide : 0 < 8) : n.log2 / 8 < k ↔ n.log2 < k * 8)
    omega

private theorem length_minimalLe (n : Nat) : (minimalLe n).length = byteLength n := by
  apply Nat.le_antisymm
  · apply (minimalLe_length_le_iff _ _).mpr
    rw [radix_eq]
    exact (byteLength_le_iff _ _).mp (Nat.le_refl _)
  · apply (byteLength_le_iff _ _).mpr
    rw [← radix_eq]
    exact (minimalLe_length_le_iff _ _).mp (Nat.le_refl _)

namespace Uint

/-- Legible minimal-digit reference; `ethereum_types/numeric.py:477–484`.
This proof model divides by 256 and reverses the digit list; zero is empty. -/
def toBeBytesReference (n : Nat) : Bytes := Bytes.ofList (minimalLe n).reverse

/-- Minimal big-endian output; `ethereum_types/numeric.py:477–484`.
Computes the width from the bit length and generates its digits in packed storage. -/
def toBeBytes (n : Nat) : Bytes :=
  (FixedBytes.ofNat (n := byteLength n) n).toBytes

/-- Packed minimal output equals the legible digit-list reference on every natural input. -/
theorem toBeBytes_eq_reference (n : Nat) : toBeBytes n = toBeBytesReference n := by
  let b := toBeBytesReference n
  have hb : b.size = byteLength n := by
    change (toBeBytesReference n).size = byteLength n
    rw [toBeBytesReference, Bytes.size_ofList, List.length_reverse, length_minimalLe]
  cases hc : FixedBytes.ofBytes? (n := byteLength n) b with
  | none => exact False.elim (FixedBytes.ofBytes?_eq_none_iff.mp hc hb)
  | some z =>
    have hz : z.toBytes = b := (FixedBytes.ofBytes?_eq_some_iff.mp hc).2
    have hn : z.toNat = n := by
      rw [FixedBytes.toNat_eq_fold, hz, ← ofBeBytes_eq_fold]
      change ofBeBytes (toBeBytesReference n) = n
      rw [toBeBytesReference, decode_reverse, decode_minimalLe]
    have he : (FixedBytes.ofNat n : FixedBytes (byteLength n)) = z := by
      apply FixedBytes.toNat_inj.mp
      rw [FixedBytes.toNat_ofNat, hn,
        Nat.mod_eq_of_lt ((byteLength_le_iff _ _).mp (Nat.le_refl _))]
    rw [toBeBytes, he, hz]

/-- The complete decoded value fits the input's byte length. -/
theorem ofBeBytes_lt (b : Bytes) : ofBeBytes b < 2 ^ (8 * b.size) := by
  cases hc : FixedBytes.ofBytes? (n := b.size) b with
  | none => exact False.elim (FixedBytes.ofBytes?_eq_none_iff.mp hc rfl)
  | some z =>
    have hz := (FixedBytes.ofBytes?_eq_some_iff.mp hc).2
    have hn : ofBeBytes b = z.toNat := by
      rw [ofBeBytes_eq_fold, FixedBytes.toNat_eq_fold, hz]
    rw [hn]
    exact FixedBytes.toNat_lt z

/-- The complete little-endian value fits the input's byte length. -/
theorem ofLeBytes_lt (b : Bytes) : ofLeBytes b < 2 ^ (8 * b.size) := by
  rw [ofLeBytes_eq_reverse]
  have h := ofBeBytes_lt (Bytes.ofList (Bytes.toList b).reverse)
  simpa only [Bytes.size_ofList, List.length_reverse, Bytes.length_toList] using h

/-- Minimal output reconstructs every unbounded input without any width limit. -/
theorem ofBeBytes_toBeBytes (n : Nat) : ofBeBytes (toBeBytes n) = n := by
  rw [toBeBytes_eq_reference, toBeBytesReference, decode_reverse, decode_minimalLe]

/-- Minimal output uses at most `k` bytes exactly when the value fits those bytes. -/
theorem size_toBeBytes_le_iff (n k : Nat) :
    (toBeBytes n).size ≤ k ↔ n < 2 ^ (8 * k) := by
  rw [← Bytes.length_toList, toBeBytes_eq_reference, toBeBytesReference, Bytes.toList_ofList,
    List.length_reverse, minimalLe_length_le_iff, radix_eq]

/-- Zero has empty minimal big-endian output. -/
theorem toBeBytes_zero : toBeBytes 0 = Bytes.empty := by
  apply Bytes.ext
  rw [toBeBytes_eq_reference, toBeBytesReference, Bytes.toList_ofList,
    Bytes.toList_empty, minimalLe, ite_eq_left rfl, List.reverse_nil]

/-- Empty minimal output characterises zero. -/
theorem toBeBytes_eq_empty_iff (n : Nat) : toBeBytes n = Bytes.empty ↔ n = 0 := by
  constructor
  · intro h
    have := congrArg ofBeBytes h
    rw [ofBeBytes_toBeBytes, ofBeBytes_eq_fold, Bytes.toList_empty] at this
    exact this
  · intro h
    subst n
    exact toBeBytes_zero

/-- Nonzero minimal output has no leading zero byte. -/
theorem toList_toBeBytes_head_ne_zero (n : Nat) (h : n ≠ 0) :
    (Bytes.toList (toBeBytes n)).head? ≠ some 0 := by
  rw [toBeBytes_eq_reference, toBeBytesReference, Bytes.toList_ofList]
  exact minimalLe_reverse_head n h

end Uint

private theorem ofBeBytes_toBytes {n : Nat} (x : FixedBytes n) :
    Uint.ofBeBytes x.toBytes = x.toNat := by
  rw [Uint.ofBeBytes_eq_fold, FixedBytes.toNat_eq_fold]

namespace Uint

/-- Checked 32-byte output; `ethereum_types/numeric.py:424`.
Rejects values at least 2^256 before producing the fixed-width result. -/
def toBeBytes32? (n : Nat) : Option Bytes32 :=
  if n < 2 ^ 256 then some (FixedBytes.ofNat n) else none

/-- Fixed output succeeds exactly with the complete unreduced numeric input. -/
theorem toBeBytes32?_eq_some_iff (n : Nat) (x : Bytes32) :
    toBeBytes32? n = some x ↔ n < 2 ^ 256 ∧ x.toNat = n := by
  unfold toBeBytes32?
  split
  · next h =>
    simp only [Option.some.injEq]
    have hm := FixedBytes.toNat_ofNat_of_lt (n := 32) n h
    constructor
    · intro he
      subst x
      exact ⟨h, hm⟩
    · intro hx
      apply FixedBytes.toNat_inj.mp
      rw [hm, hx.2]
  · next h => simp [h]

/-- Overflow is the only fixed-32 output failure. -/
theorem toBeBytes32?_eq_none_iff (n : Nat) :
    toBeBytes32? n = none ↔ 2 ^ 256 ≤ n := by
  simp [toBeBytes32?, Nat.not_lt]

end Uint

namespace U256

/-- Exact big-endian output; `ethereum_types/numeric.py:424`. -/
def toBeBytes32 (x : U256) : FixedBytes 32 := FixedBytes.ofNat x.toNat

/-- Exact little-endian output; `ethereum_types/numeric.py:495`. -/
def toLeBytes32 (x : U256) : FixedBytes 32 := FixedBytes.ofLeNat x.toNat

/-- Big-endian decoding checks source byte length before numeric interpretation;
`ethereum_types/numeric.py:566–577`. Even over-width all-zero input is rejected. -/
def ofBeBytes? (b : Bytes) : Option U256 :=
  if b.size ≤ 32 then some (ofNat (Uint.ofBeBytes b)) else none

/-- Minimal big-endian output; `ethereum_types/numeric.py:477–484`. -/
def toBeBytes (x : U256) : Bytes := Uint.toBeBytes x.toNat

/-- Exact output has the original complete unsigned numeric value. -/
theorem toNat_toBeBytes32 (x : U256) : (toBeBytes32 x).toNat = x.toNat :=
  FixedBytes.toNat_ofNat_of_lt x.toNat (toNat_lt x)

/-- Exact output has the promised fixed byte length. -/
theorem size_toBeBytes32 (x : U256) : (toBeBytes32 x).toBytes.size = 32 :=
  FixedBytes.size_toBytes _

/-- Little-endian output is precisely the reversal of big-endian output. -/
theorem toBytes_toLeBytes32 (x : U256) :
    (toLeBytes32 x).toBytes =
      Bytes.ofList (Bytes.toList (toBeBytes32 x).toBytes).reverse :=
  FixedBytes.toBytes_ofLeNat_eq_reverse x.toNat

/-- Little-endian output has the promised fixed byte length. -/
theorem size_toLeBytes32 (x : U256) : (toLeBytes32 x).toBytes.size = 32 :=
  FixedBytes.size_toBytes _

/-- Fixed big-endian output decodes to the exact input. -/
theorem ofBeBytes_toBeBytes32 (x : U256) :
    Uint.ofBeBytes (toBeBytes32 x).toBytes = x.toNat := by
  rw [ofBeBytes_toBytes, toNat_toBeBytes32]

/-- Fixed little-endian output decodes to the exact input. -/
theorem ofLeBytes_toLeBytes32 (x : U256) :
    Uint.ofLeBytes (toLeBytes32 x).toBytes = x.toNat := by
  rw [Uint.ofLeBytes_eq_reverse, toBytes_toLeBytes32, Bytes.toList_ofList,
    List.reverse_reverse]
  rw [Bytes.ofList_toList]
  exact ofBeBytes_toBeBytes32 x

/-- Success is precisely the width check and the unreduced endian value. -/
theorem ofBeBytes?_eq_some_iff (b : Bytes) (x : U256) :
    ofBeBytes? b = some x ↔ b.size ≤ 32 ∧ x.toNat = Uint.ofBeBytes b := by
  unfold ofBeBytes?
  split
  · next h =>
    have hr : Uint.ofBeBytes b < 2 ^ 256 :=
      Nat.lt_of_lt_of_le (Uint.ofBeBytes_lt b)
        (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Option.some.injEq, ← toNat_inj, toNat_ofNat_of_lt hr]
    exact ⟨fun he ↦ ⟨h, he.symm⟩, fun hx ↦ hx.2.symm⟩
  · next h => simp [h]

/-- Over-width input is the only decoding failure, regardless of leading zeros. -/
theorem ofBeBytes?_eq_none_iff (b : Bytes) :
    ofBeBytes? b = none ↔ 32 < b.size := by
  simp [ofBeBytes?, Nat.not_le]

/-- Checked decoding inverts the fixed big-endian output. -/
theorem ofBeBytes?_toBeBytes32 (x : U256) :
    ofBeBytes? (toBeBytes32 x).toBytes = some x := by
  apply (ofBeBytes?_eq_some_iff _ _).mpr
  exact ⟨by rw [size_toBeBytes32]; exact Nat.le_refl _, (ofBeBytes_toBeBytes32 x).symm⟩

/-- Minimal word output is the unbounded encoding of its public unsigned model. -/
theorem toBeBytes_eq (x : U256) : toBeBytes x = Uint.toBeBytes x.toNat := rfl

/-- The exact minimal byte-count criterion follows the public unsigned model. -/
theorem size_toBeBytes_le_iff (x : U256) (k : Nat) :
    (toBeBytes x).size ≤ k ↔ x.toNat < 2 ^ (8 * k) :=
  Uint.size_toBeBytes_le_iff x.toNat k

/-- Empty minimal word output occurs exactly at the zero unsigned value. -/
theorem toBeBytes_eq_empty_iff (x : U256) :
    toBeBytes x = Bytes.empty ↔ x = zero := by
  rw [toBeBytes_eq, Uint.toBeBytes_eq_empty_iff, ← toNat_zero, toNat_inj]

/-- Minimal output never exceeds the word's full byte width. -/
theorem size_toBeBytes_le (x : U256) : (toBeBytes x).size ≤ 32 :=
  (Uint.size_toBeBytes_le_iff _ _).mpr (toNat_lt x)

/-- Decoding minimal output reconstructs the original word. -/
theorem ofBeBytes?_toBeBytes (x : U256) : ofBeBytes? (toBeBytes x) = some x := by
  apply (ofBeBytes?_eq_some_iff _ _).mpr
  exact ⟨size_toBeBytes_le x, (Uint.ofBeBytes_toBeBytes x.toNat).symm⟩

/-- Minimal word output has no leading zero byte for a nonzero unsigned value. -/
theorem toList_toBeBytes_head_ne_zero (x : U256) (h : x.toNat ≠ 0) :
    (Bytes.toList (toBeBytes x)).head? ≠ some 0 :=
  Uint.toList_toBeBytes_head_ne_zero x.toNat h

/-- Zero has empty minimal word output. -/
theorem toBeBytes_zero : toBeBytes zero = Bytes.empty := Uint.toBeBytes_zero

/-- Total exact-32 big-endian construction; `ethereum_types/numeric.py:566`.
Its input type guarantees the source length check. -/
def ofBeBytes32 (b : Bytes32) : U256 := ofNat b.toNat

/-- Exact-32 construction preserves its byte value without reduction. -/
theorem toNat_ofBeBytes32 (b : Bytes32) : (ofBeBytes32 b).toNat = b.toNat :=
  toNat_ofNat_of_lt (FixedBytes.toNat_lt b)

/-- Total exact-32 construction inverts fixed output. -/
theorem ofBeBytes32_toBeBytes32 (x : U256) : ofBeBytes32 (toBeBytes32 x) = x := by
  apply toNat_inj.mp
  rw [toNat_ofBeBytes32, toNat_toBeBytes32]

/-- Fixed output inverts exact-32 construction. -/
theorem toBeBytes32_ofBeBytes32 (b : Bytes32) : toBeBytes32 (ofBeBytes32 b) = b := by
  apply FixedBytes.toNat_inj.mp
  rw [toNat_toBeBytes32, toNat_ofBeBytes32]

end U256

namespace U64

/-- Exact big-endian output; `ethereum_types/numeric.py:459`. -/
def toBeBytes8 (x : U64) : FixedBytes 8 := FixedBytes.ofNat x.toNat

/-- Exact little-endian output; `ethereum_types/numeric.py:452`. -/
def toLeBytes8 (x : U64) : FixedBytes 8 := FixedBytes.ofLeNat x.toNat

/-- Big-endian decoding checks source byte length before numeric interpretation;
`ethereum_types/numeric.py:566–577`. Even over-width all-zero input is rejected. -/
def ofBeBytes? (b : Bytes) : Option U64 :=
  if b.size ≤ 8 then some (ofNat (Uint.ofBeBytes b)) else none

/-- Little-endian decoding checks length before numeric interpretation;
`ethereum_types/numeric.py:580–591`. -/
def ofLeBytes? (b : Bytes) : Option U64 :=
  if b.size ≤ 8 then some (ofNat (Uint.ofLeBytes b)) else none

/-- Minimal big-endian output; `ethereum_types/numeric.py:477–484`. -/
def toBeBytes (x : U64) : Bytes := Uint.toBeBytes x.toNat

/-- Exact output has the original complete unsigned numeric value. -/
theorem toNat_toBeBytes8 (x : U64) : (toBeBytes8 x).toNat = x.toNat :=
  FixedBytes.toNat_ofNat_of_lt x.toNat (toNat_lt x)

/-- Exact output has the promised fixed byte length. -/
theorem size_toBeBytes8 (x : U64) : (toBeBytes8 x).toBytes.size = 8 :=
  FixedBytes.size_toBytes _

/-- Little-endian output is precisely the reversal of big-endian output. -/
theorem toBytes_toLeBytes8 (x : U64) :
    (toLeBytes8 x).toBytes =
      Bytes.ofList (Bytes.toList (toBeBytes8 x).toBytes).reverse :=
  FixedBytes.toBytes_ofLeNat_eq_reverse x.toNat

/-- Little-endian output has the promised fixed byte length. -/
theorem size_toLeBytes8 (x : U64) : (toLeBytes8 x).toBytes.size = 8 :=
  FixedBytes.size_toBytes _

/-- Fixed big-endian output decodes to the exact input. -/
theorem ofBeBytes_toBeBytes8 (x : U64) :
    Uint.ofBeBytes (toBeBytes8 x).toBytes = x.toNat := by
  rw [ofBeBytes_toBytes, toNat_toBeBytes8]

/-- Fixed little-endian output decodes to the exact input. -/
theorem ofLeBytes_toLeBytes8 (x : U64) :
    Uint.ofLeBytes (toLeBytes8 x).toBytes = x.toNat := by
  rw [Uint.ofLeBytes_eq_reverse, toBytes_toLeBytes8, Bytes.toList_ofList,
    List.reverse_reverse]
  rw [Bytes.ofList_toList]
  exact ofBeBytes_toBeBytes8 x

/-- Success is precisely the width check and the unreduced endian value. -/
theorem ofBeBytes?_eq_some_iff (b : Bytes) (x : U64) :
    ofBeBytes? b = some x ↔ b.size ≤ 8 ∧ x.toNat = Uint.ofBeBytes b := by
  unfold ofBeBytes?
  split
  · next h =>
    have hr : Uint.ofBeBytes b < 2 ^ 64 :=
      Nat.lt_of_lt_of_le (Uint.ofBeBytes_lt b)
        (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Option.some.injEq, ← toNat_inj, toNat_ofNat_of_lt hr]
    exact ⟨fun he ↦ ⟨h, he.symm⟩, fun hx ↦ hx.2.symm⟩
  · next h => simp [h]

/-- Over-width input is the only decoding failure, regardless of leading zeros. -/
theorem ofBeBytes?_eq_none_iff (b : Bytes) :
    ofBeBytes? b = none ↔ 8 < b.size := by
  simp [ofBeBytes?, Nat.not_le]

/-- Success is precisely the width check and the unreduced endian value. -/
theorem ofLeBytes?_eq_some_iff (b : Bytes) (x : U64) :
    ofLeBytes? b = some x ↔ b.size ≤ 8 ∧ x.toNat = Uint.ofLeBytes b := by
  unfold ofLeBytes?
  split
  · next h =>
    have hr : Uint.ofLeBytes b < 2 ^ 64 :=
      Nat.lt_of_lt_of_le (Uint.ofLeBytes_lt b)
        (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Option.some.injEq, ← toNat_inj, toNat_ofNat_of_lt hr]
    exact ⟨fun he ↦ ⟨h, he.symm⟩, fun hx ↦ hx.2.symm⟩
  · next h => simp [h]

/-- Over-width input is the only decoding failure, regardless of leading zeros. -/
theorem ofLeBytes?_eq_none_iff (b : Bytes) :
    ofLeBytes? b = none ↔ 8 < b.size := by
  simp [ofLeBytes?, Nat.not_le]

/-- Checked decoding inverts the fixed big-endian output. -/
theorem ofBeBytes?_toBeBytes8 (x : U64) :
    ofBeBytes? (toBeBytes8 x).toBytes = some x := by
  apply (ofBeBytes?_eq_some_iff _ _).mpr
  exact ⟨by rw [size_toBeBytes8]; exact Nat.le_refl _, (ofBeBytes_toBeBytes8 x).symm⟩

/-- Minimal word output is the unbounded encoding of its public unsigned model. -/
theorem toBeBytes_eq (x : U64) : toBeBytes x = Uint.toBeBytes x.toNat := rfl

/-- The exact minimal byte-count criterion follows the public unsigned model. -/
theorem size_toBeBytes_le_iff (x : U64) (k : Nat) :
    (toBeBytes x).size ≤ k ↔ x.toNat < 2 ^ (8 * k) :=
  Uint.size_toBeBytes_le_iff x.toNat k

/-- Empty minimal word output occurs exactly at the zero unsigned value. -/
theorem toBeBytes_eq_empty_iff (x : U64) :
    toBeBytes x = Bytes.empty ↔ x = zero := by
  rw [toBeBytes_eq, Uint.toBeBytes_eq_empty_iff, ← toNat_zero, toNat_inj]

/-- Minimal output never exceeds the word's full byte width. -/
theorem size_toBeBytes_le (x : U64) : (toBeBytes x).size ≤ 8 :=
  (Uint.size_toBeBytes_le_iff _ _).mpr (toNat_lt x)

/-- Decoding minimal output reconstructs the original word. -/
theorem ofBeBytes?_toBeBytes (x : U64) : ofBeBytes? (toBeBytes x) = some x := by
  apply (ofBeBytes?_eq_some_iff _ _).mpr
  exact ⟨size_toBeBytes_le x, (Uint.ofBeBytes_toBeBytes x.toNat).symm⟩

/-- Minimal word output has no leading zero byte for a nonzero unsigned value. -/
theorem toList_toBeBytes_head_ne_zero (x : U64) (h : x.toNat ≠ 0) :
    (Bytes.toList (toBeBytes x)).head? ≠ some 0 :=
  Uint.toList_toBeBytes_head_ne_zero x.toNat h

/-- Zero has empty minimal word output. -/
theorem toBeBytes_zero : toBeBytes zero = Bytes.empty := Uint.toBeBytes_zero

/-- Checked little-endian decoding inverts the fixed little-endian output. -/
theorem ofLeBytes?_toLeBytes8 (x : U64) : ofLeBytes? (toLeBytes8 x).toBytes = some x := by
  apply (ofLeBytes?_eq_some_iff _ _).mpr
  exact ⟨by rw [size_toLeBytes8]; exact Nat.le_refl _, (ofLeBytes_toLeBytes8 x).symm⟩

end U64

namespace Address

/-- Low 20 bytes of the exact 32-byte encoding; EELS
`src/ethereum/forks/amsterdam/utils/address.py:24,39` (`to_address_masked`). -/
private def maskedAddressReference (x : U256) : Address :=
  (ofBytes? (Bytes.ofList ((Bytes.toList (U256.toBeBytes32 x).toBytes).drop 12))).get (by
    apply Option.isSome_iff_ne_none.mpr
    intro hn
    apply ofBytes?_eq_none_iff.mp hn
    rw [← Bytes.length_toList, Bytes.toList_ofList, List.length_drop,
      Bytes.length_toList, U256.size_toBeBytes32])

/-- Mask an unsigned word directly through the public numeric address model;
EELS `src/ethereum/forks/amsterdam/utils/address.py:24,39`. -/
def ofU256Masked (x : U256) : Address := ofNat x.toNat

/-- Embed the complete address value in a word; EELS
`src/ethereum/forks/amsterdam/vm/instructions/environment.py:52,107,130`. -/
def toU256 (x : Address) : U256 := U256.ofNat x.toNat

/-- Masking retains precisely the final 20 bytes, including leading zeros. -/
private theorem toBytes_maskedAddressReference (x : U256) :
    (maskedAddressReference x).toBytes =
      Bytes.ofList ((Bytes.toList (U256.toBeBytes32 x).toBytes).drop 12) := by
  apply (ofBytes?_eq_some_iff.mp ?_).2
  exact (Option.some_get _).symm

/-- Masking is exactly reduction modulo 2^160 of the complete word value. -/
private theorem toNat_maskedAddressReference (x : U256) :
    (maskedAddressReference x).toNat = x.toNat % 2 ^ 160 := by
  let bs := Bytes.toList (U256.toBeBytes32 x).toBytes
  have hl : bs.length = 32 := by rw [Bytes.length_toList, U256.size_toBeBytes32]
  have hs : (bs.drop 12).length = 20 := by rw [List.length_drop, hl]
  have hd : Uint.ofBeBytes (Bytes.ofList bs) = x.toNat := by
    rw [Bytes.ofList_toList]
    exact U256.ofBeBytes_toBeBytes32 x
  have he := decode_append (bs.take 12) (bs.drop 12)
  rw [List.take_append_drop, hd, hs] at he
  have hr : Uint.ofBeBytes (Bytes.ofList (bs.drop 12)) < 256 ^ 20 := by
    have h := Uint.ofBeBytes_lt (Bytes.ofList (bs.drop 12))
    simpa only [Bytes.size_ofList, hs, radix_eq] using h
  have hm : x.toNat % 256 ^ 20 = Uint.ofBeBytes (Bytes.ofList (bs.drop 12)) := by
    simp only [he, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt hr]
  rw [toNat_eq_fold, toBytes_maskedAddressReference, ← Uint.ofBeBytes_eq_fold]
  rw [← hm, radix_eq]

/-- Masking is exactly reduction modulo 2^160 of the complete word value. -/
theorem toNat_ofU256Masked (x : U256) : (ofU256Masked x).toNat = x.toNat % 2 ^ 160 :=
  toNat_ofNat x.toNat

private theorem ofU256Masked_eq_reference (x : U256) :
    ofU256Masked x = maskedAddressReference x := by
  apply toNat_inj.mp
  rw [toNat_ofU256Masked, toNat_maskedAddressReference]

/-- Masking retains precisely the final 20 bytes, including leading zeros. -/
theorem toBytes_ofU256Masked (x : U256) :
    (ofU256Masked x).toBytes =
      Bytes.ofList ((Bytes.toList (U256.toBeBytes32 x).toBytes).drop 12) := by
  rw [ofU256Masked_eq_reference, toBytes_maskedAddressReference]

/-- The numeric conversion retains exactly the final twenty public hash bytes,
including leading zeros. -/
theorem toBytes_ofNat_toNat (hash : Hash32) :
    (Address.ofNat hash.toNat).toBytes = Bytes.ofList (hash.toBytes.toList.drop 12) := by
  have h : Address.ofNat hash.toNat =
      Address.ofU256Masked (U256.ofBeBytes32 hash.toBytes32) := by
    apply Address.toNat_inj.mp
    rw [Address.toNat_ofNat, Address.toNat_ofU256Masked, U256.toNat_ofBeBytes32,
      Hash32.toNat_toBytes32]
  rw [h, Address.toBytes_ofU256Masked, U256.toBeBytes32_ofBeBytes32,
    Hash32.toBytes_toBytes32]

/-- Embedding an address in a word preserves its complete numeric value. -/
theorem toNat_toU256 (x : Address) : x.toU256.toNat = x.toNat := by
  apply U256.toNat_ofNat_of_lt
  exact Nat.lt_trans (toNat_lt x) (by decide)

/-- Masking an embedded address reconstructs the address. -/
theorem ofU256Masked_toU256 (x : Address) : ofU256Masked x.toU256 = x := by
  apply toNat_inj.mp
  rw [toNat_ofU256Masked, toNat_toU256, Nat.mod_eq_of_lt (toNat_lt x)]

/-- Embedding a masked word has exactly its low 160 bits. -/
theorem toNat_toU256_ofU256Masked (x : U256) :
    (ofU256Masked x).toU256.toNat = x.toNat % 2 ^ 160 := by
  rw [toNat_toU256, toNat_ofU256Masked]

end Address

end STFSpec.Base
