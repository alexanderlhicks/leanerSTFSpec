/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.FixedBytes
import STFSpec.Base.Numeric
import STFSpec.Base.U256
import STFSpec.Base.U64

/-!
# Integer byte conversions

Library `EthBase`: checked bounded decoding, exact-width endian output, minimal
big-endian unsigned output and masked addresses. All consumers use public models.
Spec guidance: `STFSpec/informal/modules/EthBase.md`.
Reference: locked `ethereum-types` 0.4.1, `ethereum_types/numeric.py:424,477,566,580`.
-/

namespace STFSpec.Base

private def decodeReference : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat * 256 ^ bs.length + decodeReference bs

private def encodeReference : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, v => UInt8.ofNat (v / 256 ^ n) :: encodeReference n (v % 256 ^ n)

private theorem encode_length (n v : Nat) : (encodeReference n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp only [encodeReference, List.length_cons, ih]

private theorem decode_lt (bs : List UInt8) : decodeReference bs < 256 ^ bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    simp only [decodeReference, List.length_cons, Nat.pow_succ]
    have hb : b.toNat < 256 := b.toNat_lt
    have hp : 0 < 256 ^ bs.length := Nat.pow_pos (by decide)
    have := Nat.mul_le_mul_right (256 ^ bs.length) (show b.toNat + 1 ≤ 256 by omega)
    simp only [Nat.add_mul, Nat.one_mul] at this
    omega

private theorem decode_encode (n v : Nat) (h : v < 256 ^ n) :
    decodeReference (encodeReference n v) = v := by
  induction n generalizing v with
  | zero =>
    have hv : v = 0 := by simpa using h
    simp [encodeReference, decodeReference, hv]
  | succ n ih =>
    simp only [encodeReference, decodeReference, encode_length]
    have hp : 0 < 256 ^ n := Nat.pow_pos (by decide)
    have hd : v / 256 ^ n < 256 := by
      apply (Nat.div_lt_iff_lt_mul hp).2
      simpa only [Nat.pow_succ, Nat.mul_comm] using h
    rw [UInt8.toNat_ofNat_of_lt' hd, ih _ (Nat.mod_lt _ hp)]
    simpa only [Nat.mul_comm] using Nat.div_add_mod v (256 ^ n)

-- The Horner decoder traverses each input byte once.
private def decodeFast (bs : List UInt8) : Nat :=
  bs.foldl (fun acc b ↦ 256 * acc + b.toNat) 0

private theorem decode_fold (bs : List UInt8) (acc : Nat) :
    bs.foldl (fun acc b ↦ 256 * acc + b.toNat) acc =
      acc * 256 ^ bs.length + decodeReference bs := by
  induction bs generalizing acc with
  | nil => simp [decodeReference]
  | cons b bs ih =>
    simp only [List.foldl_cons, ih, List.length_cons, decodeReference, Nat.pow_succ]
    simp only [Nat.add_mul]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.add_assoc]

private theorem decodeFast_eq (bs : List UInt8) : decodeFast bs = decodeReference bs := by
  simp [decodeFast, decode_fold]

-- The encoder reuses one decreasing positional power across its output bytes.
private def encodeAux : Nat → Nat → Nat → List UInt8
  | 0, _, _ => []
  | n + 1, v, p => UInt8.ofNat (v / p) :: encodeAux n (v % p) (p / 256)

private theorem encodeAux_eq (n v : Nat) :
    encodeAux (n + 1) v (256 ^ n) = encodeReference (n + 1) v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    simp only [encodeAux, encodeReference]
    have hp : 256 ^ (n + 1) / 256 = 256 ^ n := by
      rw [Nat.pow_succ, Nat.mul_div_left _ (by decide)]
    rw [hp]
    exact congrArg (List.cons _) (ih _)

private def encodeFast (n v : Nat) : List UInt8 :=
  match n with
  | 0 => []
  | n + 1 => encodeAux (n + 1) v (256 ^ n)

private theorem encodeFast_eq (n v : Nat) : encodeFast n v = encodeReference n v := by
  cases n with
  | zero => rfl
  | succ n => exact encodeAux_eq n v

private theorem radix_eq (n : Nat) : 256 ^ n = 2 ^ (8 * n) := by
  rw [Nat.pow_mul]

private def decodeLeReference : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decodeLeReference bs

private theorem decode_append (xs ys : List UInt8) :
    decodeReference (xs ++ ys) =
      decodeReference xs * 256 ^ ys.length + decodeReference ys := by
  induction xs with
  | nil => simp [decodeReference]
  | cons b bs ih =>
    simp only [List.cons_append, decodeReference, List.length_append, ih,
      Nat.pow_add, Nat.add_mul, Nat.add_assoc, Nat.mul_assoc]

private theorem decode_reverse (bs : List UInt8) :
    decodeReference bs.reverse = decodeLeReference bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.reverse_cons, decode_append, List.length_singleton,
      Nat.pow_one, decodeReference, List.length_nil, Nat.pow_zero, Nat.mul_one,
      Nat.add_zero, ih, decodeLeReference]
    omega

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

namespace Uint

/-- Unbounded big-endian decoding; `ethereum_types/numeric.py:523`.
Every byte length is accepted, including leading zero bytes. -/
def ofBeBytes (b : Bytes) : Nat := b.foldl (fun acc byte ↦ 256 * acc + byte.toNat) 0

/-- Unbounded little-endian decoding; `ethereum_types/numeric.py:531`. -/
def ofLeBytes (b : Bytes) : Nat := decodeFast (Bytes.toList b).reverse

/-- Minimal big-endian output; `ethereum_types/numeric.py:477–484`.
Zero produces empty bytes; the byte loop divides by 256 at each step. -/
def toBeBytes (n : Nat) : Bytes := Bytes.ofList (minimalLe n).reverse

/-- Big-endian decoding is the positional Horner fold over the public byte model. -/
theorem ofBeBytes_eq_fold (b : Bytes) :
    ofBeBytes b = (Bytes.toList b).foldl (fun acc b ↦ 256 * acc + b.toNat) 0 :=
  Bytes.foldl_eq _ _ _

/-- Little-endian decoding is big-endian decoding of reversed byte observations. -/
theorem ofLeBytes_eq_reverse (b : Bytes) :
    ofLeBytes b = ofBeBytes (Bytes.ofList (Bytes.toList b).reverse) := by
  rw [ofBeBytes_eq_fold, Bytes.toList_ofList]
  rfl

/-- The complete decoded value fits the input's byte length. -/
theorem ofBeBytes_lt (b : Bytes) : ofBeBytes b < 2 ^ (8 * b.size) := by
  rw [ofBeBytes_eq_fold]
  change decodeFast (Bytes.toList b) < 2 ^ (8 * b.size)
  rw [decodeFast_eq, ← radix_eq, ← Bytes.length_toList]
  exact decode_lt _

/-- The complete little-endian value fits the input's byte length. -/
theorem ofLeBytes_lt (b : Bytes) : ofLeBytes b < 2 ^ (8 * b.size) := by
  rw [ofLeBytes, decodeFast_eq, ← radix_eq, ← Bytes.length_toList,
    ← List.length_reverse (as := Bytes.toList b)]
  exact decode_lt _

/-- Minimal output reconstructs every unbounded input without any width limit. -/
theorem ofBeBytes_toBeBytes (n : Nat) : ofBeBytes (toBeBytes n) = n := by
  rw [ofBeBytes_eq_fold, toBeBytes, Bytes.toList_ofList]
  change decodeFast (minimalLe n).reverse = n
  rw [decodeFast_eq, decode_reverse, decode_minimalLe]

/-- Minimal output uses at most `k` bytes exactly when the value fits those bytes. -/
theorem size_toBeBytes_le_iff (n k : Nat) :
    (toBeBytes n).size ≤ k ↔ n < 2 ^ (8 * k) := by
  rw [← Bytes.length_toList, toBeBytes, Bytes.toList_ofList,
    List.length_reverse, minimalLe_length_le_iff, radix_eq]

/-- Zero has empty minimal big-endian output. -/
theorem toBeBytes_zero : toBeBytes 0 = Bytes.empty := by
  apply Bytes.ext
  rw [toBeBytes, Bytes.toList_ofList, Bytes.toList_empty, minimalLe,
    ite_eq_left rfl, List.reverse_nil]

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
  rw [toBeBytes, Bytes.toList_ofList]
  exact minimalLe_reverse_head n h

end Uint

private def fixedOutput (n v : Nat) : FixedBytes n :=
  (FixedBytes.ofBytes? (Bytes.ofList (encodeFast n v))).get (by
    apply Option.isSome_iff_ne_none.mpr
    intro hn
    apply (FixedBytes.ofBytes?_eq_none_iff.mp hn)
    rw [← Bytes.length_toList, Bytes.toList_ofList, encodeFast_eq, encode_length])

private theorem bytes_fixedOutput (n v : Nat) :
    (fixedOutput n v).toBytes = Bytes.ofList (encodeFast n v) := by
  apply (FixedBytes.ofBytes?_eq_some_iff.mp ?_).2
  exact (Option.some_get _).symm

private theorem nat_fixedOutput (n v : Nat) (h : v < 2 ^ (8 * n)) :
    (fixedOutput n v).toNat = v := by
  rw [FixedBytes.toNat_eq_fold, bytes_fixedOutput]
  change decodeFast (Bytes.toList (Bytes.ofList (encodeFast n v))) = v
  rw [Bytes.toList_ofList, decodeFast_eq, encodeFast_eq]
  exact decode_encode n v (by simpa only [radix_eq] using h)

private theorem ofBeBytes_toBytes {n : Nat} (x : FixedBytes n) :
    Uint.ofBeBytes x.toBytes = x.toNat := by
  rw [Uint.ofBeBytes_eq_fold, FixedBytes.toNat_eq_fold]

namespace Uint

/-- Checked 32-byte output; `ethereum_types/numeric.py:424`.
Rejects values at least 2^256 before producing the fixed-width result. -/
def toBeBytes32? (n : Nat) : Option Bytes32 :=
  if n < 2 ^ 256 then some (fixedOutput 32 n) else none

/-- Fixed output succeeds exactly with the complete unreduced numeric input. -/
theorem toBeBytes32?_eq_some_iff (n : Nat) (x : Bytes32) :
    toBeBytes32? n = some x ↔ n < 2 ^ 256 ∧ x.toNat = n := by
  unfold toBeBytes32?
  split
  · next h =>
    simp only [Option.some.injEq]
    have hm := nat_fixedOutput 32 n h
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
def toBeBytes32 (x : U256) : FixedBytes 32 := fixedOutput 32 x.toNat

/-- Exact little-endian output; `ethereum_types/numeric.py:495`. -/
def toLeBytes32 (x : U256) : FixedBytes 32 :=
  (FixedBytes.ofBytes? (Bytes.ofList (Bytes.toList (toBeBytes32 x).toBytes).reverse)).get (by
    apply Option.isSome_iff_ne_none.mpr
    intro hn
    apply (FixedBytes.ofBytes?_eq_none_iff.mp hn)
    rw [← Bytes.length_toList, Bytes.toList_ofList, List.length_reverse,
      Bytes.length_toList, FixedBytes.size_toBytes])

/-- Big-endian decoding checks source byte length before numeric interpretation;
`ethereum_types/numeric.py:566–577`. Even over-width all-zero input is rejected. -/
def ofBeBytes? (b : Bytes) : Option U256 :=
  if b.size ≤ 32 then some (ofNat (Uint.ofBeBytes b)) else none

/-- Minimal big-endian output; `ethereum_types/numeric.py:477–484`. -/
def toBeBytes (x : U256) : Bytes := Uint.toBeBytes x.toNat

/-- Exact output has the original complete unsigned numeric value. -/
theorem toNat_toBeBytes32 (x : U256) : (toBeBytes32 x).toNat = x.toNat :=
  nat_fixedOutput 32 x.toNat (toNat_lt x)

/-- Exact output has the promised fixed byte length. -/
theorem size_toBeBytes32 (x : U256) : (toBeBytes32 x).toBytes.size = 32 :=
  FixedBytes.size_toBytes _

/-- Little-endian output is precisely the reversal of big-endian output. -/
theorem toBytes_toLeBytes32 (x : U256) :
    (toLeBytes32 x).toBytes =
      Bytes.ofList (Bytes.toList (toBeBytes32 x).toBytes).reverse := by
  apply (FixedBytes.ofBytes?_eq_some_iff.mp ?_).2
  exact (Option.some_get _).symm

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
  rw [toBytes_toLeBytes32, Uint.ofLeBytes, Bytes.toList_ofList,
    List.reverse_reverse]
  have h := ofBeBytes_toBeBytes32 x
  rw [Uint.ofBeBytes_eq_fold] at h
  exact h

/-- Success is precisely the width check and the unreduced endian value. -/
theorem ofBeBytes?_eq_some_iff (b : Bytes) (x : U256) :
    ofBeBytes? b = some x ↔ b.size ≤ 32 ∧ x.toNat = Uint.ofBeBytes b := by
  unfold ofBeBytes?
  split
  · next h =>
    have hr : Uint.ofBeBytes b < 2 ^ 256 :=
      Nat.lt_of_lt_of_le (Uint.ofBeBytes_lt b)
        (Nat.pow_le_pow_right (by decide) (by omega))
    have hm := toNat_ofNat_of_lt hr
    simp only [Option.some.injEq]
    constructor
    · intro he
      subst x
      exact ⟨h, hm⟩
    · intro hx
      apply toNat_inj.mp
      rw [hm, hx.2]
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
def toBeBytes8 (x : U64) : FixedBytes 8 := fixedOutput 8 x.toNat

/-- Exact little-endian output; `ethereum_types/numeric.py:452`. -/
def toLeBytes8 (x : U64) : FixedBytes 8 :=
  (FixedBytes.ofBytes? (Bytes.ofList (Bytes.toList (toBeBytes8 x).toBytes).reverse)).get (by
    apply Option.isSome_iff_ne_none.mpr
    intro hn
    apply (FixedBytes.ofBytes?_eq_none_iff.mp hn)
    rw [← Bytes.length_toList, Bytes.toList_ofList, List.length_reverse,
      Bytes.length_toList, FixedBytes.size_toBytes])

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
  nat_fixedOutput 8 x.toNat (toNat_lt x)

/-- Exact output has the promised fixed byte length. -/
theorem size_toBeBytes8 (x : U64) : (toBeBytes8 x).toBytes.size = 8 :=
  FixedBytes.size_toBytes _

/-- Little-endian output is precisely the reversal of big-endian output. -/
theorem toBytes_toLeBytes8 (x : U64) :
    (toLeBytes8 x).toBytes =
      Bytes.ofList (Bytes.toList (toBeBytes8 x).toBytes).reverse := by
  apply (FixedBytes.ofBytes?_eq_some_iff.mp ?_).2
  exact (Option.some_get _).symm

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
  rw [toBytes_toLeBytes8, Uint.ofLeBytes, Bytes.toList_ofList,
    List.reverse_reverse]
  have h := ofBeBytes_toBeBytes8 x
  rw [Uint.ofBeBytes_eq_fold] at h
  exact h

/-- Success is precisely the width check and the unreduced endian value. -/
theorem ofBeBytes?_eq_some_iff (b : Bytes) (x : U64) :
    ofBeBytes? b = some x ↔ b.size ≤ 8 ∧ x.toNat = Uint.ofBeBytes b := by
  unfold ofBeBytes?
  split
  · next h =>
    have hr : Uint.ofBeBytes b < 2 ^ 64 :=
      Nat.lt_of_lt_of_le (Uint.ofBeBytes_lt b)
        (Nat.pow_le_pow_right (by decide) (by omega))
    have hm := toNat_ofNat_of_lt hr
    simp only [Option.some.injEq]
    constructor
    · intro he
      subst x
      exact ⟨h, hm⟩
    · intro hx
      apply toNat_inj.mp
      rw [hm, hx.2]
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
    have hm := toNat_ofNat_of_lt hr
    simp only [Option.some.injEq]
    constructor
    · intro he
      subst x
      exact ⟨h, hm⟩
    · intro hx
      apply toNat_inj.mp
      rw [hm, hx.2]
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
def ofU256Masked (x : U256) : Address :=
  (ofBytes? (Bytes.ofList ((Bytes.toList (U256.toBeBytes32 x).toBytes).drop 12))).get (by
    apply Option.isSome_iff_ne_none.mpr
    intro hn
    apply ofBytes?_eq_none_iff.mp hn
    rw [← Bytes.length_toList, Bytes.toList_ofList, List.length_drop,
      Bytes.length_toList, U256.size_toBeBytes32])

/-- The address embeds as its full unsigned big-endian value in a word. -/
def toU256 (x : Address) : U256 := U256.ofNat x.toNat

/-- Masking retains precisely the final 20 bytes, including leading zeros. -/
theorem toBytes_ofU256Masked (x : U256) :
    (ofU256Masked x).toBytes =
      Bytes.ofList ((Bytes.toList (U256.toBeBytes32 x).toBytes).drop 12) := by
  apply (ofBytes?_eq_some_iff.mp ?_).2
  exact (Option.some_get _).symm

/-- Masking is exactly reduction modulo 2^160 of the complete word value. -/
theorem toNat_ofU256Masked (x : U256) : (ofU256Masked x).toNat = x.toNat % 2 ^ 160 := by
  let bs := Bytes.toList (U256.toBeBytes32 x).toBytes
  have hl : bs.length = 32 := by rw [Bytes.length_toList, U256.size_toBeBytes32]
  have hs : (bs.drop 12).length = 20 := by rw [List.length_drop, hl]
  have hd : decodeReference bs = x.toNat := by
    rw [← decodeFast_eq]
    have h := U256.ofBeBytes_toBeBytes32 x
    rw [Uint.ofBeBytes_eq_fold] at h
    exact h
  have he := decode_append (bs.take 12) (bs.drop 12)
  rw [List.take_append_drop, hd, hs] at he
  have hr : decodeReference (bs.drop 12) < 256 ^ 20 := by
    simpa only [hs] using decode_lt (bs.drop 12)
  have hm : x.toNat % 256 ^ 20 = decodeReference (bs.drop 12) := by
    simp only [he, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt hr]
  rw [toNat_eq_fold, toBytes_ofU256Masked, Bytes.toList_ofList]
  change decodeFast (bs.drop 12) = x.toNat % 2 ^ 160
  rw [decodeFast_eq, ← hm, radix_eq]

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
