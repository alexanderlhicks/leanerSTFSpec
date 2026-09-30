/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.Bytes
import Init.Data.BitVec.Lemmas
import Init.Data.UInt.Lemmas
import Init.Data.Order.Ord
import Init.Omega

/-!
# Fixed-width byte values

Library `EthBase`: exact-length byte construction, big-endian numeric observers,
and lawful lexicographic ordering at every width, including zero.
Private radix helpers relate linear byte loops to legible positional models.

Spec guidance: `STFSpec/informal/modules/EthBase.md`.
Reference: locked `ethereum-types` 0.4.1, `ethereum_types/bytes.py:29`.
-/

namespace STFSpec.Base

/-! ### Private positional models and executable byte loops -/

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

private theorem encode_decode (bs : List UInt8) :
    encodeReference bs.length (decodeReference bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, decodeReference, encodeReference]
    have hp : 0 < 256 ^ bs.length := Nat.pow_pos (by decide)
    have ht := decode_lt bs
    have hd : (b.toNat * 256 ^ bs.length + decodeReference bs) / 256 ^ bs.length = b.toNat := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt ht]
      omega
    have hm : (b.toNat * 256 ^ bs.length + decodeReference bs) % 256 ^ bs.length =
        decodeReference bs := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt ht]
    rw [hd, hm, ih, UInt8.ofNat_toNat]

private theorem compare_digit (a b r s p : Nat) (hr : r < p) (hs : s < p) :
    compare (a * p + r) (b * p + s) = (compare a b).then (compare r s) := by
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · have hm := Nat.mul_le_mul_right p (show a + 1 ≤ b by omega)
    simp only [Nat.add_mul, Nat.one_mul] at hm
    have h : a * p + r < b * p + s := by omega
    rw [Nat.compare_eq_lt.mpr h, Nat.compare_eq_lt.mpr hab]
    rfl
  · subst b
    simp only [Std.compare_self, Ordering.eq_then]
    change compareOfLessAndEq (a * p + r) (a * p + s) = compareOfLessAndEq r s
    simp only [compareOfLessAndEq, Nat.add_lt_add_iff_left, Nat.add_left_cancel_iff]
  · have hm := Nat.mul_le_mul_right p (show b + 1 ≤ a by omega)
    simp only [Nat.add_mul, Nat.one_mul] at hm
    have h : b * p + s < a * p + r := by omega
    rw [Nat.compare_eq_gt.mpr h, Nat.compare_eq_gt.mpr hab]
    rfl

private theorem compare_decode (xs ys : List UInt8) (h : xs.length = ys.length) :
    compare (decodeReference xs) (decodeReference ys) = compare xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [decodeReference]
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      have hl : xs.length = ys.length := by simpa using h
      simp only [decodeReference, ← hl]
      rw [compare_digit _ _ _ _ _ (decode_lt xs) (by simpa [hl] using decode_lt ys)]
      rw [ih _ hl]
      change _ = List.compareLex compare (a :: xs) (b :: ys)
      rw [List.compareLex_cons_cons]
      have hc : compare a b = compare a.toNat b.toNat := by
        change compareOfLessAndEq a b = compareOfLessAndEq a.toNat b.toNat
        simp only [compareOfLessAndEq, UInt8.lt_iff_toNat_lt, UInt8.toNat_inj]
      rw [hc]
      rfl

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

/-! ### Fixed-width values and their public laws -/

private theorem radix_eq (n : Nat) : 256 ^ n = 2 ^ (8 * n) := by
  rw [Nat.pow_mul]

/-- Exact-width bytes; `ethereum_types/bytes.py:16,29`. Width zero is allowed. -/
structure FixedBytes (n : Nat) where
  private ofBitVecRaw ::
  private val : BitVec (8 * n)

namespace FixedBytes

/-- The big-endian numeric value of the exact-width byte sequence. -/
def toNat {n : Nat} (x : FixedBytes n) : Nat := x.val.toNat

/-- Exact-width big-endian bytes; preserves leading zero bytes. -/
def toBytes {n : Nat} (x : FixedBytes n) : Bytes := (encodeFast n x.toNat).toByteArray

/-- Exact-length checked constructor; `ethereum_types/bytes.py:29–37`.
Rejects a wrong length before decoding any byte value, including leading zero bytes. -/
def ofBytes? {n : Nat} (b : Bytes) : Option (FixedBytes n) :=
  if b.size = n then some (ofBitVecRaw (BitVec.ofNat (8 * n) (decodeFast (Bytes.toList b))))
  else none

/-- Every numeric observation fits the entire fixed width. -/
theorem toNat_lt {n : Nat} (x : FixedBytes n) : x.toNat < 2 ^ (8 * n) := x.val.isLt

/-- Equal numeric observations determine equal fixed-width values. -/
theorem toNat_inj {n : Nat} {x y : FixedBytes n} : x.toNat = y.toNat ↔ x = y := by
  constructor
  · intro h
    have hv : x.val = y.val := BitVec.eq_of_toNat_eq h
    cases x
    cases y
    cases hv
    rfl
  · exact congrArg toNat

/-- Decidable equality observes the big-endian numeric value. -/
instance {n : Nat} : DecidableEq (FixedBytes n) := fun x y ↦
  decidable_of_iff (x.toNat = y.toNat) toNat_inj

/-- Numeric big-endian ordering, equal to lexical byte ordering by `compare_toBytes`. -/
instance {n : Nat} : Ord (FixedBytes n) where
  compare := compareOn toNat

/-- Numeric comparison is reflexive. -/
instance {n : Nat} : Std.ReflOrd (FixedBytes n) :=
  inferInstanceAs (Std.ReflCmp (compareOn toNat))

/-- Numeric comparison has the correct orientation. -/
instance {n : Nat} : Std.OrientedOrd (FixedBytes n) :=
  inferInstanceAs (Std.OrientedCmp (compareOn toNat))

/-- Numeric comparison is transitive. -/
instance {n : Nat} : Std.TransOrd (FixedBytes n) :=
  inferInstanceAs (Std.TransCmp (compareOn toNat))

/-- Comparison equality coincides with value equality. -/
instance {n : Nat} : Std.LawfulEqOrd (FixedBytes n) where
  eq_of_compare h := toNat_inj.mp (Nat.compare_eq_eq.mp h)

/-- Exact output length, including the empty output at width zero. -/
theorem size_toBytes {n : Nat} (x : FixedBytes n) : x.toBytes.size = n := by
  rw [← Bytes.length_toList, toBytes, Bytes.toList_toByteArray,
    encodeFast_eq, encode_length]

private theorem decode_toBytes {n : Nat} (x : FixedBytes n) :
    decodeFast (Bytes.toList x.toBytes) = x.toNat := by
  rw [toBytes, Bytes.toList_toByteArray, decodeFast_eq, encodeFast_eq,
    decode_encode _ _ (by simpa only [radix_eq] using toNat_lt x)]

/-- Numeric observation is the big-endian radix-256 fold of the output bytes. -/
theorem toNat_eq_fold {n : Nat} (x : FixedBytes n) :
    x.toNat = (Bytes.toList x.toBytes).foldl (fun acc b ↦ 256 * acc + b.toNat) 0 :=
  (decode_toBytes x).symm

/-- Reconstructing from the exact byte observer returns the value. -/
theorem ofBytes?_toBytes {n : Nat} (x : FixedBytes n) : ofBytes? x.toBytes = some x := by
  simp only [ofBytes?, size_toBytes, ite_true, decode_toBytes]
  congr 1
  apply toNat_inj.mp
  exact Nat.mod_eq_of_lt (toNat_lt x)

private theorem bytes_of_size {n : Nat} (b : Bytes) (h : b.size = n) :
    (ofBitVecRaw (BitVec.ofNat (8 * n) (decodeFast (Bytes.toList b))) :
      FixedBytes n).toBytes = b := by
  have hl : (Bytes.toList b).length = n := by rw [Bytes.length_toList, h]
  have hr : decodeFast (Bytes.toList b) < 2 ^ (8 * n) := by
    rw [decodeFast_eq, ← radix_eq, ← hl]
    exact decode_lt _
  have hr' : decodeReference (Bytes.toList b) < 2 ^ (8 * n) := by
    simpa only [decodeFast_eq] using hr
  apply Bytes.ext
  simp only [toBytes, Bytes.toList_toByteArray, encodeFast_eq,
    toNat, BitVec.toNat_ofNat, decodeFast_eq, Nat.mod_eq_of_lt hr']
  rw [← hl, encode_decode]

/-- Constructor success is precisely exact length and equality of byte contents. -/
theorem ofBytes?_eq_some_iff {n : Nat} {b : Bytes} {x : FixedBytes n} :
    ofBytes? b = some x ↔ b.size = n ∧ x.toBytes = b := by
  constructor
  · intro h
    unfold ofBytes? at h
    split at h
    next hs =>
      cases Option.some.inj h
      exact ⟨hs, bytes_of_size b hs⟩
    next => contradiction
  · rintro ⟨_, h⟩
    rw [← h, ofBytes?_toBytes]

/-- A wrong byte length is the only constructor rejection. -/
theorem ofBytes?_eq_none_iff {n : Nat} {b : Bytes} :
    (ofBytes? b : Option (FixedBytes n)) = none ↔ b.size ≠ n := by
  simp only [ofBytes?]
  split <;> simp_all

/-- Byte observers are injective. -/
theorem toBytes_inj {n : Nat} {x y : FixedBytes n} : x.toBytes = y.toBytes ↔ x = y := by
  constructor
  · intro h
    have := congrArg (ofBytes? (n := n)) h
    exact Option.some.inj (by simpa only [ofBytes?_toBytes] using this)
  · exact congrArg toBytes

/-- The executable order observes big-endian numeric values. -/
theorem compare_toNat {n : Nat} (x y : FixedBytes n) :
    compare x y = compare x.toNat y.toNat := rfl

/-- Equal-width numeric order is exactly EELS lexical byte order. -/
theorem compare_toBytes {n : Nat} (x y : FixedBytes n) :
    compare x y = compare (Bytes.toList x.toBytes) (Bytes.toList y.toBytes) := by
  rw [compare_toNat, ← decode_toBytes x, ← decode_toBytes y, decodeFast_eq, decodeFast_eq]
  exact compare_decode _ _ (by rw [Bytes.length_toList, Bytes.length_toList, size_toBytes,
    size_toBytes])

end FixedBytes

/-- Eight bytes; `ethereum_types/bytes.py:85` (`Bytes8`). -/
abbrev Bytes8 := FixedBytes 8
/-- Thirty-two bytes; `ethereum_types/bytes.py:109` (`Bytes32`). -/
abbrev Bytes32 := FixedBytes 32
/-- Forty-eight bytes; `ethereum_types/bytes.py:121` (`Bytes48`). -/
abbrev Bytes48 := FixedBytes 48
/-- Sixty-four bytes; `ethereum_types/bytes.py:130` (`Bytes64`). -/
abbrev Bytes64 := FixedBytes 64
/-- Ninety-six bytes; `ethereum_types/bytes.py:142` (`Bytes96`). -/
abbrev Bytes96 := FixedBytes 96
/-- 256-byte bloom; EELS `src/ethereum/forks/amsterdam/fork_types.py:34`. -/
abbrev Bloom := FixedBytes 256
/-- Sixty-four-byte hash content; EELS `src/ethereum/crypto/hash.py:20` (`Hash64`). -/
abbrev Hash64 := FixedBytes 64

/-- Distinct address domain type over 20 bytes; EELS `src/ethereum/state.py:33`.
The type distinction preserves the same byte-content equality model. -/
structure Address where
  private ofBitVecRaw ::
  private val : BitVec 160

namespace Address

private def toFixed (x : Address) : FixedBytes 20 := FixedBytes.ofBitVecRaw x.val

private def ofFixed (x : FixedBytes 20) : Address := ofBitVecRaw x.val

private theorem toFixed_ofFixed (x : FixedBytes 20) : (ofFixed x).toFixed = x := rfl

private theorem ofFixed_toFixed (x : Address) : ofFixed x.toFixed = x := rfl

/-- Stable big-endian numeric observer. -/
def toNat (x : Address) : Nat := x.toFixed.toNat

/-- Exact 20-byte observer, including leading zeros. -/
def toBytes (x : Address) : Bytes := x.toFixed.toBytes

/-- Exact-length checked constructor; EELS `src/ethereum/state.py:33` and
locked `ethereum_types/bytes.py:29`. Wrong length fails before value decoding. -/
def ofBytes? (b : Bytes) : Option Address := (FixedBytes.ofBytes? b).map ofFixed

/-- Numeric values are in the complete 160-bit range. -/
theorem toNat_lt (x : Address) : x.toNat < 2 ^ 160 := FixedBytes.toNat_lt x.toFixed

/-- Numeric observations determine domain values. -/
theorem toNat_inj {x y : Address} : x.toNat = y.toNat ↔ x = y := by
  constructor
  · intro h
    have hf := FixedBytes.toNat_inj.mp h
    exact congrArg ofFixed hf
  · exact congrArg toNat

/-- Domain equality is decidable through its stable numeric model. -/
instance : DecidableEq Address := fun x y ↦
  decidable_of_iff (x.toNat = y.toNat) toNat_inj

/-- Big-endian numeric ordering, proved lexical on bytes below. -/
instance : Ord Address where
  compare := compareOn toNat

/-- Numeric comparison is reflexive. -/
instance : Std.ReflOrd Address := inferInstanceAs (Std.ReflCmp (compareOn toNat))

/-- Numeric comparison has the correct orientation. -/
instance : Std.OrientedOrd Address := inferInstanceAs (Std.OrientedCmp (compareOn toNat))

/-- Numeric comparison is transitive. -/
instance : Std.TransOrd Address := inferInstanceAs (Std.TransCmp (compareOn toNat))

/-- Comparison equality is actual domain equality. -/
instance : Std.LawfulEqOrd Address where
  eq_of_compare h := toNat_inj.mp (Nat.compare_eq_eq.mp h)

/-- Output length is exactly 20 bytes. -/
theorem size_toBytes (x : Address) : x.toBytes.size = 20 := FixedBytes.size_toBytes x.toFixed

/-- Numeric observation is the big-endian radix-256 fold of its bytes. -/
theorem toNat_eq_fold (x : Address) :
    x.toNat = (Bytes.toList x.toBytes).foldl (fun acc b ↦ 256 * acc + b.toNat) 0 :=
  FixedBytes.toNat_eq_fold x.toFixed

/-- Reconstructing from its byte observer returns the original domain value. -/
theorem ofBytes?_toBytes (x : Address) : ofBytes? x.toBytes = some x := by
  rw [ofBytes?, toBytes, FixedBytes.ofBytes?_toBytes]
  rfl

/-- Success is exactly the required length and identical byte contents. -/
theorem ofBytes?_eq_some_iff {b : Bytes} {x : Address} :
    ofBytes? b = some x ↔ b.size = 20 ∧ x.toBytes = b := by
  rw [ofBytes?, Option.map_eq_some_iff]
  constructor
  · rintro ⟨v, hv, hx⟩
    subst x
    exact FixedBytes.ofBytes?_eq_some_iff.mp hv
  · intro h
    exact ⟨x.toFixed, FixedBytes.ofBytes?_eq_some_iff.mpr h, ofFixed_toFixed x⟩

/-- Length mismatch is the only constructor rejection. -/
theorem ofBytes?_eq_none_iff {b : Bytes} : ofBytes? b = none ↔ b.size ≠ 20 := by
  rw [ofBytes?, Option.map_eq_none_iff, FixedBytes.ofBytes?_eq_none_iff]

/-- Byte contents determine domain values. -/
theorem toBytes_inj {x y : Address} : x.toBytes = y.toBytes ↔ x = y := by
  constructor
  · intro h
    have := congrArg ofBytes? h
    exact Option.some.inj (by simpa only [ofBytes?_toBytes] using this)
  · exact congrArg toBytes

/-- Comparison observes the stable numeric model. -/
theorem compare_toNat (x y : Address) : compare x y = compare x.toNat y.toNat := rfl

/-- Domain ordering is exactly EELS lexical byte ordering. -/
theorem compare_toBytes (x y : Address) :
    compare x y = compare (Bytes.toList x.toBytes) (Bytes.toList y.toBytes) :=
  FixedBytes.compare_toBytes x.toFixed y.toFixed

end Address

/-- Distinct hash32 domain type over 32 bytes; EELS `src/ethereum/crypto/hash.py:19`.
The type distinction preserves the same byte-content equality model. -/
structure Hash32 where
  private ofBitVecRaw ::
  private val : BitVec 256

namespace Hash32

private def toFixed (x : Hash32) : FixedBytes 32 := FixedBytes.ofBitVecRaw x.val

private def ofFixed (x : FixedBytes 32) : Hash32 := ofBitVecRaw x.val

private theorem toFixed_ofFixed (x : FixedBytes 32) : (ofFixed x).toFixed = x := rfl

private theorem ofFixed_toFixed (x : Hash32) : ofFixed x.toFixed = x := rfl

/-- Stable big-endian numeric observer. -/
def toNat (x : Hash32) : Nat := x.toFixed.toNat

/-- Exact 32-byte observer, including leading zeros. -/
def toBytes (x : Hash32) : Bytes := x.toFixed.toBytes

/-- Exact-length checked constructor; EELS `src/ethereum/crypto/hash.py:19` and
locked `ethereum_types/bytes.py:29`. Wrong length fails before value decoding. -/
def ofBytes? (b : Bytes) : Option Hash32 := (FixedBytes.ofBytes? b).map ofFixed

/-- Numeric values are in the complete 256-bit range. -/
theorem toNat_lt (x : Hash32) : x.toNat < 2 ^ 256 := FixedBytes.toNat_lt x.toFixed

/-- Numeric observations determine domain values. -/
theorem toNat_inj {x y : Hash32} : x.toNat = y.toNat ↔ x = y := by
  constructor
  · intro h
    have hf := FixedBytes.toNat_inj.mp h
    exact congrArg ofFixed hf
  · exact congrArg toNat

/-- Domain equality is decidable through its stable numeric model. -/
instance : DecidableEq Hash32 := fun x y ↦
  decidable_of_iff (x.toNat = y.toNat) toNat_inj

/-- Big-endian numeric ordering, proved lexical on bytes below. -/
instance : Ord Hash32 where
  compare := compareOn toNat

/-- Numeric comparison is reflexive. -/
instance : Std.ReflOrd Hash32 := inferInstanceAs (Std.ReflCmp (compareOn toNat))

/-- Numeric comparison has the correct orientation. -/
instance : Std.OrientedOrd Hash32 := inferInstanceAs (Std.OrientedCmp (compareOn toNat))

/-- Numeric comparison is transitive. -/
instance : Std.TransOrd Hash32 := inferInstanceAs (Std.TransCmp (compareOn toNat))

/-- Comparison equality is actual domain equality. -/
instance : Std.LawfulEqOrd Hash32 where
  eq_of_compare h := toNat_inj.mp (Nat.compare_eq_eq.mp h)

/-- Output length is exactly 32 bytes. -/
theorem size_toBytes (x : Hash32) : x.toBytes.size = 32 := FixedBytes.size_toBytes x.toFixed

/-- Numeric observation is the big-endian radix-256 fold of its bytes. -/
theorem toNat_eq_fold (x : Hash32) :
    x.toNat = (Bytes.toList x.toBytes).foldl (fun acc b ↦ 256 * acc + b.toNat) 0 :=
  FixedBytes.toNat_eq_fold x.toFixed

/-- Reconstructing from its byte observer returns the original domain value. -/
theorem ofBytes?_toBytes (x : Hash32) : ofBytes? x.toBytes = some x := by
  rw [ofBytes?, toBytes, FixedBytes.ofBytes?_toBytes]
  rfl

/-- Success is exactly the required length and identical byte contents. -/
theorem ofBytes?_eq_some_iff {b : Bytes} {x : Hash32} :
    ofBytes? b = some x ↔ b.size = 32 ∧ x.toBytes = b := by
  rw [ofBytes?, Option.map_eq_some_iff]
  constructor
  · rintro ⟨v, hv, hx⟩
    subst x
    exact FixedBytes.ofBytes?_eq_some_iff.mp hv
  · intro h
    exact ⟨x.toFixed, FixedBytes.ofBytes?_eq_some_iff.mpr h, ofFixed_toFixed x⟩

/-- Length mismatch is the only constructor rejection. -/
theorem ofBytes?_eq_none_iff {b : Bytes} : ofBytes? b = none ↔ b.size ≠ 32 := by
  rw [ofBytes?, Option.map_eq_none_iff, FixedBytes.ofBytes?_eq_none_iff]

/-- Byte contents determine domain values. -/
theorem toBytes_inj {x y : Hash32} : x.toBytes = y.toBytes ↔ x = y := by
  constructor
  · intro h
    have := congrArg ofBytes? h
    exact Option.some.inj (by simpa only [ofBytes?_toBytes] using this)
  · exact congrArg toBytes

/-- Comparison observes the stable numeric model. -/
theorem compare_toNat (x y : Hash32) : compare x y = compare x.toNat y.toNat := rfl

/-- Domain ordering is exactly EELS lexical byte ordering. -/
theorem compare_toBytes (x y : Hash32) :
    compare x y = compare (Bytes.toList x.toBytes) (Bytes.toList y.toBytes) :=
  FixedBytes.compare_toBytes x.toFixed y.toFixed

/-- Forget only the hash domain distinction, retaining the same 32 bytes. -/
def toBytes32 (x : Hash32) : Bytes32 := x.toFixed

/-- Introduce only the hash domain distinction, retaining the same 32 bytes. -/
def ofBytes32 (x : Bytes32) : Hash32 := ofFixed x

/-- Removing the domain distinction after adding it returns the original bytes. -/
theorem toBytes32_ofBytes32 (x : Bytes32) : (ofBytes32 x).toBytes32 = x := rfl

/-- Adding the domain distinction after removing it returns the original hash. -/
theorem ofBytes32_toBytes32 (x : Hash32) : ofBytes32 x.toBytes32 = x := rfl

/-- Forgetting the domain distinction preserves byte contents. -/
theorem toBytes_toBytes32 (x : Hash32) : x.toBytes32.toBytes = x.toBytes := rfl

/-- Adding the domain distinction preserves byte contents. -/
theorem toBytes_ofBytes32 (x : Bytes32) : (ofBytes32 x).toBytes = x.toBytes := rfl

/-- Forgetting the domain distinction preserves the numeric model. -/
theorem toNat_toBytes32 (x : Hash32) : x.toBytes32.toNat = x.toNat := rfl

/-- Adding the domain distinction preserves the numeric model. -/
theorem toNat_ofBytes32 (x : Bytes32) : (ofBytes32 x).toNat = x.toNat := rfl

end Hash32

/-- State root hash domain; EELS `src/ethereum/state.py:34`. -/
abbrev Root := Hash32
/-- Versioned hash domain; EELS `src/ethereum/forks/amsterdam/fork_types.py:32`. -/
abbrev VersionedHash := Hash32

/-- Slot-key pair order is lexical: address first, then slot bytes (F19).
Lean supplies `lexOrd` and its lawful instances but no global pair `Ord` instance. -/
instance : Ord (Address × Bytes32) := lexOrd

/-- Slot-key comparison is lexical in its component orders. -/
theorem compare_address_slot (x y : Address × Bytes32) :
    compare x y = (compare x.1 y.1).then (compare x.2 y.2) := rfl

/-- Slot-key comparison observes lexical address and slot byte contents. -/
theorem compare_address_slot_toBytes (x y : Address × Bytes32) :
    compare x y =
      (compare (Bytes.toList x.1.toBytes) (Bytes.toList y.1.toBytes)).then
        (compare (Bytes.toList x.2.toBytes) (Bytes.toList y.2.toBytes)) := by
  rw [compare_address_slot, Address.compare_toBytes, FixedBytes.compare_toBytes]

end STFSpec.Base
