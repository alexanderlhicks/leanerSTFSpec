/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash.KeccakPermutation
import STFSpec.Base

/-!
# Fixed-rate legacy Keccak sponges

Library `EthHash`. Byte-aligned Keccak-256 and Keccak-512 use the legacy pad10*1
suffix, not SHA-3's domain suffix. Lane bytes are little endian; coordinates use
x+5*y. Only the two specified rates are provided. There is no oracle seam here.
Spec guidance: `STFSpec/informal/modules/EthHash.md` §§2–7.

## References

* Keccak team, *The Keccak reference*, version 3.0, 2011, §§1.1.2, 1.3–1.4
  (padding and sponge construction); https://keccak.team/files/Keccak-reference-3.0.pdf.
* NIST, *FIPS PUB 202*, 2015, §§3.1.2, 4, 5.1 (packing, sponge, padding).
  https://doi.org/10.6028/NIST.FIPS.202. SHA-3's extra suffix is not used.
-/

namespace STFSpec.Hash.KeccakSponge

open STFSpec.Base

/-- The two fixed standard rates; arbitrary/zero-rate behavior is not specified. -/
inductive Rate where
  | keccak256
  | keccak512
  deriving DecidableEq

/-- Rate in bytes: Keccak-256 has capacity 512, Keccak-512 capacity 1024. -/
def Rate.bytes : Rate → Nat | .keccak256 => 136 | .keccak512 => 72

/-- Fixed digest byte count, smaller than either rate. -/
def Rate.output : Rate → Nat | .keccak256 => 32 | .keccak512 => 64

/-- Both rates are positive multiples of eight and fit the 1600-bit state. -/
theorem Rate.bounds (r : Rate) :
    0 < r.bytes ∧ r.bytes % 8 = 0 ∧ r.bytes ≤ 200 ∧ r.output ≤ r.bytes := by
  cases r <;> decide

/-- Padding always adds between one byte and one full rate block. -/
def paddingCount (r : Rate) (n : Nat) : Nat := r.bytes - n % r.bytes

/-- Padded length, including a new padding block at an exact rate boundary. -/
def paddedSize (r : Rate) (n : Nat) : Nat := n + paddingCount r n

/-- Total byte lookup; block/lane readers use zero beyond the supplied bytes. -/
def byteAt (b : Bytes) (i : Nat) : UInt8 := (b[i]?).getD 0

/-- Legacy byte-aligned pad10*1: suffix 0x01 and final bit 0x80, combined if needed. -/
def pad (r : Rate) (b : Bytes) : Bytes :=
  Bytes.generate (paddedSize r b.size) fun i =>
    if i < b.size then byteAt b i
    else (if i = b.size then 1 else 0) ||| (if i + 1 = paddedSize r b.size then 128 else 0)

/-- Pack n low-to-high bytes with OR; the standard lane uses exactly eight. -/
def decodeAux (f : Nat → UInt8) : Nat → UInt64
  | 0 => 0
  | n + 1 => decodeAux f n ||| (UInt64.ofNat (f n).toNat <<< UInt64.ofNat (8 * n))

/-- Exactly eight bytes interpreted little endian. -/
def decodeLane (f : Nat → UInt8) : UInt64 := decodeAux f 8

/-- Extract one of the eight little-endian bytes of a native lane. -/
def encodeLaneByte (x : UInt64) (i : Fin 8) : UInt8 :=
  (x >>> UInt64.ofNat (8 * i.val)).toUInt8

/-- XOR one rate block into the leading lanes, leaving capacity lanes unchanged. -/
def xorBlock (r : Rate) (b : Bytes) (offset : Nat) (s : KeccakState) : KeccakState :=
  keccakOfLanes fun x y =>
    let lane := (keccakLaneIndex x y).val
    keccakLane s x y ^^^
      if 8 * lane < r.bytes then decodeLane (fun j => byteAt b (offset + 8 * lane + j)) else 0

/-- Absorb one ordered rate block and apply the accepted permutation. -/
def absorbBlock (r : Rate) (b : Bytes) (offset : Nat) (s : KeccakState) : KeccakState :=
  keccakF1600 (xorBlock r b offset s)

/-- Process a bounded number of blocks, advancing one rate each time; tail recursive. -/
def absorb (r : Rate) (b : Bytes) : Nat → Nat → KeccakState → KeccakState
  | 0, _, s => s
  | n + 1, offset, s => absorb r b n (offset + r.bytes) (absorbBlock r b offset s)

/-- All-zero initial state. -/
def zeroState : KeccakState := keccakOfLanes fun _ _ => 0

/-- Squeeze at most one state's bytes, low byte first in x+5*y lane order. -/
def squeeze (s : KeccakState) (n : Nat) (hn : n ≤ 200) : Bytes :=
  Bytes.generate n fun i =>
    if h : i < n then
      encodeLaneByte (keccakLane s ⟨i / 8 % 5, Nat.mod_lt _ (by decide)⟩
        ⟨i / 40, by omega⟩) ⟨i % 8, Nat.mod_lt _ (by decide)⟩
    else 0

/-- Reference digest bytes; fixed outputs need no further squeezing permutation. -/
def digestBytes (r : Rate) (b : Bytes) : Bytes :=
  let padded := pad r b
  let final := absorb r padded (padded.size / r.bytes) 0 zeroState
  squeeze final r.output (by have := r.bounds; omega)

namespace Model

/-- Standard low-to-high placement of the first n byte values in a 64-bit lane. -/
def decodeAux (f : Nat → UInt8) : Nat → BitVec 64
  | 0 => 0
  | n + 1 => decodeAux f n ||| (BitVec.ofNat 64 (f n).toNat <<< (8 * n))

/-- Eight-byte little-endian model lane. -/
def decodeLane (f : Nat → UInt8) : BitVec 64 := decodeAux f 8

/-- Byte-array observation is a list, including exact legacy padding positions. -/
def pad (r : Rate) (bs : List UInt8) : List UInt8 :=
  bs ++ (List.range (paddingCount r bs.length)).map fun j =>
    (if j = 0 then 1 else 0) ||| (if j + 1 = paddingCount r bs.length then 128 else 0)

/-- Absorption XOR in standard coordinates, with zero capacity contribution. -/
def xorBlock (r : Rate) (bs : List UInt8) (offset : Nat) (s : KeccakModel) : KeccakModel :=
  fun (x,y) =>
    let lane := (keccakLaneIndex x y).val
    s (x,y) ^^^
      if 8 * lane < r.bytes then
        decodeLane (fun j => (bs[offset + 8 * lane + j]?).getD 0) else 0

/-- Standard permutation after XORing one rate block. -/
def absorbBlock (r : Rate) (bs : List UInt8) (offset : Nat) (s : KeccakModel) : KeccakModel :=
  KeccakModel.rounds (xorBlock r bs offset s) 24 (by decide)

/-- Coordinate sponge absorption in message-block order. -/
def absorb (r : Rate) (bs : List UInt8) : Nat → Nat → KeccakModel → KeccakModel
  | 0, _, s => s
  | n + 1, offset, s => absorb r bs n (offset + r.bytes) (absorbBlock r bs offset s)

/-- Standard lane serialization, with byte zero at lane bit zero. -/
def squeeze (s : KeccakModel) (n : Nat) (hn : n ≤ 200) : List UInt8 :=
  (List.range n).map fun i =>
    if h : i < n then
      UInt8.ofBitVec ((s (⟨i / 8 % 5, Nat.mod_lt _ (by decide)⟩,
        ⟨i / 40, by omega⟩) >>> (8 * (i % 8))).setWidth 8)
    else 0

/-- Byte-level fixed-rate sponge model. -/
def digest (r : Rate) (bs : List UInt8) : List UInt8 :=
  let padded := pad r bs
  let final := absorb r padded (padded.length / r.bytes) 0 (fun _ => 0)
  squeeze final r.output (by have := r.bounds; omega)

end Model

end STFSpec.Hash.KeccakSponge

namespace STFSpec.Hash.KeccakSponge

open STFSpec.Base

/-- The padding count is positive and at most one full rate. -/
theorem paddingCount_bounds (r : Rate) (n : Nat) :
    0 < paddingCount r n ∧ paddingCount r n ≤ r.bytes := by
  have := Nat.mod_lt n r.bounds.1
  simp only [paddingCount]
  omega

/-- Padding has the promised exact length. -/
theorem size_pad (r : Rate) (b : Bytes) : (pad r b).size = paddedSize r b.size :=
  Bytes.size_generate _ _

/-- The padded length is a positive multiple of the rate, including aligned inputs. -/
theorem paddedSize_eq (r : Rate) (n : Nat) :
    paddedSize r n = (n / r.bytes + 1) * r.bytes := by
  have h : n % r.bytes + (n / r.bytes) * r.bytes = n := by
    simpa only [Nat.mul_comm] using Nat.mod_add_div n r.bytes
  have hm := Nat.mod_lt n r.bounds.1
  simp only [paddedSize, paddingCount]
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Every padded message ends at a block boundary. -/
theorem paddedSize_mod (r : Rate) (n : Nat) : paddedSize r n % r.bytes = 0 := by
  rw [paddedSize_eq, Nat.mul_mod_left]

/-- Padding strictly extends every input, so prefix accesses are valid. -/
theorem paddedSize_gt (r : Rate) (n : Nat) : n < paddedSize r n := by
  have := paddingCount_bounds r n
  simp only [paddedSize]
  omega

/-- An aligned input receives an entire new padding block. -/
theorem paddingCount_of_mod_zero (r : Rate) (n : Nat) (h : n % r.bytes = 0) :
    paddingCount r n = r.bytes := by simp only [paddingCount, h, Nat.sub_zero]

/-- Optional byte access agrees with the public list observer. -/
theorem byteAt_model (b : Bytes) (i : Nat) : byteAt b i = (b.toList[i]?).getD 0 := by
  by_cases hi : i < b.size
  · simp only [byteAt, getElem?_pos b i hi,
      List.getElem?_eq_getElem (by rw [Bytes.length_toList]; exact hi), Option.getD_some]
    exact (Bytes.getElem_toList b i hi).symm
  · have hl : ¬ i < b.toList.length := by rw [Bytes.length_toList]; exact hi
    simp only [byteAt, getElem?_neg b i hi, List.getElem?_eq_none (by omega : b.toList.length ≤ i), Option.getD_none]

/-- Every original input byte is preserved. -/
theorem getElem_pad_prefix (r : Rate) (b : Bytes) (i : Nat) (hi : i < b.size) :
    (pad r b)[i]'(by rw [size_pad]; have := paddingCount_bounds r b.size; unfold paddedSize; omega) = b[i] := by
  have hpad : i < (pad r b).size := by
    rw [size_pad]; have := paddingCount_bounds r b.size; unfold paddedSize; omega
  calc
    (pad r b)[i] = (if i < b.size then byteAt b i else
      (if i = b.size then 1 else 0) ||| (if i + 1 = paddedSize r b.size then 128 else 0)) :=
        Bytes.getElem_generate _ _ i (by have := paddingCount_bounds r b.size; unfold paddedSize; omega)
    _ = b[i] := by simp only [hi, ite_true, byteAt, getElem?_pos b i hi, Option.getD_some]

/-- The entire suffix has exactly the two pad10*1 boundary bits. -/
theorem getElem_pad_suffix (r : Rate) (b : Bytes) (j : Nat)
    (hj : j < paddingCount r b.size) :
    (pad r b)[b.size + j]'(by rw [size_pad]; unfold paddedSize; omega) =
      (if j = 0 then 1 else 0) ||| (if j + 1 = paddingCount r b.size then 128 else 0) := by
  have hpad : b.size + j < (pad r b).size := by
    rw [size_pad]; unfold paddedSize; omega
  calc
    (pad r b)[b.size + j] = (if b.size + j < b.size then byteAt b (b.size + j) else
      (if b.size + j = b.size then 1 else 0) |||
        (if b.size + j + 1 = paddedSize r b.size then 128 else 0)) :=
          Bytes.getElem_generate _ _ _ (by unfold paddedSize; omega)
    _ = _ := by simp only [show ¬ b.size + j < b.size by omega, ite_false,
    show (b.size + j = b.size) ↔ j = 0 by omega,
    show (b.size + j + 1 = paddedSize r b.size) ↔ j + 1 = paddingCount r b.size by
      unfold paddedSize; omega]

/-- The one-byte padding case combines 0x01 and 0x80 into 0x81. -/
theorem getElem_pad_single (r : Rate) (b : Bytes) (h : paddingCount r b.size = 1) :
    (pad r b)[b.size]'(by rw [size_pad]; unfold paddedSize; omega) = 129 := by
  simpa only [Nat.add_zero, h, ite_true, show (1 : UInt8) ||| 128 = 129 from rfl] using getElem_pad_suffix r b 0 (by omega)

/-- With two or more suffix bytes, the first is 0x01. -/
theorem getElem_pad_first (r : Rate) (b : Bytes) (h : 1 < paddingCount r b.size) :
    (pad r b)[b.size]'(by rw [size_pad]; unfold paddedSize; omega) = 1 := by
  simpa [show 1 ≠ paddingCount r b.size by omega] using getElem_pad_suffix r b 0 (by omega)

/-- With two or more suffix bytes, the last is 0x80. -/
theorem getElem_pad_last (r : Rate) (b : Bytes) (h : 1 < paddingCount r b.size) :
    (pad r b)[b.size + (paddingCount r b.size - 1)]'(by
      rw [size_pad]; unfold paddedSize; omega) = 128 := by
  simpa [show paddingCount r b.size - 1 ≠ 0 by omega,
    show paddingCount r b.size - 1 + 1 = paddingCount r b.size by omega]
    using getElem_pad_suffix r b (paddingCount r b.size - 1) (by omega)

/-- No additional bit appears in the interior zero padding bytes. -/
theorem getElem_pad_middle (r : Rate) (b : Bytes) (j : Nat)
    (hj : 0 < j) (hl : j + 1 < paddingCount r b.size) :
    (pad r b)[b.size + j]'(by rw [size_pad]; unfold paddedSize; omega) = 0 := by
  simpa [show j ≠ 0 by omega, show j + 1 ≠ paddingCount r b.size by omega]
    using getElem_pad_suffix r b j (by omega)

/-- Native packed padding equals the byte-list legacy padding model. -/
theorem pad_model (r : Rate) (b : Bytes) : (pad r b).toList = Model.pad r b.toList := by
  apply List.ext_getElem
  · simp only [Bytes.length_toList, size_pad, Model.pad, List.length_append,
      List.length_map, List.length_range, paddedSize]
  · intro i hi hj
    by_cases hb : i < b.size
    · simp only [Model.pad]
      rw [List.getElem_append_left (by rw [Bytes.length_toList]; exact hb)]
      calc
        (pad r b).toList[i] = (pad r b)[i] := Bytes.getElem_toList _ _ (by
          rw [size_pad]; have := paddingCount_bounds r b.size; unfold paddedSize; omega)
        _ = b[i] := getElem_pad_prefix r b i hb
        _ = b.toList[i] := (Bytes.getElem_toList b i hb).symm
    · have hs : i - b.size < paddingCount r b.size := by
        have hh : i < b.size + paddingCount r b.size := by
          simpa only [Bytes.length_toList, size_pad, paddedSize] using hi
        omega
      simp only [Model.pad]
      rw [List.getElem_append_right (by rw [Bytes.length_toList]; omega)]
      simp only [Bytes.length_toList, List.getElem_map, List.getElem_range]
      rw [Bytes.getElem_toList _ _ (by rw [size_pad]; unfold paddedSize; omega)]
      have h := getElem_pad_suffix r b (i - b.size) hs
      have he : b.size + (i - b.size) = i := by omega
      simpa only [he] using h

/-- Native lane packing observes the standard little-endian model for n≤8 bytes. -/
theorem decodeAux_model (f : Nat → UInt8) (n : Nat) (hn : n ≤ 8) :
    (decodeAux f n).toBitVec = Model.decodeAux f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he := UInt64.ofBitVec_shiftLeft (BitVec.ofNat 64 (f n).toNat) (8 * n) (by omega)
    have hs : (UInt64.ofNat (f n).toNat <<< UInt64.ofNat (8 * n)).toBitVec =
        BitVec.ofNat 64 (f n).toNat <<< (8 * n) :=
      (congrArg UInt64.toBitVec he).symm
    simp only [decodeAux, Model.decodeAux, UInt64.toBitVec_or, ih (by omega), hs]

/-- All eight input bytes pack into a standard lane. -/
theorem decodeLane_model (f : Nat → UInt8) :
    (decodeLane f).toBitVec = Model.decodeLane f := decodeAux_model f 8 (by decide)

/-- A squeezed native byte is precisely the low eight bits of the shifted model lane. -/
theorem encodeLaneByte_model (x : UInt64) (i : Fin 8) :
    (encodeLaneByte x i).toBitVec = (x.toBitVec >>> (8 * i.val)).setWidth 8 := by
  have he := UInt64.ofBitVec_shiftRight x.toBitVec (8 * i.val) (by have := i.isLt; omega)
  have hs : (x >>> UInt64.ofNat (8 * i.val)).toBitVec = x.toBitVec >>> (8 * i.val) :=
    (congrArg UInt64.toBitVec he).symm
  simp only [encodeLaneByte, UInt64.toBitVec_toUInt8, hs]

/-- Absorption XOR commutes with the accepted coordinate observer. -/
theorem xorBlock_model (r : Rate) (b : Bytes) (offset : Nat) (s : KeccakState) :
    keccakToModel (xorBlock r b offset s) = Model.xorBlock r b.toList offset (keccakToModel s) := by
  funext p
  rcases p with ⟨x,y⟩
  simp only [keccakToModel, xorBlock, keccakLane_ofLanes, UInt64.toBitVec_xor,
    Model.xorBlock]
  split
  · rw [decodeLane_model]
    congr 2
    funext j
    exact byteAt_model b _
  · rfl

/-- One absorption step uses the public permutation correspondence theorem. -/
theorem absorbBlock_model (r : Rate) (b : Bytes) (offset : Nat) (s : KeccakState) :
    keccakToModel (absorbBlock r b offset s) =
      Model.absorbBlock r b.toList offset (keccakToModel s) := by
  rw [absorbBlock, keccakToModel_f1600, xorBlock_model]
  rfl

/-- Block induction relates the native and coordinate sponges at arbitrary offsets/states. -/
theorem absorb_model (r : Rate) (b : Bytes) (n offset : Nat) (s : KeccakState) :
    keccakToModel (absorb r b n offset s) = Model.absorb r b.toList n offset (keccakToModel s) := by
  induction n generalizing offset s with
  | zero => rfl
  | succ n ih =>
    rw [absorb, Model.absorb, ih, absorbBlock_model]

/-- An empty block sequence leaves the state unchanged. -/
theorem absorb_zero (r : Rate) (b : Bytes) (offset : Nat) (s : KeccakState) :
    absorb r b 0 offset s = s := rfl

/-- Consecutive block segments compose in their original order. -/
theorem absorb_add (r : Rate) (b : Bytes) (m n offset : Nat) (s : KeccakState) :
    absorb r b (m + n) offset s =
      absorb r b n (offset + m * r.bytes) (absorb r b m offset s) := by
  induction m generalizing offset s with
  | zero => simp only [Nat.zero_add, Nat.zero_mul, Nat.add_zero, absorb_zero]
  | succ m ih =>
    rw [Nat.succ_add, absorb, ih, absorb]
    congr 1
    simp only [Nat.add_mul, Nat.one_mul]
    omega

/-- Squeezing preserves its exact output width. -/
theorem size_squeeze (s : KeccakState) (n : Nat) (hn : n ≤ 200) :
    (squeeze s n hn).size = n := Bytes.size_generate _ _

/-- Native lane serialization agrees byte for byte with the coordinate model. -/
theorem squeeze_model (s : KeccakState) (n : Nat) (hn : n ≤ 200) :
    (squeeze s n hn).toList = Model.squeeze (keccakToModel s) n hn := by
  rw [squeeze, Bytes.toList_generate, Model.squeeze]
  apply List.map_congr_left
  intro i hi
  split
  · apply UInt8.eq_of_toBitVec_eq
    rw [encodeLaneByte_model]
    rfl
  · rfl

/-- The sponge begins with a zero bit at every coordinate. -/
theorem zeroState_model : keccakToModel zeroState = fun _ => 0 := by
  funext p
  rcases p with ⟨x,y⟩
  simp only [zeroState, keccakToModel, keccakLane_ofLanes]
  rfl

/-- Fixed-rate digest bytes have their specified width. -/
theorem size_digestBytes (r : Rate) (b : Bytes) : (digestBytes r b).size = r.output :=
  size_squeeze _ _ (by have := r.bounds; omega)

/-- Padding, ordered absorption and little-endian squeezing compose to the sponge model. -/
theorem digestBytes_model (r : Rate) (b : Bytes) :
    (digestBytes r b).toList = Model.digest r b.toList := by
  rw [digestBytes, squeeze_model, absorb_model, zeroState_model, pad_model]
  simp only [Model.digest, ← Bytes.length_toList, pad_model]

end STFSpec.Hash.KeccakSponge

namespace STFSpec.Hash

open STFSpec.Base

/-- Construct a fixed result through Base's checked public API and a length proof. -/
private def spongeFixedOutput (n : Nat) (b : Bytes) (h : b.size = n) : FixedBytes n :=
  (FixedBytes.ofBytes? b).get (by
    apply Option.isSome_iff_ne_none.mpr
    intro hn
    exact FixedBytes.ofBytes?_eq_none_iff.mp hn h)

private theorem spongeFixedOutput_bytes (n : Nat) (b : Bytes) (h : b.size = n) :
    (spongeFixedOutput n b h).toBytes = b := by
  apply (FixedBytes.ofBytes?_eq_some_iff.mp ?_).2
  exact (Option.some_get _).symm

/-- Legacy Keccak-256; pinned EELS `src/ethereum/crypto/hash.py:62–77`.
The pure concrete function uses rate 136 bytes; the query seam is separate. -/
def keccak256 (msg : ByteArray) : Hash32 :=
  Hash32.ofBytes32 (spongeFixedOutput 32
    (KeccakSponge.digestBytes .keccak256 (Bytes.ofByteArray msg))
    (by simpa only [KeccakSponge.Rate.output] using
      KeccakSponge.size_digestBytes .keccak256 (Bytes.ofByteArray msg)))

/-- Legacy Keccak-512; pinned EELS `src/ethereum/crypto/hash.py:80–95`.
Rate 72 bytes; retained until the Q18 exclusion is adopted. -/
def keccak512 (msg : ByteArray) : Hash64 :=
  spongeFixedOutput 64 (KeccakSponge.digestBytes .keccak512 (Bytes.ofByteArray msg))
    (by simpa only [KeccakSponge.Rate.output] using
      KeccakSponge.size_digestBytes .keccak512 (Bytes.ofByteArray msg))

/-- Keccak-256 retains every squeezed byte across the Base domain constructor. -/
theorem keccak256_bytes (msg : ByteArray) :
    (keccak256 msg).toBytes = KeccakSponge.digestBytes .keccak256 (Bytes.ofByteArray msg) := by
  rw [keccak256, Hash32.toBytes_ofBytes32]
  exact spongeFixedOutput_bytes _ _ _

/-- Keccak-512 retains every squeezed byte across the Base fixed-width constructor. -/
theorem keccak512_bytes (msg : ByteArray) :
    (keccak512 msg).toBytes = KeccakSponge.digestBytes .keccak512 (Bytes.ofByteArray msg) := by
  exact spongeFixedOutput_bytes _ _ _

/-- Keccak-256 byte-level standard sponge correspondence on every finite input. -/
theorem keccak256_model (msg : ByteArray) :
    (keccak256 msg).toBytes.toList = KeccakSponge.Model.digest .keccak256 msg.data.toList := by
  rw [keccak256_bytes, KeccakSponge.digestBytes_model, Bytes.toList_ofByteArray]

/-- Keccak-512 byte-level standard sponge correspondence on every finite input. -/
theorem keccak512_model (msg : ByteArray) :
    (keccak512 msg).toBytes.toList = KeccakSponge.Model.digest .keccak512 msg.data.toList := by
  rw [keccak512_bytes, KeccakSponge.digestBytes_model, Bytes.toList_ofByteArray]

/-- The public Keccak-256 result contains exactly 32 bytes. -/
theorem size_keccak256 (msg : ByteArray) : (keccak256 msg).toBytes.size = 32 :=
  Hash32.size_toBytes _

/-- The public Keccak-512 result contains exactly 64 bytes. -/
theorem size_keccak512 (msg : ByteArray) : (keccak512 msg).toBytes.size = 64 :=
  FixedBytes.size_toBytes _

end STFSpec.Hash
