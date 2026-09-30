/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash.Sha256Compression

/-!
# SHA-256 message digest

Library `EthHash`. FIPS 180-4 §§5.1.1, 5.2.1, 6.2.1–6.2.2,
https://doi.org/10.6028/NIST.FIPS.180-4. Q46 defines the total extension:
the length trailer wraps modulo 2^64; standard correspondence requires
`8 * msg.size < 2^64`. Blocks and words are processed in ascending order.
Spec guidance: `STFSpec/informal/modules/EthHash.md` §§3, 7.
-/

namespace STFSpec.Hash.Sha256

open STFSpec.Base

/-- Low 64 bits of the original bit length, for any conceptual byte count. -/
def bitLength (byteLength : Nat) : Nat := (8 * byteLength) % 2 ^ 64

/-- The eight big-endian trailer bytes, without allocating a conceptual message. -/
def lengthTrailer (byteLength : Nat) : Bytes :=
  Bytes.generate 8 (fun i => UInt8.ofNat (bitLength byteLength / 256 ^ (7 - i)))

/-- Number of zeros after 0x80 and before the length trailer. -/
def zeroCount (byteLength : Nat) : Nat := (119 - byteLength % 64) % 64

def paddedLength (byteLength : Nat) : Nat := byteLength + 1 + zeroCount byteLength + 8

/-- A bounded suffix: marker, at most 63 zeros, then the original length. -/
def paddingSuffix (byteLength : Nat) : Bytes :=
  Bytes.generate (1 + zeroCount byteLength + 8) fun i =>
    if i = 0 then 0x80 else if i ≤ zeroCount byteLength then 0
    else UInt8.ofNat (bitLength byteLength / 256 ^ (7 - (i - (1 + zeroCount byteLength))))

/-- One append; the original message is never traversed once per block. -/
def pad (msg : ByteArray) : Bytes := Bytes.ofByteArray msg ++ paddingSuffix msg.size

theorem bitLength_mod (n : Nat) : bitLength n = (8 * n) % 2 ^ 64 := rfl

theorem bitLength_lt (n : Nat) : bitLength n < 2 ^ 64 := Nat.mod_lt _ (by decide)

/-- Qualified FIPS-domain equivalence; outside this domain Q46 is an extension. -/
theorem bitLength_of_fipsDomain (n : Nat) (h : 8 * n < 2 ^ 64) : bitLength n = 8 * n :=
  Nat.mod_eq_of_lt h

theorem size_lengthTrailer (n : Nat) : (lengthTrailer n).size = 8 := Bytes.size_generate _ _

theorem getElem_lengthTrailer (n i : Nat) (hi : i < 8) :
    (lengthTrailer n)[i]'(by rw [size_lengthTrailer]; exact hi) =
      UInt8.ofNat (bitLength n / 256 ^ (7 - i)) := Bytes.getElem_generate _ _ _ hi

theorem zeroCount_lt (n : Nat) : zeroCount n < 64 := Nat.mod_lt _ (by decide)

theorem paddedLength_mod (n : Nat) : paddedLength n % 64 = 0 := by
  have hn := Nat.mod_lt n (by decide : 0 < 64)
  unfold paddedLength zeroCount
  omega

theorem padding_boundary (n : Nat) :
    (n % 64 = 55 → zeroCount n = 0) ∧
    (n % 64 = 56 → zeroCount n = 63) ∧
    (n % 64 = 63 → zeroCount n = 56) ∧
    (n % 64 = 0 → zeroCount n = 55) := by
  unfold zeroCount
  constructor
  · intro h; rw [h]
  constructor
  · intro h; rw [h]
  constructor <;> intro h <;> rw [h] <;> decide

theorem size_paddingSuffix (n : Nat) :
    (paddingSuffix n).size = 1 + zeroCount n + 8 := Bytes.size_generate _ _

/-- Exact byte-list suffix, including all eight big-endian length bytes. -/
theorem toList_paddingSuffix (n : Nat) :
    (paddingSuffix n).toList = [0x80] ++ List.replicate (zeroCount n) 0 ++
      (lengthTrailer n).toList := by
  unfold paddingSuffix
  rw [Bytes.toList_generate]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_append, List.length_singleton,
      List.length_replicate, Bytes.length_toList, size_lengthTrailer]
  · intro i hi hj
    have hib : i < 1 + zeroCount n + 8 := by
      simpa only [List.length_map, List.length_range] using hi
    simp only [List.getElem_map, List.getElem_range]
    simp only [List.getElem_append, List.length_append, List.length_singleton,
      List.length_replicate]
    by_cases h0 : i = 0
    · subst i; simp
    · by_cases hz : i ≤ zeroCount n
      · simp [h0, hz, show ¬ i < 1 from by omega, show i < 1 + zeroCount n from by omega,
          List.getElem_replicate]
      · simp only [h0, hz, ite_false, show ¬ i < 1 + zeroCount n from by omega, dite_false]
        rw [Bytes.getElem_toList, getElem_lengthTrailer]
        all_goals first | omega | (rw [size_lengthTrailer]; omega)

theorem paddedLength_ge (n : Nat) : n ≤ paddedLength n := by
  unfold paddedLength
  omega

theorem size_pad (msg : ByteArray) : (pad msg).size = paddedLength msg.size := by
  rw [pad, Bytes.size_append, Bytes.size_ofByteArray, size_paddingSuffix]
  unfold paddedLength
  omega

/-- The original prefix and the exact FIPS/Q46 suffix in the stable byte model. -/
theorem toList_pad (msg : ByteArray) :
    (pad msg).toList = msg.data.toList ++ [0x80] ++
      List.replicate (zeroCount msg.size) 0 ++ (lengthTrailer msg.size).toList := by
  rw [pad, Bytes.toList_append, Bytes.toList_ofByteArray, toList_paddingSuffix]
  simp only [List.append_assoc]

theorem pad_prefix (msg : ByteArray) : (pad msg).toList.take msg.size = msg.data.toList := by
  rw [toList_pad, List.append_assoc, List.append_assoc]
  simpa only [Array.length_toList, ByteArray.size, List.append_assoc] using
    (List.take_left (l₁ := msg.data.toList) (l₂ := [0x80] ++ (List.replicate (zeroCount msg.size) 0 ++
      (lengthTrailer msg.size).toList)))

theorem pad_multiple64 (msg : ByteArray) : (pad msg).size % 64 = 0 := by
  rw [size_pad, paddedLength_mod]

/-- Positional big-endian decoding of exactly four bytes. -/
def parseWord (a b c d : UInt8) : UInt32 :=
  UInt32.ofNat (16777216 * a.toNat + 65536 * b.toNat + 256 * c.toNat + d.toNat)

/-- Constant-width serialization keeps leading zeros. -/
def wordByte (word : UInt32) (i : Nat) : UInt8 :=
  UInt8.ofNat (word.toNat / 256 ^ (3 - i))

/-- All accesses are checked before the runtime byte primitive. The digest calls
this only at complete 64-byte block offsets; the helper is total at other offsets. -/
def parseBlock (bytes : Bytes) (offset : Nat) : Vector UInt32 16 :=
  Vector.ofFn fun i =>
    let pos := offset + 4 * i.val
    parseWord (bytes.toByteArray[pos]?.getD 0) (bytes.toByteArray[pos + 1]?.getD 0)
      (bytes.toByteArray[pos + 2]?.getD 0) (bytes.toByteArray[pos + 3]?.getD 0)

/-- Tail recursion over remaining blocks, visiting offset, offset+64, ... . -/
def blocks (bytes : Bytes) : Nat → Nat → Vector UInt32 8 → Vector UInt32 8
  | 0, _, state => state
  | remaining + 1, offset, state =>
    blocks bytes remaining (offset + 64) (sha256Compress state (parseBlock bytes offset))

def serialize (state : Vector UInt32 8) : Bytes :=
  Bytes.generate 32 fun i => wordByte state[i / 4 % 8] (i % 4)

/-- Build a fixed digest using only the checked public Base constructor. -/
def digestValue (state : Vector UInt32 8) : Bytes32 :=
  (FixedBytes.ofBytes? (serialize state)).get (by
    apply Option.isSome_iff_ne_none.mpr
    intro h
    have := FixedBytes.ofBytes?_eq_none_iff.mp h
    exact this (Bytes.size_generate _ _))

namespace Model

/-- Explicit byte model uses positional values and standard BitVec32 words. -/
def parseWord (a b c d : UInt8) : BitVec 32 :=
  BitVec.ofNat 32 (16777216 * a.toNat + 65536 * b.toNat + 256 * c.toNat + d.toNat)

def parseBlock (bytes : List UInt8) (offset : Nat) : Vector (BitVec 32) 16 :=
  Vector.ofFn fun i =>
    let pos := offset + 4 * i.val
    parseWord (bytes[pos]?.getD 0) (bytes[pos + 1]?.getD 0)
      (bytes[pos + 2]?.getD 0) (bytes[pos + 3]?.getD 0)

def serialize (state : Vector (BitVec 32) 8) : List UInt8 :=
  (List.range 32).map fun i => UInt8.ofNat (state[i / 4 % 8].toNat / 256 ^ (3 - i % 4))

/-- Serial composition model: standard compression folded over ascending offsets. -/
def blocks (bytes : List UInt8) (offset count : Nat) (state : Vector (BitVec 32) 8) :
    Vector (BitVec 32) 8 :=
  (List.range count).foldl (fun s i => compress s (parseBlock bytes (offset + 64 * i))) state

end Model

end STFSpec.Hash.Sha256

namespace STFSpec.Hash

open STFSpec.Base

/-- Pure total SHA-256. Q46 wraps the eight-byte bit-length trailer for all sizes;
FIPS 180-4 correspondence has the explicit `8 * msg.size < 2^64` domain. -/
def sha256 (msg : ByteArray) : Bytes32 :=
  let bytes := Sha256.pad msg
  Sha256.digestValue (Sha256.blocks bytes (bytes.size / 64) 0 Sha256.initialState)

end STFSpec.Hash

namespace STFSpec.Hash.Sha256

open STFSpec.Base

/-- Parsing observes the four ordered radix-256 digits. -/
theorem toNat_parseWord (a b c d : UInt8) :
    (parseWord a b c d).toNat =
      16777216 * a.toNat + 65536 * b.toNat + 256 * c.toNat + d.toNat := by
  rw [parseWord, UInt32.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  change _ < 4294967296
  omega

/-- Ordered four-byte serialization recovers every native word. -/
theorem parseWord_wordByte (word : UInt32) :
    parseWord (wordByte word 0) (wordByte word 1) (wordByte word 2) (wordByte word 3) = word := by
  apply UInt32.toNat_inj.mp
  rw [toNat_parseWord]
  simp only [wordByte, UInt8.toNat_ofNat', Nat.reduceSub, Nat.reducePow, Nat.div_one]
  change 16777216 * (word.toNat / 16777216 % 256) +
    65536 * (word.toNat / 65536 % 256) + 256 * (word.toNat / 256 % 256) +
    word.toNat % 256 = word.toNat
  have h := word.toNat_lt
  change word.toNat < 4294967296 at h
  omega

theorem toBitVec_parseWord (a b c d : UInt8) :
    (parseWord a b c d).toBitVec = Model.parseWord a b c d := rfl

/-- Bounds-checked packed byte reads agree with the stable list observer. -/
theorem getElem?_toByteArray (bytes : Bytes) (i : Nat) :
    bytes.toByteArray[i]? = bytes.toList[i]? := by
  rw [← Bytes.toList_toByteArray]
  change bytes.toByteArray.data[i]? = bytes.toByteArray.data.toList[i]?
  simp only [Array.getElem?_toList]

theorem wordsModel_parseBlock (bytes : Bytes) (offset : Nat) :
    wordsModel (parseBlock bytes offset) = Model.parseBlock bytes.toList offset := by
  apply Vector.ext
  intro i hi
  simp only [wordsModel_get, parseBlock, Model.parseBlock, Vector.getElem_ofFn,
    getElem?_toByteArray, toBitVec_parseWord]

theorem serialize_model (state : Vector UInt32 8) :
    (serialize state).toList = Model.serialize (wordsModel state) := by
  simp only [serialize, Bytes.toList_generate, Model.serialize, wordByte,
    wordsModel_get]
  rfl

theorem size_serialize (state : Vector UInt32 8) : (serialize state).size = 32 :=
  Bytes.size_generate _ _

/-- Fixed output construction retains precisely the serialized state. -/
theorem toBytes_digestValue (state : Vector UInt32 8) :
    (digestValue state).toBytes = serialize state := by
  have h : FixedBytes.ofBytes? (serialize state) = some (digestValue state) :=
    (Option.some_get (x := FixedBytes.ofBytes? (serialize state)) _).symm
  exact (FixedBytes.ofBytes?_eq_some_iff.mp h).2

/-- Standard serial fold consumes its first block before the remaining range. -/
theorem Model.blocks_succ (bytes : List UInt8) (offset count : Nat)
    (state : Vector (BitVec 32) 8) :
    Model.blocks bytes offset (count + 1) state =
      Model.blocks bytes (offset + 64) count (Model.compress state (Model.parseBlock bytes offset)) := by
  unfold Model.blocks
  rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
  simp only [Nat.mul_zero, Nat.add_zero]
  apply congrArg (fun f => (List.range count).foldl f
    (Model.compress state (Model.parseBlock bytes offset)))
  funext s i
  rw [show offset + 64 * Nat.succ i = offset + 64 + 64 * i by omega]

/-- Induction over the native tail-recursive block loop, using the accepted
compression theorem at each step, establishes the separate serial model. -/
theorem blocks_model (bytes : Bytes) (count offset : Nat) (state : Vector UInt32 8) :
    wordsModel (blocks bytes count offset state) =
      Model.blocks bytes.toList offset count (wordsModel state) := by
  induction count generalizing offset state with
  | zero => rfl
  | succ count ih =>
    rw [blocks, ih, sha256Compress_model, wordsModel_parseBlock, Model.blocks_succ]

/-- Splitting a block run does not change order or introduce another IV. -/
theorem blocks_add (bytes : Bytes) (first rest offset : Nat) (state : Vector UInt32 8) :
    blocks bytes (first + rest) offset state =
      blocks bytes rest (offset + 64 * first) (blocks bytes first offset state) := by
  induction first generalizing offset state with
  | zero => simp [blocks]
  | succ first ih =>
    rw [Nat.succ_add, blocks, blocks, ih]
    congr 1
    omega

/-- The complete message digest is the standard BitVec chaining fold's ordered
big-endian serialization. Q46's padding is total at every mathematical size. -/
theorem sha256_model (msg : ByteArray) :
    (sha256 msg).toBytes.toList =
      Model.serialize (Model.blocks (pad msg).toList 0 ((pad msg).size / 64)
        (wordsModel initialState)) := by
  rw [sha256, toBytes_digestValue, serialize_model, blocks_model]

/-- Standard-domain digest correspondence additionally uses the nonwrapping
bit-length equation, so no above-domain host or FIPS claim is implicit. -/
theorem sha256_fipsDomain (msg : ByteArray) (h : 8 * msg.size < 2 ^ 64) :
    bitLength msg.size = 8 * msg.size ∧
    (sha256 msg).toBytes.toList =
      Model.serialize (Model.blocks (pad msg).toList 0 ((pad msg).size / 64)
        (wordsModel initialState)) :=
  ⟨bitLength_of_fipsDomain _ h, sha256_model msg⟩

end STFSpec.Hash.Sha256

namespace STFSpec.Hash

/-- The public digest has exactly 32 bytes at every input size. -/
theorem size_sha256 (msg : ByteArray) : (sha256 msg).toBytes.size = 32 :=
  STFSpec.Base.FixedBytes.size_toBytes _

end STFSpec.Hash

namespace STFSpec.Hash.Sha256

open STFSpec.Base

/-- The trailer denotes the exact low-64-bit value in the public Base endian model. -/
theorem lengthTrailer_value (n : Nat) : Uint.ofBeBytes (lengthTrailer n) = bitLength n := by
  rw [Uint.ofBeBytes_eq_fold, lengthTrailer, Bytes.toList_generate]
  simp only [List.range_succ, List.range_zero, List.map_nil,
    List.map_cons, List.nil_append, List.cons_append, List.foldl_cons, List.foldl_nil,
    Nat.reduceSub, Nat.reducePow, Nat.div_one, UInt8.toNat_ofNat']
  have h := bitLength_lt n
  change bitLength n < 18446744073709551616 at h
  omega

namespace Model

/-- Padding observed purely as a byte list; Q46's modular extension is explicit. -/
def pad (message : List UInt8) : List UInt8 :=
  message ++ [0x80] ++ List.replicate ((119 - message.length % 64) % 64) 0 ++
    (List.range 8).map (fun i => UInt8.ofNat
      (((8 * message.length) % 2 ^ 64) / 256 ^ (7 - i)))

/-- Standard byte-domain padding uses the original, unwrapped bit length. -/
def fipsPad (message : List UInt8) : List UInt8 :=
  message ++ [0x80] ++ List.replicate ((119 - message.length % 64) % 64) 0 ++
    (List.range 8).map (fun i => UInt8.ofNat ((8 * message.length) / 256 ^ (7 - i)))

/-- A standard chaining trace consumes complete blocks in increasing byte order. -/
inductive Chain (bytes : List UInt8) : Nat → Nat → Vector (BitVec 32) 8 →
    Vector (BitVec 32) 8 → Prop
  | done (offset : Nat) (state : Vector (BitVec 32) 8) : Chain bytes offset 0 state state
  | step (offset count : Nat) (state final : Vector (BitVec 32) 8)
      (next : Chain bytes (offset + 64) count (compress state (parseBlock bytes offset)) final) :
      Chain bytes offset (count + 1) state final

/-- A full digest is a chaining trace from the standard IV followed by all eight
big-endian output words. This relation mentions no executable digest definition. -/
def DigestOnPad (bytes digest : List UInt8) : Prop :=
  ∃ state, Chain bytes 0 (bytes.length / 64) (wordsModel initialState) state ∧
    digest = serialize state

def Digest (message digest : List UInt8) : Prop := DigestOnPad (pad message) digest

/-- The readable serial fold constructs the corresponding inductive trace. -/
theorem blocks_chain (bytes : List UInt8) (count offset : Nat) (state : Vector (BitVec 32) 8) :
    Chain bytes offset count state (blocks bytes offset count state) := by
  induction count generalizing offset state with
  | zero => exact Chain.done offset state
  | succ count ih =>
    rw [blocks_succ]
    exact Chain.step offset count state _ (ih _ _)

/-- Every trace has the serial fold's final state; the relation is deterministic. -/
theorem Chain.eq_blocks {bytes : List UInt8} {offset count : Nat}
    {state final : Vector (BitVec 32) 8} (trace : Chain bytes offset count state final) :
    final = blocks bytes offset count state := by
  induction trace with
  | done => rfl
  | step offset count state final next ih => rw [blocks_succ, ← ih]

end Model

theorem pad_model (msg : ByteArray) : (pad msg).toList = Model.pad msg.data.toList := by
  rw [toList_pad, lengthTrailer, Bytes.toList_generate]
  simp only [Model.pad, Array.length_toList, ByteArray.size, zeroCount, bitLength]

/-- Within the stated domain the modular padding equals FIPS byte padding. -/
theorem pad_fipsDomain (msg : ByteArray) (h : 8 * msg.size < 2 ^ 64) :
    (pad msg).toList = Model.fipsPad msg.data.toList := by
  rw [toList_pad, lengthTrailer, Bytes.toList_generate, bitLength_of_fipsDomain _ h]
  simp only [Model.fipsPad, Array.length_toList, ByteArray.size, zeroCount]

/-- Full digest correctness against the inductive byte/chaining model. -/
theorem sha256_digest (msg : ByteArray) : Model.Digest msg.data.toList (sha256 msg).toBytes.toList := by
  unfold Model.Digest
  rw [← pad_model]
  refine ⟨Model.blocks (pad msg).toList 0 ((pad msg).size / 64) (wordsModel initialState), ?_,
    sha256_model msg⟩
  rw [Bytes.length_toList]
  exact Model.blocks_chain _ _ _ _

/-- FIPS-domain correspondence, with the original unwrapped length and an
inductive full-digest trace. Above-domain extension claims only `sha256_digest`. -/
theorem sha256_fipsDigest (msg : ByteArray) (h : 8 * msg.size < 2 ^ 64) :
    Model.DigestOnPad (Model.fipsPad msg.data.toList) (sha256 msg).toBytes.toList := by
  rw [← pad_fipsDomain _ h]
  refine ⟨Model.blocks (pad msg).toList 0 ((pad msg).size / 64) (wordsModel initialState), ?_,
    sha256_model msg⟩
  rw [Bytes.length_toList]
  exact Model.blocks_chain _ _ _ _

end STFSpec.Hash.Sha256

namespace STFSpec.Hash.Sha256

open STFSpec.Base

/-- Padding produces the ceiling of (original bytes + nine suffix bytes)/64 blocks. -/
theorem blockCount (n : Nat) : paddedLength n / 64 = (n + 72) / 64 := by
  have hn := Nat.mod_lt n (by decide : 0 < 64)
  unfold paddedLength zeroCount
  omega

theorem getElem?_toByteArray_of_lt (bytes : Bytes) (i : Nat) (hi : i < bytes.size) :
    bytes.toByteArray[i]? = some bytes[i] := by
  rw [getElem?_toByteArray, List.getElem?_eq_getElem (by rw [Bytes.length_toList]; exact hi),
    Bytes.getElem_toList]

/-- A complete 64-byte block parses each four-byte word with no zero extension. -/
theorem parseBlock_get (bytes : Bytes) (offset i : Nat) (hi : i < 16)
    (hblock : offset + 64 ≤ bytes.size) :
    (parseBlock bytes offset)[i] =
      parseWord (bytes[offset + 4 * i]'(by omega))
        (bytes[offset + 4 * i + 1]'(by omega))
        (bytes[offset + 4 * i + 2]'(by omega))
        (bytes[offset + 4 * i + 3]'(by omega)) := by
  simp only [parseBlock, Vector.getElem_ofFn]
  rw [getElem?_toByteArray_of_lt bytes _ (by omega),
    getElem?_toByteArray_of_lt bytes _ (by omega),
    getElem?_toByteArray_of_lt bytes _ (by omega),
    getElem?_toByteArray_of_lt bytes _ (by omega)]
  rfl

/-- Serialization keeps word order and emits each word's most significant byte first. -/
theorem serialize_get (state : Vector UInt32 8) (word : Fin 8) (byte : Fin 4) :
    (serialize state)[4 * word.val + byte.val]'(by rw [size_serialize]; omega) =
      wordByte state[word.val] byte.val := by
  unfold serialize
  rw [Bytes.getElem_generate _ _ _ (by omega)]
  have hw : (4 * word.val + byte.val) / 4 % 8 = word.val := by omega
  have hb : (4 * word.val + byte.val) % 4 = byte.val := by omega
  simp only [hw, hb]

end STFSpec.Hash.Sha256
