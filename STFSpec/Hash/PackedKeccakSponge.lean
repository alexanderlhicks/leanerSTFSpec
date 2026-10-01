/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash.PackedKeccakPermutation
import STFSpec.Hash.KeccakSponge

/-!
# Packed fixed-rate legacy Keccak candidate

Library `EthHash`. The native 25-field state is retained across forward block
absorption. Padding and little-endian lane codecs are the public reference
operations, while XOR, permutation and squeezing use the packed state directly.
The ordinary all-input endpoint equations include public Base fixed-width
construction. Existing default hashes and the future `Id` query choice remain
owned by the reference module and D5; this candidate changes neither.

Pinned EELS `src/ethereum/crypto/hash.py:62–95` delegates to pycryptodome 3.23.0
on the checked frozen host. The underlying algorithm is legacy Keccak, with
suffix 0x01, from FIPS 202's sponge/permutation and the Keccak team submission.
Spec guidance: `STFSpec/informal/modules/EthHash.md` §§3,6,7.
-/

namespace STFSpec.Hash.PackedKeccak
open STFSpec.Base
open KeccakSponge (Rate byteAt decodeLane encodeLaneByte)

/-- The packed all-zero sponge state. -/
def zero : State :=
  ⟨0, 0, 0, 0, 0,
   0, 0, 0, 0, 0,
   0, 0, 0, 0, 0,
   0, 0, 0, 0, 0,
   0, 0, 0, 0, 0⟩

/-- XOR one zero-extended rate block into packed lanes; capacity lanes remain unchanged. -/
def xorBlock (r : Rate) (b : Bytes) (offset : Nat) (s : State) : State :=
  ⟨s.a00 ^^^ (if 0 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 0 + j)) else 0),
   s.a10 ^^^ (if 8 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 8 + j)) else 0),
   s.a20 ^^^ (if 16 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 16 + j)) else 0),
   s.a30 ^^^ (if 24 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 24 + j)) else 0),
   s.a40 ^^^ (if 32 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 32 + j)) else 0),
   s.a01 ^^^ (if 40 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 40 + j)) else 0),
   s.a11 ^^^ (if 48 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 48 + j)) else 0),
   s.a21 ^^^ (if 56 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 56 + j)) else 0),
   s.a31 ^^^ (if 64 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 64 + j)) else 0),
   s.a41 ^^^ (if 72 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 72 + j)) else 0),
   s.a02 ^^^ (if 80 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 80 + j)) else 0),
   s.a12 ^^^ (if 88 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 88 + j)) else 0),
   s.a22 ^^^ (if 96 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 96 + j)) else 0),
   s.a32 ^^^ (if 104 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 104 + j)) else 0),
   s.a42 ^^^ (if 112 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 112 + j)) else 0),
   s.a03 ^^^ (if 120 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 120 + j)) else 0),
   s.a13 ^^^ (if 128 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 128 + j)) else 0),
   s.a23 ^^^ (if 136 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 136 + j)) else 0),
   s.a33 ^^^ (if 144 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 144 + j)) else 0),
   s.a43 ^^^ (if 152 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 152 + j)) else 0),
   s.a04 ^^^ (if 160 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 160 + j)) else 0),
   s.a14 ^^^ (if 168 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 168 + j)) else 0),
   s.a24 ^^^ (if 176 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 176 + j)) else 0),
   s.a34 ^^^ (if 184 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 184 + j)) else 0),
   s.a44 ^^^ (if 192 < r.bytes then decodeLane (fun j ↦ byteAt b (offset + 192 + j)) else 0)⟩

/-- One ordered packed absorption block: rate XOR followed by 24-round permutation. -/
def absorbBlock (r : Rate) (b : Bytes) (offset : Nat) (s : State) : State :=
  permutation (xorBlock r b offset s)

/-- Absorb the given remaining block count forward, retaining packed state between blocks. -/
def absorb (r : Rate) (b : Bytes) : Nat → Nat → State → State
  | 0, _, s => s
  | n + 1, offset, s => absorb r b n (offset + r.bytes) (absorbBlock r b offset s)

/-- Emit up to 200 bytes in little-endian lane order without constructing a reference state. -/
def squeeze (s : State) (n : Nat) (hn : n ≤ 200) : Bytes :=
  Bytes.generate n fun i ↦ if h : i < n then
    encodeLaneByte (lane s ⟨i / 8, by omega⟩) ⟨i % 8, Nat.mod_lt _ (by decide)⟩ else 0

/-- Fixed-rate legacy sponge: reference padding, packed absorption and packed output bytes. -/
def digestBytes (r : Rate) (b : Bytes) : Bytes :=
  let padded := KeccakSponge.pad r b
  squeeze (absorb r padded (padded.size / r.bytes) 0 zero) r.output (by
    have := r.bounds
    omega)

/-- The packed zero state observes as the reference zero state. -/
theorem toReference_zero : toReference zero = KeccakSponge.zeroState := by
  apply keccakToModel_inj
  funext p
  rcases p with ⟨x, y⟩
  simp only [keccakToModel, KeccakSponge.zeroState, keccakLane_ofLanes,
    toReference_lane]
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  have hxc : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by omega
  have hyc : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 := by omega
  rcases hxc with rfl | rfl | rfl | rfl | rfl <;>
    rcases hyc with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Packed rate XOR commutes with the public reference block operation. -/
theorem toReference_xorBlock (r : Rate) (b : Bytes) (offset : Nat) (s : State) :
    toReference (xorBlock r b offset s) = KeccakSponge.xorBlock r b offset (toReference s) := by
  apply keccakToModel_inj
  funext p
  rcases p with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  have hxc : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by omega
  have hyc : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 := by omega
  cases r <;> rcases hxc with rfl | rfl | rfl | rfl | rfl <;>
    rcases hyc with rfl | rfl | rfl | rfl | rfl <;>
    simp only [keccakToModel, toReference, KeccakSponge.xorBlock, keccakLane_ofLanes] <;>
    dsimp only [Rate.bytes, xorBlock, lane, keccakLaneIndex] <;> rfl

/-- A complete packed absorption block commutes with the reference. -/
theorem toReference_absorbBlock (r : Rate) (b : Bytes) (offset : Nat) (s : State) :
    toReference (absorbBlock r b offset s) =
      KeccakSponge.absorbBlock r b offset (toReference s) := by
  rw [absorbBlock, toReference_permutation, toReference_xorBlock]
  rfl

/-- Every finite ordered block sequence commutes with the reference absorption loop. -/
theorem toReference_absorb (r : Rate) (b : Bytes) (count offset : Nat) (s : State) :
    toReference (absorb r b count offset s) =
      KeccakSponge.absorb r b count offset (toReference s) := by
  induction count generalizing offset s with
  | zero => rfl
  | succ count ih => rw [absorb, ih, toReference_absorbBlock, KeccakSponge.absorb]

/-- Packed squeeze equals reference squeeze after public state observation. -/
theorem squeeze_eq (s : State) (n : Nat) (hn : n ≤ 200) :
    squeeze s n hn = KeccakSponge.squeeze (toReference s) n hn := by
  apply Bytes.ext
  simp only [squeeze, KeccakSponge.squeeze, Bytes.toList_generate]
  apply List.map_congr_left
  intro i hi
  by_cases h : i < n
  · simp only [h, dite_true]
    rw [toReference_lane]
    congr 2
    apply Fin.ext
    simp only [keccakLaneIndex]
    omega
  · simp only [h, dite_false]

/-- The complete packed fixed-rate sponge equals the retained reference on every input. -/
theorem digestBytes_eq (r : Rate) (b : Bytes) :
    digestBytes r b = KeccakSponge.digestBytes r b := by
  rw [digestBytes, squeeze_eq, toReference_absorb, toReference_zero]
  rfl

/-- The fixed-rate packed digest has the exact selected output width. -/
theorem size_digestBytes (r : Rate) (b : Bytes) : (digestBytes r b).size = r.output := by
  rw [digestBytes_eq, KeccakSponge.size_digestBytes]

/-- Construct fixed bytes using the public checked Base constructor and proved exact width. -/
private def fixedOutput (n : Nat) (b : Bytes) (h : b.size = n) : FixedBytes n :=
  (FixedBytes.ofBytes? b).get (by
    apply Option.isSome_iff_ne_none.mpr
    intro hn
    exact FixedBytes.ofBytes?_eq_none_iff.mp hn h)

/-- The checked output constructor retains every digest byte. -/
private theorem fixedOutput_bytes (n : Nat) (b : Bytes) (h : b.size = n) :
    (fixedOutput n b h).toBytes = b := by
  apply (FixedBytes.ofBytes?_eq_some_iff.mp ?_).2
  exact (Option.some_get _).symm

/-- Packed legacy Keccak-256 candidate; EELS src/ethereum/crypto/hash.py:62 at the pin. -/
def keccak256 (msg : ByteArray) : Hash32 := Hash32.ofBytes32
  (fixedOutput 32 (digestBytes .keccak256 (Bytes.ofByteArray msg))
    (by simpa only [Rate.output] using size_digestBytes .keccak256 (Bytes.ofByteArray msg)))

/-- Packed legacy Keccak-512 candidate; EELS src/ethereum/crypto/hash.py:80 at the pin. -/
def keccak512 (msg : ByteArray) : Hash64 :=
  fixedOutput 64 (digestBytes .keccak512 (Bytes.ofByteArray msg))
    (by simpa only [Rate.output] using size_digestBytes .keccak512 (Bytes.ofByteArray msg))

/-- The public candidate Hash32 observes as the complete rate-136 packed sponge bytes. -/
theorem keccak256_bytes (msg : ByteArray) :
    (keccak256 msg).toBytes = digestBytes .keccak256 (Bytes.ofByteArray msg) := by
  rw [keccak256, Hash32.toBytes_ofBytes32]
  exact fixedOutput_bytes _ _ _

/-- The public candidate Hash64 observes as the complete rate-72 packed sponge bytes. -/
theorem keccak512_bytes (msg : ByteArray) :
    (keccak512 msg).toBytes = digestBytes .keccak512 (Bytes.ofByteArray msg) :=
  fixedOutput_bytes _ _ _

/-- Every packed Keccak-256 result equals the retained default reference result. -/
theorem keccak256_eq (msg : ByteArray) : keccak256 msg = STFSpec.Hash.keccak256 msg := by
  apply Hash32.toBytes_inj.mp
  rw [keccak256_bytes, STFSpec.Hash.keccak256_bytes, digestBytes_eq]

/-- Every packed Keccak-512 result equals the retained default reference result. -/
theorem keccak512_eq (msg : ByteArray) : keccak512 msg = STFSpec.Hash.keccak512 msg := by
  apply FixedBytes.toBytes_inj.mp
  rw [keccak512_bytes, STFSpec.Hash.keccak512_bytes, digestBytes_eq]

/-- Packed block XOR commutes with the independent byte/coordinate model. -/
theorem xorBlock_model (r : Rate) (b : Bytes) (offset : Nat) (s : State) :
    toModel (xorBlock r b offset s) =
      KeccakSponge.Model.xorBlock r b.toList offset (toModel s) := by
  rw [toModel, toReference_xorBlock, KeccakSponge.xorBlock_model]
  rfl

/-- Packed forward absorption commutes with the byte/coordinate model. -/
theorem absorb_model (r : Rate) (b : Bytes) (count offset : Nat) (s : State) :
    toModel (absorb r b count offset s) =
      KeccakSponge.Model.absorb r b.toList count offset (toModel s) := by
  rw [toModel, toReference_absorb, KeccakSponge.absorb_model]
  rfl

/-- Packed bounded output bytes satisfy the public model squeeze equation. -/
theorem squeeze_model (s : State) (n : Nat) (hn : n ≤ 200) :
    (squeeze s n hn).toList = KeccakSponge.Model.squeeze (toModel s) n hn := by
  rw [squeeze_eq, KeccakSponge.squeeze_model]
  rfl

/-- Packed complete fixed-rate digest bytes satisfy the legacy sponge model. -/
theorem digestBytes_model (r : Rate) (b : Bytes) :
    (digestBytes r b).toList = KeccakSponge.Model.digest r b.toList := by
  rw [digestBytes_eq, KeccakSponge.digestBytes_model]

/-- All-input public candidate Keccak-256 correspondence with the legacy byte model. -/
theorem keccak256_model (msg : ByteArray) :
    (keccak256 msg).toBytes.toList =
      KeccakSponge.Model.digest .keccak256 msg.data.toList := by
  rw [keccak256_eq, STFSpec.Hash.keccak256_model]

/-- All-input public candidate Keccak-512 correspondence with the legacy byte model. -/
theorem keccak512_model (msg : ByteArray) :
    (keccak512 msg).toBytes.toList =
      KeccakSponge.Model.digest .keccak512 msg.data.toList := by
  rw [keccak512_eq, STFSpec.Hash.keccak512_model]

/-- The candidate Keccak-256 byte observer has exactly 32 bytes. -/
theorem size_keccak256 (msg : ByteArray) : (keccak256 msg).toBytes.size = 32 := by
  rw [keccak256_eq, STFSpec.Hash.size_keccak256]

/-- The candidate Keccak-512 byte observer has exactly 64 bytes. -/
theorem size_keccak512 (msg : ByteArray) : (keccak512 msg).toBytes.size = 64 := by
  rw [keccak512_eq, STFSpec.Hash.size_keccak512]

/-- Splitting an ordered packed block sequence retains the same packed final state. -/
theorem absorb_add (r : Rate) (b : Bytes) (m n offset : Nat) (s : State) :
    absorb r b (m + n) offset s =
      absorb r b n (offset + m * r.bytes) (absorb r b m offset s) := by
  apply toReference_injective
  rw [toReference_absorb, toReference_absorb, toReference_absorb, KeccakSponge.absorb_add]

end STFSpec.Hash.PackedKeccak
