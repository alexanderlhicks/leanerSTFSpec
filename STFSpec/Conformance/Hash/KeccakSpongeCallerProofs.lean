/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash

/-!
# Keccak sponge composition clients

Library `EthConformance`. These clients use only the public byte/model laws and
accepted permutation seam; no provider container definition is unfolded.
Spec guidance: `STFSpec/informal/modules/EthHash.md` §7.
-/

open STFSpec.Base STFSpec.Hash STFSpec.Hash.KeccakSponge

example (msg : ByteArray) : (keccak256 msg).toBytes.toList.length = 32 := by
  rw [Bytes.length_toList, size_keccak256]

example (msg : ByteArray) : (keccak512 msg).toBytes.toList.length = 64 := by
  rw [Bytes.length_toList, size_keccak512]

example (msg : ByteArray) (candidate : Hash32)
    (h : candidate.toBytes.toList = Model.digest .keccak256 msg.data.toList) :
    candidate = keccak256 msg := by
  apply Hash32.toBytes_inj.mp
  apply Bytes.ext
  rw [h, keccak256_model]

example (r : Rate) (b : Bytes) (m n offset : Nat) (s : KeccakState) :
    keccakToModel (absorb r b n (offset + m * r.bytes) (absorb r b m offset s)) =
      Model.absorb r b.toList (m + n) offset (keccakToModel s) := by
  rw [← absorb_add, absorb_model]

example (r : Rate) (b : Bytes) : (pad r b).size % r.bytes = 0 := by
  rw [size_pad, paddedSize_mod]

example (r : Rate) (b : Bytes) (i : Nat) (hi : i < b.size) :
    (pad r b)[i]'(by rw [size_pad]; have := paddedSize_gt r b.size; omega) = b[i] :=
  getElem_pad_prefix r b i hi

example (s : KeccakState) : (squeeze s 32 (by decide)).toList =
    Model.squeeze (keccakToModel s) 32 (by decide) := squeeze_model s 32 (by decide)

example (f : Nat → UInt8) : (decodeLane f).toBitVec = Model.decodeLane f :=
  decodeLane_model f
