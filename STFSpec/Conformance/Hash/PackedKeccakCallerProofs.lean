/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash

/-!
# Packed Keccak public-law clients

Library `EthConformance`. Clients use the public state, reference and semantic
model equations. No packed field, executable step or provider container is unfolded.
Original reference caller scripts remain separate and unchanged.
Spec guidance: `STFSpec/informal/modules/EthHash.md` §§3,7.
-/

open STFSpec.Base STFSpec.Hash
namespace STFSpec.Conformance.Hash.PackedKeccak

example (s t : PackedKeccak.State)
    (h : PackedKeccak.toReference s = PackedKeccak.toReference t) : s = t :=
  PackedKeccak.toReference_injective h

example (s t : PackedKeccak.State)
    (h : PackedKeccak.toModel s = PackedKeccak.toModel t) : s = t :=
  PackedKeccak.toModel_injective h

example (s : KeccakState) :
    PackedKeccak.toReference (PackedKeccak.permutation (PackedKeccak.ofReference s)) =
      keccakF1600 s := by
  rw [PackedKeccak.toReference_permutation, PackedKeccak.toReference_ofReference]

example (s : PackedKeccak.State) (r : Fin 24) :
    PackedKeccak.toModel (PackedKeccak.round s r) = KeccakModel.round
      (PackedKeccak.toModel s) r := PackedKeccak.toModel_round s r

example (s : PackedKeccak.State) (n : Nat) (hn : n ≤ 24) :
    PackedKeccak.toModel (PackedKeccak.rounds s n hn) =
      KeccakModel.rounds (PackedKeccak.toModel s) n hn :=
  PackedKeccak.toModel_rounds s n hn

example (r : KeccakSponge.Rate) (b : Bytes) (m n offset : Nat) (s : PackedKeccak.State) :
    PackedKeccak.toModel (PackedKeccak.absorb r b n (offset + m * r.bytes)
      (PackedKeccak.absorb r b m offset s)) =
      KeccakSponge.Model.absorb r b.toList (m + n) offset (PackedKeccak.toModel s) := by
  rw [← PackedKeccak.absorb_add, PackedKeccak.absorb_model]

example (s : PackedKeccak.State) :
    (PackedKeccak.squeeze s 32 (by decide)).toList =
      KeccakSponge.Model.squeeze (PackedKeccak.toModel s) 32 (by decide) :=
  PackedKeccak.squeeze_model s 32 (by decide)

example (r : KeccakSponge.Rate) (b : Bytes) :
    (PackedKeccak.digestBytes r b).toList = KeccakSponge.Model.digest r b.toList :=
  PackedKeccak.digestBytes_model r b

example (msg : ByteArray) : (PackedKeccak.keccak256 msg).toBytes.toList.length = 32 := by
  rw [Bytes.length_toList, PackedKeccak.size_keccak256]

example (msg : ByteArray) : (PackedKeccak.keccak512 msg).toBytes.toList.length = 64 := by
  rw [Bytes.length_toList, PackedKeccak.size_keccak512]

example (msg : ByteArray) (candidate : Hash32)
    (h : candidate.toBytes.toList =
      KeccakSponge.Model.digest .keccak256 msg.data.toList) :
    candidate = PackedKeccak.keccak256 msg := by
  apply Hash32.toBytes_inj.mp
  apply Bytes.ext
  rw [h, PackedKeccak.keccak256_model]

example (msg : ByteArray) : PackedKeccak.keccak256 msg = STFSpec.Hash.keccak256 msg :=
  PackedKeccak.keccak256_eq msg

example (msg : ByteArray) : PackedKeccak.keccak512 msg = STFSpec.Hash.keccak512 msg :=
  PackedKeccak.keccak512_eq msg

example (msg : ByteArray) :
    (PackedKeccak.keccak256 msg).toBytes = (STFSpec.Hash.keccak256 msg).toBytes := by
  rw [PackedKeccak.keccak256_eq]

end STFSpec.Conformance.Hash.PackedKeccak
