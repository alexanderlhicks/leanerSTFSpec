/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Public-only padded-buffer clients

Library `EthConformance`. Clients consume all three ordinary buffer laws and the
existing Base extension seam, without unfolding either provider or private storage.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/7.
-/

namespace STFSpec.Conformance.Vm.Core.BufferReadCallerProofs
open STFSpec.Vm.Core STFSpec.Base

private theorem zero_size (b : Bytes) (start : U256) :
    bufferRead b start U256.zero = Bytes.empty := by
  apply Bytes.size_eq_zero_iff.mp
  rw [bufferRead_size, U256.toNat_zero]

private theorem unavailable (b : Bytes) (start size : U256) (h : b.size ≤ start.toNat) :
    (bufferRead b start size).toList = List.replicate size.toNat 0 := by
  rw [bufferRead_toList, List.drop_of_length_le (by rw [Bytes.length_toList]; exact h)]
  simp [Nat.sub_eq_zero_of_le h]

private theorem contained (b : Bytes) (start size : U256)
    (h : start.toNat + size.toNat ≤ b.size) :
    (bufferRead b start size).toList = (b.toList.drop start.toNat).take size.toNat := by
  rw [bufferRead_toList, Nat.min_eq_left (show size.toNat ≤ b.size - start.toNat by omega)]
  simp

private theorem provider_bridge (b : Bytes) (start size : U256) :
    bufferRead b start size = Bytes.extractPadded b start.toNat size.toNat := by
  exact bufferRead_eq_extractPadded b start size

private theorem zero_extension (b : Bytes) (n : Nat) (start size : U256)
    (h : start.toNat + size.toNat ≤ max b.size n) :
    bufferRead (Bytes.rightPadZero b n) start size = bufferRead b start size := by
  rw [bufferRead_eq_extractPadded, bufferRead_eq_extractPadded]
  exact Bytes.extractPadded_rightPadZero b n start.toNat size.toNat h

end STFSpec.Conformance.Vm.Core.BufferReadCallerProofs
