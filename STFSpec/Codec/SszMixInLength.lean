/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash

/-!
# SSZ length mix-in

Library `EthCodec`. The successful-value length mix-in preserves the natural
count with one local uint256 range proof. Source construction and lazy hashing
order belong to enclosing consumers, not this pure helper.
Reference: locked eth-remerkleable 0.1.31 `remerkleable/complex.py:367–368`,
`byte_arrays.py:228–232`, `progressive.py:118`, `basic.py:226–227,303–309`.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7 (Q76).
-/

namespace STFSpec.Codec

/-- SHA-256 of the complete root followed by the checked count's 32 LE bytes.
Counts outside uint256 have no argument at this seam; no runtime rejection or
outside-domain value is selected. The equation itself is the legible reference. -/
def Ssz.mixInLength (root : Base.Bytes32) (len : Nat)
    (h : len < 2 ^ 256) : Base.Bytes32 :=
  let _ := h
  Hash.sha256
    ((root.toBytes ++ (Base.FixedBytes.ofLeNat len : Base.Bytes32).toBytes).toByteArray)

/-- Complete successful-value equation; Base's public byte law expands every
one of the 32 count digits in increasing significance, including zero bytes. -/
theorem Ssz.mixInLength_eq (root : Base.Bytes32) (len : Nat)
    (h : len < 2 ^ 256) :
    mixInLength root len h =
      STFSpec.Hash.sha256
        ((root.toBytes ++
          (Base.FixedBytes.ofLeNat len : Base.Bytes32).toBytes).toByteArray) := rfl

end STFSpec.Codec
