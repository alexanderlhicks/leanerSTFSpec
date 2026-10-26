/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash

/-!
# SSZ active-field mix-in

Library `EthCodec`. Head activity has weight one. This pure successful-value
helper mixes a supplied contents root with the complete low-first mask chunk.
Reference: locked eth-remerkleable 0.1.31 `progressive.py:460–529,550–563`,
`bitfields.py:381–416`, `core.py:326–341`, `tree.py:175–202`.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7 (Q77).
-/

namespace STFSpec.Codec

/-- SHA-256 of root32 followed by maskLE32. The sole local width proof excludes
unsupported positions; empty and trailing-false masks remain mathematical inputs.
Source class admission and the meaning of the supplied contents root are separate.
The complete equation is the legible executable reference. -/
def Ssz.mixInActiveFields (root : Base.Bytes32) (active : List Bool)
    (h : active.length ≤ 256) : Base.Bytes32 :=
  let _ := h
  Hash.sha256
    ((root.toBytes ++
      (Base.FixedBytes.ofLeNat
        (active.foldr (fun bit n => (if bit then 1 else 0) + 2 * n) 0)
        : Base.Bytes32).toBytes).toByteArray)

/-- Complete reference equation; Base's public LE byte law describes all 32
mask digits, including zeros. No count, delimiter or extra mask hash is inserted. -/
theorem Ssz.mixInActiveFields_eq (root : Base.Bytes32) (active : List Bool)
    (h : active.length ≤ 256) :
    mixInActiveFields root active h =
      STFSpec.Hash.sha256
        ((root.toBytes ++
          (Base.FixedBytes.ofLeNat
            (active.foldr (fun bit n => (if bit then 1 else 0) + 2 * n) 0)
            : Base.Bytes32).toBytes).toByteArray) := rfl

end STFSpec.Codec
