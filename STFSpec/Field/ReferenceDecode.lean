/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Field.Reference
import STFSpec.Base.IntegerBytes

/-!
# Checked natural-reference big-endian decoding

Library `EthField`. Compose the public byte and unbounded natural decoder with
checked canonical construction, for every finite ByteArray and admitted modulus.
Spec guidance: `STFSpec/informal/modules/EthField.md` §§3–7.
-/

namespace STFSpec.Field.PrimeFieldRef

variable {p : Nat} [FieldModulus p]

/-- Interpret all input bytes big-endian and accept exactly values below `p`, without
reduction or a length restriction (R2/R8/R10). Corresponds conditionally to pinned
`src/ethereum/crypto/kzg.py:96–104` on typed 32-byte, assertion-active inputs and
`src/ethereum/forks/amsterdam/vm/precompiled_contracts/bls12_381/__init__.py:426–454`
on exactly 64-byte inputs. Consumers retain their length checks and failure mapping. -/
def ofBytesBE? (b : ByteArray) : Option (PrimeFieldRef p) :=
  ofNat? (STFSpec.Base.Uint.ofBeBytes (STFSpec.Base.Bytes.ofByteArray b))

/-- Decoding succeeds exactly at the original, strictly admitted positional natural. -/
theorem ofBytesBE?_eq_some_iff (b : ByteArray) (a : PrimeFieldRef p) :
    ofBytesBE? b = some a ↔
      STFSpec.Base.Uint.ofBeBytes (STFSpec.Base.Bytes.ofByteArray b) < p ∧
      a.toNat = STFSpec.Base.Uint.ofBeBytes (STFSpec.Base.Bytes.ofByteArray b) :=
  ofNat?_eq_some_iff _ _

end STFSpec.Field.PrimeFieldRef
