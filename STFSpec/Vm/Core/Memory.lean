/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.Bytes
import STFSpec.Base.U256

/-!
# Zero-padded immutable buffer reads

Library `EthVmCore`. This standalone adapter uses the public Base padded-window
provider; the prospective aligned Memory carrier remains separate. Exact natural
offsets are checked by that provider before any packed index conversion.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/5/7.
-/

namespace STFSpec.Vm.Core
open STFSpec.Base

/-- Read exactly `size` bytes, padding unavailable bytes with zeros.
EELS `src/ethereum/forks/amsterdam/vm/memory.py:63,82–83` casts both operands to
unbounded Uint before endpoint addition. No gas, Memory or host-width premise is
part of this total mathematical operation. -/
def bufferRead (b : Bytes) (start size : U256) : Bytes :=
  Bytes.extractPadded b start.toNat size.toNat

/-- Buffer reading is the existing public Base padded-window operation. -/
theorem bufferRead_eq_extractPadded (b : Bytes) (start size : U256) :
    bufferRead b start size = Bytes.extractPadded b start.toNat size.toNat := rfl

/-- The complete result model contains the available window followed by missing zeros. -/
theorem bufferRead_toList (b : Bytes) (start size : U256) :
    (bufferRead b start size).toList =
      (b.toList.drop start.toNat).take size.toNat ++
        List.replicate (size.toNat - min size.toNat (b.size - start.toNat)) 0 := by
  exact Bytes.toList_extractPadded_window b start.toNat size.toNat

/-- Every padded read has exactly the requested natural byte length. -/
theorem bufferRead_size (b : Bytes) (start size : U256) :
    (bufferRead b start size).size = size.toNat := by
  exact Bytes.size_extractPadded b start.toNat size.toNat

end STFSpec.Vm.Core
