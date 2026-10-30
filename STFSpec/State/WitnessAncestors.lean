/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import Init.Data.ByteArray.Basic

/-!
# Opaque witness ancestor selection

Library `EthState`: select an ordered suffix of supplied byte payloads without decoding.
Spec guidance: `STFSpec/informal/modules/EthState.md` R27/§3/§5/§7.
-/

namespace STFSpec.State

/-- Select the headers requested by an optional ancestor offset.
Implements `src/ethereum/forks/amsterdam/state_tracker.py:903–922` at the pin.
Zero retains every header, matching Python's `[-0:]`; payloads remain opaque. -/
def getWitnessAncestors (headers : List ByteArray) (offset : Option Nat) : List ByteArray :=
  match offset with
  | none => []
  | some n => if n = 0 then headers else headers.drop (headers.length - n)

/-- Complete value equation, including absent, zero and arbitrarily large offsets. -/
theorem getWitnessAncestors_eq (headers : List ByteArray) (offset : Option Nat) :
    getWitnessAncestors headers offset =
      match offset with
      | none => []
      | some n => if n = 0 then headers else headers.drop (headers.length - n) := rfl

end STFSpec.State
