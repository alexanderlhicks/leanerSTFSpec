/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.Frame
import STFSpec.Base.IntegerBytes

/-!
# Pure supplied-address transfer logs

Library `EthVmCore`. Zero amounts preserve the actual complete frame. Nonzero
amounts append one complete log, leaving producer guards and context to callers.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§2.2/3/5/7.
-/

namespace STFSpec.Vm.Core
open STFSpec.Base

/-- Append an EIP-7708 transfer log, or return the actual frame for amount zero.
Pinned EELS `src/ethereum/forks/amsterdam/vm/__init__.py:253–289`.
Address and first topic are supplied; this pure helper performs no hash query,
producer self-suppression, transfer, charge, static check or settlement. -/
def emitTransferLog (f : Frame) (systemAddress : Address) (topic : Hash32)
    (sender recipient : Address) (amount : U256) : Frame :=
  if amount = U256.zero then f else
    { f with logs := LogRope.append f.logs (LogRope.leaf
      [Log.mk systemAddress
        #[topic, Hash32.ofBytes32 sender.toU256.toBeBytes32,
          Hash32.ofBytes32 recipient.toU256.toBeBytes32]
        amount.toBeBytes32.toBytes]) }

/-- A zero amount preserves the complete supplied frame, including raw log shape. -/
theorem emitTransferLog_zero (f : Frame) (systemAddress : Address) (topic : Hash32)
    (sender recipient : Address) :
    emitTransferLog f systemAddress topic sender recipient U256.zero = f := by
  simp only [emitTransferLog, ↓reduceIte]

/-- A nonzero amount updates only logs with the complete supplied-address entry.
No distinct-party, policy, gas, world or source-literal premise is required. -/
theorem emitTransferLog_of_ne_zero (f : Frame) (systemAddress : Address) (topic : Hash32)
    (sender recipient : Address) (amount : U256) (h : amount ≠ U256.zero) :
    emitTransferLog f systemAddress topic sender recipient amount =
      { f with logs := LogRope.append f.logs (LogRope.leaf
        [Log.mk systemAddress
          #[topic, Hash32.ofBytes32 sender.toU256.toBeBytes32,
            Hash32.ofBytes32 recipient.toU256.toBeBytes32]
          amount.toBeBytes32.toBytes]) } := by
  simp only [emitTransferLog, h, ↓reduceIte]

end STFSpec.Vm.Core
