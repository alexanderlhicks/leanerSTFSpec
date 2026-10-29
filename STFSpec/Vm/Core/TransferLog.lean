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

-- The numeric topic spelling implements exact left-padding through public laws.
private theorem padded_topic_exists (sender : Address) :
    ∃ h : Hash32, h.toBytes = Bytes.leftPadZero sender.toBytes 32 := by
  have hs : (Hash32.ofBytes? (Bytes.leftPadZero sender.toBytes 32)).isSome := by
    apply Option.isSome_iff_ne_none.mpr
    intro hn
    have bad := Hash32.ofBytes?_eq_none_iff.mp hn
    apply bad
    rw [Bytes.size_leftPadZero, Address.size_toBytes]
    decide
  refine ⟨(Hash32.ofBytes? (Bytes.leftPadZero sender.toBytes 32)).get hs, ?_⟩
  exact (Hash32.ofBytes?_eq_some_iff.mp (Option.some_get hs).symm).2

private theorem fold_zero_prefix (n : Nat) :
    (List.replicate n (0 : UInt8)).foldl (fun acc b ↦ 256 * acc + b.toNat) 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.foldl_cons, UInt8.toNat_zero,
      Nat.mul_zero, Nat.zero_add] using ih

private theorem numeric_topic_toBytes (sender : Address) :
    (Hash32.ofBytes32 sender.toU256.toBeBytes32).toBytes =
      Bytes.leftPadZero sender.toBytes 32 := by
  obtain ⟨padded, hpadded⟩ := padded_topic_exists sender
  have hp : padded.toNat = sender.toNat := by
    rw [Hash32.toNat_eq_fold, hpadded, Bytes.toList_leftPadZero,
      Address.size_toBytes, List.foldl_append, fold_zero_prefix,
      ← Address.toNat_eq_fold]
  have he : Hash32.ofBytes32 sender.toU256.toBeBytes32 = padded := by
    apply Hash32.toNat_inj.mp
    rw [Hash32.toNat_ofBytes32, U256.toNat_toBeBytes32, Address.toNat_toU256, hp]
  rw [he, hpadded]

private theorem numeric_topic_full_model (sender : Address) :
    (Hash32.ofBytes32 sender.toU256.toBeBytes32).toBytes.toList =
      List.replicate 12 0 ++ sender.toBytes.toList := by
  rw [numeric_topic_toBytes, Bytes.toList_leftPadZero, Address.size_toBytes]

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
