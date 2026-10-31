/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Transfer-log public-facade clients

Library `EthConformance`. Private generic clients derive complete frame identity,
chronological full-log observations and every unchanged field from the two public
whole-Frame laws, and prove that the numeric topic spelling is the source `pad32`. No foreign container representation is unfolded.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Core.TransferLogCallerProofs
open STFSpec.Base STFSpec.Vm.Core

-- The numeric topic spelling is exact twelve-zero-byte left-padding, through public Base laws.
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

private theorem zero_complete_frame (f : Frame) (addr : Address) (topic : Hash32)
    (sender recipient : Address) :
    emitTransferLog f addr topic sender recipient U256.zero = f := by
  exact emitTransferLog_zero f addr topic sender recipient

private theorem chronological_full_logs (f : Frame) (addr : Address) (topic : Hash32)
    (sender recipient : Address) (amount : U256) (h : amount ≠ U256.zero) :
    (emitTransferLog f addr topic sender recipient amount).logs.toList =
      f.logs.toList ++ [Log.mk addr
        #[topic, Hash32.ofBytes32 sender.toU256.toBeBytes32,
          Hash32.ofBytes32 recipient.toU256.toBeBytes32] amount.toBeBytes32.toBytes] := by
  rw [emitTransferLog_of_ne_zero f addr topic sender recipient amount h,
    LogRope.toList_append, LogRope.toList_leaf]

private theorem unchanged_pc (f : Frame) (addr : Address) (topic : Hash32)
    (sender recipient : Address) (amount : U256) :
    (emitTransferLog f addr topic sender recipient amount).pc = f.pc := by
  by_cases h : amount = U256.zero
  · rw [h, emitTransferLog_zero]
  · rw [emitTransferLog_of_ne_zero f addr topic sender recipient amount h]

private theorem unchanged_stack (f : Frame) (addr : Address) (topic : Hash32)
    (sender recipient : Address) (amount : U256) :
    (emitTransferLog f addr topic sender recipient amount).stack = f.stack := by
  by_cases h : amount = U256.zero
  · rw [h, emitTransferLog_zero]
  · rw [emitTransferLog_of_ne_zero f addr topic sender recipient amount h]

private theorem unchanged_memory (f : Frame) (addr : Address) (topic : Hash32)
    (sender recipient : Address) (amount : U256) :
    (emitTransferLog f addr topic sender recipient amount).memory = f.memory := by
  by_cases h : amount = U256.zero
  · rw [h, emitTransferLog_zero]
  · rw [emitTransferLog_of_ne_zero f addr topic sender recipient amount h]

private theorem unchanged_gasMeter (f : Frame) (addr : Address) (topic : Hash32)
    (sender recipient : Address) (amount : U256) :
    (emitTransferLog f addr topic sender recipient amount).gasMeter = f.gasMeter := by
  by_cases h : amount = U256.zero
  · rw [h, emitTransferLog_zero]
  · rw [emitTransferLog_of_ne_zero f addr topic sender recipient amount h]

private theorem unchanged_accountsToDelete (f : Frame) (addr : Address) (topic : Hash32)
    (sender recipient : Address) (amount : U256) :
    (emitTransferLog f addr topic sender recipient amount).accountsToDelete =
      f.accountsToDelete := by
  by_cases h : amount = U256.zero
  · rw [h, emitTransferLog_zero]
  · rw [emitTransferLog_of_ne_zero f addr topic sender recipient amount h]

private theorem unchanged_returnData (f : Frame) (addr : Address) (topic : Hash32)
    (sender recipient : Address) (amount : U256) :
    (emitTransferLog f addr topic sender recipient amount).returnData = f.returnData := by
  by_cases h : amount = U256.zero
  · rw [h, emitTransferLog_zero]
  · rw [emitTransferLog_of_ne_zero f addr topic sender recipient amount h]

private theorem unchanged_accessedAddresses (f : Frame) (addr : Address) (topic : Hash32)
    (sender recipient : Address) (amount : U256) :
    (emitTransferLog f addr topic sender recipient amount).accessedAddresses =
      f.accessedAddresses := by
  by_cases h : amount = U256.zero
  · rw [h, emitTransferLog_zero]
  · rw [emitTransferLog_of_ne_zero f addr topic sender recipient amount h]

private theorem unchanged_accessedStorageKeys (f : Frame) (addr : Address) (topic : Hash32)
    (sender recipient : Address) (amount : U256) :
    (emitTransferLog f addr topic sender recipient amount).accessedStorageKeys =
      f.accessedStorageKeys := by
  by_cases h : amount = U256.zero
  · rw [h, emitTransferLog_zero]
  · rw [emitTransferLog_of_ne_zero f addr topic sender recipient amount h]

private theorem repeated_chronology (f : Frame) (addr addr' : Address)
    (topic topic' : Hash32) (sender recipient : Address) (a b : U256)
    (ha : a ≠ U256.zero) (hb : b ≠ U256.zero) :
    (emitTransferLog (emitTransferLog f addr topic sender recipient a)
      addr' topic' recipient sender b).logs.toList =
      f.logs.toList ++ [Log.mk addr
        #[topic, Hash32.ofBytes32 sender.toU256.toBeBytes32,
          Hash32.ofBytes32 recipient.toU256.toBeBytes32] a.toBeBytes32.toBytes,
        Log.mk addr'
        #[topic', Hash32.ofBytes32 recipient.toU256.toBeBytes32,
          Hash32.ofBytes32 sender.toU256.toBeBytes32] b.toBeBytes32.toBytes] := by
  rw [chronological_full_logs _ _ _ _ _ _ hb,
    chronological_full_logs _ _ _ _ _ _ ha, List.append_assoc]
  rfl

end STFSpec.Conformance.Vm.Core.TransferLogCallerProofs
