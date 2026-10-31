/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Complete transfer-log controls

Library `EthConformance`. Hand-selected arbitrary emitter/topic inputs and full
independent byte-model expectations. Retained input and repeated-call controls
exercise empty, leaf and concatenated ropes with duplicate prior entries.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Core.TransferLogGuards
open STFSpec.Base STFSpec.Vm.Core

private def words : Stack :=
  ((Stack.empty.push (U256.ofNat 7)).toOption.get (by decide)).push
    (U256.ofNat (2 ^ 255 + 19)) |>.toOption.get (by decide)
private def expanded : Memory := Memory.empty.expand 32 (by decide)
private theorem expanded_size : expanded.size = 32 := by
  rw [← Memory.length_toBytes, expanded, Memory.toBytes_expand, Memory.toBytes_empty]
  rfl
private def written : Memory := expanded.write 2 (Bytes.ofList [0, 128, 255, 1]) (by
  right
  rw [expanded_size]
  decide)
private def deleted : AddrSet := (∅ : AddrSet).insert (Address.ofNat 256)
private def warm : AddrSet := (∅ : AddrSet).insert (Address.ofNat 1)
private def slots : SlotSet := ((∅ : SlotSet).insert
  (Address.ofNat 1, FixedBytes.ofNat 256)).insert (Address.ofNat 256, FixedBytes.ofNat 1)
private def oldLog : Log := Log.mk (Address.ofNat 256)
  #[Hash32.ofBytes32 (FixedBytes.ofNat 256), Hash32.ofBytes32 (FixedBytes.ofNat 1),
    Hash32.ofBytes32 (FixedBytes.ofNat 256)] (Bytes.ofList [255, 0, 128])
private def rawRope : LogRope := .concat (.leaf [oldLog]) (.concat .empty (.leaf [oldLog]))
private def sample (logs : LogRope) : Frame :=
  Frame.mk (2 ^ 300 + 19) words written
    (GasMeter.mk 3 101 2 (-17) 5 11) logs deleted
    (Bytes.ofList [0, 255, 128, 0]) warm slots

private def logModel (entry : Log) :=
  (entry.address.toBytes.toList, entry.topics.toList.map (fun t ↦ t.toBytes.toList),
    entry.data.toList)
private def frameModel (f : Frame) :=
  (f.pc, f.stack.toList.map U256.toNat, f.memory.toBytes,
    (f.gasMeter.gasLeft, f.gasMeter.stateGasLeft, f.gasMeter.stateGasBaseline,
      f.gasMeter.refundCounter, f.gasMeter.stateGasSpilled, f.gasMeter.stateGasCommittedSpill),
    f.logs.toList.map logModel, f.accountsToDelete.toList.map Address.toNat,
    f.returnData.toList, f.accessedAddresses.toList.map Address.toNat,
    f.accessedStorageKeys.toList.map (fun (a, k) ↦ (a.toNat, k.toNat)))
private def expected (logs : List (List UInt8 × List (List UInt8) × List UInt8)) :=
  (2 ^ 300 + 19, [2 ^ 255 + 19, 7], ([0, 0, 0, 128, 255, 1] : List UInt8) ++ List.replicate 26 0,
    (3, 101, 2, (-17 : Int), 5, 11), logs, [256], ([0, 255, 128, 0] : List UInt8), [1],
    [(1, 256), (256, 1)])
private def oldModel : List UInt8 × List (List UInt8) × List UInt8 :=
  (List.replicate 18 0 ++ [1, 0],
    [List.replicate 30 0 ++ [1, 0], List.replicate 31 0 ++ [1],
      List.replicate 30 0 ++ [1, 0]], [255, 0, 128])

-- Complete case 01: every frame field and every log byte.
#guard frameModel (emitTransferLog (sample (.empty))
  (Address.ofNat 0) (Hash32.ofBytes32 (FixedBytes.ofNat 0))
  (Address.ofNat 0) (Address.ofNat 1) (U256.ofNat 0)) ==
    expected ([])

-- Complete case 02: every frame field and every log byte.
#guard frameModel (emitTransferLog (sample (.leaf [oldLog, oldLog]))
  (Address.ofNat 1) (Hash32.ofBytes32 (FixedBytes.ofNat 1))
  (Address.ofNat 1) (Address.ofNat 0) (U256.ofNat 1)) ==
    expected ([oldModel, oldModel] ++ [([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0]], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 1])])

-- Complete case 03: every frame field and every log byte.
#guard frameModel (emitTransferLog (sample (rawRope))
  (Address.ofNat 730750818665451459101842416358141509827966271616) (Hash32.ofBytes32
    (FixedBytes.ofNat
    57896044618658097711785492504343953926634992332820282019728792003956564820225))
  (Address.ofNat 730750818665451459101842416358141509827966271488) (Address.ofNat 1) (U256.ofNat
    57896044618658097711785492504343953926634992332820282019728792003956564819968)) ==
    expected ([oldModel, oldModel] ++ [([128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      128], [[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 1]], [128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])])

-- Complete case 04: every frame field and every log byte.
#guard frameModel (emitTransferLog (sample (rawRope))
  (Address.ofNat 1461501637330902918203684832716283019655932542975) (Hash32.ofBytes32
    (FixedBytes.ofNat
    115792089237316195423570985008687907853269984665640564039457584007913129639935))
  (Address.ofNat 1461501637330902918203684832716283019655932542975) (Address.ofNat 0) (U256.ofNat
    115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==
    expected ([oldModel, oldModel] ++ [([255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255], [[255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255], [0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], [255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255])])

-- Complete case 05: every frame field and every log byte.
#guard frameModel (emitTransferLog (sample (rawRope))
  (Address.ofNat 1) (Hash32.ofBytes32 (FixedBytes.ofNat 1))
  (Address.ofNat 256) (Address.ofNat 256) (U256.ofNat 1)) ==
    expected ([oldModel, oldModel] ++ [([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, 0]], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 1])])

-- Complete case 06: every frame field and every log byte.
#guard frameModel (emitTransferLog (sample (rawRope))
  (Address.ofNat 256) (Hash32.ofBytes32 (FixedBytes.ofNat 1))
  (Address.ofNat 256) (Address.ofNat 256) (U256.ofNat 1)) ==
    expected ([oldModel, oldModel] ++ [([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      0], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, 0]], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 1])])

-- Complete case 07: every frame field and every log byte.
#guard frameModel (emitTransferLog (sample (rawRope))
  (Address.ofNat 1) (Hash32.ofBytes32 (FixedBytes.ofNat 256))
  (Address.ofNat 256) (Address.ofNat 256) (U256.ofNat 1)) ==
    expected ([oldModel, oldModel] ++ [([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, 0]], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 1])])

-- Complete case 08: every frame field and every log byte.
#guard frameModel (emitTransferLog (sample (.empty))
  (Address.ofNat 1) (Hash32.ofBytes32 (FixedBytes.ofNat 1))
  (Address.ofNat 1) (Address.ofNat 256) (U256.ofNat 1)) ==
    expected ([] ++ [([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [[0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      0]], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 1])])

-- Complete case 09: every frame field and every log byte.
#guard frameModel (emitTransferLog (sample (.leaf [oldLog, oldLog]))
  (Address.ofNat 1) (Hash32.ofBytes32 (FixedBytes.ofNat 1))
  (Address.ofNat 256) (Address.ofNat 1) (U256.ofNat 1)) ==
    expected ([oldModel, oldModel] ++ [([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1]], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 1])])

-- Complete case 10: every frame field and every log byte.
#guard frameModel (emitTransferLog (sample (rawRope))
  (Address.ofNat 0) (Hash32.ofBytes32 (FixedBytes.ofNat 0))
  (Address.ofNat 730750818665451459101842416358141509827966271616) (Address.ofNat 0) (U256.ofNat
    1)) ==
    expected ([oldModel, oldModel] ++ [([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 128], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0]], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 1])])

-- Complete case 11: every frame field and every log byte.
#guard frameModel (emitTransferLog (sample (.leaf [oldLog, oldLog]))
  (Address.ofNat 1461501637330902918203684832716283019655932542975) (Hash32.ofBytes32
    (FixedBytes.ofNat 0))
  (Address.ofNat 0) (Address.ofNat 1461501637330902918203684832716283019655932542975) (U256.ofNat
    1)) ==
    expected ([oldModel, oldModel] ++ [([255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255]], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1])])

-- Complete case 12: every frame field and every log byte.
#guard frameModel (emitTransferLog (sample (rawRope))
  (Address.ofNat 1) (Hash32.ofBytes32 (FixedBytes.ofNat
    57896044618658097711785492504343953926634992332820282019728792003956564819968))
  (Address.ofNat 22475995960490625424124334220934763854762515) (Address.ofNat
    730750818665451459101842416358141509827966271616) (U256.ofNat
    57896044618658097711785492504343953926634992332820282019728792003956564819969)) ==
    expected ([oldModel, oldModel] ++ [([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1], [[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12,
      13, 14, 15, 16, 17, 18, 19], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128]], [128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])])

-- Complete case 13: every frame field and every log byte.
#guard frameModel (emitTransferLog (sample (rawRope))
  (Address.ofNat 256) (Hash32.ofBytes32 (FixedBytes.ofNat 257))
  (Address.ofNat 730750818665451459101842416358141509827966271616) (Address.ofNat
    22475995960490625424124334220934763854762515) (U256.ofNat
    115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==
    expected ([oldModel, oldModel] ++ [([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      0], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 128], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
      12, 13, 14, 15, 16, 17, 18, 19]], [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255])])

-- Complete case 14: every frame field and every log byte.
#guard frameModel (emitTransferLog (sample (rawRope))
  (Address.ofNat 730750818665451459101842416358141509827966271488) (Hash32.ofBytes32
    (FixedBytes.ofNat
    115792089237316195423570985008687907853269984665640564039457584007913129639935))
  (Address.ofNat 1) (Address.ofNat 1) (U256.ofNat 0)) ==
    expected ([oldModel, oldModel])

-- Complete case 15: every frame field and every log byte.
#guard frameModel (emitTransferLog (sample (.empty))
  (Address.ofNat 1) (Hash32.ofBytes32 (FixedBytes.ofNat 0))
  (Address.ofNat 0) (Address.ofNat 0) (U256.ofNat 1)) ==
    expected ([] ++ [([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [[0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0]], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 1])])

-- Complete case 16: every frame field and every log byte.
#guard frameModel (emitTransferLog (sample (.leaf [oldLog, oldLog]))
  (Address.ofNat 0) (Hash32.ofBytes32 (FixedBytes.ofNat 1))
  (Address.ofNat 1461501637330902918203684832716283019655932542975) (Address.ofNat
    1461501637330902918203684832716283019655932542975) (U256.ofNat
    115792089237316195423570985008687907853269984665640564039457584007913129639935)) ==
    expected ([oldModel, oldModel] ++ [([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255]], [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255])])

private def first : Frame := emitTransferLog (sample rawRope) (Address.ofNat 1)
  (Hash32.ofBytes32 (FixedBytes.ofNat 2)) (Address.ofNat 3) (Address.ofNat 4) U256.one
private def second : Frame := emitTransferLog first (Address.ofNat 5)
  (Hash32.ofBytes32 (FixedBytes.ofNat 6)) (Address.ofNat 4) (Address.ofNat 3)
  (U256.ofNat 256)
#guard frameModel (sample rawRope) == expected [oldModel, oldModel]
#guard frameModel first == expected [oldModel, oldModel, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 1], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 4]], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 1])]
#guard frameModel second == expected [oldModel, oldModel, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 1], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 4]], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 1]), ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5], [[0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6], [0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4], [0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3]],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
  0])]

end STFSpec.Conformance.Vm.Core.TransferLogGuards
