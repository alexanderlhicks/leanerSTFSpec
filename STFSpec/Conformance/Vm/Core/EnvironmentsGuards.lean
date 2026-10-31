/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Complete raw environment controls

Library `EthConformance`. All fields are observed through complete public models.
Zero and distinct high/max markers, ordered duplicate arrays, raw 257-entry history,
noncanonical authorization parity and independent quantities/options are deliberate
carrier controls. They assert no protocol history or transaction admissibility.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/5/7.
-/

namespace STFSpec.Conformance.Vm.Core.EnvironmentsGuards
open STFSpec.Vm.Core STFSpec.Base

private def hash (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def max64 : Nat := 2 ^ 64 - 1
private def max160 : Nat := 2 ^ 160 - 1
private def max256 : Nat := 2 ^ 256 - 1
private def highAddress : Address := Address.ofNat (2 ^ 159 + 257)
private def maxAddress : Address := Address.ofNat max160
private def zeroAddress : Address := Address.ofNat 0
private def addresses : AddrSet := ((∅ : AddrSet).insert maxAddress).insert highAddress
private def slots : SlotSet :=
  (((∅ : SlotSet).insert (maxAddress, FixedBytes.ofNat 256)).insert
    (highAddress, FixedBytes.ofNat max256)).insert (highAddress, FixedBytes.ofNat 0)

private def blockView (e : BlockEnvironment) :=
  (e.chainId.toNat, e.blockGasLimit, e.blockHashes.toList.map Hash32.toNat,
    e.coinbase.toNat, e.number, e.baseFeePerGas, e.time.toNat, e.prevRandao.toNat,
    e.excessBlobGas.toNat, e.parentBeaconBlockRoot.toNat, e.slotNumber.toNat)

private def authorizationView (a : Authorization) :=
  (a.chainId.toNat, a.address.toNat, a.nonce.toNat, a.yParity.toNat, a.r.toNat, a.s.toNat)

private def transactionView (e : TransactionEnvironment) :=
  (e.origin.toNat, e.recipient.toNat, e.isCreate, e.data.toList, e.value.toNat,
    e.gasLimit, e.effectiveGasPrice, e.executionGasGrant, e.stateGasReservoir, e.calldataFloor,
    e.accessListAddresses.toList.map Address.toNat,
    e.accessListStorageKeys.toList.map (fun (address, slot) ↦ (address.toNat, slot.toNat)),
    e.blobVersionedHashes.toList.map Hash32.toNat,
    e.authorizations.toList.map authorizationView, e.indexInBlock, e.txHash.map Hash32.toNat)

private def zeroBlock : BlockEnvironment :=
  BlockEnvironment.mk U64.zero 0 #[] zeroAddress 0 0 U256.zero
    (FixedBytes.ofNat 0) U64.zero (hash 0) U64.zero

#guard blockView zeroBlock == (0, 0, [], 0, 0, 0, 0, 0, 0, 0, 0)

private def markedBlock : BlockEnvironment :=
  BlockEnvironment.mk U64.max (2 ^ 300 + 3)
    #[hash max256, hash 0, hash (2 ^ 255 + 17), hash max256] maxAddress
    (2 ^ 301 + 5) (2 ^ 302 + 7) U256.max (FixedBytes.ofNat max256)
    (U64.ofNat (2 ^ 63 + 11)) (hash (2 ^ 255 + 19)) (U64.ofNat (max64 - 1))

#guard blockView markedBlock ==
  (max64, 2 ^ 300 + 3, [max256, 0, 2 ^ 255 + 17, max256], max160,
    2 ^ 301 + 5, 2 ^ 302 + 7, max256, max256, 2 ^ 63 + 11, 2 ^ 255 + 19, max64 - 1)

-- This synthetic history is intentionally duplicated, unordered and longer than 256.
private def rawHistory : Array Hash32 := #[hash 2, hash 1, hash 2] ++ (Array.range 254).map hash
private def longHistoryBlock : BlockEnvironment := { markedBlock with blockHashes := rawHistory }

#guard longHistoryBlock.blockHashes.size == 257
#guard blockView longHistoryBlock ==
  (max64, 2 ^ 300 + 3, [2, 1, 2] ++ List.range 254, max160,
    2 ^ 301 + 5, 2 ^ 302 + 7, max256, max256, 2 ^ 63 + 11, 2 ^ 255 + 19, max64 - 1)

-- All six components remain raw; parity 255 and 2 are not signature-validity claims.
private def zeroAuthorization : Authorization :=
  Authorization.mk U256.zero zeroAddress U64.zero U8.zero U256.zero U256.zero
private def firstAuthorization : Authorization :=
  Authorization.mk (U256.ofNat (2 ^ 255 + 11)) highAddress U64.max (U8.ofNat 255)
    U256.max (U256.ofNat (2 ^ 255 + 9))
private def secondAuthorization : Authorization :=
  Authorization.mk U256.max maxAddress (U64.ofNat (2 ^ 63 + 3)) (U8.ofNat 2)
    (U256.ofNat 256) (U256.ofNat 1)
private def authorizations : Array Authorization :=
  #[firstAuthorization, zeroAuthorization, secondAuthorization, firstAuthorization]
private def expectedAuthorizations :=
  [(2 ^ 255 + 11, 2 ^ 159 + 257, max64, 255, max256, 2 ^ 255 + 9),
    (0, 0, 0, 0, 0, 0),
    (max256, max160, 2 ^ 63 + 3, 2, 256, 1),
    (2 ^ 255 + 11, 2 ^ 159 + 257, max64, 255, max256, 2 ^ 255 + 9)]

private def zeroTransaction : TransactionEnvironment :=
  TransactionEnvironment.mk zeroAddress zeroAddress false Bytes.empty U256.zero
    0 0 0 0 0 ∅ ∅ #[] #[] none none

#guard transactionView zeroTransaction ==
  (0, 0, false, [], 0, 0, 0, 0, 0, 0, [], [], [], [], none, none)

-- Grant, reservoir and floor may exceed the independent limit in a raw carrier.
private def markedTransaction : TransactionEnvironment :=
  TransactionEnvironment.mk highAddress maxAddress true (Bytes.ofList [0, 255, 128, 1, 0])
    U256.max (2 ^ 300 + 3) (2 ^ 301 + 5) (2 ^ 302 + 7) (2 ^ 303 + 11) (2 ^ 304 + 13)
    addresses slots #[hash (2 ^ 255 + 23), hash 0, hash max256, hash (2 ^ 255 + 23)]
    authorizations (some 0) (some (hash 0))

#guard transactionView markedTransaction ==
  (2 ^ 159 + 257, max160, true, [0, 255, 128, 1, 0], max256,
    2 ^ 300 + 3, 2 ^ 301 + 5, 2 ^ 302 + 7, 2 ^ 303 + 11, 2 ^ 304 + 13,
    [2 ^ 159 + 257, max160],
    [(2 ^ 159 + 257, 0), (2 ^ 159 + 257, max256), (max160, 256)],
    [2 ^ 255 + 23, 0, max256, 2 ^ 255 + 23], expectedAuthorizations, some 0, some 0)

private def indexedTransaction : TransactionEnvironment :=
  { markedTransaction with
    origin := maxAddress
    recipient := zeroAddress
    isCreate := false
    indexInBlock := some (2 ^ 350 + 17)
    txHash := some (hash max256) }

#guard transactionView indexedTransaction ==
  (max160, 0, false, [0, 255, 128, 1, 0], max256,
    2 ^ 300 + 3, 2 ^ 301 + 5, 2 ^ 302 + 7, 2 ^ 303 + 11, 2 ^ 304 + 13,
    [2 ^ 159 + 257, max160],
    [(2 ^ 159 + 257, 0), (2 ^ 159 + 257, max256), (max160, 256)],
    [2 ^ 255 + 23, 0, max256, 2 ^ 255 + 23], expectedAuthorizations,
    some (2 ^ 350 + 17), some max256)

-- A snapshot with one zeroed quantity retains every unrelated supplied field.
private theorem zero_price_retains_complete_transaction :
    { markedTransaction with effectiveGasPrice := 0 } =
      TransactionEnvironment.mk highAddress maxAddress true (Bytes.ofList [0, 255, 128, 1, 0])
        U256.max (2 ^ 300 + 3) 0 (2 ^ 302 + 7) (2 ^ 303 + 11) (2 ^ 304 + 13)
        addresses slots #[hash (2 ^ 255 + 23), hash 0, hash max256, hash (2 ^ 255 + 23)]
        authorizations (some 0) (some (hash 0)) := by
  rfl

end STFSpec.Conformance.Vm.Core.EnvironmentsGuards
