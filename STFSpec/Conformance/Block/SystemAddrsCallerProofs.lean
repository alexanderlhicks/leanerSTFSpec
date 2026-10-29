/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block

/-!
# Public raw system-address clients

Library `EthConformance`. Complete arbitrary construction, reconstruction and updates
through the public Block facade, with full nominal and byte observations.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–7.
-/

open STFSpec.Base STFSpec.Block

private def constructor_type :
    Address → Address → Address → Address → Address → Address → Address → Address →
      Nat → Nat → SystemAddrs := SystemAddrs.mk

private def systemAddress_type : SystemAddrs → Address := SystemAddrs.systemAddress
private def beaconRoots_type : SystemAddrs → Address := SystemAddrs.beaconRoots
private def historyStorage_type : SystemAddrs → Address := SystemAddrs.historyStorage
private def withdrawalRequests_type : SystemAddrs → Address := SystemAddrs.withdrawalRequests
private def consolidationRequests_type : SystemAddrs → Address :=
  SystemAddrs.consolidationRequests
private def builderDeposits_type : SystemAddrs → Address := SystemAddrs.builderDeposits
private def builderExits_type : SystemAddrs → Address := SystemAddrs.builderExits
private def depositContract_type : SystemAddrs → Address := SystemAddrs.depositContract
private def txGas_type : SystemAddrs → Nat := SystemAddrs.txGas
private def maxSstoresPerCall_type : SystemAddrs → Nat := SystemAddrs.maxSstoresPerCall

private theorem systemAddress_projection (a b c d e f g h : Address) (gas stores : Nat) :
    (SystemAddrs.mk a b c d e f g h gas stores).systemAddress = a := rfl

private theorem beaconRoots_projection (a b c d e f g h : Address) (gas stores : Nat) :
    (SystemAddrs.mk a b c d e f g h gas stores).beaconRoots = b := rfl

private theorem historyStorage_projection (a b c d e f g h : Address) (gas stores : Nat) :
    (SystemAddrs.mk a b c d e f g h gas stores).historyStorage = c := rfl

private theorem withdrawalRequests_projection (a b c d e f g h : Address) (gas stores : Nat) :
    (SystemAddrs.mk a b c d e f g h gas stores).withdrawalRequests = d := rfl

private theorem consolidationRequests_projection (a b c d e f g h : Address) (gas stores : Nat) :
    (SystemAddrs.mk a b c d e f g h gas stores).consolidationRequests = e := rfl

private theorem builderDeposits_projection (a b c d e f g h : Address) (gas stores : Nat) :
    (SystemAddrs.mk a b c d e f g h gas stores).builderDeposits = f := rfl

private theorem builderExits_projection (a b c d e f g h : Address) (gas stores : Nat) :
    (SystemAddrs.mk a b c d e f g h gas stores).builderExits = g := rfl

private theorem depositContract_projection (a b c d e f g h : Address) (gas stores : Nat) :
    (SystemAddrs.mk a b c d e f g h gas stores).depositContract = h := rfl

private theorem txGas_projection (a b c d e f g h : Address) (gas stores : Nat) :
    (SystemAddrs.mk a b c d e f g h gas stores).txGas = gas := rfl

private theorem maxSstoresPerCall_projection (a b c d e f g h : Address) (gas stores : Nat) :
    (SystemAddrs.mk a b c d e f g h gas stores).maxSstoresPerCall = stores := rfl

private theorem reconstruct (p : SystemAddrs) :
    SystemAddrs.mk p.systemAddress p.beaconRoots p.historyStorage p.withdrawalRequests
      p.consolidationRequests p.builderDeposits p.builderExits p.depositContract
      p.txGas p.maxSstoresPerCall = p := rfl

private def observe (p : SystemAddrs) : List Address × Nat × Nat :=
  ([p.systemAddress, p.beaconRoots, p.historyStorage, p.withdrawalRequests,
    p.consolidationRequests, p.builderDeposits, p.builderExits, p.depositContract],
    p.txGas, p.maxSstoresPerCall)

private theorem update_systemAddress (p : SystemAddrs) (value : Address) :
    observe { p with systemAddress := value } =
      ([value, p.beaconRoots, p.historyStorage, p.withdrawalRequests,
        p.consolidationRequests, p.builderDeposits, p.builderExits, p.depositContract],
        p.txGas, p.maxSstoresPerCall) := rfl

private theorem update_beaconRoots (p : SystemAddrs) (value : Address) :
    observe { p with beaconRoots := value } =
      ([p.systemAddress, value, p.historyStorage, p.withdrawalRequests,
        p.consolidationRequests, p.builderDeposits, p.builderExits, p.depositContract],
        p.txGas, p.maxSstoresPerCall) := rfl

private theorem update_historyStorage (p : SystemAddrs) (value : Address) :
    observe { p with historyStorage := value } =
      ([p.systemAddress, p.beaconRoots, value, p.withdrawalRequests,
        p.consolidationRequests, p.builderDeposits, p.builderExits, p.depositContract],
        p.txGas, p.maxSstoresPerCall) := rfl

private theorem update_withdrawalRequests (p : SystemAddrs) (value : Address) :
    observe { p with withdrawalRequests := value } =
      ([p.systemAddress, p.beaconRoots, p.historyStorage, value,
        p.consolidationRequests, p.builderDeposits, p.builderExits, p.depositContract],
        p.txGas, p.maxSstoresPerCall) := rfl

private theorem update_consolidationRequests (p : SystemAddrs) (value : Address) :
    observe { p with consolidationRequests := value } =
      ([p.systemAddress, p.beaconRoots, p.historyStorage, p.withdrawalRequests,
        value, p.builderDeposits, p.builderExits, p.depositContract],
        p.txGas, p.maxSstoresPerCall) := rfl

private theorem update_builderDeposits (p : SystemAddrs) (value : Address) :
    observe { p with builderDeposits := value } =
      ([p.systemAddress, p.beaconRoots, p.historyStorage, p.withdrawalRequests,
        p.consolidationRequests, value, p.builderExits, p.depositContract],
        p.txGas, p.maxSstoresPerCall) := rfl

private theorem update_builderExits (p : SystemAddrs) (value : Address) :
    observe { p with builderExits := value } =
      ([p.systemAddress, p.beaconRoots, p.historyStorage, p.withdrawalRequests,
        p.consolidationRequests, p.builderDeposits, value, p.depositContract],
        p.txGas, p.maxSstoresPerCall) := rfl

private theorem update_depositContract (p : SystemAddrs) (value : Address) :
    observe { p with depositContract := value } =
      ([p.systemAddress, p.beaconRoots, p.historyStorage, p.withdrawalRequests,
        p.consolidationRequests, p.builderDeposits, p.builderExits, value],
        p.txGas, p.maxSstoresPerCall) := rfl

private theorem update_txGas (p : SystemAddrs) (value : Nat) :
    observe { p with txGas := value } =
      ([p.systemAddress, p.beaconRoots, p.historyStorage, p.withdrawalRequests,
        p.consolidationRequests, p.builderDeposits, p.builderExits, p.depositContract],
        value, p.maxSstoresPerCall) := rfl

private theorem update_maxSstoresPerCall (p : SystemAddrs) (value : Nat) :
    observe { p with maxSstoresPerCall := value } =
      ([p.systemAddress, p.beaconRoots, p.historyStorage, p.withdrawalRequests,
        p.consolidationRequests, p.builderDeposits, p.builderExits, p.depositContract],
        p.txGas, value) := rfl

private def observeBytes (p : SystemAddrs) : List (List UInt8) × Nat × Nat :=
  ((observe p).1.map (fun a ↦ a.toBytes.toList), p.txGas, p.maxSstoresPerCall)

private def address1 : Address := Address.ofNat 0x1d242b323940474e555c636a71787f868d949ba2
private def address2 : Address := Address.ofNat 0x3a41484f565d646b727980878e959ca3aab1b8bf
private def address3 : Address := Address.ofNat 0x575e656c737a81888f969da4abb2b9c0c7ced5dc
private def address4 : Address := Address.ofNat 0x747b828990979ea5acb3bac1c8cfd6dde4ebf2f9
private def address5 : Address := Address.ofNat 0x91989fa6adb4bbc2c9d0d7dee5ecf3fa01080f16
private def address6 : Address := Address.ofNat 0xaeb5bcc3cad1d8dfe6edf4fb020910171e252c33
private def address7 : Address := Address.ofNat 0xcbd2d9e0e7eef5fc030a11181f262d343b424950
private def address8 : Address := Address.ofNat 0xe8eff6fd040b121920272e353c434a51585f666d
private def address9 : Address := Address.ofNat 0x050c131a21282f363d444b525960676e757c838a

private def addresses : List Address :=
  [address1, address2, address3, address4, address5, address6, address7, address8]

private def addressBytes : List (List UInt8) :=
  [[29, 36, 43, 50, 57, 64, 71, 78, 85, 92, 99, 106, 113, 120, 127, 134, 141, 148, 155, 162],
   [58, 65, 72, 79, 86, 93, 100, 107, 114, 121, 128, 135, 142, 149, 156, 163, 170, 177, 184, 191],
   [87, 94, 101, 108, 115, 122, 129, 136, 143, 150,
    157, 164, 171, 178, 185, 192, 199, 206, 213, 220],
   [116, 123, 130, 137, 144, 151, 158, 165, 172, 179,
    186, 193, 200, 207, 214, 221, 228, 235, 242, 249],
   [145, 152, 159, 166, 173, 180, 187, 194, 201, 208, 215, 222, 229, 236, 243, 250, 1, 8, 15, 22],
   [174, 181, 188, 195, 202, 209, 216, 223, 230, 237, 244, 251, 2, 9, 16, 23, 30, 37, 44, 51],
   [203, 210, 217, 224, 231, 238, 245, 252, 3, 10, 17, 24, 31, 38, 45, 52, 59, 66, 73, 80],
   [232, 239, 246, 253, 4, 11, 18, 25, 32, 39, 46, 53, 60, 67, 74, 81, 88, 95, 102, 109]]

private def replacementBytes : List UInt8 :=
  [5, 12, 19, 26, 33, 40, 47, 54, 61, 68, 75, 82, 89, 96, 103, 110, 117, 124, 131, 138]

private def sample : SystemAddrs :=
  SystemAddrs.mk address1 address2 address3 address4 address5 address6 address7 address8 17 43

#guard decide (observe sample = (addresses, 17, 43))
#guard observeBytes sample == (addressBytes, 17, 43)

private def zero : SystemAddrs :=
  let a := Address.ofNat 0
  SystemAddrs.mk a a a a a a a a 0 0

#guard decide (observe zero = (List.replicate 8 (Address.ofNat 0), 0, 0))
#guard observeBytes zero == (List.replicate 8 (List.replicate 20 0), 0, 0)

#guard decide (observe { sample with txGas := 2 ^ 256 } =
  (addresses, 2 ^ 256, 43))
#guard observeBytes { sample with txGas := 2 ^ 256 } ==
  (addressBytes, 2 ^ 256, 43)

#guard decide (observe { sample with maxSstoresPerCall := 2 ^ 512 + 1 } =
  (addresses, 17, 2 ^ 512 + 1))
#guard observeBytes { sample with maxSstoresPerCall := 2 ^ 512 + 1 } ==
  (addressBytes, 17, 2 ^ 512 + 1)

#guard observeBytes { sample with txGas := 0, maxSstoresPerCall := 2 ^ 300 + 7 } ==
  (addressBytes, 0, 2 ^ 300 + 7)
#guard observeBytes { sample with txGas := 2 ^ 400 + 11, maxSstoresPerCall := 0 } ==
  (addressBytes, 2 ^ 400 + 11, 0)

#guard decide (observe { sample with systemAddress := address9 } =
  (addresses.set 0 address9, 17, 43))
#guard observeBytes { sample with systemAddress := address9 } ==
  (addressBytes.set 0 replacementBytes, 17, 43)

#guard decide (observe { sample with beaconRoots := address9 } =
  (addresses.set 1 address9, 17, 43))
#guard observeBytes { sample with beaconRoots := address9 } ==
  (addressBytes.set 1 replacementBytes, 17, 43)

#guard decide (observe { sample with historyStorage := address9 } =
  (addresses.set 2 address9, 17, 43))
#guard observeBytes { sample with historyStorage := address9 } ==
  (addressBytes.set 2 replacementBytes, 17, 43)

#guard decide (observe { sample with withdrawalRequests := address9 } =
  (addresses.set 3 address9, 17, 43))
#guard observeBytes { sample with withdrawalRequests := address9 } ==
  (addressBytes.set 3 replacementBytes, 17, 43)

#guard decide (observe { sample with consolidationRequests := address9 } =
  (addresses.set 4 address9, 17, 43))
#guard observeBytes { sample with consolidationRequests := address9 } ==
  (addressBytes.set 4 replacementBytes, 17, 43)

#guard decide (observe { sample with builderDeposits := address9 } =
  (addresses.set 5 address9, 17, 43))
#guard observeBytes { sample with builderDeposits := address9 } ==
  (addressBytes.set 5 replacementBytes, 17, 43)

#guard decide (observe { sample with builderExits := address9 } =
  (addresses.set 6 address9, 17, 43))
#guard observeBytes { sample with builderExits := address9 } ==
  (addressBytes.set 6 replacementBytes, 17, 43)

#guard decide (observe { sample with depositContract := address9 } =
  (addresses.set 7 address9, 17, 43))
#guard observeBytes { sample with depositContract := address9 } ==
  (addressBytes.set 7 replacementBytes, 17, 43)
