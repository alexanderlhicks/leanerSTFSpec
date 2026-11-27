/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions
import STFSpec.Fork.Amsterdam
import STFSpec.State.BlockInitialization
import STFSpec.State.TransactionInitialization

/-!
# Delegation resolver controls

Library `EthConformance`. Exercise the public facade with recording providers and
the State precedence rules. Spec guidance in EthVmInstructions §4.
-/

namespace STFSpec.Conformance.Vm.Instructions.DelegationResolutionControls
open STFSpec.Base STFSpec.State STFSpec.Vm.Core STFSpec.Vm.Instructions

private inductive Placement where
  | tx | block | pre | missing | absent | reserved | malformed | self | provider | providerCodeFault | accountFault
  deriving BEq

private def addressOf (byte : UInt8) : Address :=
  (Address.ofBytes? (Bytes.ofList (List.replicate 20 byte))).getD (Address.ofNat 0)

private def hashOf (byte : UInt8) : Hash32 :=
  (Hash32.ofBytes? (Bytes.ofList (List.replicate 32 byte))).getD (Hash32.ofBytes32 (FixedBytes.ofNat 0))

private def origin := addressOf 0x61
private def delegate := Address.ofNat 0x000102030405060708090a0b0c0d0e0f10111213
private def secondary := addressOf 0x92
private def originalKey := hashOf 0x14
private def secondaryKey := hashOf 0x15
private def providerKey := hashOf 0x73
private def faultyKey := hashOf 0x79
private def reservedKey := HashConsts.literals.emptyCodeHash

private def tagged (destination : Address) : ByteArray :=
  (Bytes.ofList ([0xef, 0x01, 0x00] ++ destination.toBytes.toList)).toByteArray

private def keyFor (whereCode : Placement) : Hash32 :=
  match whereCode with
  | .reserved | .absent => reservedKey
  | .provider | .providerCodeFault => providerKey
  | _ => originalKey

private def token (key : Hash32) : Account := ⟨1, U256.ofNat 3, key⟩
private abbrev Calls := List (Nat × Nat)
private abbrev Reads := StateT Calls Id

private def provider (whereCode : Placement) : PreState Reads :=
  ⟨fun address ↦ do
      modify (· ++ [(0, address.toNat)])
      if address == origin && (whereCode == .provider || whereCode == .providerCodeFault) then
        pure (.ok (some (token providerKey)))
      else
        pure (.error (.missing (.node faultyKey))),
    fun address slot ↦ do
      modify (· ++ [(2, address.toNat + slot.toNat)])
      pure (.ok (U256.ofNat 151)),
    fun key ↦ do
      modify (· ++ [(1, key.toNat)])
      if (whereCode == .pre && key == originalKey) || (whereCode == .provider && key == providerKey) then
        pure (.ok (tagged delegate))
      else
        pure (.error (.missing (.code key))),
    fun _ ↦ do
      modify (· ++ [(3, 0)])
      pure (.ok faultyKey)⟩

private def world (whereCode : Placement) : VmWorld Reads :=
  let key := keyFor whereCode
  let initial := BlockState.new (provider whereCode) HashConsts.literals
  let block := { initial with
    accountWrites := if whereCode == .block || whereCode == .absent then
      initial.accountWrites.insert origin (some (token originalKey)) else initial.accountWrites
    codeWrites := if whereCode == .block || whereCode == .reserved || whereCode == .absent then
      initial.codeWrites.insert key (tagged delegate)
    else if whereCode == .tx || whereCode == .malformed || whereCode == .self then
      initial.codeWrites.insert key (ByteArray.mk #[0xfe])
    else initial.codeWrites
    oldestAncestorOffset := some (2 ^ 270 + 157) }
  let tx := TxState.new block
  let rev := tx.rev
  let accounts := rev.accountWrites.insert delegate (some (token secondaryKey))
  let accounts := match whereCode with
    | .block | .provider | .providerCodeFault | .accountFault => accounts
    | .absent => accounts.insert origin none
    | _ => accounts.insert origin (some (token key))
  let codes := rev.codeWrites.insert secondaryKey (tagged secondary)
  let codes := match whereCode with
    | .reserved | .absent | .tx => codes.insert key (tagged delegate)
    | .self => codes.insert key (tagged origin)
    | .malformed => codes.insert key ((tagged delegate).push 1)
    | _ => codes
  let rev := { rev with
    accountWrites := accounts
    codeWrites := codes
    transient := rev.transient.insert (addressOf 0xa5, FixedBytes.ofNat 163) (U256.ofNat 167) }
  ⟨{ tx with
    rev := rev
    obs := { tx.obs with
      storageReads := tx.obs.storageReads.insert (addressOf 0x33, FixedBytes.ofNat 173)
      createdAccounts := tx.obs.createdAccounts.insert (addressOf 0x5a) } }⟩

private abbrev MeterView := Nat × Nat × Nat × Int × Nat × Nat

private def meterFields (g : GasMeter) : MeterView :=
  (g.gasLeft, g.stateGasLeft, g.stateGasBaseline, g.refundCounter, g.stateGasSpilled, g.stateGasCommittedSpill)

private structure Observed where
  result : String
  returned : Option (Nat × Bool × MeterView × List Nat)
  accountReads : Option (List Nat)
  codeReads : Option (List Nat)
  faultKey : Option Nat
  calls : Calls
  unrelated : Option Bool
  deriving BEq

private def otherFields (w : VmWorld Reads) :=
  (w.tx.block.oldestAncestorOffset, w.tx.block.consts.emptyCodeHash.toNat,
    w.tx.block.accountWrites.toList.map
      (fun (a, v) ↦ (a.toNat, v.map (fun (account : Account) ↦ account.codeHash.toNat))),
    w.tx.block.codeWrites.toList.map (fun (h, code) ↦ (h.toNat, code.toList)),
    w.tx.rev.accountWrites.toList.map
      (fun (a, v) ↦ (a.toNat, v.map (fun (account : Account) ↦ account.codeHash.toNat))),
    w.tx.rev.codeWrites.toList.map (fun (h, code) ↦ (h.toNat, code.toList)),
    w.tx.rev.transient.toList.map (fun ((a,k), v) ↦ (a.toNat, k.toNat, v.toNat)),
    w.tx.obs.storageReads.toList.map (fun (a,k) ↦ (a.toNat, k.toNat)),
    w.tx.obs.createdAccounts.toList.map Address.toNat)

private def observe (whereCode : Placement) (gas : Nat) (warmTarget warmOrigin : Bool)
    (zeroPrice warmPrice coldPrice : Nat) : Observed :=
  let costs := { STFSpec.Fork.Amsterdam.gasCosts with
    zero := zeroPrice
    warmAccess := warmPrice
    coldAccountAccess := coldPrice }
  let g : GasMeter := ⟨gas, 71, 89, -13, 7, 11⟩
  let initial : AddrSet := (∅ : AddrSet).insert secondary
  let initial := if warmTarget then initial.insert delegate else initial
  let initial := if warmOrigin then initial.insert origin else initial
  let before := world whereCode
  let (result, calls) := (((resolveDelegatedCodeAddress costs g initial origin).run before).run).run []
  let retained := fun name returned (after : VmWorld Reads) ↦
    Observed.mk name returned
      (some (after.tx.obs.accountReads.toList.map Address.toNat).mergeSort)
      (some (after.tx.obs.codeReads.toList.map Hash32.toNat).mergeSort) none calls
      (some (otherFields after == otherFields before))
  match result with
  | .ok (.ok (to, flag, paid, warmed), after) =>
    retained "ok" (some (to.toNat, flag, meterFields paid, warmed.toList.map Address.toNat)) after
  | .ok (.error .outOfGas, after) => retained "out-of-gas" none after
  | .error (.state (.witness (.missing (.node key)))) =>
    ⟨"account-fault", none, none, none, some key.toNat, calls, none⟩
  | .error (.state (.witness (.missing (.code key)))) =>
    ⟨"code-fault", none, none, none, some key.toNat, calls, none⟩
  | _ => ⟨"unexpected", none, none, none, none, calls, none⟩

private def expected (to : Address) (flag : Bool) (gas : Nat) (warm : List Address)
    (codes : List Nat) (calls : Calls) : Observed :=
  ⟨"ok", some (to.toNat, flag, (gas, 71, 89, -13, 7, 11), warm.map Address.toNat),
    some [origin.toNat], some codes, none, calls, some true⟩

#guard observe .tx 43 false false 17 23 43 == expected delegate true 0 [delegate, secondary] [] []
#guard observe .block 23 true false 17 23 43 == expected delegate true 0 [delegate, secondary] [] []
#guard observe .tx 42 false false 17 23 43 == ⟨"out-of-gas", none, some [origin.toNat], some [], none, [], some true⟩
#guard observe .pre 0 false false 997 83 0 == expected delegate true 0 [delegate, secondary]
  [originalKey.toNat] [(1, originalKey.toNat)]
#guard observe .provider 43 false true 17 23 43 == expected delegate true 0 [delegate, origin, secondary]
  [providerKey.toNat] [(0, origin.toNat), (1, providerKey.toNat)]
#guard observe .accountFault 0 false false 277 0 0 ==
  ⟨"account-fault", none, none, none, some faultyKey.toNat, [(0, origin.toNat)], none⟩
#guard observe .missing 91 false false 17 0 0 ==
  ⟨"code-fault", none, none, none, some originalKey.toNat, [(1, originalKey.toNat)], none⟩
#guard observe .providerCodeFault 91 false false 17 0 0 ==
  ⟨"code-fault", none, none, none, some providerKey.toNat, [(0, origin.toNat), (1, providerKey.toNat)], none⟩
#guard observe .absent 0 true false 313 17 23 == expected origin false 0 [delegate, secondary] [] []
#guard observe .reserved 0 true false 313 17 23 == expected origin false 0 [delegate, secondary] [] []
#guard observe .malformed 0 false false 313 17 23 == expected origin false 0 [secondary] [] []
#guard observe .self 97 false false 0 83 97 == expected origin true 0 [origin, secondary] [] []

private theorem readsRetain (initial middle final : TxState Id) (a : Address) (token : Account)
    (code : ByteArray) (accountRead : ((getAccount a).run initial).run = .ok (token, middle))
    (codeRead : ((getCode token.codeHash).run middle).run = .ok (code, final)) :
    final.block = initial.block ∧ final.rev = initial.rev ∧
      final.obs.storageReads = initial.obs.storageReads ∧ final.obs.createdAccounts = initial.obs.createdAccounts ∧
      (∀ b, b ∈ final.obs.accountReads ↔ b = a ∨ b ∈ initial.obs.accountReads) := by
  obtain ⟨block, rev, slots, _, created⟩ := getAccount_frames initial a token middle accountRead
  obtain ⟨block', rev', accounts', slots', created'⟩ := getCode_frames middle token.codeHash code final codeRead
  refine ⟨block'.trans block, rev'.trans rev, slots'.trans slots, created'.trans created, ?_⟩
  intro b
  rw [accounts']
  exact getAccount_mem initial a b token middle accountRead

end STFSpec.Conformance.Vm.Instructions.DelegationResolutionControls
