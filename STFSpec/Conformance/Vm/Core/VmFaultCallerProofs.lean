/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Nominal VM fault facade clients

Library `EthConformance`: private exact-type, exhaustive elimination, injectivity,
disjointness and complete-value controls through the public Core facade.
No opcode, tracker, runner or guest action is executed by these clients.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/5/7.
-/

namespace STFSpec.Conformance.Vm.Core.VmFaultCallerProofs

open STFSpec.Base STFSpec.State STFSpec.Vm.Core

universe u

private def blobSite : OverflowSite := OverflowSite.blobBaseFee
private def refundSite : OverflowSite := OverflowSite.refundCounter
private def stateConstructor : StateError → VmFault := VmFault.state
private def ancestorConstructor : Nat → VmFault := VmFault.ancestorHashUnavailable
private def overflowConstructor : OverflowSite → VmFault := VmFault.u256Overflow

private def eliminateSite {P : OverflowSite → Sort u}
    (blob : P .blobBaseFee) (refund : P .refundCounter) (site : OverflowSite) : P site :=
  match site with
  | .blobBaseFee => blob
  | .refundCounter => refund

private def eliminateFault {P : VmFault → Sort u}
    (state : ∀ e, P (.state e)) (ancestor : ∀ offset, P (.ancestorHashUnavailable offset))
    (overflow : ∀ site, P (.u256Overflow site)) (fault : VmFault) : P fault :=
  match fault with
  | .state e => state e
  | .ancestorHashUnavailable offset => ancestor offset
  | .u256Overflow site => overflow site

private def reconstruct : VmFault → VmFault
  | .state e => .state e
  | .ancestorHashUnavailable offset => .ancestorHashUnavailable offset
  | .u256Overflow site => .u256Overflow site

private theorem reconstruct_eq (fault : VmFault) : reconstruct fault = fault := by
  cases fault <;> rfl

private theorem state_injective (a b : StateError) (h : VmFault.state a = .state b) :
    a = b := by
  cases h
  rfl

private theorem ancestor_injective (a b : Nat)
    (h : VmFault.ancestorHashUnavailable a = .ancestorHashUnavailable b) : a = b := by
  cases h
  rfl

private theorem overflow_injective (a b : OverflowSite)
    (h : VmFault.u256Overflow a = .u256Overflow b) : a = b := by
  cases h
  rfl

private theorem sites_distinct : OverflowSite.blobBaseFee ≠ .refundCounter := by
  intro h
  cases h

private theorem tags_distinct (e : StateError) (offset : Nat) (site : OverflowSite) :
    VmFault.state e ≠ .ancestorHashUnavailable offset ∧
    VmFault.state e ≠ .u256Overflow site ∧
    VmFault.ancestorHashUnavailable offset ≠ .u256Overflow site := by
  exact ⟨VmFault.noConfusion, VmFault.noConfusion, VmFault.noConfusion⟩

-- Complete observations retain every outer/nested tag and every hash byte.
private def witnessValue : WitnessError → Nat × Nat × List Nat
  | .missing (.node h) => (0, 0, h.toBytes.toList.map UInt8.toNat)
  | .missing (.code h) => (0, 1, h.toBytes.toList.map UInt8.toNat)
  | .missing .leaf => (0, 2, [])
  | .malformed (.node h) => (1, 0, h.toBytes.toList.map UInt8.toNat)
  | .malformed (.code h) => (1, 1, h.toBytes.toList.map UInt8.toNat)
  | .malformed .leaf => (1, 2, [])
  | .unresolved h => (2, 3, h.toBytes.toList.map UInt8.toNat)

private def stateValue : StateError → Nat × Option (Nat × Nat × List Nat)
  | .witness e => (0, some (witnessValue e))
  | .balanceUnderflow => (1, none)
  | .balanceOverflow => (2, none)
  | .storageOnMissingAccount => (3, none)

private def siteValue : OverflowSite → Nat
  | .blobBaseFee => 0
  | .refundCounter => 1

private def observe : VmFault →
    Sum (Nat × Option (Nat × Nat × List Nat)) (Sum Nat Nat)
  | .state e => .inl (stateValue e)
  | .ancestorHashUnavailable offset => .inr (.inl offset)
  | .u256Overflow site => .inr (.inr (siteValue site))

private def payloadHash (bytes : List Nat) : Hash32 :=
  Hash32.ofBytes32 (FixedBytes.ofNat (bytes.foldl (fun acc byte ↦ 256 * acc + byte) 0))

private def hashCases : List (List Nat) :=
  [List.replicate 32 0, List.replicate 32 255,
   (List.range 32).map (fun i ↦ (i * 37 + 129) % 256)] ++
  (List.range 32).flatMap (fun pos ↦
    [(List.range 32).map (fun i ↦ if i == pos then 255 else 0),
     (List.range 32).map (fun i ↦ if i == pos then 0 else 255)])

private def payloadControls (bytes : List Nat) : Bool :=
  let h := payloadHash bytes
  let cases : List (StateError × (Nat × Option (Nat × Nat × List Nat))) :=
    [(.witness (.missing (.node h)), (0, some (0, 0, bytes))),
     (.witness (.missing (.code h)), (0, some (0, 1, bytes))),
     (.witness (.malformed (.node h)), (0, some (1, 0, bytes))),
     (.witness (.malformed (.code h)), (0, some (1, 1, bytes))),
     (.witness (.unresolved h), (0, some (2, 3, bytes)))]
  cases.all (fun (e, expected) ↦ observe (stateConstructor e) == .inl expected)

#guard hashCases.length == 67
#guard hashCases.all payloadControls
#guard observe (stateConstructor .balanceUnderflow) == .inl (1, none)
#guard observe (stateConstructor .balanceOverflow) == .inl (2, none)
#guard observe (stateConstructor .storageOnMissingAccount) == .inl (3, none)
#guard observe (stateConstructor (.witness (.missing .leaf))) == .inl (0, some (0, 2, []))
#guard observe (stateConstructor (.witness (.malformed .leaf))) == .inl (0, some (1, 2, []))
#guard observe (overflowConstructor blobSite) == .inr (.inr 0)
#guard observe (overflowConstructor refundSite) == .inr (.inr 1)
#guard ([0, 1, 255, 256, 257, 2^64, 2^256, 2^4096] : List Nat).all
  (fun offset ↦ observe (ancestorConstructor offset) == .inr (.inl offset))

end STFSpec.Conformance.Vm.Core.VmFaultCallerProofs
