/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State

/-!
# Nominal state-error construction and elimination

Library `EthConformance`: private structural examples and shared complete supplied-payload guards.
These cases execute no tracker, provider, adapter or guest operation.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/5.
-/

namespace STFSpec.Conformance.State.StateErrorGuards

open STFSpec.Base STFSpec.State

/-- Complete nested witness tag, item tag and hash-byte payload observation. -/
abbrev WitnessValue := Nat × Nat × List Nat
/-- Complete state tag and optional nested witness observation. -/
abbrev Value := Nat × Option WitnessValue

/-- Observe every supplied witness tag and complete hash payload. -/
def witnessValue : WitnessError → WitnessValue
  | .missing (.node h) => (0, 0, h.toBytes.toList.map UInt8.toNat)
  | .missing (.code h) => (0, 1, h.toBytes.toList.map UInt8.toNat)
  | .missing .leaf => (0, 2, [])
  | .malformed (.node h) => (1, 0, h.toBytes.toList.map UInt8.toNat)
  | .malformed (.code h) => (1, 1, h.toBytes.toList.map UInt8.toNat)
  | .malformed .leaf => (1, 2, [])
  | .unresolved h => (2, 3, h.toBytes.toList.map UInt8.toNat)

/-- Observe the state tag, retaining the supplied witness observation unchanged. -/
def observe {α : Type} (f : WitnessError → α) : StateError → Nat × Option α
  | .witness e => (0, some (f e))
  | .balanceUnderflow => (1, none)
  | .balanceOverflow => (2, none)
  | .storageOnMissingAccount => (3, none)

/-- Construct the supplied fixed-width hash from its complete big-endian byte list. -/
def payloadHash (bytes : List Nat) : Hash32 :=
  Hash32.ofBytes32 (FixedBytes.ofNat (bytes.foldl (fun acc byte ↦ 256 * acc + byte) 0))

/-- Zero, maximum, mixed and every-position high/low complete hash patterns. -/
def hashCases : List (String × List Nat) :=
  [("zero", List.replicate 32 0), ("max", List.replicate 32 255),
   ("mixed", (List.range 32).map (fun i ↦ (i * 37 + 129) % 256))] ++
  (List.range 32).flatMap (fun pos ↦
    [(s!"position-{pos}-high", (List.range 32).map (fun i ↦ if i == pos then 255 else 0)),
     (s!"position-{pos}-low", (List.range 32).map (fun i ↦ if i == pos then 0 else 255))])

/-- Complete expected cases for all five hash-bearing witness variants. -/
def payloadCases (label : String) (bytes : List Nat) :
    List (String × StateError × Value) :=
  let h := payloadHash bytes
  [(label ++ "-missing-node", .witness (.missing (.node h)), (0, some (0, 0, bytes))),
   (label ++ "-missing-code", .witness (.missing (.code h)), (0, some (0, 1, bytes))),
   (label ++ "-malformed-node", .witness (.malformed (.node h)), (0, some (1, 0, bytes))),
   (label ++ "-malformed-code", .witness (.malformed (.code h)), (0, some (1, 1, bytes))),
   (label ++ "-unresolved", .witness (.unresolved h), (0, some (2, 3, bytes)))]

/-- Shared 340-case corpus with complete tags/payloads and independent expected values. -/
def cases : List (String × StateError × Value) :=
  [("underflow", .balanceUnderflow, (1, none)),
   ("overflow", .balanceOverflow, (2, none)),
   ("storage-missing", .storageOnMissingAccount, (3, none)),
   ("missing-leaf", .witness (.missing .leaf), (0, some (0, 2, []))),
   ("malformed-leaf", .witness (.malformed .leaf), (0, some (1, 2, [])))] ++
  hashCases.flatMap (fun (label, bytes) ↦ payloadCases label bytes)

private theorem arbitrary_witness_retained (e : WitnessError) :
    (match StateError.witness e with
     | .witness payload => payload
     | _ => e) = e := rfl

private theorem arbitrary_observer_retained {α : Type} (f : WitnessError → α)
    (e : WitnessError) : observe f (.witness e) = (0, some (f e)) := rfl

private theorem outer_tags_distinct (e : WitnessError) :
    StateError.witness e ≠ .balanceUnderflow ∧
    StateError.witness e ≠ .balanceOverflow ∧
    StateError.witness e ≠ .storageOnMissingAccount ∧
    StateError.balanceUnderflow ≠ .balanceOverflow ∧
    StateError.balanceUnderflow ≠ .storageOnMissingAccount ∧
    StateError.balanceOverflow ≠ .storageOnMissingAccount := by
  exact ⟨StateError.noConfusion, StateError.noConfusion, StateError.noConfusion,
    StateError.noConfusion, StateError.noConfusion, StateError.noConfusion⟩

#guard cases.length == 340
#guard cases.all (fun (_, error, expected) ↦ observe witnessValue error == expected)

end STFSpec.Conformance.State.StateErrorGuards
