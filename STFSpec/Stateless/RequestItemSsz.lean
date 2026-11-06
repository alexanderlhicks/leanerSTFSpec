/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless.RequestItems
import STFSpec.Codec.SszSchema
import STFSpec.Codec.SszWellFormed
import STFSpec.Codec.SszWellTyped

/-!
# Execution-request item SSZ schemas

Library `EthStateless`. Five actual fixed-container dictionaries retain every raw
field. Their certificates establish structural typing and complete adapter inversion.
Wire-domain validity adds no protocol, cryptographic or source-host condition.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3–7 (Q81).
-/

namespace STFSpec.Stateless

open Base Codec

private theorem fixed_preserves {n : Nat} (b : ByteArray) (x : FixedBytes n)
    (h : FixedBytes.ofBytes? (Bytes.ofByteArray b) = some x) :
    x.toBytes.toByteArray = b := by
  rw [(FixedBytes.ofBytes?_eq_some_iff.mp h).2, Bytes.toByteArray_ofByteArray]

private theorem address_preserves (b : ByteArray) (x : Address)
    (h : Address.ofBytes? (Bytes.ofByteArray b) = some x) :
    x.toBytes.toByteArray = b := by
  rw [(Address.ofBytes?_eq_some_iff.mp h).2, Bytes.toByteArray_ofByteArray]

namespace DepositRequest

private def fromValue? : SszValue → Option DepositRequest
  | .container [.bytes pubkey, .bytes withdrawalCredentials, .uint amount, .bytes signature,
    .uint index] => do
      let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray pubkey)
      let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32)
        (Bytes.ofByteArray withdrawalCredentials)
      let amount ← U64.ofNat? amount
      let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray signature)
      let index ← U64.ofNat? index
      pure ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
  | _ => none

/-- Actual fixed-container metadata; EELS
`src/ethereum/forks/amsterdam/execution_engine/requests.py:42` and
`src/ethereum/utils/ssz.py:174–320` at the pin. Validity concerns the wire domain. -/
instance instSszSchema : SszSchema DepositRequest where
  type := .container [.byteVector 48, .byteVector 32, .uint 8, .byteVector 96, .uint 8]
  fieldNames := ["pubkey", "withdrawal_credentials", "amount", "signature", "index"]
  valid _ := True
  toValue a := .container [.bytes a.pubkey.toBytes.toByteArray,
    .bytes a.withdrawalCredentials.toBytes.toByteArray, .uint a.amount.toNat,
    .bytes a.signature.toBytes.toByteArray, .uint a.index.toNat]
  ofValue? := fromValue?

private theorem fromValue?_roundtrip (a : DepositRequest) :
    instSszSchema.ofValue? (instSszSchema.toValue a) = some a := by
  cases a
  dsimp only [SszSchema.ofValue?, SszSchema.toValue, instSszSchema]
  simp [fromValue?, Bytes.ofByteArray_toByteArray, FixedBytes.ofBytes?_toBytes, U64.ofNat?_toNat]

private theorem fromValue?_preserves (v : SszValue) (a : DepositRequest)
    (h : instSszSchema.ofValue? v = some a) : instSszSchema.toValue a = v := by
  change fromValue? v = some a at h
  unfold fromValue? at h
  split at h
  next pubkey withdrawalCredentials amount signature index =>
    cases h0 : FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray pubkey) with
    | none => simp [h0] at h
    | some x0 =>
      cases h1 : FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray withdrawalCredentials) with
      | none => simp [h0, h1] at h
      | some x1 =>
        cases h2 : U64.ofNat? amount with
        | none => simp [h0, h1, h2] at h
        | some x2 =>
          cases h3 : FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray signature) with
          | none => simp [h0, h1, h2, h3] at h
          | some x3 =>
            cases h4 : U64.ofNat? index with
            | none => simp [h0, h1, h2, h3, h4] at h
            | some x4 =>
              simp [h0, h1, h2, h3, h4] at h
              subst a
              dsimp only [SszSchema.toValue, instSszSchema]
              simp only [fixed_preserves pubkey x0 h0,
                fixed_preserves withdrawalCredentials x1 h1,
                ((U64.ofNat?_eq_some_iff _ _).mp h2 |>.2), fixed_preserves signature x3 h3,
                ((U64.ofNat?_eq_some_iff _ _).mp h4 |>.2)]
  next => contradiction

private theorem typed_forward (a : DepositRequest) :
    SszValue.WellTyped instSszSchema.type (instSszSchema.toValue a) := by
  dsimp only [SszSchema.type, SszSchema.toValue, instSszSchema]
  simp [SszValue.wellTyped_iff (.container _), SszValue.wellTyped_iff (.byteVector _) _,
    SszValue.wellTyped_iff (.uint _) _, Bytes.size_toByteArray,
    FixedBytes.size_toBytes]
  exact ⟨U64.toNat_lt _, U64.toNat_lt _⟩

/-- The actual fixed-container descriptor is structurally well formed (Q81). -/
theorem ssz_type_wellFormed : instSszSchema.type.WellFormed := by
  dsimp only [SszSchema.type, instSszSchema]
  simp [SszType.wellFormed_iff (.container _),
    SszType.wellFormed_iff (.byteVector _), SszType.wellFormed_iff (.uint _)]

/-- Every wire-domain value round trips completely and has a well-typed image (Q81). -/
theorem ssz_ofValue_toValue (a : DepositRequest) (h : instSszSchema.valid a) :
    instSszSchema.ofValue? (instSszSchema.toValue a) = some a ∧
      SszValue.WellTyped instSszSchema.type (instSszSchema.toValue a) :=
  have _ := h
  ⟨fromValue?_roundtrip a, typed_forward a⟩

/-- Successful reconstruction of a well-typed value preserves its entire model (Q81). -/
theorem ssz_toValue_ofValue (v : SszValue) (a : DepositRequest)
    (h : SszValue.WellTyped instSszSchema.type v ∧ instSszSchema.ofValue? v = some a) :
    instSszSchema.valid a ∧ instSszSchema.toValue a = v :=
  ⟨True.intro, fromValue?_preserves v a h.2⟩

end DepositRequest

namespace WithdrawalRequest

private def fromValue? : SszValue → Option WithdrawalRequest
  | .container [.bytes sourceAddress, .bytes validatorPubkey, .uint amount] => do
      let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray sourceAddress)
      let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray validatorPubkey)
      let amount ← U64.ofNat? amount
      pure ⟨sourceAddress, validatorPubkey, amount⟩
  | _ => none

/-- Actual fixed-container metadata; EELS
`src/ethereum/forks/amsterdam/execution_engine/requests.py:55` and
`src/ethereum/utils/ssz.py:174–320` at the pin. Validity concerns the wire domain. -/
instance instSszSchema : SszSchema WithdrawalRequest where
  type := .container [.byteVector 20, .byteVector 48, .uint 8]
  fieldNames := ["source_address", "validator_pubkey", "amount"]
  valid _ := True
  toValue a := .container [.bytes a.sourceAddress.toBytes.toByteArray,
    .bytes a.validatorPubkey.toBytes.toByteArray, .uint a.amount.toNat]
  ofValue? := fromValue?

private theorem fromValue?_roundtrip (a : WithdrawalRequest) :
    instSszSchema.ofValue? (instSszSchema.toValue a) = some a := by
  cases a
  dsimp only [SszSchema.ofValue?, SszSchema.toValue, instSszSchema]
  simp [fromValue?, Bytes.ofByteArray_toByteArray, FixedBytes.ofBytes?_toBytes,
    Address.ofBytes?_toBytes, U64.ofNat?_toNat]

private theorem fromValue?_preserves (v : SszValue) (a : WithdrawalRequest)
    (h : instSszSchema.ofValue? v = some a) : instSszSchema.toValue a = v := by
  change fromValue? v = some a at h
  unfold fromValue? at h
  split at h
  next sourceAddress validatorPubkey amount =>
    cases h0 : Address.ofBytes? (Bytes.ofByteArray sourceAddress) with
    | none => simp [h0] at h
    | some x0 =>
      cases h1 : FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray validatorPubkey) with
      | none => simp [h0, h1] at h
      | some x1 =>
        cases h2 : U64.ofNat? amount with
        | none => simp [h0, h1, h2] at h
        | some x2 =>
          simp [h0, h1, h2] at h
          subst a
          dsimp only [SszSchema.toValue, instSszSchema]
          simp only [address_preserves sourceAddress x0 h0,
            fixed_preserves validatorPubkey x1 h1, ((U64.ofNat?_eq_some_iff _ _).mp h2 |>.2)]
  next => contradiction

private theorem typed_forward (a : WithdrawalRequest) :
    SszValue.WellTyped instSszSchema.type (instSszSchema.toValue a) := by
  dsimp only [SszSchema.type, SszSchema.toValue, instSszSchema]
  simp [SszValue.wellTyped_iff (.container _), SszValue.wellTyped_iff (.byteVector _) _,
    SszValue.wellTyped_iff (.uint _) _, Bytes.size_toByteArray,
    FixedBytes.size_toBytes, Address.size_toBytes]
  exact U64.toNat_lt _

/-- The actual fixed-container descriptor is structurally well formed (Q81). -/
theorem ssz_type_wellFormed : instSszSchema.type.WellFormed := by
  dsimp only [SszSchema.type, instSszSchema]
  simp [SszType.wellFormed_iff (.container _),
    SszType.wellFormed_iff (.byteVector _), SszType.wellFormed_iff (.uint _)]

/-- Every wire-domain value round trips completely and has a well-typed image (Q81). -/
theorem ssz_ofValue_toValue (a : WithdrawalRequest) (h : instSszSchema.valid a) :
    instSszSchema.ofValue? (instSszSchema.toValue a) = some a ∧
      SszValue.WellTyped instSszSchema.type (instSszSchema.toValue a) :=
  have _ := h
  ⟨fromValue?_roundtrip a, typed_forward a⟩

/-- Successful reconstruction of a well-typed value preserves its entire model (Q81). -/
theorem ssz_toValue_ofValue (v : SszValue) (a : WithdrawalRequest)
    (h : SszValue.WellTyped instSszSchema.type v ∧ instSszSchema.ofValue? v = some a) :
    instSszSchema.valid a ∧ instSszSchema.toValue a = v :=
  ⟨True.intro, fromValue?_preserves v a h.2⟩

end WithdrawalRequest

namespace ConsolidationRequest

private def fromValue? : SszValue → Option ConsolidationRequest
  | .container [.bytes sourceAddress, .bytes sourcePubkey, .bytes targetPubkey] => do
      let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray sourceAddress)
      let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray sourcePubkey)
      let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray targetPubkey)
      pure ⟨sourceAddress, sourcePubkey, targetPubkey⟩
  | _ => none

/-- Actual fixed-container metadata; EELS
`src/ethereum/forks/amsterdam/execution_engine/requests.py:66` and
`src/ethereum/utils/ssz.py:174–320` at the pin. Validity concerns the wire domain. -/
instance instSszSchema : SszSchema ConsolidationRequest where
  type := .container [.byteVector 20, .byteVector 48, .byteVector 48]
  fieldNames := ["source_address", "source_pubkey", "target_pubkey"]
  valid _ := True
  toValue a := .container [.bytes a.sourceAddress.toBytes.toByteArray,
    .bytes a.sourcePubkey.toBytes.toByteArray, .bytes a.targetPubkey.toBytes.toByteArray]
  ofValue? := fromValue?

private theorem fromValue?_roundtrip (a : ConsolidationRequest) :
    instSszSchema.ofValue? (instSszSchema.toValue a) = some a := by
  cases a
  dsimp only [SszSchema.ofValue?, SszSchema.toValue, instSszSchema]
  simp [fromValue?, Bytes.ofByteArray_toByteArray, FixedBytes.ofBytes?_toBytes,
    Address.ofBytes?_toBytes]

private theorem fromValue?_preserves (v : SszValue) (a : ConsolidationRequest)
    (h : instSszSchema.ofValue? v = some a) : instSszSchema.toValue a = v := by
  change fromValue? v = some a at h
  unfold fromValue? at h
  split at h
  next sourceAddress sourcePubkey targetPubkey =>
    cases h0 : Address.ofBytes? (Bytes.ofByteArray sourceAddress) with
    | none => simp [h0] at h
    | some x0 =>
      cases h1 : FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray sourcePubkey) with
      | none => simp [h0, h1] at h
      | some x1 =>
        cases h2 : FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray targetPubkey) with
        | none => simp [h0, h1, h2] at h
        | some x2 =>
          simp [h0, h1, h2] at h
          subst a
          dsimp only [SszSchema.toValue, instSszSchema]
          simp only [address_preserves sourceAddress x0 h0, fixed_preserves sourcePubkey x1 h1,
            fixed_preserves targetPubkey x2 h2]
  next => contradiction

private theorem typed_forward (a : ConsolidationRequest) :
    SszValue.WellTyped instSszSchema.type (instSszSchema.toValue a) := by
  dsimp only [SszSchema.type, SszSchema.toValue, instSszSchema]
  simp [SszValue.wellTyped_iff (.container _), SszValue.wellTyped_iff (.byteVector _) _,
    Bytes.size_toByteArray,
    FixedBytes.size_toBytes, Address.size_toBytes]


/-- The actual fixed-container descriptor is structurally well formed (Q81). -/
theorem ssz_type_wellFormed : instSszSchema.type.WellFormed := by
  dsimp only [SszSchema.type, instSszSchema]
  simp [SszType.wellFormed_iff (.container _),
    SszType.wellFormed_iff (.byteVector _)]

/-- Every wire-domain value round trips completely and has a well-typed image (Q81). -/
theorem ssz_ofValue_toValue (a : ConsolidationRequest) (h : instSszSchema.valid a) :
    instSszSchema.ofValue? (instSszSchema.toValue a) = some a ∧
      SszValue.WellTyped instSszSchema.type (instSszSchema.toValue a) :=
  have _ := h
  ⟨fromValue?_roundtrip a, typed_forward a⟩

/-- Successful reconstruction of a well-typed value preserves its entire model (Q81). -/
theorem ssz_toValue_ofValue (v : SszValue) (a : ConsolidationRequest)
    (h : SszValue.WellTyped instSszSchema.type v ∧ instSszSchema.ofValue? v = some a) :
    instSszSchema.valid a ∧ instSszSchema.toValue a = v :=
  ⟨True.intro, fromValue?_preserves v a h.2⟩

end ConsolidationRequest

namespace BuilderDepositRequest

private def fromValue? : SszValue → Option BuilderDepositRequest
  | .container [.bytes pubkey, .bytes withdrawalCredentials, .uint amount, .bytes signature] => do
      let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray pubkey)
      let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32)
        (Bytes.ofByteArray withdrawalCredentials)
      let amount ← U64.ofNat? amount
      let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray signature)
      pure ⟨pubkey, withdrawalCredentials, amount, signature⟩
  | _ => none

/-- Actual fixed-container metadata; EELS
`src/ethereum/forks/amsterdam/execution_engine/requests.py:77` and
`src/ethereum/utils/ssz.py:174–320` at the pin. Validity concerns the wire domain. -/
instance instSszSchema : SszSchema BuilderDepositRequest where
  type := .container [.byteVector 48, .byteVector 32, .uint 8, .byteVector 96]
  fieldNames := ["pubkey", "withdrawal_credentials", "amount", "signature"]
  valid _ := True
  toValue a := .container [.bytes a.pubkey.toBytes.toByteArray,
    .bytes a.withdrawalCredentials.toBytes.toByteArray, .uint a.amount.toNat,
    .bytes a.signature.toBytes.toByteArray]
  ofValue? := fromValue?

private theorem fromValue?_roundtrip (a : BuilderDepositRequest) :
    instSszSchema.ofValue? (instSszSchema.toValue a) = some a := by
  cases a
  dsimp only [SszSchema.ofValue?, SszSchema.toValue, instSszSchema]
  simp [fromValue?, Bytes.ofByteArray_toByteArray, FixedBytes.ofBytes?_toBytes, U64.ofNat?_toNat]

private theorem fromValue?_preserves (v : SszValue) (a : BuilderDepositRequest)
    (h : instSszSchema.ofValue? v = some a) : instSszSchema.toValue a = v := by
  change fromValue? v = some a at h
  unfold fromValue? at h
  split at h
  next pubkey withdrawalCredentials amount signature =>
    cases h0 : FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray pubkey) with
    | none => simp [h0] at h
    | some x0 =>
      cases h1 : FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray withdrawalCredentials) with
      | none => simp [h0, h1] at h
      | some x1 =>
        cases h2 : U64.ofNat? amount with
        | none => simp [h0, h1, h2] at h
        | some x2 =>
          cases h3 : FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray signature) with
          | none => simp [h0, h1, h2, h3] at h
          | some x3 =>
            simp [h0, h1, h2, h3] at h
            subst a
            dsimp only [SszSchema.toValue, instSszSchema]
            simp only [fixed_preserves pubkey x0 h0, fixed_preserves withdrawalCredentials x1 h1,
              ((U64.ofNat?_eq_some_iff _ _).mp h2 |>.2), fixed_preserves signature x3 h3]
  next => contradiction

private theorem typed_forward (a : BuilderDepositRequest) :
    SszValue.WellTyped instSszSchema.type (instSszSchema.toValue a) := by
  dsimp only [SszSchema.type, SszSchema.toValue, instSszSchema]
  simp [SszValue.wellTyped_iff (.container _), SszValue.wellTyped_iff (.byteVector _) _,
    SszValue.wellTyped_iff (.uint _) _, Bytes.size_toByteArray,
    FixedBytes.size_toBytes]
  exact U64.toNat_lt _

/-- The actual fixed-container descriptor is structurally well formed (Q81). -/
theorem ssz_type_wellFormed : instSszSchema.type.WellFormed := by
  dsimp only [SszSchema.type, instSszSchema]
  simp [SszType.wellFormed_iff (.container _),
    SszType.wellFormed_iff (.byteVector _), SszType.wellFormed_iff (.uint _)]

/-- Every wire-domain value round trips completely and has a well-typed image (Q81). -/
theorem ssz_ofValue_toValue (a : BuilderDepositRequest) (h : instSszSchema.valid a) :
    instSszSchema.ofValue? (instSszSchema.toValue a) = some a ∧
      SszValue.WellTyped instSszSchema.type (instSszSchema.toValue a) :=
  have _ := h
  ⟨fromValue?_roundtrip a, typed_forward a⟩

/-- Successful reconstruction of a well-typed value preserves its entire model (Q81). -/
theorem ssz_toValue_ofValue (v : SszValue) (a : BuilderDepositRequest)
    (h : SszValue.WellTyped instSszSchema.type v ∧ instSszSchema.ofValue? v = some a) :
    instSszSchema.valid a ∧ instSszSchema.toValue a = v :=
  ⟨True.intro, fromValue?_preserves v a h.2⟩

end BuilderDepositRequest

namespace BuilderExitRequest

private def fromValue? : SszValue → Option BuilderExitRequest
  | .container [.bytes sourceAddress, .bytes pubkey] => do
      let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray sourceAddress)
      let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray pubkey)
      pure ⟨sourceAddress, pubkey⟩
  | _ => none

/-- Actual fixed-container metadata; EELS
`src/ethereum/forks/amsterdam/execution_engine/requests.py:89` and
`src/ethereum/utils/ssz.py:174–320` at the pin. Validity concerns the wire domain. -/
instance instSszSchema : SszSchema BuilderExitRequest where
  type := .container [.byteVector 20, .byteVector 48]
  fieldNames := ["source_address", "pubkey"]
  valid _ := True
  toValue a := .container [.bytes a.sourceAddress.toBytes.toByteArray,
    .bytes a.pubkey.toBytes.toByteArray]
  ofValue? := fromValue?

private theorem fromValue?_roundtrip (a : BuilderExitRequest) :
    instSszSchema.ofValue? (instSszSchema.toValue a) = some a := by
  cases a
  dsimp only [SszSchema.ofValue?, SszSchema.toValue, instSszSchema]
  simp [fromValue?, Bytes.ofByteArray_toByteArray, FixedBytes.ofBytes?_toBytes,
    Address.ofBytes?_toBytes]

private theorem fromValue?_preserves (v : SszValue) (a : BuilderExitRequest)
    (h : instSszSchema.ofValue? v = some a) : instSszSchema.toValue a = v := by
  change fromValue? v = some a at h
  unfold fromValue? at h
  split at h
  next sourceAddress pubkey =>
    cases h0 : Address.ofBytes? (Bytes.ofByteArray sourceAddress) with
    | none => simp [h0] at h
    | some x0 =>
      cases h1 : FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray pubkey) with
      | none => simp [h0, h1] at h
      | some x1 =>
        simp [h0, h1] at h
        subst a
        dsimp only [SszSchema.toValue, instSszSchema]
        simp only [address_preserves sourceAddress x0 h0, fixed_preserves pubkey x1 h1]
  next => contradiction

private theorem typed_forward (a : BuilderExitRequest) :
    SszValue.WellTyped instSszSchema.type (instSszSchema.toValue a) := by
  dsimp only [SszSchema.type, SszSchema.toValue, instSszSchema]
  simp [SszValue.wellTyped_iff (.container _), SszValue.wellTyped_iff (.byteVector _) _,
    Bytes.size_toByteArray,
    FixedBytes.size_toBytes, Address.size_toBytes]


/-- The actual fixed-container descriptor is structurally well formed (Q81). -/
theorem ssz_type_wellFormed : instSszSchema.type.WellFormed := by
  dsimp only [SszSchema.type, instSszSchema]
  simp [SszType.wellFormed_iff (.container _),
    SszType.wellFormed_iff (.byteVector _)]

/-- Every wire-domain value round trips completely and has a well-typed image (Q81). -/
theorem ssz_ofValue_toValue (a : BuilderExitRequest) (h : instSszSchema.valid a) :
    instSszSchema.ofValue? (instSszSchema.toValue a) = some a ∧
      SszValue.WellTyped instSszSchema.type (instSszSchema.toValue a) :=
  have _ := h
  ⟨fromValue?_roundtrip a, typed_forward a⟩

/-- Successful reconstruction of a well-typed value preserves its entire model (Q81). -/
theorem ssz_toValue_ofValue (v : SszValue) (a : BuilderExitRequest)
    (h : SszValue.WellTyped instSszSchema.type v ∧ instSszSchema.ofValue? v = some a) :
    instSszSchema.valid a ∧ instSszSchema.toValue a = v :=
  ⟨True.intro, fromValue?_preserves v a h.2⟩

end BuilderExitRequest

end STFSpec.Stateless
