/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block.Withdrawal
import STFSpec.Codec.SszSchema
import STFSpec.Codec.SszWellFormed
import STFSpec.Codec.SszWellTyped

/-!
# Withdrawal SSZ schema

Library `EthBlock`. The ordinary container retains the four source fields and
checks each complete value on reconstruction. EELS
`src/ethereum/forks/amsterdam/blocks.py:38–66` and `src/ethereum/utils/ssz.py:174–320`.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3–7 (Q81).
-/

namespace STFSpec.Block.Withdrawal

open Base Codec

private def ofSszValue? : SszValue → Option Withdrawal
  | .container [.uint index, .uint validatorIndex, .bytes address, .uint amount] => do
      let index ← U64.ofNat? index
      let validatorIndex ← U64.ofNat? validatorIndex
      let address ← Address.ofBytes? (Bytes.ofByteArray address)
      let amount ← U64.ofNat? amount
      return ⟨index, validatorIndex, address, amount⟩
  | _ => none

/-- Ordinary Withdrawal schema; EELS `src/ethereum/forks/amsterdam/blocks.py:38–66`
and `src/ethereum/utils/ssz.py:174–320`. Validity describes only the wire domain. -/
instance instSszSchema : SszSchema Withdrawal where
  type := .container [.uint 8, .uint 8, .byteVector 20, .uint 8]
  fieldNames := ["index", "validator_index", "address", "amount"]
  valid := fun _ ↦ True
  toValue := fun a ↦ .container [.uint a.index.toNat, .uint a.validatorIndex.toNat,
    .bytes a.address.toBytes.toByteArray, .uint a.amount.toNat]
  ofValue? := ofSszValue?

/-- The actual Withdrawal descriptor is structurally well formed (Q81). -/
theorem ssz_type_wellFormed : instSszSchema.type.WellFormed := by
  change (SszType.container [.uint 8, .uint 8, .byteVector 20, .uint 8]).WellFormed
  simp [SszType.wellFormed_iff (.container _),
    SszType.wellFormed_iff (.uint _), SszType.wellFormed_iff (.byteVector _)]

/-- Every wire-domain Withdrawal reconstructs completely and has the declared payload type. -/
theorem ssz_ofValue_toValue (a : Withdrawal) (h : instSszSchema.valid a) :
    instSszSchema.ofValue? (instSszSchema.toValue a) = some a ∧
      SszValue.WellTyped instSszSchema.type (instSszSchema.toValue a) := by
  constructor
  · change ofSszValue? (.container [.uint a.index.toNat, .uint a.validatorIndex.toNat,
      .bytes a.address.toBytes.toByteArray, .uint a.amount.toNat]) = some a
    cases a
    simp [ofSszValue?, U64.ofNat?_toNat, Bytes.ofByteArray_toByteArray,
      Address.ofBytes?_toBytes, bind, pure]
  · change SszValue.WellTyped (.container [.uint 8, .uint 8, .byteVector 20, .uint 8])
      (.container [.uint a.index.toNat, .uint a.validatorIndex.toNat,
        .bytes a.address.toBytes.toByteArray, .uint a.amount.toNat])
    simpa [SszValue.wellTyped_iff (.container _) (.container _),
      SszValue.wellTyped_iff (.uint _) (.uint _),
      SszValue.wellTyped_iff (.byteVector _) (.bytes _),
      Bytes.size_toByteArray, Address.size_toBytes] using
      And.intro (U64.toNat_lt a.index)
        (And.intro (U64.toNat_lt a.validatorIndex) (U64.toNat_lt a.amount))

private theorem toValue_of_reconstruction (v : SszValue) (a : Withdrawal)
    (h : ofSszValue? v = some a) : instSszSchema.toValue a = v := by
  unfold ofSszValue? at h
  split at h
  next index validatorIndex address amount =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨i, hi, j, hj, b, hb, n, hn, ha⟩ := h
    cases ha
    have hi' := (U64.ofNat?_eq_some_iff _ _).mp hi
    have hj' := (U64.ofNat?_eq_some_iff _ _).mp hj
    have hb' := Address.ofBytes?_eq_some_iff.mp hb
    have hn' := (U64.ofNat?_eq_some_iff _ _).mp hn
    change SszValue.container [.uint i.toNat, .uint j.toNat,
      .bytes b.toBytes.toByteArray, .uint n.toNat] = _
    simp only [hi'.2, hj'.2, hb'.2, hn'.2,
      Bytes.toByteArray_ofByteArray]
  next => contradiction

/-- A typed successful reconstruction retains the entire raw value and wire validity (Q81). -/
theorem ssz_toValue_ofValue (v : SszValue) (a : Withdrawal)
    (h : SszValue.WellTyped instSszSchema.type v ∧ instSszSchema.ofValue? v = some a) :
    instSszSchema.valid a ∧ instSszSchema.toValue a = v :=
  ⟨True.intro, toValue_of_reconstruction v a h.2⟩

end STFSpec.Block.Withdrawal
