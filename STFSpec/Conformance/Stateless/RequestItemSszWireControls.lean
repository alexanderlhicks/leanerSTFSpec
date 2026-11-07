/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless

/-!
# Complete request-item wire controls

Library `EthConformance`. Private ordinary clients establish support and the entire
fixed wire on arbitrary records. Complete mathematical inputs and literal expected
bytes exercise actual dictionaries and checked Base constructors, independently of
source execution, guest execution, byte decoding and root support.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Stateless.RequestItemSszWireControls

open STFSpec.Stateless STFSpec.Base STFSpec.Codec

private theorem bytes_ext {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b :=
  ByteArray.ext (Array.toList_inj.mp h)

private def digits (n : Nat) : List UInt8 :=
  (List.range 8).map (fun i ↦ UInt8.ofNat ((n / 256 ^ i) % 256))

private theorem byte_supported {n : Nat} (x : FixedBytes n) :
    Ssz.Serializable (.byteVector n) (.bytes x.toBytes.toByteArray) :=
  (Ssz.serializable_iff _ _).mpr (by
    change x.toBytes.toByteArray.size = n
    rw [Bytes.size_toByteArray, FixedBytes.size_toBytes])

private theorem address_supported (x : Address) :
    Ssz.Serializable (.byteVector 20) (.bytes x.toBytes.toByteArray) :=
  (Ssz.serializable_iff _ _).mpr (by
    change x.toBytes.toByteArray.size = 20
    rw [Bytes.size_toByteArray, Address.size_toBytes])

private theorem uint_supported (x : U64) : Ssz.Serializable (.uint 8) (.uint x.toNat) :=
  (Ssz.serializable_iff _ _).mpr ⟨by omega, U64.toNat_lt x⟩

private theorem fixed_vector (n : Nat) : SszType.fixedSize? (.byteVector n) = some n :=
  SszType.fixedSize?_eq _

private theorem fixed_uint : SszType.fixedSize? (.uint 8) = some 8 := SszType.fixedSize?_eq _

private theorem uint_bytes (n : Nat) (h : Ssz.Serializable (.uint 8) (.uint n)) :
    Ssz.encode (.uint 8) (.uint n) h = (digits n).toByteArray := by
  apply bytes_ext
  simpa only [List.toList_data_toByteArray, digits] using Ssz.encode_eq (.uint 8) (.uint n) h

private def leafEqual : SszValue → SszValue → Bool
  | .bytes a, .bytes b => a.data.toList == b.data.toList
  | .uint a, .uint b => a == b
  | _, _ => false

private def modelEqual : SszValue → SszValue → Bool
  | .container a, .container b =>
      a.length == b.length && (a.zip b).all (fun p ↦ leafEqual p.1 p.2)
  | _, _ => false

private theorem fixed_fold (ps : List (SszType × SszValue)) (lengths : List Nat)
    (state : Nat × List Nat)
    (hf : ∀ p ∈ ps, ∃ n, p.1.fixedSize? = some n) :
    (ps.zip lengths).foldl (fun (s : Nat × List Nat) q ↦
      match q.1.1.fixedSize? with
      | some _ => s
      | none => (s.1 + q.2, s.2 ++ [s.1])) state = state := by
  induction ps generalizing lengths state with
  | nil => rfl
  | cons p ps ih =>
    cases lengths with
    | nil => rfl
    | cons l ls =>
      obtain ⟨n, hn⟩ := hf p (by simp)
      simp only [List.zip_cons_cons, List.foldl_cons, hn]
      exact ih ls state (fun p hp ↦ hf p (by simp [hp]))

private theorem fixed_container_supported (fs : List SszType) (xs : List SszValue)
    (hl : fs.length = xs.length)
    (hs : ∀ p ∈ fs.zip xs, Ssz.Serializable p.1 p.2)
    (hf : ∀ f ∈ fs, ∃ n, f.fixedSize? = some n) :
    Ssz.Serializable (.container fs) (.container xs) := by
  apply (Ssz.serializable_iff (.container fs) (.container xs)).mpr
  refine ⟨hl, hs, ?_⟩
  have hfixed : ∀ p ∈ fs.zip xs, ∃ n, p.1.fixedSize? = some n :=
    fun p hp ↦ hf p.1 (List.of_mem_zip hp).1
  dsimp only
  change ∀ o ∈ (((fs.zip xs).zip _).foldl (fun (s : Nat × List Nat) q ↦
    match q.1.1.fixedSize? with
    | some _ => s
    | none => (s.1 + q.2, s.2 ++ [s.1])) (_, ([] : List Nat))).2, o < 2 ^ 32
  rw [fixed_fold (hf := hfixed)]
  simp only [List.not_mem_nil, false_implies, implies_true]

private theorem fixed_wire_fold (ps : List (SszType × SszValue)) (bs : List ByteArray)
    (state : Nat × List UInt8 × List UInt8) (hl : ps.length = bs.length)
    (hf : ∀ p ∈ ps, ∃ n, p.1.fixedSize? = some n) :
    let r := (ps.zip bs).foldl (fun (s : Nat × List UInt8 × List UInt8) q ↦
      match q.1.1.fixedSize? with
      | some _ => (s.1, s.2.1 ++ q.2.data.toList, s.2.2)
      | none => (s.1 + q.2.size, s.2.1 ++
        ((List.range 4).map (fun i ↦ UInt8.ofNat ((s.1 / 256 ^ i) % 256))), s.2.2 ++
        q.2.data.toList)) state
    r.2.1 ++ r.2.2 = state.2.1 ++ (bs.map (fun b ↦ b.data.toList)).flatten ++ state.2.2 := by
  induction ps generalizing bs state with
  | nil =>
    cases bs with
    | nil => simp
    | cons b bs => simp at hl
  | cons p ps ih =>
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      obtain ⟨n, hn⟩ := hf p (by simp)
      simp only [List.zip_cons_cons, List.foldl_cons, hn]
      rw [ih bs _ (by simpa using hl) (fun p hp ↦ hf p (by simp [hp]))]
      simp only [List.map_cons, List.flatten_cons, List.append_assoc]

private theorem fixed_container_wire (fs : List SszType) (xs : List SszValue)
    (h : Ssz.Serializable (.container fs) (.container xs)) (bs : List ByteArray)
    (hb : (fs.zip xs).length = bs.length ∧ ∀ q ∈ (fs.zip xs).zip bs,
      ∀ hc : Ssz.Serializable q.1.1 q.1.2, Ssz.encode q.1.1 q.1.2 hc = q.2)
    (hf : ∀ f ∈ fs, ∃ n, f.fixedSize? = some n) :
    (Ssz.encode (.container fs) (.container xs) h).data.toList =
      (bs.map (fun b ↦ b.data.toList)).flatten := by
  have he := Ssz.encode_eq (.container fs) (.container xs) h bs hb
  have hfixed : ∀ p ∈ fs.zip xs, ∃ n, p.1.fixedSize? = some n :=
    fun p hp ↦ hf p.1 (List.of_mem_zip hp).1
  dsimp only at he
  change (Ssz.encode (.container fs) (.container xs) h).data.toList =
    (let r := ((fs.zip xs).zip bs).foldl
      (fun (s : Nat × List UInt8 × List UInt8) q ↦
        match q.1.1.fixedSize? with
        | some _ => (s.1, s.2.1 ++ q.2.data.toList, s.2.2)
        | none => (s.1 + q.2.size, s.2.1 ++
          ((List.range 4).map (fun i ↦ UInt8.ofNat ((s.1 / 256 ^ i) % 256))), s.2.2 ++
          q.2.data.toList))
      (_, [], [])
    r.2.1 ++ r.2.2) at he
  rw [fixed_wire_fold (hl := hb.1) (hf := hfixed)] at he
  simpa only [List.nil_append, List.append_nil] using he

namespace DepositRequest

private abbrev schema : SszSchema DepositRequest := STFSpec.Stateless.DepositRequest.instSszSchema

private theorem fields_fixed : ∀ f ∈ ([.byteVector 48, .byteVector 32, .uint 8, .byteVector 96,
  .uint 8] : List SszType),
    ∃ n, f.fixedSize? = some n := by
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact ⟨48, fixed_vector 48⟩
  · exact ⟨32, fixed_vector 32⟩
  · exact ⟨8, fixed_uint⟩
  · exact ⟨96, fixed_vector 96⟩
  · exact ⟨8, fixed_uint⟩


private theorem supported (a : DepositRequest) :
    Ssz.Serializable schema.type (schema.toValue a) := by
  dsimp only [schema, SszSchema.type, SszSchema.toValue,
    STFSpec.Stateless.DepositRequest.instSszSchema]
  apply fixed_container_supported
  · rfl
  · simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      forall_eq_or_imp, false_implies, implies_true, and_true]
    exact ⟨byte_supported a.pubkey, byte_supported a.withdrawalCredentials,
      uint_supported a.amount, byte_supported a.signature, uint_supported a.index⟩
  · exact fields_fixed

private theorem whole_wire (a : DepositRequest) :
    (SszSchema.encodeBytes (s := schema) a (supported a)).data.toList =
      a.pubkey.toBytes.toList ++ a.withdrawalCredentials.toBytes.toList ++
        digits a.amount.toNat ++ a.signature.toBytes.toList ++ digits a.index.toNat := by
  rw [SszSchema.encodeBytes_eq (s := schema)]
  let bs := [a.pubkey.toBytes.toByteArray, a.withdrawalCredentials.toBytes.toByteArray,
    (digits a.amount.toNat).toByteArray, a.signature.toBytes.toByteArray,
    (digits a.index.toNat).toByteArray]
  have hb : ∀ q ∈ ([.byteVector 48, .byteVector 32, .uint 8, .byteVector 96,
    .uint 8] : List SszType).zip
      [(.bytes a.pubkey.toBytes.toByteArray : SszValue),
        .bytes a.withdrawalCredentials.toBytes.toByteArray, .uint a.amount.toNat,
        .bytes a.signature.toBytes.toByteArray, .uint a.index.toNat] |>.zip bs,
      ∀ h : Ssz.Serializable q.1.1 q.1.2, Ssz.encode q.1.1 q.1.2 h = q.2 := by
    simp only [bs, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.not_mem_nil, forall_eq_or_imp, false_implies, implies_true, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro h
      exact bytes_ext (Ssz.encode_eq (.byteVector 48) (.bytes a.pubkey.toBytes.toByteArray) h)
    · intro h
      exact bytes_ext (Ssz.encode_eq (.byteVector 32)
        (.bytes a.withdrawalCredentials.toBytes.toByteArray) h)
    · intro h
      exact uint_bytes a.amount.toNat h
    · intro h
      exact bytes_ext (Ssz.encode_eq (.byteVector 96) (.bytes a.signature.toBytes.toByteArray) h)
    · intro h
      exact uint_bytes a.index.toNat h
  have he := fixed_container_wire
    [.byteVector 48, .byteVector 32, .uint 8, .byteVector 96, .uint 8]
    [(.bytes a.pubkey.toBytes.toByteArray : SszValue),
      .bytes a.withdrawalCredentials.toBytes.toByteArray, .uint a.amount.toNat,
      .bytes a.signature.toBytes.toByteArray, .uint a.index.toNat]
    (supported a) bs ⟨rfl, hb⟩ fields_fixed
  simpa only [schema, SszSchema.type, SszSchema.toValue,
    STFSpec.Stateless.DepositRequest.instSszSchema, bs, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.toList_data_toByteArray,
    Bytes.toList_toByteArray, List.nil_append, List.append_nil, List.append_assoc] using he

private def observe (a : DepositRequest) : List (Sum (List UInt8) Nat) :=
  [.inl a.pubkey.toBytes.toList, .inl a.withdrawalCredentials.toBytes.toList,
    .inr a.amount.toNat, .inl a.signature.toBytes.toList, .inr a.index.toNat]

private def check (a : DepositRequest) (fields : List (Sum (List UInt8) Nat))
    (model : SszValue) (wire : ByteArray) : Bool :=
  observe a == fields && modelEqual (schema.toValue a) model &&
    (schema.ofValue? model).map observe == some fields &&
    (SszSchema.encodeBytes (s := schema) a (supported a)).data.toList == wire.data.toList

end DepositRequest

namespace WithdrawalRequest

private abbrev schema : SszSchema WithdrawalRequest :=
  STFSpec.Stateless.WithdrawalRequest.instSszSchema

private theorem fields_fixed : ∀ f ∈ ([.byteVector 20, .byteVector 48, .uint 8] : List SszType),
    ∃ n, f.fixedSize? = some n := by
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact ⟨20, fixed_vector 20⟩
  · exact ⟨48, fixed_vector 48⟩
  · exact ⟨8, fixed_uint⟩


private theorem supported (a : WithdrawalRequest) :
    Ssz.Serializable schema.type (schema.toValue a) := by
  dsimp only [schema, SszSchema.type, SszSchema.toValue,
    STFSpec.Stateless.WithdrawalRequest.instSszSchema]
  apply fixed_container_supported
  · rfl
  · simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      forall_eq_or_imp, false_implies, implies_true, and_true]
    exact ⟨address_supported a.sourceAddress, byte_supported a.validatorPubkey,
      uint_supported a.amount⟩
  · exact fields_fixed

private theorem whole_wire (a : WithdrawalRequest) :
    (SszSchema.encodeBytes (s := schema) a (supported a)).data.toList =
      a.sourceAddress.toBytes.toList ++ a.validatorPubkey.toBytes.toList ++
        digits a.amount.toNat := by
  rw [SszSchema.encodeBytes_eq (s := schema)]
  let bs := [a.sourceAddress.toBytes.toByteArray, a.validatorPubkey.toBytes.toByteArray,
    (digits a.amount.toNat).toByteArray]
  have hb : ∀ q ∈ ([.byteVector 20, .byteVector 48, .uint 8] : List SszType).zip
      [(.bytes a.sourceAddress.toBytes.toByteArray : SszValue),
        .bytes a.validatorPubkey.toBytes.toByteArray, .uint a.amount.toNat] |>.zip bs,
      ∀ h : Ssz.Serializable q.1.1 q.1.2, Ssz.encode q.1.1 q.1.2 h = q.2 := by
    simp only [bs, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.not_mem_nil, forall_eq_or_imp, false_implies, implies_true, and_true]
    refine ⟨?_, ?_, ?_⟩
    · intro h
      exact bytes_ext (Ssz.encode_eq (.byteVector 20)
        (.bytes a.sourceAddress.toBytes.toByteArray) h)
    · intro h
      exact bytes_ext (Ssz.encode_eq (.byteVector 48)
        (.bytes a.validatorPubkey.toBytes.toByteArray) h)
    · intro h
      exact uint_bytes a.amount.toNat h
  have he := fixed_container_wire [.byteVector 20, .byteVector 48, .uint 8]
    [(.bytes a.sourceAddress.toBytes.toByteArray : SszValue),
      .bytes a.validatorPubkey.toBytes.toByteArray, .uint a.amount.toNat]
    (supported a) bs ⟨rfl, hb⟩ fields_fixed
  simpa only [schema, SszSchema.type, SszSchema.toValue,
    STFSpec.Stateless.WithdrawalRequest.instSszSchema, bs, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.toList_data_toByteArray,
    Bytes.toList_toByteArray, List.nil_append, List.append_nil, List.append_assoc] using he

private def observe (a : WithdrawalRequest) : List (Sum (List UInt8) Nat) :=
  [.inl a.sourceAddress.toBytes.toList, .inl a.validatorPubkey.toBytes.toList, .inr a.amount.toNat]

private def check (a : WithdrawalRequest) (fields : List (Sum (List UInt8) Nat))
    (model : SszValue) (wire : ByteArray) : Bool :=
  observe a == fields && modelEqual (schema.toValue a) model &&
    (schema.ofValue? model).map observe == some fields &&
    (SszSchema.encodeBytes (s := schema) a (supported a)).data.toList == wire.data.toList

end WithdrawalRequest

namespace ConsolidationRequest

private abbrev schema : SszSchema ConsolidationRequest :=
  STFSpec.Stateless.ConsolidationRequest.instSszSchema

private theorem fields_fixed : ∀ f ∈ ([.byteVector 20, .byteVector 48,
  .byteVector 48] : List SszType),
    ∃ n, f.fixedSize? = some n := by
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact ⟨20, fixed_vector 20⟩
  · exact ⟨48, fixed_vector 48⟩
  · exact ⟨48, fixed_vector 48⟩


private theorem supported (a : ConsolidationRequest) :
    Ssz.Serializable schema.type (schema.toValue a) := by
  dsimp only [schema, SszSchema.type, SszSchema.toValue,
    STFSpec.Stateless.ConsolidationRequest.instSszSchema]
  apply fixed_container_supported
  · rfl
  · simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      forall_eq_or_imp, false_implies, implies_true, and_true]
    exact ⟨address_supported a.sourceAddress, byte_supported a.sourcePubkey,
      byte_supported a.targetPubkey⟩
  · exact fields_fixed

private theorem whole_wire (a : ConsolidationRequest) :
    (SszSchema.encodeBytes (s := schema) a (supported a)).data.toList =
      a.sourceAddress.toBytes.toList ++ a.sourcePubkey.toBytes.toList ++
        a.targetPubkey.toBytes.toList := by
  rw [SszSchema.encodeBytes_eq (s := schema)]
  let bs := [a.sourceAddress.toBytes.toByteArray, a.sourcePubkey.toBytes.toByteArray,
    a.targetPubkey.toBytes.toByteArray]
  have hb : ∀ q ∈ ([.byteVector 20, .byteVector 48, .byteVector 48] : List SszType).zip
      [(.bytes a.sourceAddress.toBytes.toByteArray : SszValue),
        .bytes a.sourcePubkey.toBytes.toByteArray,
        .bytes a.targetPubkey.toBytes.toByteArray] |>.zip bs,
      ∀ h : Ssz.Serializable q.1.1 q.1.2, Ssz.encode q.1.1 q.1.2 h = q.2 := by
    simp only [bs, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.not_mem_nil, forall_eq_or_imp, false_implies, implies_true, and_true]
    refine ⟨?_, ?_, ?_⟩
    · intro h
      exact bytes_ext (Ssz.encode_eq (.byteVector 20)
        (.bytes a.sourceAddress.toBytes.toByteArray) h)
    · intro h
      exact bytes_ext (Ssz.encode_eq (.byteVector 48)
        (.bytes a.sourcePubkey.toBytes.toByteArray) h)
    · intro h
      exact bytes_ext (Ssz.encode_eq (.byteVector 48)
        (.bytes a.targetPubkey.toBytes.toByteArray) h)
  have he := fixed_container_wire [.byteVector 20, .byteVector 48, .byteVector 48]
    [(.bytes a.sourceAddress.toBytes.toByteArray : SszValue),
      .bytes a.sourcePubkey.toBytes.toByteArray, .bytes a.targetPubkey.toBytes.toByteArray]
    (supported a) bs ⟨rfl, hb⟩ fields_fixed
  simpa only [schema, SszSchema.type, SszSchema.toValue,
    STFSpec.Stateless.ConsolidationRequest.instSszSchema, bs, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.toList_data_toByteArray,
    Bytes.toList_toByteArray, List.nil_append, List.append_nil, List.append_assoc] using he

private def observe (a : ConsolidationRequest) : List (Sum (List UInt8) Nat) :=
  [.inl a.sourceAddress.toBytes.toList, .inl a.sourcePubkey.toBytes.toList,
    .inl a.targetPubkey.toBytes.toList]

private def check (a : ConsolidationRequest) (fields : List (Sum (List UInt8) Nat))
    (model : SszValue) (wire : ByteArray) : Bool :=
  observe a == fields && modelEqual (schema.toValue a) model &&
    (schema.ofValue? model).map observe == some fields &&
    (SszSchema.encodeBytes (s := schema) a (supported a)).data.toList == wire.data.toList

end ConsolidationRequest

namespace BuilderDepositRequest

private abbrev schema : SszSchema BuilderDepositRequest :=
  STFSpec.Stateless.BuilderDepositRequest.instSszSchema

private theorem fields_fixed : ∀ f ∈ ([.byteVector 48, .byteVector 32, .uint 8,
  .byteVector 96] : List SszType),
    ∃ n, f.fixedSize? = some n := by
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact ⟨48, fixed_vector 48⟩
  · exact ⟨32, fixed_vector 32⟩
  · exact ⟨8, fixed_uint⟩
  · exact ⟨96, fixed_vector 96⟩


private theorem supported (a : BuilderDepositRequest) :
    Ssz.Serializable schema.type (schema.toValue a) := by
  dsimp only [schema, SszSchema.type, SszSchema.toValue,
    STFSpec.Stateless.BuilderDepositRequest.instSszSchema]
  apply fixed_container_supported
  · rfl
  · simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      forall_eq_or_imp, false_implies, implies_true, and_true]
    exact ⟨byte_supported a.pubkey, byte_supported a.withdrawalCredentials,
      uint_supported a.amount, byte_supported a.signature⟩
  · exact fields_fixed

private theorem whole_wire (a : BuilderDepositRequest) :
    (SszSchema.encodeBytes (s := schema) a (supported a)).data.toList =
      a.pubkey.toBytes.toList ++ a.withdrawalCredentials.toBytes.toList ++
        digits a.amount.toNat ++ a.signature.toBytes.toList := by
  rw [SszSchema.encodeBytes_eq (s := schema)]
  let bs := [a.pubkey.toBytes.toByteArray, a.withdrawalCredentials.toBytes.toByteArray,
    (digits a.amount.toNat).toByteArray, a.signature.toBytes.toByteArray]
  have hb : ∀ q ∈ ([.byteVector 48, .byteVector 32, .uint 8, .byteVector 96] : List SszType).zip
      [(.bytes a.pubkey.toBytes.toByteArray : SszValue),
        .bytes a.withdrawalCredentials.toBytes.toByteArray, .uint a.amount.toNat,
        .bytes a.signature.toBytes.toByteArray] |>.zip bs,
      ∀ h : Ssz.Serializable q.1.1 q.1.2, Ssz.encode q.1.1 q.1.2 h = q.2 := by
    simp only [bs, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.not_mem_nil, forall_eq_or_imp, false_implies, implies_true, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      exact bytes_ext (Ssz.encode_eq (.byteVector 48) (.bytes a.pubkey.toBytes.toByteArray) h)
    · intro h
      exact bytes_ext (Ssz.encode_eq (.byteVector 32)
        (.bytes a.withdrawalCredentials.toBytes.toByteArray) h)
    · intro h
      exact uint_bytes a.amount.toNat h
    · intro h
      exact bytes_ext (Ssz.encode_eq (.byteVector 96) (.bytes a.signature.toBytes.toByteArray) h)
  have he := fixed_container_wire [.byteVector 48, .byteVector 32, .uint 8, .byteVector 96]
    [(.bytes a.pubkey.toBytes.toByteArray : SszValue),
      .bytes a.withdrawalCredentials.toBytes.toByteArray, .uint a.amount.toNat,
      .bytes a.signature.toBytes.toByteArray]
    (supported a) bs ⟨rfl, hb⟩ fields_fixed
  simpa only [schema, SszSchema.type, SszSchema.toValue,
    STFSpec.Stateless.BuilderDepositRequest.instSszSchema, bs, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.toList_data_toByteArray,
    Bytes.toList_toByteArray, List.nil_append, List.append_nil, List.append_assoc] using he

private def observe (a : BuilderDepositRequest) : List (Sum (List UInt8) Nat) :=
  [.inl a.pubkey.toBytes.toList, .inl a.withdrawalCredentials.toBytes.toList,
    .inr a.amount.toNat, .inl a.signature.toBytes.toList]

private def check (a : BuilderDepositRequest) (fields : List (Sum (List UInt8) Nat))
    (model : SszValue) (wire : ByteArray) : Bool :=
  observe a == fields && modelEqual (schema.toValue a) model &&
    (schema.ofValue? model).map observe == some fields &&
    (SszSchema.encodeBytes (s := schema) a (supported a)).data.toList == wire.data.toList

end BuilderDepositRequest

namespace BuilderExitRequest

private abbrev schema : SszSchema BuilderExitRequest :=
  STFSpec.Stateless.BuilderExitRequest.instSszSchema

private theorem fields_fixed : ∀ f ∈ ([.byteVector 20, .byteVector 48] : List SszType),
    ∃ n, f.fixedSize? = some n := by
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact ⟨20, fixed_vector 20⟩
  · exact ⟨48, fixed_vector 48⟩


private theorem supported (a : BuilderExitRequest) :
    Ssz.Serializable schema.type (schema.toValue a) := by
  dsimp only [schema, SszSchema.type, SszSchema.toValue,
    STFSpec.Stateless.BuilderExitRequest.instSszSchema]
  apply fixed_container_supported
  · rfl
  · simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      forall_eq_or_imp, false_implies, implies_true, and_true]
    exact ⟨address_supported a.sourceAddress, byte_supported a.pubkey⟩
  · exact fields_fixed

private theorem whole_wire (a : BuilderExitRequest) :
    (SszSchema.encodeBytes (s := schema) a (supported a)).data.toList =
      a.sourceAddress.toBytes.toList ++ a.pubkey.toBytes.toList := by
  rw [SszSchema.encodeBytes_eq (s := schema)]
  let bs := [a.sourceAddress.toBytes.toByteArray, a.pubkey.toBytes.toByteArray]
  have hb : ∀ q ∈ ([.byteVector 20, .byteVector 48] : List SszType).zip
      [(.bytes a.sourceAddress.toBytes.toByteArray : SszValue),
        .bytes a.pubkey.toBytes.toByteArray] |>.zip bs,
      ∀ h : Ssz.Serializable q.1.1 q.1.2, Ssz.encode q.1.1 q.1.2 h = q.2 := by
    simp only [bs, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.not_mem_nil, forall_eq_or_imp, false_implies, implies_true, and_true]
    refine ⟨?_, ?_⟩
    · intro h
      exact bytes_ext (Ssz.encode_eq (.byteVector 20)
        (.bytes a.sourceAddress.toBytes.toByteArray) h)
    · intro h
      exact bytes_ext (Ssz.encode_eq (.byteVector 48) (.bytes a.pubkey.toBytes.toByteArray) h)
  have he := fixed_container_wire [.byteVector 20, .byteVector 48]
    [(.bytes a.sourceAddress.toBytes.toByteArray : SszValue), .bytes a.pubkey.toBytes.toByteArray]
    (supported a) bs ⟨rfl, hb⟩ fields_fixed
  simpa only [schema, SszSchema.type, SszSchema.toValue,
    STFSpec.Stateless.BuilderExitRequest.instSszSchema, bs, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.toList_data_toByteArray,
    Bytes.toList_toByteArray, List.nil_append, List.append_nil, List.append_assoc] using he

private def observe (a : BuilderExitRequest) : List (Sum (List UInt8) Nat) :=
  [.inl a.sourceAddress.toBytes.toList, .inl a.pubkey.toBytes.toList]

private def check (a : BuilderExitRequest) (fields : List (Sum (List UInt8) Nat))
    (model : SszValue) (wire : ByteArray) : Bool :=
  observe a == fields && modelEqual (schema.toValue a) model &&
    (schema.ofValue? model).map observe == some fields &&
    (SszSchema.encodeBytes (s := schema) a (supported a)).data.toList == wire.data.toList

end BuilderExitRequest

-- Closed literal sharing preserves every input field and complete expected wire.
private def block0000 : List UInt8 := [0, 128, 156, 193, 230, 11, 48, 85]
private def block0001 : List UInt8 := [122, 159, 196, 233, 14, 51, 88, 125]
private def block0002 : List UInt8 := [162, 199, 236, 17, 54, 91, 128, 165]
private def block0003 : List UInt8 := [0, 255, 20, 57, 94, 131, 168, 205]
private def block0004 : List UInt8 := [242, 23, 60, 97, 134, 171, 208, 245]
private def block0005 : List UInt8 := [26, 63, 100, 137, 174, 211, 129, 0]
private def block0006 : List UInt8 := [0, 128, 209, 246, 27, 64, 101, 138]
private def block0007 : List UInt8 := [175, 212, 249, 30, 67, 104, 141, 178]
private def block0008 : List UInt8 := [0, 255, 33, 70, 107, 144, 181, 218]
private def block0009 : List UInt8 := [255, 36, 73, 110, 147, 184, 129, 0]
private def block0010 : List UInt8 := [0, 128, 59, 96, 133, 170, 207, 244]
private def block0011 : List UInt8 := [25, 62, 99, 136, 173, 210, 247, 28]
private def block0012 : List UInt8 := [65, 102, 139, 176, 213, 250, 31, 68]
private def block0013 : List UInt8 := [105, 142, 179, 216, 253, 34, 71, 108]
private def block0014 : List UInt8 := [145, 182, 219, 0, 37, 74, 111, 148]
private def block0015 : List UInt8 := [185, 222, 3, 40, 77, 114, 151, 188]
private def block0016 : List UInt8 := [0, 255, 43, 80, 117, 154, 191, 228]
private def block0017 : List UInt8 := [9, 46, 83, 120, 157, 194, 231, 12]
private def block0018 : List UInt8 := [49, 86, 123, 160, 197, 234, 15, 52]
private def block0019 : List UInt8 := [89, 126, 163, 200, 237, 18, 55, 92]
private def block0020 : List UInt8 := [129, 166, 203, 240, 21, 58, 95, 132]
private def block0021 : List UInt8 := [169, 206, 243, 24, 61, 98, 129, 0]
private def block0022 : List UInt8 := [130, 144, 96, 80, 64, 48, 32, 16]
private def block0023 : List UInt8 := [132, 176, 96, 80, 64, 48, 32, 16]
private def block0024 : List UInt8 := [0, 0, 0, 0, 0, 0, 0, 0]
private def block0025 : List UInt8 := [255, 255, 255, 255, 255, 255, 255, 255]
private def block0026 : List UInt8 := [1, 128, 156, 193, 230, 11, 48, 85]
private def block0027 : List UInt8 := [0, 129, 156, 193, 230, 11, 48, 85]
private def block0028 : List UInt8 := [0, 128, 157, 193, 230, 11, 48, 85]
private def block0029 : List UInt8 := [0, 128, 156, 192, 230, 11, 48, 85]
private def block0030 : List UInt8 := [0, 128, 156, 193, 231, 11, 48, 85]
private def block0031 : List UInt8 := [0, 128, 156, 193, 230, 10, 48, 85]
private def block0032 : List UInt8 := [0, 128, 156, 193, 230, 11, 49, 85]
private def block0033 : List UInt8 := [0, 128, 156, 193, 230, 11, 48, 84]
private def block0034 : List UInt8 := [123, 159, 196, 233, 14, 51, 88, 125]
private def block0035 : List UInt8 := [122, 158, 196, 233, 14, 51, 88, 125]
private def block0036 : List UInt8 := [122, 159, 197, 233, 14, 51, 88, 125]
private def block0037 : List UInt8 := [122, 159, 196, 232, 14, 51, 88, 125]
private def block0038 : List UInt8 := [122, 159, 196, 233, 15, 51, 88, 125]
private def block0039 : List UInt8 := [122, 159, 196, 233, 14, 50, 88, 125]
private def block0040 : List UInt8 := [122, 159, 196, 233, 14, 51, 89, 125]
private def block0041 : List UInt8 := [122, 159, 196, 233, 14, 51, 88, 124]
private def block0042 : List UInt8 := [163, 199, 236, 17, 54, 91, 128, 165]
private def block0043 : List UInt8 := [162, 198, 236, 17, 54, 91, 128, 165]
private def block0044 : List UInt8 := [162, 199, 237, 17, 54, 91, 128, 165]
private def block0045 : List UInt8 := [162, 199, 236, 16, 54, 91, 128, 165]
private def block0046 : List UInt8 := [162, 199, 236, 17, 55, 91, 128, 165]
private def block0047 : List UInt8 := [162, 199, 236, 17, 54, 90, 128, 165]
private def block0048 : List UInt8 := [162, 199, 236, 17, 54, 91, 129, 165]
private def block0049 : List UInt8 := [162, 199, 236, 17, 54, 91, 128, 164]
private def block0050 : List UInt8 := [1, 255, 20, 57, 94, 131, 168, 205]
private def block0051 : List UInt8 := [0, 254, 20, 57, 94, 131, 168, 205]
private def block0052 : List UInt8 := [0, 255, 21, 57, 94, 131, 168, 205]
private def block0053 : List UInt8 := [0, 255, 20, 56, 94, 131, 168, 205]
private def block0054 : List UInt8 := [0, 255, 20, 57, 95, 131, 168, 205]
private def block0055 : List UInt8 := [0, 255, 20, 57, 94, 130, 168, 205]
private def block0056 : List UInt8 := [0, 255, 20, 57, 94, 131, 169, 205]
private def block0057 : List UInt8 := [0, 255, 20, 57, 94, 131, 168, 204]
private def block0058 : List UInt8 := [243, 23, 60, 97, 134, 171, 208, 245]
private def block0059 : List UInt8 := [242, 22, 60, 97, 134, 171, 208, 245]
private def block0060 : List UInt8 := [242, 23, 61, 97, 134, 171, 208, 245]
private def block0061 : List UInt8 := [242, 23, 60, 96, 134, 171, 208, 245]
private def block0062 : List UInt8 := [242, 23, 60, 97, 135, 171, 208, 245]
private def block0063 : List UInt8 := [242, 23, 60, 97, 134, 170, 208, 245]
private def block0064 : List UInt8 := [242, 23, 60, 97, 134, 171, 209, 245]
private def block0065 : List UInt8 := [242, 23, 60, 97, 134, 171, 208, 244]
private def block0066 : List UInt8 := [27, 63, 100, 137, 174, 211, 129, 0]
private def block0067 : List UInt8 := [26, 62, 100, 137, 174, 211, 129, 0]
private def block0068 : List UInt8 := [26, 63, 101, 137, 174, 211, 129, 0]
private def block0069 : List UInt8 := [26, 63, 100, 136, 174, 211, 129, 0]
private def block0070 : List UInt8 := [26, 63, 100, 137, 175, 211, 129, 0]
private def block0071 : List UInt8 := [26, 63, 100, 137, 174, 210, 129, 0]
private def block0072 : List UInt8 := [26, 63, 100, 137, 174, 211, 128, 0]
private def block0073 : List UInt8 := [26, 63, 100, 137, 174, 211, 129, 1]
private def block0074 : List UInt8 := [1, 128, 209, 246, 27, 64, 101, 138]
private def block0075 : List UInt8 := [0, 129, 209, 246, 27, 64, 101, 138]
private def block0076 : List UInt8 := [0, 128, 208, 246, 27, 64, 101, 138]
private def block0077 : List UInt8 := [0, 128, 209, 247, 27, 64, 101, 138]
private def block0078 : List UInt8 := [0, 128, 209, 246, 26, 64, 101, 138]
private def block0079 : List UInt8 := [0, 128, 209, 246, 27, 65, 101, 138]
private def block0080 : List UInt8 := [0, 128, 209, 246, 27, 64, 100, 138]
private def block0081 : List UInt8 := [0, 128, 209, 246, 27, 64, 101, 139]
private def block0082 : List UInt8 := [174, 212, 249, 30, 67, 104, 141, 178]
private def block0083 : List UInt8 := [175, 213, 249, 30, 67, 104, 141, 178]
private def block0084 : List UInt8 := [175, 212, 248, 30, 67, 104, 141, 178]
private def block0085 : List UInt8 := [175, 212, 249, 31, 67, 104, 141, 178]
private def block0086 : List UInt8 := [175, 212, 249, 30, 66, 104, 141, 178]
private def block0087 : List UInt8 := [175, 212, 249, 30, 67, 105, 141, 178]
private def block0088 : List UInt8 := [175, 212, 249, 30, 67, 104, 140, 178]
private def block0089 : List UInt8 := [175, 212, 249, 30, 67, 104, 141, 179]
private def block0090 : List UInt8 := [1, 255, 33, 70, 107, 144, 181, 218]
private def block0091 : List UInt8 := [0, 254, 33, 70, 107, 144, 181, 218]
private def block0092 : List UInt8 := [0, 255, 32, 70, 107, 144, 181, 218]
private def block0093 : List UInt8 := [0, 255, 33, 71, 107, 144, 181, 218]
private def block0094 : List UInt8 := [0, 255, 33, 70, 106, 144, 181, 218]
private def block0095 : List UInt8 := [0, 255, 33, 70, 107, 145, 181, 218]
private def block0096 : List UInt8 := [0, 255, 33, 70, 107, 144, 180, 218]
private def block0097 : List UInt8 := [0, 255, 33, 70, 107, 144, 181, 219]
private def block0098 : List UInt8 := [254, 36, 73, 110, 147, 184, 129, 0]
private def block0099 : List UInt8 := [255, 37, 73, 110, 147, 184, 129, 0]
private def block0100 : List UInt8 := [255, 36, 72, 110, 147, 184, 129, 0]
private def block0101 : List UInt8 := [255, 36, 73, 111, 147, 184, 129, 0]
private def block0102 : List UInt8 := [255, 36, 73, 110, 146, 184, 129, 0]
private def block0103 : List UInt8 := [255, 36, 73, 110, 147, 185, 129, 0]
private def block0104 : List UInt8 := [255, 36, 73, 110, 147, 184, 128, 0]
private def block0105 : List UInt8 := [255, 36, 73, 110, 147, 184, 129, 1]
private def block0106 : List UInt8 := [1, 0, 0, 0, 0, 0, 0, 0]
private def block0107 : List UInt8 := [255, 0, 0, 0, 0, 0, 0, 0]
private def block0108 : List UInt8 := [0, 1, 0, 0, 0, 0, 0, 0]
private def block0109 : List UInt8 := [255, 255, 255, 255, 0, 0, 0, 0]
private def block0110 : List UInt8 := [0, 0, 0, 0, 1, 0, 0, 0]
private def block0111 : List UInt8 := [0, 0, 0, 0, 0, 0, 0, 128]
private def block0112 : List UInt8 := [1, 128, 59, 96, 133, 170, 207, 244]
private def block0113 : List UInt8 := [0, 129, 59, 96, 133, 170, 207, 244]
private def block0114 : List UInt8 := [0, 128, 58, 96, 133, 170, 207, 244]
private def block0115 : List UInt8 := [0, 128, 59, 97, 133, 170, 207, 244]
private def block0116 : List UInt8 := [0, 128, 59, 96, 132, 170, 207, 244]
private def block0117 : List UInt8 := [0, 128, 59, 96, 133, 171, 207, 244]
private def block0118 : List UInt8 := [0, 128, 59, 96, 133, 170, 206, 244]
private def block0119 : List UInt8 := [0, 128, 59, 96, 133, 170, 207, 245]
private def block0120 : List UInt8 := [24, 62, 99, 136, 173, 210, 247, 28]
private def block0121 : List UInt8 := [25, 63, 99, 136, 173, 210, 247, 28]
private def block0122 : List UInt8 := [25, 62, 98, 136, 173, 210, 247, 28]
private def block0123 : List UInt8 := [25, 62, 99, 137, 173, 210, 247, 28]
private def block0124 : List UInt8 := [25, 62, 99, 136, 172, 210, 247, 28]
private def block0125 : List UInt8 := [25, 62, 99, 136, 173, 211, 247, 28]
private def block0126 : List UInt8 := [25, 62, 99, 136, 173, 210, 246, 28]
private def block0127 : List UInt8 := [25, 62, 99, 136, 173, 210, 247, 29]
private def block0128 : List UInt8 := [64, 102, 139, 176, 213, 250, 31, 68]
private def block0129 : List UInt8 := [65, 103, 139, 176, 213, 250, 31, 68]
private def block0130 : List UInt8 := [65, 102, 138, 176, 213, 250, 31, 68]
private def block0131 : List UInt8 := [65, 102, 139, 177, 213, 250, 31, 68]
private def block0132 : List UInt8 := [65, 102, 139, 176, 212, 250, 31, 68]
private def block0133 : List UInt8 := [65, 102, 139, 176, 213, 251, 31, 68]
private def block0134 : List UInt8 := [65, 102, 139, 176, 213, 250, 30, 68]
private def block0135 : List UInt8 := [65, 102, 139, 176, 213, 250, 31, 69]
private def block0136 : List UInt8 := [104, 142, 179, 216, 253, 34, 71, 108]
private def block0137 : List UInt8 := [105, 143, 179, 216, 253, 34, 71, 108]
private def block0138 : List UInt8 := [105, 142, 178, 216, 253, 34, 71, 108]
private def block0139 : List UInt8 := [105, 142, 179, 217, 253, 34, 71, 108]
private def block0140 : List UInt8 := [105, 142, 179, 216, 252, 34, 71, 108]
private def block0141 : List UInt8 := [105, 142, 179, 216, 253, 35, 71, 108]
private def block0142 : List UInt8 := [105, 142, 179, 216, 253, 34, 70, 108]
private def block0143 : List UInt8 := [105, 142, 179, 216, 253, 34, 71, 109]
private def block0144 : List UInt8 := [144, 182, 219, 0, 37, 74, 111, 148]
private def block0145 : List UInt8 := [145, 183, 219, 0, 37, 74, 111, 148]
private def block0146 : List UInt8 := [145, 182, 218, 0, 37, 74, 111, 148]
private def block0147 : List UInt8 := [145, 182, 219, 1, 37, 74, 111, 148]
private def block0148 : List UInt8 := [145, 182, 219, 0, 36, 74, 111, 148]
private def block0149 : List UInt8 := [145, 182, 219, 0, 37, 75, 111, 148]
private def block0150 : List UInt8 := [145, 182, 219, 0, 37, 74, 110, 148]
private def block0151 : List UInt8 := [145, 182, 219, 0, 37, 74, 111, 149]
private def block0152 : List UInt8 := [184, 222, 3, 40, 77, 114, 151, 188]
private def block0153 : List UInt8 := [185, 223, 3, 40, 77, 114, 151, 188]
private def block0154 : List UInt8 := [185, 222, 2, 40, 77, 114, 151, 188]
private def block0155 : List UInt8 := [185, 222, 3, 41, 77, 114, 151, 188]
private def block0156 : List UInt8 := [185, 222, 3, 40, 76, 114, 151, 188]
private def block0157 : List UInt8 := [185, 222, 3, 40, 77, 115, 151, 188]
private def block0158 : List UInt8 := [185, 222, 3, 40, 77, 114, 150, 188]
private def block0159 : List UInt8 := [185, 222, 3, 40, 77, 114, 151, 189]
private def block0160 : List UInt8 := [1, 255, 43, 80, 117, 154, 191, 228]
private def block0161 : List UInt8 := [0, 254, 43, 80, 117, 154, 191, 228]
private def block0162 : List UInt8 := [0, 255, 42, 80, 117, 154, 191, 228]
private def block0163 : List UInt8 := [0, 255, 43, 81, 117, 154, 191, 228]
private def block0164 : List UInt8 := [0, 255, 43, 80, 116, 154, 191, 228]
private def block0165 : List UInt8 := [0, 255, 43, 80, 117, 155, 191, 228]
private def block0166 : List UInt8 := [0, 255, 43, 80, 117, 154, 190, 228]
private def block0167 : List UInt8 := [0, 255, 43, 80, 117, 154, 191, 229]
private def block0168 : List UInt8 := [8, 46, 83, 120, 157, 194, 231, 12]
private def block0169 : List UInt8 := [9, 47, 83, 120, 157, 194, 231, 12]
private def block0170 : List UInt8 := [9, 46, 82, 120, 157, 194, 231, 12]
private def block0171 : List UInt8 := [9, 46, 83, 121, 157, 194, 231, 12]
private def block0172 : List UInt8 := [9, 46, 83, 120, 156, 194, 231, 12]
private def block0173 : List UInt8 := [9, 46, 83, 120, 157, 195, 231, 12]
private def block0174 : List UInt8 := [9, 46, 83, 120, 157, 194, 230, 12]
private def block0175 : List UInt8 := [9, 46, 83, 120, 157, 194, 231, 13]
private def block0176 : List UInt8 := [48, 86, 123, 160, 197, 234, 15, 52]
private def block0177 : List UInt8 := [49, 87, 123, 160, 197, 234, 15, 52]
private def block0178 : List UInt8 := [49, 86, 122, 160, 197, 234, 15, 52]
private def block0179 : List UInt8 := [49, 86, 123, 161, 197, 234, 15, 52]
private def block0180 : List UInt8 := [49, 86, 123, 160, 196, 234, 15, 52]
private def block0181 : List UInt8 := [49, 86, 123, 160, 197, 235, 15, 52]
private def block0182 : List UInt8 := [49, 86, 123, 160, 197, 234, 14, 52]
private def block0183 : List UInt8 := [49, 86, 123, 160, 197, 234, 15, 53]
private def block0184 : List UInt8 := [88, 126, 163, 200, 237, 18, 55, 92]
private def block0185 : List UInt8 := [89, 127, 163, 200, 237, 18, 55, 92]
private def block0186 : List UInt8 := [89, 126, 162, 200, 237, 18, 55, 92]
private def block0187 : List UInt8 := [89, 126, 163, 201, 237, 18, 55, 92]
private def block0188 : List UInt8 := [89, 126, 163, 200, 236, 18, 55, 92]
private def block0189 : List UInt8 := [89, 126, 163, 200, 237, 19, 55, 92]
private def block0190 : List UInt8 := [89, 126, 163, 200, 237, 18, 54, 92]
private def block0191 : List UInt8 := [89, 126, 163, 200, 237, 18, 55, 93]
private def block0192 : List UInt8 := [128, 166, 203, 240, 21, 58, 95, 132]
private def block0193 : List UInt8 := [129, 167, 203, 240, 21, 58, 95, 132]
private def block0194 : List UInt8 := [129, 166, 202, 240, 21, 58, 95, 132]
private def block0195 : List UInt8 := [129, 166, 203, 241, 21, 58, 95, 132]
private def block0196 : List UInt8 := [129, 166, 203, 240, 20, 58, 95, 132]
private def block0197 : List UInt8 := [129, 166, 203, 240, 21, 59, 95, 132]
private def block0198 : List UInt8 := [129, 166, 203, 240, 21, 58, 94, 132]
private def block0199 : List UInt8 := [129, 166, 203, 240, 21, 58, 95, 133]
private def block0200 : List UInt8 := [168, 206, 243, 24, 61, 98, 129, 0]
private def block0201 : List UInt8 := [169, 207, 243, 24, 61, 98, 129, 0]
private def block0202 : List UInt8 := [169, 206, 242, 24, 61, 98, 129, 0]
private def block0203 : List UInt8 := [169, 206, 243, 25, 61, 98, 129, 0]
private def block0204 : List UInt8 := [169, 206, 243, 24, 60, 98, 129, 0]
private def block0205 : List UInt8 := [169, 206, 243, 24, 61, 99, 129, 0]
private def block0206 : List UInt8 := [169, 206, 243, 24, 61, 98, 128, 0]
private def block0207 : List UInt8 := [169, 206, 243, 24, 61, 98, 129, 1]
private def block0208 : List UInt8 := [0, 128, 185, 222, 3, 40, 77, 114]
private def block0209 : List UInt8 := [151, 188, 0, 255, 43, 80, 117, 154]
private def block0210 : List UInt8 := [191, 228, 129, 0]
private def block0211 : List UInt8 := [0, 128, 238, 19, 56, 93, 130, 167]
private def block0212 : List UInt8 := [204, 241, 22, 59, 96, 133, 170, 207]
private def block0213 : List UInt8 := [244, 25, 62, 99, 136, 173, 210, 247]
private def block0214 : List UInt8 := [0, 255, 102, 139, 176, 213, 250, 31]
private def block0215 : List UInt8 := [68, 105, 142, 179, 216, 253, 34, 71]
private def block0216 : List UInt8 := [108, 145, 182, 219, 0, 37, 129, 0]
private def block0217 : List UInt8 := [191, 228, 129, 0, 0, 128, 238, 19]
private def block0218 : List UInt8 := [56, 93, 130, 167, 204, 241, 22, 59]
private def block0219 : List UInt8 := [96, 133, 170, 207, 244, 25, 62, 99]
private def block0220 : List UInt8 := [136, 173, 210, 247, 0, 255, 102, 139]
private def block0221 : List UInt8 := [176, 213, 250, 31, 68, 105, 142, 179]
private def block0222 : List UInt8 := [216, 253, 34, 71, 108, 145, 182, 219]
private def block0223 : List UInt8 := [0, 37, 129, 0, 130, 160, 112, 80]
private def block0224 : List UInt8 := [64, 48, 32, 16]
private def block0225 : List UInt8 := [0, 0, 0, 0]
private def block0226 : List UInt8 := [255, 255, 255, 255]
private def block0227 : List UInt8 := [1, 128, 185, 222, 3, 40, 77, 114]
private def block0228 : List UInt8 := [0, 129, 185, 222, 3, 40, 77, 114]
private def block0229 : List UInt8 := [0, 128, 184, 222, 3, 40, 77, 114]
private def block0230 : List UInt8 := [0, 128, 185, 223, 3, 40, 77, 114]
private def block0231 : List UInt8 := [0, 128, 185, 222, 2, 40, 77, 114]
private def block0232 : List UInt8 := [0, 128, 185, 222, 3, 41, 77, 114]
private def block0233 : List UInt8 := [0, 128, 185, 222, 3, 40, 76, 114]
private def block0234 : List UInt8 := [0, 128, 185, 222, 3, 40, 77, 115]
private def block0235 : List UInt8 := [150, 188, 0, 255, 43, 80, 117, 154]
private def block0236 : List UInt8 := [151, 189, 0, 255, 43, 80, 117, 154]
private def block0237 : List UInt8 := [151, 188, 1, 255, 43, 80, 117, 154]
private def block0238 : List UInt8 := [151, 188, 0, 254, 43, 80, 117, 154]
private def block0239 : List UInt8 := [151, 188, 0, 255, 42, 80, 117, 154]
private def block0240 : List UInt8 := [151, 188, 0, 255, 43, 81, 117, 154]
private def block0241 : List UInt8 := [151, 188, 0, 255, 43, 80, 116, 154]
private def block0242 : List UInt8 := [151, 188, 0, 255, 43, 80, 117, 155]
private def block0243 : List UInt8 := [190, 228, 129, 0]
private def block0244 : List UInt8 := [190, 228, 129, 0, 0, 128, 238, 19]
private def block0245 : List UInt8 := [191, 229, 129, 0]
private def block0246 : List UInt8 := [191, 229, 129, 0, 0, 128, 238, 19]
private def block0247 : List UInt8 := [191, 228, 128, 0]
private def block0248 : List UInt8 := [191, 228, 128, 0, 0, 128, 238, 19]
private def block0249 : List UInt8 := [191, 228, 129, 1]
private def block0250 : List UInt8 := [191, 228, 129, 1, 0, 128, 238, 19]
private def block0251 : List UInt8 := [0, 0, 0, 0, 0, 128, 238, 19]
private def block0252 : List UInt8 := [255, 255, 255, 255, 0, 128, 238, 19]
private def block0253 : List UInt8 := [1, 128, 238, 19, 56, 93, 130, 167]
private def block0254 : List UInt8 := [191, 228, 129, 0, 1, 128, 238, 19]
private def block0255 : List UInt8 := [0, 129, 238, 19, 56, 93, 130, 167]
private def block0256 : List UInt8 := [191, 228, 129, 0, 0, 129, 238, 19]
private def block0257 : List UInt8 := [0, 128, 239, 19, 56, 93, 130, 167]
private def block0258 : List UInt8 := [191, 228, 129, 0, 0, 128, 239, 19]
private def block0259 : List UInt8 := [0, 128, 238, 18, 56, 93, 130, 167]
private def block0260 : List UInt8 := [191, 228, 129, 0, 0, 128, 238, 18]
private def block0261 : List UInt8 := [0, 128, 238, 19, 57, 93, 130, 167]
private def block0262 : List UInt8 := [57, 93, 130, 167, 204, 241, 22, 59]
private def block0263 : List UInt8 := [0, 128, 238, 19, 56, 92, 130, 167]
private def block0264 : List UInt8 := [56, 92, 130, 167, 204, 241, 22, 59]
private def block0265 : List UInt8 := [0, 128, 238, 19, 56, 93, 131, 167]
private def block0266 : List UInt8 := [56, 93, 131, 167, 204, 241, 22, 59]
private def block0267 : List UInt8 := [0, 128, 238, 19, 56, 93, 130, 166]
private def block0268 : List UInt8 := [56, 93, 130, 166, 204, 241, 22, 59]
private def block0269 : List UInt8 := [205, 241, 22, 59, 96, 133, 170, 207]
private def block0270 : List UInt8 := [56, 93, 130, 167, 205, 241, 22, 59]
private def block0271 : List UInt8 := [204, 240, 22, 59, 96, 133, 170, 207]
private def block0272 : List UInt8 := [56, 93, 130, 167, 204, 240, 22, 59]
private def block0273 : List UInt8 := [204, 241, 23, 59, 96, 133, 170, 207]
private def block0274 : List UInt8 := [56, 93, 130, 167, 204, 241, 23, 59]
private def block0275 : List UInt8 := [204, 241, 22, 58, 96, 133, 170, 207]
private def block0276 : List UInt8 := [56, 93, 130, 167, 204, 241, 22, 58]
private def block0277 : List UInt8 := [204, 241, 22, 59, 97, 133, 170, 207]
private def block0278 : List UInt8 := [97, 133, 170, 207, 244, 25, 62, 99]
private def block0279 : List UInt8 := [204, 241, 22, 59, 96, 132, 170, 207]
private def block0280 : List UInt8 := [96, 132, 170, 207, 244, 25, 62, 99]
private def block0281 : List UInt8 := [204, 241, 22, 59, 96, 133, 171, 207]
private def block0282 : List UInt8 := [96, 133, 171, 207, 244, 25, 62, 99]
private def block0283 : List UInt8 := [204, 241, 22, 59, 96, 133, 170, 206]
private def block0284 : List UInt8 := [96, 133, 170, 206, 244, 25, 62, 99]
private def block0285 : List UInt8 := [245, 25, 62, 99, 136, 173, 210, 247]
private def block0286 : List UInt8 := [96, 133, 170, 207, 245, 25, 62, 99]
private def block0287 : List UInt8 := [244, 24, 62, 99, 136, 173, 210, 247]
private def block0288 : List UInt8 := [96, 133, 170, 207, 244, 24, 62, 99]
private def block0289 : List UInt8 := [244, 25, 63, 99, 136, 173, 210, 247]
private def block0290 : List UInt8 := [96, 133, 170, 207, 244, 25, 63, 99]
private def block0291 : List UInt8 := [244, 25, 62, 98, 136, 173, 210, 247]
private def block0292 : List UInt8 := [96, 133, 170, 207, 244, 25, 62, 98]
private def block0293 : List UInt8 := [244, 25, 62, 99, 137, 173, 210, 247]
private def block0294 : List UInt8 := [137, 173, 210, 247, 0, 255, 102, 139]
private def block0295 : List UInt8 := [244, 25, 62, 99, 136, 172, 210, 247]
private def block0296 : List UInt8 := [136, 172, 210, 247, 0, 255, 102, 139]
private def block0297 : List UInt8 := [244, 25, 62, 99, 136, 173, 211, 247]
private def block0298 : List UInt8 := [136, 173, 211, 247, 0, 255, 102, 139]
private def block0299 : List UInt8 := [244, 25, 62, 99, 136, 173, 210, 246]
private def block0300 : List UInt8 := [136, 173, 210, 246, 0, 255, 102, 139]
private def block0301 : List UInt8 := [1, 255, 102, 139, 176, 213, 250, 31]
private def block0302 : List UInt8 := [136, 173, 210, 247, 1, 255, 102, 139]
private def block0303 : List UInt8 := [0, 254, 102, 139, 176, 213, 250, 31]
private def block0304 : List UInt8 := [136, 173, 210, 247, 0, 254, 102, 139]
private def block0305 : List UInt8 := [0, 255, 103, 139, 176, 213, 250, 31]
private def block0306 : List UInt8 := [136, 173, 210, 247, 0, 255, 103, 139]
private def block0307 : List UInt8 := [0, 255, 102, 138, 176, 213, 250, 31]
private def block0308 : List UInt8 := [136, 173, 210, 247, 0, 255, 102, 138]
private def block0309 : List UInt8 := [0, 255, 102, 139, 177, 213, 250, 31]
private def block0310 : List UInt8 := [177, 213, 250, 31, 68, 105, 142, 179]
private def block0311 : List UInt8 := [0, 255, 102, 139, 176, 212, 250, 31]
private def block0312 : List UInt8 := [176, 212, 250, 31, 68, 105, 142, 179]
private def block0313 : List UInt8 := [0, 255, 102, 139, 176, 213, 251, 31]
private def block0314 : List UInt8 := [176, 213, 251, 31, 68, 105, 142, 179]
private def block0315 : List UInt8 := [0, 255, 102, 139, 176, 213, 250, 30]
private def block0316 : List UInt8 := [176, 213, 250, 30, 68, 105, 142, 179]
private def block0317 : List UInt8 := [69, 105, 142, 179, 216, 253, 34, 71]
private def block0318 : List UInt8 := [176, 213, 250, 31, 69, 105, 142, 179]
private def block0319 : List UInt8 := [68, 104, 142, 179, 216, 253, 34, 71]
private def block0320 : List UInt8 := [176, 213, 250, 31, 68, 104, 142, 179]
private def block0321 : List UInt8 := [68, 105, 143, 179, 216, 253, 34, 71]
private def block0322 : List UInt8 := [176, 213, 250, 31, 68, 105, 143, 179]
private def block0323 : List UInt8 := [68, 105, 142, 178, 216, 253, 34, 71]
private def block0324 : List UInt8 := [176, 213, 250, 31, 68, 105, 142, 178]
private def block0325 : List UInt8 := [68, 105, 142, 179, 217, 253, 34, 71]
private def block0326 : List UInt8 := [217, 253, 34, 71, 108, 145, 182, 219]
private def block0327 : List UInt8 := [68, 105, 142, 179, 216, 252, 34, 71]
private def block0328 : List UInt8 := [216, 252, 34, 71, 108, 145, 182, 219]
private def block0329 : List UInt8 := [68, 105, 142, 179, 216, 253, 35, 71]
private def block0330 : List UInt8 := [216, 253, 35, 71, 108, 145, 182, 219]
private def block0331 : List UInt8 := [68, 105, 142, 179, 216, 253, 34, 70]
private def block0332 : List UInt8 := [216, 253, 34, 70, 108, 145, 182, 219]
private def block0333 : List UInt8 := [109, 145, 182, 219, 0, 37, 129, 0]
private def block0334 : List UInt8 := [216, 253, 34, 71, 109, 145, 182, 219]
private def block0335 : List UInt8 := [108, 144, 182, 219, 0, 37, 129, 0]
private def block0336 : List UInt8 := [216, 253, 34, 71, 108, 144, 182, 219]
private def block0337 : List UInt8 := [108, 145, 183, 219, 0, 37, 129, 0]
private def block0338 : List UInt8 := [216, 253, 34, 71, 108, 145, 183, 219]
private def block0339 : List UInt8 := [108, 145, 182, 218, 0, 37, 129, 0]
private def block0340 : List UInt8 := [216, 253, 34, 71, 108, 145, 182, 218]
private def block0341 : List UInt8 := [108, 145, 182, 219, 1, 37, 129, 0]
private def block0342 : List UInt8 := [1, 37, 129, 0, 130, 160, 112, 80]
private def block0343 : List UInt8 := [108, 145, 182, 219, 0, 36, 129, 0]
private def block0344 : List UInt8 := [0, 36, 129, 0, 130, 160, 112, 80]
private def block0345 : List UInt8 := [108, 145, 182, 219, 0, 37, 128, 0]
private def block0346 : List UInt8 := [0, 37, 128, 0, 130, 160, 112, 80]
private def block0347 : List UInt8 := [108, 145, 182, 219, 0, 37, 129, 1]
private def block0348 : List UInt8 := [0, 37, 129, 1, 130, 160, 112, 80]
private def block0349 : List UInt8 := [191, 228, 129, 0, 0, 0, 0, 0]
private def block0350 : List UInt8 := [0, 0, 0, 0, 130, 160, 112, 80]
private def block0351 : List UInt8 := [191, 228, 129, 0, 255, 255, 255, 255]
private def block0352 : List UInt8 := [255, 255, 255, 255, 130, 160, 112, 80]
private def block0353 : List UInt8 := [0, 37, 129, 0, 0, 0, 0, 0]
private def block0354 : List UInt8 := [0, 37, 129, 0, 1, 0, 0, 0]
private def block0355 : List UInt8 := [0, 37, 129, 0, 255, 0, 0, 0]
private def block0356 : List UInt8 := [0, 37, 129, 0, 0, 1, 0, 0]
private def block0357 : List UInt8 := [0, 37, 129, 0, 255, 255, 255, 255]
private def block0358 : List UInt8 := [1, 0, 0, 0]
private def block0359 : List UInt8 := [0, 0, 0, 128]
private def block0360 : List UInt8 := [0, 128, 214, 251, 32, 69, 106, 143]
private def block0361 : List UInt8 := [180, 217, 0, 255, 72, 109, 146, 183]
private def block0362 : List UInt8 := [220, 1, 129, 0]
private def block0363 : List UInt8 := [0, 128, 11, 48, 85, 122, 159, 196]
private def block0364 : List UInt8 := [233, 14, 51, 88, 125, 162, 199, 236]
private def block0365 : List UInt8 := [17, 54, 91, 128, 165, 202, 239, 20]
private def block0366 : List UInt8 := [0, 255, 131, 168, 205, 242, 23, 60]
private def block0367 : List UInt8 := [97, 134, 171, 208, 245, 26, 63, 100]
private def block0368 : List UInt8 := [137, 174, 211, 248, 29, 66, 129, 0]
private def block0369 : List UInt8 := [0, 128, 64, 101, 138, 175, 212, 249]
private def block0370 : List UInt8 := [30, 67, 104, 141, 178, 215, 252, 33]
private def block0371 : List UInt8 := [70, 107, 144, 181, 218, 255, 36, 73]
private def block0372 : List UInt8 := [0, 255, 184, 221, 2, 39, 76, 113]
private def block0373 : List UInt8 := [150, 187, 224, 5, 42, 79, 116, 153]
private def block0374 : List UInt8 := [190, 227, 8, 45, 82, 119, 129, 0]
private def block0375 : List UInt8 := [220, 1, 129, 0, 0, 128, 11, 48]
private def block0376 : List UInt8 := [85, 122, 159, 196, 233, 14, 51, 88]
private def block0377 : List UInt8 := [125, 162, 199, 236, 17, 54, 91, 128]
private def block0378 : List UInt8 := [165, 202, 239, 20, 0, 255, 131, 168]
private def block0379 : List UInt8 := [205, 242, 23, 60, 97, 134, 171, 208]
private def block0380 : List UInt8 := [245, 26, 63, 100, 137, 174, 211, 248]
private def block0381 : List UInt8 := [29, 66, 129, 0, 0, 128, 64, 101]
private def block0382 : List UInt8 := [138, 175, 212, 249, 30, 67, 104, 141]
private def block0383 : List UInt8 := [178, 215, 252, 33, 70, 107, 144, 181]
private def block0384 : List UInt8 := [218, 255, 36, 73, 0, 255, 184, 221]
private def block0385 : List UInt8 := [2, 39, 76, 113, 150, 187, 224, 5]
private def block0386 : List UInt8 := [42, 79, 116, 153, 190, 227, 8, 45]
private def block0387 : List UInt8 := [82, 119, 129, 0]
private def block0388 : List UInt8 := [1, 128, 214, 251, 32, 69, 106, 143]
private def block0389 : List UInt8 := [0, 129, 214, 251, 32, 69, 106, 143]
private def block0390 : List UInt8 := [0, 128, 215, 251, 32, 69, 106, 143]
private def block0391 : List UInt8 := [0, 128, 214, 250, 32, 69, 106, 143]
private def block0392 : List UInt8 := [0, 128, 214, 251, 33, 69, 106, 143]
private def block0393 : List UInt8 := [0, 128, 214, 251, 32, 68, 106, 143]
private def block0394 : List UInt8 := [0, 128, 214, 251, 32, 69, 107, 143]
private def block0395 : List UInt8 := [0, 128, 214, 251, 32, 69, 106, 142]
private def block0396 : List UInt8 := [181, 217, 0, 255, 72, 109, 146, 183]
private def block0397 : List UInt8 := [180, 216, 0, 255, 72, 109, 146, 183]
private def block0398 : List UInt8 := [180, 217, 1, 255, 72, 109, 146, 183]
private def block0399 : List UInt8 := [180, 217, 0, 254, 72, 109, 146, 183]
private def block0400 : List UInt8 := [180, 217, 0, 255, 73, 109, 146, 183]
private def block0401 : List UInt8 := [180, 217, 0, 255, 72, 108, 146, 183]
private def block0402 : List UInt8 := [180, 217, 0, 255, 72, 109, 147, 183]
private def block0403 : List UInt8 := [180, 217, 0, 255, 72, 109, 146, 182]
private def block0404 : List UInt8 := [221, 1, 129, 0]
private def block0405 : List UInt8 := [221, 1, 129, 0, 0, 128, 11, 48]
private def block0406 : List UInt8 := [220, 0, 129, 0]
private def block0407 : List UInt8 := [220, 0, 129, 0, 0, 128, 11, 48]
private def block0408 : List UInt8 := [220, 1, 128, 0]
private def block0409 : List UInt8 := [220, 1, 128, 0, 0, 128, 11, 48]
private def block0410 : List UInt8 := [220, 1, 129, 1]
private def block0411 : List UInt8 := [220, 1, 129, 1, 0, 128, 11, 48]
private def block0412 : List UInt8 := [0, 0, 0, 0, 0, 128, 11, 48]
private def block0413 : List UInt8 := [255, 255, 255, 255, 0, 128, 11, 48]
private def block0414 : List UInt8 := [1, 128, 11, 48, 85, 122, 159, 196]
private def block0415 : List UInt8 := [220, 1, 129, 0, 1, 128, 11, 48]
private def block0416 : List UInt8 := [0, 129, 11, 48, 85, 122, 159, 196]
private def block0417 : List UInt8 := [220, 1, 129, 0, 0, 129, 11, 48]
private def block0418 : List UInt8 := [0, 128, 10, 48, 85, 122, 159, 196]
private def block0419 : List UInt8 := [220, 1, 129, 0, 0, 128, 10, 48]
private def block0420 : List UInt8 := [0, 128, 11, 49, 85, 122, 159, 196]
private def block0421 : List UInt8 := [220, 1, 129, 0, 0, 128, 11, 49]
private def block0422 : List UInt8 := [0, 128, 11, 48, 84, 122, 159, 196]
private def block0423 : List UInt8 := [84, 122, 159, 196, 233, 14, 51, 88]
private def block0424 : List UInt8 := [0, 128, 11, 48, 85, 123, 159, 196]
private def block0425 : List UInt8 := [85, 123, 159, 196, 233, 14, 51, 88]
private def block0426 : List UInt8 := [0, 128, 11, 48, 85, 122, 158, 196]
private def block0427 : List UInt8 := [85, 122, 158, 196, 233, 14, 51, 88]
private def block0428 : List UInt8 := [0, 128, 11, 48, 85, 122, 159, 197]
private def block0429 : List UInt8 := [85, 122, 159, 197, 233, 14, 51, 88]
private def block0430 : List UInt8 := [232, 14, 51, 88, 125, 162, 199, 236]
private def block0431 : List UInt8 := [85, 122, 159, 196, 232, 14, 51, 88]
private def block0432 : List UInt8 := [233, 15, 51, 88, 125, 162, 199, 236]
private def block0433 : List UInt8 := [85, 122, 159, 196, 233, 15, 51, 88]
private def block0434 : List UInt8 := [233, 14, 50, 88, 125, 162, 199, 236]
private def block0435 : List UInt8 := [85, 122, 159, 196, 233, 14, 50, 88]
private def block0436 : List UInt8 := [233, 14, 51, 89, 125, 162, 199, 236]
private def block0437 : List UInt8 := [85, 122, 159, 196, 233, 14, 51, 89]
private def block0438 : List UInt8 := [233, 14, 51, 88, 124, 162, 199, 236]
private def block0439 : List UInt8 := [124, 162, 199, 236, 17, 54, 91, 128]
private def block0440 : List UInt8 := [233, 14, 51, 88, 125, 163, 199, 236]
private def block0441 : List UInt8 := [125, 163, 199, 236, 17, 54, 91, 128]
private def block0442 : List UInt8 := [233, 14, 51, 88, 125, 162, 198, 236]
private def block0443 : List UInt8 := [125, 162, 198, 236, 17, 54, 91, 128]
private def block0444 : List UInt8 := [233, 14, 51, 88, 125, 162, 199, 237]
private def block0445 : List UInt8 := [125, 162, 199, 237, 17, 54, 91, 128]
private def block0446 : List UInt8 := [16, 54, 91, 128, 165, 202, 239, 20]
private def block0447 : List UInt8 := [125, 162, 199, 236, 16, 54, 91, 128]
private def block0448 : List UInt8 := [17, 55, 91, 128, 165, 202, 239, 20]
private def block0449 : List UInt8 := [125, 162, 199, 236, 17, 55, 91, 128]
private def block0450 : List UInt8 := [17, 54, 90, 128, 165, 202, 239, 20]
private def block0451 : List UInt8 := [125, 162, 199, 236, 17, 54, 90, 128]
private def block0452 : List UInt8 := [17, 54, 91, 129, 165, 202, 239, 20]
private def block0453 : List UInt8 := [125, 162, 199, 236, 17, 54, 91, 129]
private def block0454 : List UInt8 := [17, 54, 91, 128, 164, 202, 239, 20]
private def block0455 : List UInt8 := [164, 202, 239, 20, 0, 255, 131, 168]
private def block0456 : List UInt8 := [17, 54, 91, 128, 165, 203, 239, 20]
private def block0457 : List UInt8 := [165, 203, 239, 20, 0, 255, 131, 168]
private def block0458 : List UInt8 := [17, 54, 91, 128, 165, 202, 238, 20]
private def block0459 : List UInt8 := [165, 202, 238, 20, 0, 255, 131, 168]
private def block0460 : List UInt8 := [17, 54, 91, 128, 165, 202, 239, 21]
private def block0461 : List UInt8 := [165, 202, 239, 21, 0, 255, 131, 168]
private def block0462 : List UInt8 := [1, 255, 131, 168, 205, 242, 23, 60]
private def block0463 : List UInt8 := [165, 202, 239, 20, 1, 255, 131, 168]
private def block0464 : List UInt8 := [0, 254, 131, 168, 205, 242, 23, 60]
private def block0465 : List UInt8 := [165, 202, 239, 20, 0, 254, 131, 168]
private def block0466 : List UInt8 := [0, 255, 130, 168, 205, 242, 23, 60]
private def block0467 : List UInt8 := [165, 202, 239, 20, 0, 255, 130, 168]
private def block0468 : List UInt8 := [0, 255, 131, 169, 205, 242, 23, 60]
private def block0469 : List UInt8 := [165, 202, 239, 20, 0, 255, 131, 169]
private def block0470 : List UInt8 := [0, 255, 131, 168, 204, 242, 23, 60]
private def block0471 : List UInt8 := [204, 242, 23, 60, 97, 134, 171, 208]
private def block0472 : List UInt8 := [0, 255, 131, 168, 205, 243, 23, 60]
private def block0473 : List UInt8 := [205, 243, 23, 60, 97, 134, 171, 208]
private def block0474 : List UInt8 := [0, 255, 131, 168, 205, 242, 22, 60]
private def block0475 : List UInt8 := [205, 242, 22, 60, 97, 134, 171, 208]
private def block0476 : List UInt8 := [0, 255, 131, 168, 205, 242, 23, 61]
private def block0477 : List UInt8 := [205, 242, 23, 61, 97, 134, 171, 208]
private def block0478 : List UInt8 := [96, 134, 171, 208, 245, 26, 63, 100]
private def block0479 : List UInt8 := [205, 242, 23, 60, 96, 134, 171, 208]
private def block0480 : List UInt8 := [97, 135, 171, 208, 245, 26, 63, 100]
private def block0481 : List UInt8 := [205, 242, 23, 60, 97, 135, 171, 208]
private def block0482 : List UInt8 := [97, 134, 170, 208, 245, 26, 63, 100]
private def block0483 : List UInt8 := [205, 242, 23, 60, 97, 134, 170, 208]
private def block0484 : List UInt8 := [97, 134, 171, 209, 245, 26, 63, 100]
private def block0485 : List UInt8 := [205, 242, 23, 60, 97, 134, 171, 209]
private def block0486 : List UInt8 := [97, 134, 171, 208, 244, 26, 63, 100]
private def block0487 : List UInt8 := [244, 26, 63, 100, 137, 174, 211, 248]
private def block0488 : List UInt8 := [97, 134, 171, 208, 245, 27, 63, 100]
private def block0489 : List UInt8 := [245, 27, 63, 100, 137, 174, 211, 248]
private def block0490 : List UInt8 := [97, 134, 171, 208, 245, 26, 62, 100]
private def block0491 : List UInt8 := [245, 26, 62, 100, 137, 174, 211, 248]
private def block0492 : List UInt8 := [97, 134, 171, 208, 245, 26, 63, 101]
private def block0493 : List UInt8 := [245, 26, 63, 101, 137, 174, 211, 248]
private def block0494 : List UInt8 := [136, 174, 211, 248, 29, 66, 129, 0]
private def block0495 : List UInt8 := [245, 26, 63, 100, 136, 174, 211, 248]
private def block0496 : List UInt8 := [137, 175, 211, 248, 29, 66, 129, 0]
private def block0497 : List UInt8 := [245, 26, 63, 100, 137, 175, 211, 248]
private def block0498 : List UInt8 := [137, 174, 210, 248, 29, 66, 129, 0]
private def block0499 : List UInt8 := [245, 26, 63, 100, 137, 174, 210, 248]
private def block0500 : List UInt8 := [137, 174, 211, 249, 29, 66, 129, 0]
private def block0501 : List UInt8 := [245, 26, 63, 100, 137, 174, 211, 249]
private def block0502 : List UInt8 := [137, 174, 211, 248, 28, 66, 129, 0]
private def block0503 : List UInt8 := [28, 66, 129, 0, 0, 128, 64, 101]
private def block0504 : List UInt8 := [137, 174, 211, 248, 29, 67, 129, 0]
private def block0505 : List UInt8 := [29, 67, 129, 0, 0, 128, 64, 101]
private def block0506 : List UInt8 := [137, 174, 211, 248, 29, 66, 128, 0]
private def block0507 : List UInt8 := [29, 66, 128, 0, 0, 128, 64, 101]
private def block0508 : List UInt8 := [137, 174, 211, 248, 29, 66, 129, 1]
private def block0509 : List UInt8 := [29, 66, 129, 1, 0, 128, 64, 101]
private def block0510 : List UInt8 := [220, 1, 129, 0, 0, 0, 0, 0]
private def block0511 : List UInt8 := [0, 0, 0, 0, 0, 128, 64, 101]
private def block0512 : List UInt8 := [220, 1, 129, 0, 255, 255, 255, 255]
private def block0513 : List UInt8 := [255, 255, 255, 255, 0, 128, 64, 101]
private def block0514 : List UInt8 := [1, 128, 64, 101, 138, 175, 212, 249]
private def block0515 : List UInt8 := [29, 66, 129, 0, 1, 128, 64, 101]
private def block0516 : List UInt8 := [0, 129, 64, 101, 138, 175, 212, 249]
private def block0517 : List UInt8 := [29, 66, 129, 0, 0, 129, 64, 101]
private def block0518 : List UInt8 := [0, 128, 65, 101, 138, 175, 212, 249]
private def block0519 : List UInt8 := [29, 66, 129, 0, 0, 128, 65, 101]
private def block0520 : List UInt8 := [0, 128, 64, 100, 138, 175, 212, 249]
private def block0521 : List UInt8 := [29, 66, 129, 0, 0, 128, 64, 100]
private def block0522 : List UInt8 := [0, 128, 64, 101, 139, 175, 212, 249]
private def block0523 : List UInt8 := [139, 175, 212, 249, 30, 67, 104, 141]
private def block0524 : List UInt8 := [0, 128, 64, 101, 138, 174, 212, 249]
private def block0525 : List UInt8 := [138, 174, 212, 249, 30, 67, 104, 141]
private def block0526 : List UInt8 := [0, 128, 64, 101, 138, 175, 213, 249]
private def block0527 : List UInt8 := [138, 175, 213, 249, 30, 67, 104, 141]
private def block0528 : List UInt8 := [0, 128, 64, 101, 138, 175, 212, 248]
private def block0529 : List UInt8 := [138, 175, 212, 248, 30, 67, 104, 141]
private def block0530 : List UInt8 := [31, 67, 104, 141, 178, 215, 252, 33]
private def block0531 : List UInt8 := [138, 175, 212, 249, 31, 67, 104, 141]
private def block0532 : List UInt8 := [30, 66, 104, 141, 178, 215, 252, 33]
private def block0533 : List UInt8 := [138, 175, 212, 249, 30, 66, 104, 141]
private def block0534 : List UInt8 := [30, 67, 105, 141, 178, 215, 252, 33]
private def block0535 : List UInt8 := [138, 175, 212, 249, 30, 67, 105, 141]
private def block0536 : List UInt8 := [30, 67, 104, 140, 178, 215, 252, 33]
private def block0537 : List UInt8 := [138, 175, 212, 249, 30, 67, 104, 140]
private def block0538 : List UInt8 := [30, 67, 104, 141, 179, 215, 252, 33]
private def block0539 : List UInt8 := [179, 215, 252, 33, 70, 107, 144, 181]
private def block0540 : List UInt8 := [30, 67, 104, 141, 178, 214, 252, 33]
private def block0541 : List UInt8 := [178, 214, 252, 33, 70, 107, 144, 181]
private def block0542 : List UInt8 := [30, 67, 104, 141, 178, 215, 253, 33]
private def block0543 : List UInt8 := [178, 215, 253, 33, 70, 107, 144, 181]
private def block0544 : List UInt8 := [30, 67, 104, 141, 178, 215, 252, 32]
private def block0545 : List UInt8 := [178, 215, 252, 32, 70, 107, 144, 181]
private def block0546 : List UInt8 := [71, 107, 144, 181, 218, 255, 36, 73]
private def block0547 : List UInt8 := [178, 215, 252, 33, 71, 107, 144, 181]
private def block0548 : List UInt8 := [70, 106, 144, 181, 218, 255, 36, 73]
private def block0549 : List UInt8 := [178, 215, 252, 33, 70, 106, 144, 181]
private def block0550 : List UInt8 := [70, 107, 145, 181, 218, 255, 36, 73]
private def block0551 : List UInt8 := [178, 215, 252, 33, 70, 107, 145, 181]
private def block0552 : List UInt8 := [70, 107, 144, 180, 218, 255, 36, 73]
private def block0553 : List UInt8 := [178, 215, 252, 33, 70, 107, 144, 180]
private def block0554 : List UInt8 := [70, 107, 144, 181, 219, 255, 36, 73]
private def block0555 : List UInt8 := [219, 255, 36, 73, 0, 255, 184, 221]
private def block0556 : List UInt8 := [70, 107, 144, 181, 218, 254, 36, 73]
private def block0557 : List UInt8 := [218, 254, 36, 73, 0, 255, 184, 221]
private def block0558 : List UInt8 := [70, 107, 144, 181, 218, 255, 37, 73]
private def block0559 : List UInt8 := [218, 255, 37, 73, 0, 255, 184, 221]
private def block0560 : List UInt8 := [70, 107, 144, 181, 218, 255, 36, 72]
private def block0561 : List UInt8 := [218, 255, 36, 72, 0, 255, 184, 221]
private def block0562 : List UInt8 := [1, 255, 184, 221, 2, 39, 76, 113]
private def block0563 : List UInt8 := [218, 255, 36, 73, 1, 255, 184, 221]
private def block0564 : List UInt8 := [0, 254, 184, 221, 2, 39, 76, 113]
private def block0565 : List UInt8 := [218, 255, 36, 73, 0, 254, 184, 221]
private def block0566 : List UInt8 := [0, 255, 185, 221, 2, 39, 76, 113]
private def block0567 : List UInt8 := [218, 255, 36, 73, 0, 255, 185, 221]
private def block0568 : List UInt8 := [0, 255, 184, 220, 2, 39, 76, 113]
private def block0569 : List UInt8 := [218, 255, 36, 73, 0, 255, 184, 220]
private def block0570 : List UInt8 := [0, 255, 184, 221, 3, 39, 76, 113]
private def block0571 : List UInt8 := [3, 39, 76, 113, 150, 187, 224, 5]
private def block0572 : List UInt8 := [0, 255, 184, 221, 2, 38, 76, 113]
private def block0573 : List UInt8 := [2, 38, 76, 113, 150, 187, 224, 5]
private def block0574 : List UInt8 := [0, 255, 184, 221, 2, 39, 77, 113]
private def block0575 : List UInt8 := [2, 39, 77, 113, 150, 187, 224, 5]
private def block0576 : List UInt8 := [0, 255, 184, 221, 2, 39, 76, 112]
private def block0577 : List UInt8 := [2, 39, 76, 112, 150, 187, 224, 5]
private def block0578 : List UInt8 := [151, 187, 224, 5, 42, 79, 116, 153]
private def block0579 : List UInt8 := [2, 39, 76, 113, 151, 187, 224, 5]
private def block0580 : List UInt8 := [150, 186, 224, 5, 42, 79, 116, 153]
private def block0581 : List UInt8 := [2, 39, 76, 113, 150, 186, 224, 5]
private def block0582 : List UInt8 := [150, 187, 225, 5, 42, 79, 116, 153]
private def block0583 : List UInt8 := [2, 39, 76, 113, 150, 187, 225, 5]
private def block0584 : List UInt8 := [150, 187, 224, 4, 42, 79, 116, 153]
private def block0585 : List UInt8 := [2, 39, 76, 113, 150, 187, 224, 4]
private def block0586 : List UInt8 := [150, 187, 224, 5, 43, 79, 116, 153]
private def block0587 : List UInt8 := [43, 79, 116, 153, 190, 227, 8, 45]
private def block0588 : List UInt8 := [150, 187, 224, 5, 42, 78, 116, 153]
private def block0589 : List UInt8 := [42, 78, 116, 153, 190, 227, 8, 45]
private def block0590 : List UInt8 := [150, 187, 224, 5, 42, 79, 117, 153]
private def block0591 : List UInt8 := [42, 79, 117, 153, 190, 227, 8, 45]
private def block0592 : List UInt8 := [150, 187, 224, 5, 42, 79, 116, 152]
private def block0593 : List UInt8 := [42, 79, 116, 152, 190, 227, 8, 45]
private def block0594 : List UInt8 := [191, 227, 8, 45, 82, 119, 129, 0]
private def block0595 : List UInt8 := [42, 79, 116, 153, 191, 227, 8, 45]
private def block0596 : List UInt8 := [190, 226, 8, 45, 82, 119, 129, 0]
private def block0597 : List UInt8 := [42, 79, 116, 153, 190, 226, 8, 45]
private def block0598 : List UInt8 := [190, 227, 9, 45, 82, 119, 129, 0]
private def block0599 : List UInt8 := [42, 79, 116, 153, 190, 227, 9, 45]
private def block0600 : List UInt8 := [190, 227, 8, 44, 82, 119, 129, 0]
private def block0601 : List UInt8 := [42, 79, 116, 153, 190, 227, 8, 44]
private def block0602 : List UInt8 := [190, 227, 8, 45, 83, 119, 129, 0]
private def block0603 : List UInt8 := [83, 119, 129, 0]
private def block0604 : List UInt8 := [190, 227, 8, 45, 82, 118, 129, 0]
private def block0605 : List UInt8 := [82, 118, 129, 0]
private def block0606 : List UInt8 := [190, 227, 8, 45, 82, 119, 128, 0]
private def block0607 : List UInt8 := [82, 119, 128, 0]
private def block0608 : List UInt8 := [190, 227, 8, 45, 82, 119, 129, 1]
private def block0609 : List UInt8 := [82, 119, 129, 1]
private def block0610 : List UInt8 := [29, 66, 129, 0, 0, 0, 0, 0]
private def block0611 : List UInt8 := [29, 66, 129, 0, 255, 255, 255, 255]
private def block0612 : List UInt8 := [0, 128, 243, 24, 61, 98, 135, 172]
private def block0613 : List UInt8 := [209, 246, 27, 64, 101, 138, 175, 212]
private def block0614 : List UInt8 := [249, 30, 67, 104, 141, 178, 215, 252]
private def block0615 : List UInt8 := [0, 255, 107, 144, 181, 218, 255, 36]
private def block0616 : List UInt8 := [73, 110, 147, 184, 221, 2, 39, 76]
private def block0617 : List UInt8 := [113, 150, 187, 224, 5, 42, 129, 0]
private def block0618 : List UInt8 := [0, 128, 40, 77, 114, 151, 188, 225]
private def block0619 : List UInt8 := [6, 43, 80, 117, 154, 191, 228, 9]
private def block0620 : List UInt8 := [0, 255, 120, 157, 194, 231, 12, 49]
private def block0621 : List UInt8 := [86, 123, 160, 197, 234, 15, 129, 0]
private def block0622 : List UInt8 := [0, 128, 146, 183, 220, 1, 38, 75]
private def block0623 : List UInt8 := [112, 149, 186, 223, 4, 41, 78, 115]
private def block0624 : List UInt8 := [152, 189, 226, 7, 44, 81, 118, 155]
private def block0625 : List UInt8 := [192, 229, 10, 47, 84, 121, 158, 195]
private def block0626 : List UInt8 := [232, 13, 50, 87, 124, 161, 198, 235]
private def block0627 : List UInt8 := [16, 53, 90, 127, 164, 201, 238, 19]
private def block0628 : List UInt8 := [0, 255, 130, 167, 204, 241, 22, 59]
private def block0629 : List UInt8 := [136, 173, 210, 247, 28, 65, 102, 139]
private def block0630 : List UInt8 := [0, 37, 74, 111, 148, 185, 129, 0]
private def block0631 : List UInt8 := [130, 192, 144, 80, 64, 48, 32, 16]
private def block0632 : List UInt8 := [1, 128, 243, 24, 61, 98, 135, 172]
private def block0633 : List UInt8 := [0, 129, 243, 24, 61, 98, 135, 172]
private def block0634 : List UInt8 := [0, 128, 242, 24, 61, 98, 135, 172]
private def block0635 : List UInt8 := [0, 128, 243, 25, 61, 98, 135, 172]
private def block0636 : List UInt8 := [0, 128, 243, 24, 60, 98, 135, 172]
private def block0637 : List UInt8 := [0, 128, 243, 24, 61, 99, 135, 172]
private def block0638 : List UInt8 := [0, 128, 243, 24, 61, 98, 134, 172]
private def block0639 : List UInt8 := [0, 128, 243, 24, 61, 98, 135, 173]
private def block0640 : List UInt8 := [208, 246, 27, 64, 101, 138, 175, 212]
private def block0641 : List UInt8 := [209, 247, 27, 64, 101, 138, 175, 212]
private def block0642 : List UInt8 := [209, 246, 26, 64, 101, 138, 175, 212]
private def block0643 : List UInt8 := [209, 246, 27, 65, 101, 138, 175, 212]
private def block0644 : List UInt8 := [209, 246, 27, 64, 100, 138, 175, 212]
private def block0645 : List UInt8 := [209, 246, 27, 64, 101, 139, 175, 212]
private def block0646 : List UInt8 := [209, 246, 27, 64, 101, 138, 174, 212]
private def block0647 : List UInt8 := [209, 246, 27, 64, 101, 138, 175, 213]
private def block0648 : List UInt8 := [248, 30, 67, 104, 141, 178, 215, 252]
private def block0649 : List UInt8 := [249, 31, 67, 104, 141, 178, 215, 252]
private def block0650 : List UInt8 := [249, 30, 66, 104, 141, 178, 215, 252]
private def block0651 : List UInt8 := [249, 30, 67, 105, 141, 178, 215, 252]
private def block0652 : List UInt8 := [249, 30, 67, 104, 140, 178, 215, 252]
private def block0653 : List UInt8 := [249, 30, 67, 104, 141, 179, 215, 252]
private def block0654 : List UInt8 := [249, 30, 67, 104, 141, 178, 214, 252]
private def block0655 : List UInt8 := [249, 30, 67, 104, 141, 178, 215, 253]
private def block0656 : List UInt8 := [1, 255, 107, 144, 181, 218, 255, 36]
private def block0657 : List UInt8 := [0, 254, 107, 144, 181, 218, 255, 36]
private def block0658 : List UInt8 := [0, 255, 106, 144, 181, 218, 255, 36]
private def block0659 : List UInt8 := [0, 255, 107, 145, 181, 218, 255, 36]
private def block0660 : List UInt8 := [0, 255, 107, 144, 180, 218, 255, 36]
private def block0661 : List UInt8 := [0, 255, 107, 144, 181, 219, 255, 36]
private def block0662 : List UInt8 := [0, 255, 107, 144, 181, 218, 254, 36]
private def block0663 : List UInt8 := [0, 255, 107, 144, 181, 218, 255, 37]
private def block0664 : List UInt8 := [72, 110, 147, 184, 221, 2, 39, 76]
private def block0665 : List UInt8 := [73, 111, 147, 184, 221, 2, 39, 76]
private def block0666 : List UInt8 := [73, 110, 146, 184, 221, 2, 39, 76]
private def block0667 : List UInt8 := [73, 110, 147, 185, 221, 2, 39, 76]
private def block0668 : List UInt8 := [73, 110, 147, 184, 220, 2, 39, 76]
private def block0669 : List UInt8 := [73, 110, 147, 184, 221, 3, 39, 76]
private def block0670 : List UInt8 := [73, 110, 147, 184, 221, 2, 38, 76]
private def block0671 : List UInt8 := [73, 110, 147, 184, 221, 2, 39, 77]
private def block0672 : List UInt8 := [112, 150, 187, 224, 5, 42, 129, 0]
private def block0673 : List UInt8 := [113, 151, 187, 224, 5, 42, 129, 0]
private def block0674 : List UInt8 := [113, 150, 186, 224, 5, 42, 129, 0]
private def block0675 : List UInt8 := [113, 150, 187, 225, 5, 42, 129, 0]
private def block0676 : List UInt8 := [113, 150, 187, 224, 4, 42, 129, 0]
private def block0677 : List UInt8 := [113, 150, 187, 224, 5, 43, 129, 0]
private def block0678 : List UInt8 := [113, 150, 187, 224, 5, 42, 128, 0]
private def block0679 : List UInt8 := [113, 150, 187, 224, 5, 42, 129, 1]
private def block0680 : List UInt8 := [1, 128, 40, 77, 114, 151, 188, 225]
private def block0681 : List UInt8 := [0, 129, 40, 77, 114, 151, 188, 225]
private def block0682 : List UInt8 := [0, 128, 41, 77, 114, 151, 188, 225]
private def block0683 : List UInt8 := [0, 128, 40, 76, 114, 151, 188, 225]
private def block0684 : List UInt8 := [0, 128, 40, 77, 115, 151, 188, 225]
private def block0685 : List UInt8 := [0, 128, 40, 77, 114, 150, 188, 225]
private def block0686 : List UInt8 := [0, 128, 40, 77, 114, 151, 189, 225]
private def block0687 : List UInt8 := [0, 128, 40, 77, 114, 151, 188, 224]
private def block0688 : List UInt8 := [7, 43, 80, 117, 154, 191, 228, 9]
private def block0689 : List UInt8 := [6, 42, 80, 117, 154, 191, 228, 9]
private def block0690 : List UInt8 := [6, 43, 81, 117, 154, 191, 228, 9]
private def block0691 : List UInt8 := [6, 43, 80, 116, 154, 191, 228, 9]
private def block0692 : List UInt8 := [6, 43, 80, 117, 155, 191, 228, 9]
private def block0693 : List UInt8 := [6, 43, 80, 117, 154, 190, 228, 9]
private def block0694 : List UInt8 := [6, 43, 80, 117, 154, 191, 229, 9]
private def block0695 : List UInt8 := [6, 43, 80, 117, 154, 191, 228, 8]
private def block0696 : List UInt8 := [1, 255, 120, 157, 194, 231, 12, 49]
private def block0697 : List UInt8 := [0, 254, 120, 157, 194, 231, 12, 49]
private def block0698 : List UInt8 := [0, 255, 121, 157, 194, 231, 12, 49]
private def block0699 : List UInt8 := [0, 255, 120, 156, 194, 231, 12, 49]
private def block0700 : List UInt8 := [0, 255, 120, 157, 195, 231, 12, 49]
private def block0701 : List UInt8 := [0, 255, 120, 157, 194, 230, 12, 49]
private def block0702 : List UInt8 := [0, 255, 120, 157, 194, 231, 13, 49]
private def block0703 : List UInt8 := [0, 255, 120, 157, 194, 231, 12, 48]
private def block0704 : List UInt8 := [87, 123, 160, 197, 234, 15, 129, 0]
private def block0705 : List UInt8 := [86, 122, 160, 197, 234, 15, 129, 0]
private def block0706 : List UInt8 := [86, 123, 161, 197, 234, 15, 129, 0]
private def block0707 : List UInt8 := [86, 123, 160, 196, 234, 15, 129, 0]
private def block0708 : List UInt8 := [86, 123, 160, 197, 235, 15, 129, 0]
private def block0709 : List UInt8 := [86, 123, 160, 197, 234, 14, 129, 0]
private def block0710 : List UInt8 := [86, 123, 160, 197, 234, 15, 128, 0]
private def block0711 : List UInt8 := [86, 123, 160, 197, 234, 15, 129, 1]
private def block0712 : List UInt8 := [1, 128, 146, 183, 220, 1, 38, 75]
private def block0713 : List UInt8 := [0, 129, 146, 183, 220, 1, 38, 75]
private def block0714 : List UInt8 := [0, 128, 147, 183, 220, 1, 38, 75]
private def block0715 : List UInt8 := [0, 128, 146, 182, 220, 1, 38, 75]
private def block0716 : List UInt8 := [0, 128, 146, 183, 221, 1, 38, 75]
private def block0717 : List UInt8 := [0, 128, 146, 183, 220, 0, 38, 75]
private def block0718 : List UInt8 := [0, 128, 146, 183, 220, 1, 39, 75]
private def block0719 : List UInt8 := [0, 128, 146, 183, 220, 1, 38, 74]
private def block0720 : List UInt8 := [113, 149, 186, 223, 4, 41, 78, 115]
private def block0721 : List UInt8 := [112, 148, 186, 223, 4, 41, 78, 115]
private def block0722 : List UInt8 := [112, 149, 187, 223, 4, 41, 78, 115]
private def block0723 : List UInt8 := [112, 149, 186, 222, 4, 41, 78, 115]
private def block0724 : List UInt8 := [112, 149, 186, 223, 5, 41, 78, 115]
private def block0725 : List UInt8 := [112, 149, 186, 223, 4, 40, 78, 115]
private def block0726 : List UInt8 := [112, 149, 186, 223, 4, 41, 79, 115]
private def block0727 : List UInt8 := [112, 149, 186, 223, 4, 41, 78, 114]
private def block0728 : List UInt8 := [153, 189, 226, 7, 44, 81, 118, 155]
private def block0729 : List UInt8 := [152, 188, 226, 7, 44, 81, 118, 155]
private def block0730 : List UInt8 := [152, 189, 227, 7, 44, 81, 118, 155]
private def block0731 : List UInt8 := [152, 189, 226, 6, 44, 81, 118, 155]
private def block0732 : List UInt8 := [152, 189, 226, 7, 45, 81, 118, 155]
private def block0733 : List UInt8 := [152, 189, 226, 7, 44, 80, 118, 155]
private def block0734 : List UInt8 := [152, 189, 226, 7, 44, 81, 119, 155]
private def block0735 : List UInt8 := [152, 189, 226, 7, 44, 81, 118, 154]
private def block0736 : List UInt8 := [193, 229, 10, 47, 84, 121, 158, 195]
private def block0737 : List UInt8 := [192, 228, 10, 47, 84, 121, 158, 195]
private def block0738 : List UInt8 := [192, 229, 11, 47, 84, 121, 158, 195]
private def block0739 : List UInt8 := [192, 229, 10, 46, 84, 121, 158, 195]
private def block0740 : List UInt8 := [192, 229, 10, 47, 85, 121, 158, 195]
private def block0741 : List UInt8 := [192, 229, 10, 47, 84, 120, 158, 195]
private def block0742 : List UInt8 := [192, 229, 10, 47, 84, 121, 159, 195]
private def block0743 : List UInt8 := [192, 229, 10, 47, 84, 121, 158, 194]
private def block0744 : List UInt8 := [233, 13, 50, 87, 124, 161, 198, 235]
private def block0745 : List UInt8 := [232, 12, 50, 87, 124, 161, 198, 235]
private def block0746 : List UInt8 := [232, 13, 51, 87, 124, 161, 198, 235]
private def block0747 : List UInt8 := [232, 13, 50, 86, 124, 161, 198, 235]
private def block0748 : List UInt8 := [232, 13, 50, 87, 125, 161, 198, 235]
private def block0749 : List UInt8 := [232, 13, 50, 87, 124, 160, 198, 235]
private def block0750 : List UInt8 := [232, 13, 50, 87, 124, 161, 199, 235]
private def block0751 : List UInt8 := [232, 13, 50, 87, 124, 161, 198, 234]
private def block0752 : List UInt8 := [17, 53, 90, 127, 164, 201, 238, 19]
private def block0753 : List UInt8 := [16, 52, 90, 127, 164, 201, 238, 19]
private def block0754 : List UInt8 := [16, 53, 91, 127, 164, 201, 238, 19]
private def block0755 : List UInt8 := [16, 53, 90, 126, 164, 201, 238, 19]
private def block0756 : List UInt8 := [16, 53, 90, 127, 165, 201, 238, 19]
private def block0757 : List UInt8 := [16, 53, 90, 127, 164, 200, 238, 19]
private def block0758 : List UInt8 := [16, 53, 90, 127, 164, 201, 239, 19]
private def block0759 : List UInt8 := [16, 53, 90, 127, 164, 201, 238, 18]
private def block0760 : List UInt8 := [1, 255, 130, 167, 204, 241, 22, 59]
private def block0761 : List UInt8 := [0, 254, 130, 167, 204, 241, 22, 59]
private def block0762 : List UInt8 := [0, 255, 131, 167, 204, 241, 22, 59]
private def block0763 : List UInt8 := [0, 255, 130, 166, 204, 241, 22, 59]
private def block0764 : List UInt8 := [0, 255, 130, 167, 205, 241, 22, 59]
private def block0765 : List UInt8 := [0, 255, 130, 167, 204, 240, 22, 59]
private def block0766 : List UInt8 := [0, 255, 130, 167, 204, 241, 23, 59]
private def block0767 : List UInt8 := [0, 255, 130, 167, 204, 241, 22, 58]
private def block0768 : List UInt8 := [137, 173, 210, 247, 28, 65, 102, 139]
private def block0769 : List UInt8 := [136, 172, 210, 247, 28, 65, 102, 139]
private def block0770 : List UInt8 := [136, 173, 211, 247, 28, 65, 102, 139]
private def block0771 : List UInt8 := [136, 173, 210, 246, 28, 65, 102, 139]
private def block0772 : List UInt8 := [136, 173, 210, 247, 29, 65, 102, 139]
private def block0773 : List UInt8 := [136, 173, 210, 247, 28, 64, 102, 139]
private def block0774 : List UInt8 := [136, 173, 210, 247, 28, 65, 103, 139]
private def block0775 : List UInt8 := [136, 173, 210, 247, 28, 65, 102, 138]
private def block0776 : List UInt8 := [1, 37, 74, 111, 148, 185, 129, 0]
private def block0777 : List UInt8 := [0, 36, 74, 111, 148, 185, 129, 0]
private def block0778 : List UInt8 := [0, 37, 75, 111, 148, 185, 129, 0]
private def block0779 : List UInt8 := [0, 37, 74, 110, 148, 185, 129, 0]
private def block0780 : List UInt8 := [0, 37, 74, 111, 149, 185, 129, 0]
private def block0781 : List UInt8 := [0, 37, 74, 111, 148, 184, 129, 0]
private def block0782 : List UInt8 := [0, 37, 74, 111, 148, 185, 128, 0]
private def block0783 : List UInt8 := [0, 37, 74, 111, 148, 185, 129, 1]
private def block0784 : List UInt8 := [0, 128, 16, 53, 90, 127, 164, 201]
private def block0785 : List UInt8 := [238, 19, 0, 255, 130, 167, 204, 241]
private def block0786 : List UInt8 := [22, 59, 129, 0]
private def block0787 : List UInt8 := [0, 128, 69, 106, 143, 180, 217, 254]
private def block0788 : List UInt8 := [35, 72, 109, 146, 183, 220, 1, 38]
private def block0789 : List UInt8 := [75, 112, 149, 186, 223, 4, 41, 78]
private def block0790 : List UInt8 := [0, 255, 189, 226, 7, 44, 81, 118]
private def block0791 : List UInt8 := [155, 192, 229, 10, 47, 84, 121, 158]
private def block0792 : List UInt8 := [195, 232, 13, 50, 87, 124, 129, 0]
private def block0793 : List UInt8 := [22, 59, 129, 0, 0, 128, 69, 106]
private def block0794 : List UInt8 := [143, 180, 217, 254, 35, 72, 109, 146]
private def block0795 : List UInt8 := [183, 220, 1, 38, 75, 112, 149, 186]
private def block0796 : List UInt8 := [223, 4, 41, 78, 0, 255, 189, 226]
private def block0797 : List UInt8 := [7, 44, 81, 118, 155, 192, 229, 10]
private def block0798 : List UInt8 := [47, 84, 121, 158, 195, 232, 13, 50]
private def block0799 : List UInt8 := [87, 124, 129, 0]
private def block0800 : List UInt8 := [1, 128, 16, 53, 90, 127, 164, 201]
private def block0801 : List UInt8 := [0, 129, 16, 53, 90, 127, 164, 201]
private def block0802 : List UInt8 := [0, 128, 17, 53, 90, 127, 164, 201]
private def block0803 : List UInt8 := [0, 128, 16, 52, 90, 127, 164, 201]
private def block0804 : List UInt8 := [0, 128, 16, 53, 91, 127, 164, 201]
private def block0805 : List UInt8 := [0, 128, 16, 53, 90, 126, 164, 201]
private def block0806 : List UInt8 := [0, 128, 16, 53, 90, 127, 165, 201]
private def block0807 : List UInt8 := [0, 128, 16, 53, 90, 127, 164, 200]
private def block0808 : List UInt8 := [239, 19, 0, 255, 130, 167, 204, 241]
private def block0809 : List UInt8 := [238, 18, 0, 255, 130, 167, 204, 241]
private def block0810 : List UInt8 := [238, 19, 1, 255, 130, 167, 204, 241]
private def block0811 : List UInt8 := [238, 19, 0, 254, 130, 167, 204, 241]
private def block0812 : List UInt8 := [238, 19, 0, 255, 131, 167, 204, 241]
private def block0813 : List UInt8 := [238, 19, 0, 255, 130, 166, 204, 241]
private def block0814 : List UInt8 := [238, 19, 0, 255, 130, 167, 205, 241]
private def block0815 : List UInt8 := [238, 19, 0, 255, 130, 167, 204, 240]
private def block0816 : List UInt8 := [23, 59, 129, 0]
private def block0817 : List UInt8 := [23, 59, 129, 0, 0, 128, 69, 106]
private def block0818 : List UInt8 := [22, 58, 129, 0]
private def block0819 : List UInt8 := [22, 58, 129, 0, 0, 128, 69, 106]
private def block0820 : List UInt8 := [22, 59, 128, 0]
private def block0821 : List UInt8 := [22, 59, 128, 0, 0, 128, 69, 106]
private def block0822 : List UInt8 := [22, 59, 129, 1]
private def block0823 : List UInt8 := [22, 59, 129, 1, 0, 128, 69, 106]
private def block0824 : List UInt8 := [0, 0, 0, 0, 0, 128, 69, 106]
private def block0825 : List UInt8 := [255, 255, 255, 255, 0, 128, 69, 106]
private def block0826 : List UInt8 := [1, 128, 69, 106, 143, 180, 217, 254]
private def block0827 : List UInt8 := [22, 59, 129, 0, 1, 128, 69, 106]
private def block0828 : List UInt8 := [0, 129, 69, 106, 143, 180, 217, 254]
private def block0829 : List UInt8 := [22, 59, 129, 0, 0, 129, 69, 106]
private def block0830 : List UInt8 := [0, 128, 68, 106, 143, 180, 217, 254]
private def block0831 : List UInt8 := [22, 59, 129, 0, 0, 128, 68, 106]
private def block0832 : List UInt8 := [0, 128, 69, 107, 143, 180, 217, 254]
private def block0833 : List UInt8 := [22, 59, 129, 0, 0, 128, 69, 107]
private def block0834 : List UInt8 := [0, 128, 69, 106, 142, 180, 217, 254]
private def block0835 : List UInt8 := [142, 180, 217, 254, 35, 72, 109, 146]
private def block0836 : List UInt8 := [0, 128, 69, 106, 143, 181, 217, 254]
private def block0837 : List UInt8 := [143, 181, 217, 254, 35, 72, 109, 146]
private def block0838 : List UInt8 := [0, 128, 69, 106, 143, 180, 216, 254]
private def block0839 : List UInt8 := [143, 180, 216, 254, 35, 72, 109, 146]
private def block0840 : List UInt8 := [0, 128, 69, 106, 143, 180, 217, 255]
private def block0841 : List UInt8 := [143, 180, 217, 255, 35, 72, 109, 146]
private def block0842 : List UInt8 := [34, 72, 109, 146, 183, 220, 1, 38]
private def block0843 : List UInt8 := [143, 180, 217, 254, 34, 72, 109, 146]
private def block0844 : List UInt8 := [35, 73, 109, 146, 183, 220, 1, 38]
private def block0845 : List UInt8 := [143, 180, 217, 254, 35, 73, 109, 146]
private def block0846 : List UInt8 := [35, 72, 108, 146, 183, 220, 1, 38]
private def block0847 : List UInt8 := [143, 180, 217, 254, 35, 72, 108, 146]
private def block0848 : List UInt8 := [35, 72, 109, 147, 183, 220, 1, 38]
private def block0849 : List UInt8 := [143, 180, 217, 254, 35, 72, 109, 147]
private def block0850 : List UInt8 := [35, 72, 109, 146, 182, 220, 1, 38]
private def block0851 : List UInt8 := [182, 220, 1, 38, 75, 112, 149, 186]
private def block0852 : List UInt8 := [35, 72, 109, 146, 183, 221, 1, 38]
private def block0853 : List UInt8 := [183, 221, 1, 38, 75, 112, 149, 186]
private def block0854 : List UInt8 := [35, 72, 109, 146, 183, 220, 0, 38]
private def block0855 : List UInt8 := [183, 220, 0, 38, 75, 112, 149, 186]
private def block0856 : List UInt8 := [35, 72, 109, 146, 183, 220, 1, 39]
private def block0857 : List UInt8 := [183, 220, 1, 39, 75, 112, 149, 186]
private def block0858 : List UInt8 := [74, 112, 149, 186, 223, 4, 41, 78]
private def block0859 : List UInt8 := [183, 220, 1, 38, 74, 112, 149, 186]
private def block0860 : List UInt8 := [75, 113, 149, 186, 223, 4, 41, 78]
private def block0861 : List UInt8 := [183, 220, 1, 38, 75, 113, 149, 186]
private def block0862 : List UInt8 := [75, 112, 148, 186, 223, 4, 41, 78]
private def block0863 : List UInt8 := [183, 220, 1, 38, 75, 112, 148, 186]
private def block0864 : List UInt8 := [75, 112, 149, 187, 223, 4, 41, 78]
private def block0865 : List UInt8 := [183, 220, 1, 38, 75, 112, 149, 187]
private def block0866 : List UInt8 := [75, 112, 149, 186, 222, 4, 41, 78]
private def block0867 : List UInt8 := [222, 4, 41, 78, 0, 255, 189, 226]
private def block0868 : List UInt8 := [75, 112, 149, 186, 223, 5, 41, 78]
private def block0869 : List UInt8 := [223, 5, 41, 78, 0, 255, 189, 226]
private def block0870 : List UInt8 := [75, 112, 149, 186, 223, 4, 40, 78]
private def block0871 : List UInt8 := [223, 4, 40, 78, 0, 255, 189, 226]
private def block0872 : List UInt8 := [75, 112, 149, 186, 223, 4, 41, 79]
private def block0873 : List UInt8 := [223, 4, 41, 79, 0, 255, 189, 226]
private def block0874 : List UInt8 := [1, 255, 189, 226, 7, 44, 81, 118]
private def block0875 : List UInt8 := [223, 4, 41, 78, 1, 255, 189, 226]
private def block0876 : List UInt8 := [0, 254, 189, 226, 7, 44, 81, 118]
private def block0877 : List UInt8 := [223, 4, 41, 78, 0, 254, 189, 226]
private def block0878 : List UInt8 := [0, 255, 188, 226, 7, 44, 81, 118]
private def block0879 : List UInt8 := [223, 4, 41, 78, 0, 255, 188, 226]
private def block0880 : List UInt8 := [0, 255, 189, 227, 7, 44, 81, 118]
private def block0881 : List UInt8 := [223, 4, 41, 78, 0, 255, 189, 227]
private def block0882 : List UInt8 := [0, 255, 189, 226, 6, 44, 81, 118]
private def block0883 : List UInt8 := [6, 44, 81, 118, 155, 192, 229, 10]
private def block0884 : List UInt8 := [0, 255, 189, 226, 7, 45, 81, 118]
private def block0885 : List UInt8 := [7, 45, 81, 118, 155, 192, 229, 10]
private def block0886 : List UInt8 := [0, 255, 189, 226, 7, 44, 80, 118]
private def block0887 : List UInt8 := [7, 44, 80, 118, 155, 192, 229, 10]
private def block0888 : List UInt8 := [0, 255, 189, 226, 7, 44, 81, 119]
private def block0889 : List UInt8 := [7, 44, 81, 119, 155, 192, 229, 10]
private def block0890 : List UInt8 := [154, 192, 229, 10, 47, 84, 121, 158]
private def block0891 : List UInt8 := [7, 44, 81, 118, 154, 192, 229, 10]
private def block0892 : List UInt8 := [155, 193, 229, 10, 47, 84, 121, 158]
private def block0893 : List UInt8 := [7, 44, 81, 118, 155, 193, 229, 10]
private def block0894 : List UInt8 := [155, 192, 228, 10, 47, 84, 121, 158]
private def block0895 : List UInt8 := [7, 44, 81, 118, 155, 192, 228, 10]
private def block0896 : List UInt8 := [155, 192, 229, 11, 47, 84, 121, 158]
private def block0897 : List UInt8 := [7, 44, 81, 118, 155, 192, 229, 11]
private def block0898 : List UInt8 := [155, 192, 229, 10, 46, 84, 121, 158]
private def block0899 : List UInt8 := [46, 84, 121, 158, 195, 232, 13, 50]
private def block0900 : List UInt8 := [155, 192, 229, 10, 47, 85, 121, 158]
private def block0901 : List UInt8 := [47, 85, 121, 158, 195, 232, 13, 50]
private def block0902 : List UInt8 := [155, 192, 229, 10, 47, 84, 120, 158]
private def block0903 : List UInt8 := [47, 84, 120, 158, 195, 232, 13, 50]
private def block0904 : List UInt8 := [155, 192, 229, 10, 47, 84, 121, 159]
private def block0905 : List UInt8 := [47, 84, 121, 159, 195, 232, 13, 50]
private def block0906 : List UInt8 := [194, 232, 13, 50, 87, 124, 129, 0]
private def block0907 : List UInt8 := [47, 84, 121, 158, 194, 232, 13, 50]
private def block0908 : List UInt8 := [195, 233, 13, 50, 87, 124, 129, 0]
private def block0909 : List UInt8 := [47, 84, 121, 158, 195, 233, 13, 50]
private def block0910 : List UInt8 := [195, 232, 12, 50, 87, 124, 129, 0]
private def block0911 : List UInt8 := [47, 84, 121, 158, 195, 232, 12, 50]
private def block0912 : List UInt8 := [195, 232, 13, 51, 87, 124, 129, 0]
private def block0913 : List UInt8 := [47, 84, 121, 158, 195, 232, 13, 51]
private def block0914 : List UInt8 := [195, 232, 13, 50, 86, 124, 129, 0]
private def block0915 : List UInt8 := [86, 124, 129, 0]
private def block0916 : List UInt8 := [195, 232, 13, 50, 87, 125, 129, 0]
private def block0917 : List UInt8 := [87, 125, 129, 0]
private def block0918 : List UInt8 := [195, 232, 13, 50, 87, 124, 128, 0]
private def block0919 : List UInt8 := [87, 124, 128, 0]
private def block0920 : List UInt8 := [195, 232, 13, 50, 87, 124, 129, 1]
private def block0921 : List UInt8 := [87, 124, 129, 1]
private def block0922 : List UInt8 := [22, 59, 129, 0, 0, 0, 0, 0]
private def block0923 : List UInt8 := [22, 59, 129, 0, 255, 255, 255, 255]
private def block0924 : List UInt8 := [220, 1, 129, 0, 0, 128, 64, 101]
private def block0925 : List UInt8 := [82, 119, 129, 0, 0, 128, 11, 48]
private def block0926 : List UInt8 := [29, 66, 129, 0]
private def block0927 : List UInt8 := [0, 128, 81, 118, 155, 192, 229, 10]
private def block0928 : List UInt8 := [87, 124, 161, 198, 235, 16, 53, 90]
private def block0929 : List UInt8 := [0, 255, 201, 238, 19, 56, 93, 130]
private def block0930 : List UInt8 := [167, 204, 241, 22, 59, 96, 133, 170]
private def block0931 : List UInt8 := [207, 244, 25, 62, 99, 136, 129, 0]
private def block0932 : List UInt8 := [0, 128, 28, 65, 102, 139, 176, 213]
private def block0933 : List UInt8 := [250, 31, 68, 105, 142, 179, 216, 253]
private def block0934 : List UInt8 := [34, 71, 108, 145, 182, 219, 0, 37]
private def block0935 : List UInt8 := [0, 255, 148, 185, 222, 3, 40, 77]
private def block0936 : List UInt8 := [114, 151, 188, 225, 6, 43, 80, 117]
private def block0937 : List UInt8 := [154, 191, 228, 9, 46, 83, 129, 0]
private def block0938 : List UInt8 := [220, 1, 129, 0, 0, 128, 81, 118]
private def block0939 : List UInt8 := [195, 232, 13, 50, 87, 124, 161, 198]
private def block0940 : List UInt8 := [235, 16, 53, 90, 0, 255, 201, 238]
private def block0941 : List UInt8 := [19, 56, 93, 130, 167, 204, 241, 22]
private def block0942 : List UInt8 := [59, 96, 133, 170, 207, 244, 25, 62]
private def block0943 : List UInt8 := [99, 136, 129, 0, 0, 128, 28, 65]
private def block0944 : List UInt8 := [102, 139, 176, 213, 250, 31, 68, 105]
private def block0945 : List UInt8 := [142, 179, 216, 253, 34, 71, 108, 145]
private def block0946 : List UInt8 := [182, 219, 0, 37, 0, 255, 148, 185]
private def block0947 : List UInt8 := [222, 3, 40, 77, 114, 151, 188, 225]
private def block0948 : List UInt8 := [46, 83, 129, 0]
private def block0949 : List UInt8 := [0, 128, 98, 135, 172, 209, 246, 27]
private def block0950 : List UInt8 := [64, 101, 138, 175, 212, 249, 30, 67]
private def block0951 : List UInt8 := [104, 141, 178, 215, 252, 33, 70, 107]
private def block0952 : List UInt8 := [0, 255, 218, 255, 36, 73, 110, 147]
private def block0953 : List UInt8 := [184, 221, 2, 39, 76, 113, 150, 187]
private def block0954 : List UInt8 := [224, 5, 42, 79, 116, 153, 129, 0]
private def block0955 : List UInt8 := [0, 128, 45, 82, 119, 156, 193, 230]
private def block0956 : List UInt8 := [11, 48, 85, 122, 159, 196, 233, 14]
private def block0957 : List UInt8 := [51, 88, 125, 162, 199, 236, 17, 54]
private def block0958 : List UInt8 := [0, 255, 165, 202, 239, 20, 57, 94]
private def block0959 : List UInt8 := [131, 168, 205, 242, 23, 60, 97, 134]
private def block0960 : List UInt8 := [171, 208, 245, 26, 63, 100, 129, 0]
private def block0961 : List UInt8 := [220, 1, 129, 0, 0, 128, 98, 135]
private def block0962 : List UInt8 := [172, 209, 246, 27, 64, 101, 138, 175]
private def block0963 : List UInt8 := [212, 249, 30, 67, 104, 141, 178, 215]
private def block0964 : List UInt8 := [252, 33, 70, 107, 0, 255, 218, 255]
private def block0965 : List UInt8 := [36, 73, 110, 147, 184, 221, 2, 39]
private def block0966 : List UInt8 := [76, 113, 150, 187, 224, 5, 42, 79]
private def block0967 : List UInt8 := [116, 153, 129, 0, 0, 128, 45, 82]
private def block0968 : List UInt8 := [119, 156, 193, 230, 11, 48, 85, 122]
private def block0969 : List UInt8 := [159, 196, 233, 14, 51, 88, 125, 162]
private def block0970 : List UInt8 := [199, 236, 17, 54, 0, 255, 165, 202]
private def block0971 : List UInt8 := [239, 20, 57, 94, 131, 168, 205, 242]
private def block0972 : List UInt8 := [23, 60, 97, 134, 171, 208, 245, 26]
private def block0973 : List UInt8 := [63, 100, 129, 0]
private def block0974 : List UInt8 := [0, 128, 115, 152, 189, 226, 7, 44]
private def block0975 : List UInt8 := [81, 118, 155, 192, 229, 10, 47, 84]
private def block0976 : List UInt8 := [121, 158, 195, 232, 13, 50, 87, 124]
private def block0977 : List UInt8 := [0, 255, 235, 16, 53, 90, 127, 164]
private def block0978 : List UInt8 := [201, 238, 19, 56, 93, 130, 167, 204]
private def block0979 : List UInt8 := [241, 22, 59, 96, 133, 170, 129, 0]
private def block0980 : List UInt8 := [0, 128, 62, 99, 136, 173, 210, 247]
private def block0981 : List UInt8 := [28, 65, 102, 139, 176, 213, 250, 31]
private def block0982 : List UInt8 := [0, 255, 182, 219, 0, 37, 74, 111]
private def block0983 : List UInt8 := [148, 185, 222, 3, 40, 77, 114, 151]
private def block0984 : List UInt8 := [188, 225, 6, 43, 80, 117, 129, 0]
private def block0985 : List UInt8 := [220, 1, 129, 0, 0, 128, 115, 152]
private def block0986 : List UInt8 := [189, 226, 7, 44, 81, 118, 155, 192]
private def block0987 : List UInt8 := [229, 10, 47, 84, 121, 158, 195, 232]
private def block0988 : List UInt8 := [13, 50, 87, 124, 0, 255, 235, 16]
private def block0989 : List UInt8 := [53, 90, 127, 164, 201, 238, 19, 56]
private def block0990 : List UInt8 := [93, 130, 167, 204, 241, 22, 59, 96]
private def block0991 : List UInt8 := [133, 170, 129, 0, 0, 128, 62, 99]
private def block0992 : List UInt8 := [216, 253, 34, 71, 0, 255, 182, 219]
private def block0993 : List UInt8 := [0, 37, 74, 111, 148, 185, 222, 3]
private def block0994 : List UInt8 := [40, 77, 114, 151, 188, 225, 6, 43]
private def block0995 : List UInt8 := [80, 117, 129, 0]
private def bytes0000 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0001 : ByteArray :=
  (block0006 ++ block0007 ++ block0008 ++ block0009).toByteArray
private def bytes0002 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0003 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0004 : ByteArray :=
  (block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024).toByteArray
private def bytes0005 : ByteArray :=
  (block0024 ++ block0024 ++ block0024 ++ block0024).toByteArray
private def bytes0006 : ByteArray :=
  (block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++
    block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024).toByteArray
private def bytes0007 : ByteArray :=
  (block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++
    block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++
    block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++
    block0024 ++ block0024 ++ block0024).toByteArray
private def bytes0008 : ByteArray :=
  (block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025).toByteArray
private def bytes0009 : ByteArray :=
  (block0025 ++ block0025 ++ block0025 ++ block0025).toByteArray
private def bytes0010 : ByteArray :=
  (block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++
    block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025).toByteArray
private def bytes0011 : ByteArray :=
  (block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++
    block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++
    block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++
    block0025 ++ block0025 ++ block0025).toByteArray
private def bytes0012 : ByteArray :=
  (block0026 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0013 : ByteArray :=
  (block0026 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0014 : ByteArray :=
  (block0027 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0015 : ByteArray :=
  (block0027 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0016 : ByteArray :=
  (block0028 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0017 : ByteArray :=
  (block0028 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0018 : ByteArray :=
  (block0029 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0019 : ByteArray :=
  (block0029 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0020 : ByteArray :=
  (block0030 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0021 : ByteArray :=
  (block0030 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0022 : ByteArray :=
  (block0031 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0023 : ByteArray :=
  (block0031 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0024 : ByteArray :=
  (block0032 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0025 : ByteArray :=
  (block0032 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0026 : ByteArray :=
  (block0033 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0027 : ByteArray :=
  (block0033 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0028 : ByteArray :=
  (block0000 ++ block0034 ++ block0002 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0029 : ByteArray :=
  (block0000 ++ block0034 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0030 : ByteArray :=
  (block0000 ++ block0035 ++ block0002 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0031 : ByteArray :=
  (block0000 ++ block0035 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0032 : ByteArray :=
  (block0000 ++ block0036 ++ block0002 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0033 : ByteArray :=
  (block0000 ++ block0036 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0034 : ByteArray :=
  (block0000 ++ block0037 ++ block0002 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0035 : ByteArray :=
  (block0000 ++ block0037 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0036 : ByteArray :=
  (block0000 ++ block0038 ++ block0002 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0037 : ByteArray :=
  (block0000 ++ block0038 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0038 : ByteArray :=
  (block0000 ++ block0039 ++ block0002 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0039 : ByteArray :=
  (block0000 ++ block0039 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0040 : ByteArray :=
  (block0000 ++ block0040 ++ block0002 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0041 : ByteArray :=
  (block0000 ++ block0040 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0042 : ByteArray :=
  (block0000 ++ block0041 ++ block0002 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0043 : ByteArray :=
  (block0000 ++ block0041 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0044 : ByteArray :=
  (block0000 ++ block0001 ++ block0042 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0045 : ByteArray :=
  (block0000 ++ block0001 ++ block0042 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0046 : ByteArray :=
  (block0000 ++ block0001 ++ block0043 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0047 : ByteArray :=
  (block0000 ++ block0001 ++ block0043 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0048 : ByteArray :=
  (block0000 ++ block0001 ++ block0044 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0049 : ByteArray :=
  (block0000 ++ block0001 ++ block0044 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0050 : ByteArray :=
  (block0000 ++ block0001 ++ block0045 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0051 : ByteArray :=
  (block0000 ++ block0001 ++ block0045 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0052 : ByteArray :=
  (block0000 ++ block0001 ++ block0046 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0053 : ByteArray :=
  (block0000 ++ block0001 ++ block0046 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0054 : ByteArray :=
  (block0000 ++ block0001 ++ block0047 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0055 : ByteArray :=
  (block0000 ++ block0001 ++ block0047 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0056 : ByteArray :=
  (block0000 ++ block0001 ++ block0048 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0057 : ByteArray :=
  (block0000 ++ block0001 ++ block0048 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0058 : ByteArray :=
  (block0000 ++ block0001 ++ block0049 ++ block0003 ++ block0004 ++ block0005).toByteArray
private def bytes0059 : ByteArray :=
  (block0000 ++ block0001 ++ block0049 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0060 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0050 ++ block0004 ++ block0005).toByteArray
private def bytes0061 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0050 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0062 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0051 ++ block0004 ++ block0005).toByteArray
private def bytes0063 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0051 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0064 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0052 ++ block0004 ++ block0005).toByteArray
private def bytes0065 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0052 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0066 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0053 ++ block0004 ++ block0005).toByteArray
private def bytes0067 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0053 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0068 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0054 ++ block0004 ++ block0005).toByteArray
private def bytes0069 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0054 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0070 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0055 ++ block0004 ++ block0005).toByteArray
private def bytes0071 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0055 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0072 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0056 ++ block0004 ++ block0005).toByteArray
private def bytes0073 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0056 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0074 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0057 ++ block0004 ++ block0005).toByteArray
private def bytes0075 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0057 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0076 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0058 ++ block0005).toByteArray
private def bytes0077 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0058 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0078 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0059 ++ block0005).toByteArray
private def bytes0079 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0059 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0080 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0060 ++ block0005).toByteArray
private def bytes0081 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0060 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0082 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0061 ++ block0005).toByteArray
private def bytes0083 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0061 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0084 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0062 ++ block0005).toByteArray
private def bytes0085 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0062 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0086 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0063 ++ block0005).toByteArray
private def bytes0087 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0063 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0088 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0064 ++ block0005).toByteArray
private def bytes0089 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0064 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0090 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0065 ++ block0005).toByteArray
private def bytes0091 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0065 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0092 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0066).toByteArray
private def bytes0093 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0066 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0094 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0067).toByteArray
private def bytes0095 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0067 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0096 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0068).toByteArray
private def bytes0097 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0068 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0098 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0069).toByteArray
private def bytes0099 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0069 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0100 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0070).toByteArray
private def bytes0101 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0070 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0102 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0071).toByteArray
private def bytes0103 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0071 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0104 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0072).toByteArray
private def bytes0105 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0072 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0106 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0073).toByteArray
private def bytes0107 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0073 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0108 : ByteArray :=
  (block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0109 : ByteArray :=
  (block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0110 : ByteArray :=
  (block0074 ++ block0007 ++ block0008 ++ block0009).toByteArray
private def bytes0111 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0074 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0112 : ByteArray :=
  (block0075 ++ block0007 ++ block0008 ++ block0009).toByteArray
private def bytes0113 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0075 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0114 : ByteArray :=
  (block0076 ++ block0007 ++ block0008 ++ block0009).toByteArray
private def bytes0115 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0076 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0116 : ByteArray :=
  (block0077 ++ block0007 ++ block0008 ++ block0009).toByteArray
private def bytes0117 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0077 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0118 : ByteArray :=
  (block0078 ++ block0007 ++ block0008 ++ block0009).toByteArray
private def bytes0119 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0078 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0120 : ByteArray :=
  (block0079 ++ block0007 ++ block0008 ++ block0009).toByteArray
private def bytes0121 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0079 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0122 : ByteArray :=
  (block0080 ++ block0007 ++ block0008 ++ block0009).toByteArray
private def bytes0123 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0080 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0124 : ByteArray :=
  (block0081 ++ block0007 ++ block0008 ++ block0009).toByteArray
private def bytes0125 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0081 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0126 : ByteArray :=
  (block0006 ++ block0082 ++ block0008 ++ block0009).toByteArray
private def bytes0127 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0082 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0128 : ByteArray :=
  (block0006 ++ block0083 ++ block0008 ++ block0009).toByteArray
private def bytes0129 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0083 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0130 : ByteArray :=
  (block0006 ++ block0084 ++ block0008 ++ block0009).toByteArray
private def bytes0131 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0084 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0132 : ByteArray :=
  (block0006 ++ block0085 ++ block0008 ++ block0009).toByteArray
private def bytes0133 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0085 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0134 : ByteArray :=
  (block0006 ++ block0086 ++ block0008 ++ block0009).toByteArray
private def bytes0135 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0086 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0136 : ByteArray :=
  (block0006 ++ block0087 ++ block0008 ++ block0009).toByteArray
private def bytes0137 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0087 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0138 : ByteArray :=
  (block0006 ++ block0088 ++ block0008 ++ block0009).toByteArray
private def bytes0139 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0088 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0140 : ByteArray :=
  (block0006 ++ block0089 ++ block0008 ++ block0009).toByteArray
private def bytes0141 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0089 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0142 : ByteArray :=
  (block0006 ++ block0007 ++ block0090 ++ block0009).toByteArray
private def bytes0143 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0090 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0144 : ByteArray :=
  (block0006 ++ block0007 ++ block0091 ++ block0009).toByteArray
private def bytes0145 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0091 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0146 : ByteArray :=
  (block0006 ++ block0007 ++ block0092 ++ block0009).toByteArray
private def bytes0147 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0092 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0148 : ByteArray :=
  (block0006 ++ block0007 ++ block0093 ++ block0009).toByteArray
private def bytes0149 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0093 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0150 : ByteArray :=
  (block0006 ++ block0007 ++ block0094 ++ block0009).toByteArray
private def bytes0151 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0094 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0152 : ByteArray :=
  (block0006 ++ block0007 ++ block0095 ++ block0009).toByteArray
private def bytes0153 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0095 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0154 : ByteArray :=
  (block0006 ++ block0007 ++ block0096 ++ block0009).toByteArray
private def bytes0155 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0096 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0156 : ByteArray :=
  (block0006 ++ block0007 ++ block0097 ++ block0009).toByteArray
private def bytes0157 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0097 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0158 : ByteArray :=
  (block0006 ++ block0007 ++ block0008 ++ block0098).toByteArray
private def bytes0159 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0098 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0160 : ByteArray :=
  (block0006 ++ block0007 ++ block0008 ++ block0099).toByteArray
private def bytes0161 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0099 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0162 : ByteArray :=
  (block0006 ++ block0007 ++ block0008 ++ block0100).toByteArray
private def bytes0163 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0100 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0164 : ByteArray :=
  (block0006 ++ block0007 ++ block0008 ++ block0101).toByteArray
private def bytes0165 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0101 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0166 : ByteArray :=
  (block0006 ++ block0007 ++ block0008 ++ block0102).toByteArray
private def bytes0167 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0102 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0168 : ByteArray :=
  (block0006 ++ block0007 ++ block0008 ++ block0103).toByteArray
private def bytes0169 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0103 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0170 : ByteArray :=
  (block0006 ++ block0007 ++ block0008 ++ block0104).toByteArray
private def bytes0171 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0104 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0172 : ByteArray :=
  (block0006 ++ block0007 ++ block0008 ++ block0105).toByteArray
private def bytes0173 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0105 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0174 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0024 ++
    block0024 ++ block0024 ++ block0024 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0175 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0025 ++
    block0025 ++ block0025 ++ block0025 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0176 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0024 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0177 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0106 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0178 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0107 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0179 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0108 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0180 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0109 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0181 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0110 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0182 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0111 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0183 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0025 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0184 : ByteArray :=
  (block0112 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0185 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0112 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0186 : ByteArray :=
  (block0113 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0187 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0113 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0188 : ByteArray :=
  (block0114 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0189 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0114 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0190 : ByteArray :=
  (block0115 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0191 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0115 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0192 : ByteArray :=
  (block0116 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0193 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0116 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0194 : ByteArray :=
  (block0117 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0195 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0117 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0196 : ByteArray :=
  (block0118 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0197 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0118 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0198 : ByteArray :=
  (block0119 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0199 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0119 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0200 : ByteArray :=
  (block0010 ++ block0120 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0201 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0120 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0202 : ByteArray :=
  (block0010 ++ block0121 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0203 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0121 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0204 : ByteArray :=
  (block0010 ++ block0122 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0205 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0122 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0206 : ByteArray :=
  (block0010 ++ block0123 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0207 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0123 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0208 : ByteArray :=
  (block0010 ++ block0124 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0209 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0124 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0210 : ByteArray :=
  (block0010 ++ block0125 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0211 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0125 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0212 : ByteArray :=
  (block0010 ++ block0126 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0213 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0126 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0214 : ByteArray :=
  (block0010 ++ block0127 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0215 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0127 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0216 : ByteArray :=
  (block0010 ++ block0011 ++ block0128 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0217 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0128 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0218 : ByteArray :=
  (block0010 ++ block0011 ++ block0129 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0219 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0129 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0220 : ByteArray :=
  (block0010 ++ block0011 ++ block0130 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0221 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0130 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0222 : ByteArray :=
  (block0010 ++ block0011 ++ block0131 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0223 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0131 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0224 : ByteArray :=
  (block0010 ++ block0011 ++ block0132 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0225 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0132 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0226 : ByteArray :=
  (block0010 ++ block0011 ++ block0133 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0227 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0133 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0228 : ByteArray :=
  (block0010 ++ block0011 ++ block0134 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0229 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0134 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0230 : ByteArray :=
  (block0010 ++ block0011 ++ block0135 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0231 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0135 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0232 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0136 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0233 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0136 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0234 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0137 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0235 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0137 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0236 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0138 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0237 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0138 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0238 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0139 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0239 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0139 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0240 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0140 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0241 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0140 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0242 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0141 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0243 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0141 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0244 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0142 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0245 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0142 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0246 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0143 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0247 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0143 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0248 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0144 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0249 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0144 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0250 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0145 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0251 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0145 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0252 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0146 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0253 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0146 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0254 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0147 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0255 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0147 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0256 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0148 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0257 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0148 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0258 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0149 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0259 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0149 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0260 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0150 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0261 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0150 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0262 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0151 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0263 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0151 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0264 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0152 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0265 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0152 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0266 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0153 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0267 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0153 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0268 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0154 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0269 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0154 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0270 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0155 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0271 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0155 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0272 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0156 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0273 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0156 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0274 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0157 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0275 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0157 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0276 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0158 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0277 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0158 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0278 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0159 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0279 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0159 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0280 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0160 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0281 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0160 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0282 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0161 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0283 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0161 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0284 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0162 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0285 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0162 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0286 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0163 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0287 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0163 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0288 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0164 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0289 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0164 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0290 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0165 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0291 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0165 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0292 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0166 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0293 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0166 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0294 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0167 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0295 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0167 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0296 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0168 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0297 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0168 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0298 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0169 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0299 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0169 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0300 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0170 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0301 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0170 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0302 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0171 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0303 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0171 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0304 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0172 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0305 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0172 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0306 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0173 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0307 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0173 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0308 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0174 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0309 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0174 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0310 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0175 ++ block0018 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0311 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0175 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0312 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0176 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0313 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0176 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0314 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0177 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0315 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0177 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0316 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0178 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0317 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0178 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0318 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0179 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0319 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0179 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0320 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0180 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0321 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0180 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0322 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0181 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0323 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0181 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0324 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0182 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0325 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0182 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0326 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0183 ++ block0019 ++ block0020 ++ block0021).toByteArray
private def bytes0327 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0183 ++ block0019 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0328 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0184 ++ block0020 ++ block0021).toByteArray
private def bytes0329 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0184 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0330 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0185 ++ block0020 ++ block0021).toByteArray
private def bytes0331 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0185 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0332 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0186 ++ block0020 ++ block0021).toByteArray
private def bytes0333 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0186 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0334 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0187 ++ block0020 ++ block0021).toByteArray
private def bytes0335 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0187 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0336 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0188 ++ block0020 ++ block0021).toByteArray
private def bytes0337 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0188 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0338 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0189 ++ block0020 ++ block0021).toByteArray
private def bytes0339 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0189 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0340 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0190 ++ block0020 ++ block0021).toByteArray
private def bytes0341 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0190 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0342 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0191 ++ block0020 ++ block0021).toByteArray
private def bytes0343 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0191 ++
    block0020 ++ block0021 ++ block0023).toByteArray
private def bytes0344 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0192 ++ block0021).toByteArray
private def bytes0345 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0192 ++ block0021 ++ block0023).toByteArray
private def bytes0346 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0193 ++ block0021).toByteArray
private def bytes0347 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0193 ++ block0021 ++ block0023).toByteArray
private def bytes0348 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0194 ++ block0021).toByteArray
private def bytes0349 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0194 ++ block0021 ++ block0023).toByteArray
private def bytes0350 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0195 ++ block0021).toByteArray
private def bytes0351 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0195 ++ block0021 ++ block0023).toByteArray
private def bytes0352 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0196 ++ block0021).toByteArray
private def bytes0353 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0196 ++ block0021 ++ block0023).toByteArray
private def bytes0354 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0197 ++ block0021).toByteArray
private def bytes0355 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0197 ++ block0021 ++ block0023).toByteArray
private def bytes0356 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0198 ++ block0021).toByteArray
private def bytes0357 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0198 ++ block0021 ++ block0023).toByteArray
private def bytes0358 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0199 ++ block0021).toByteArray
private def bytes0359 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0199 ++ block0021 ++ block0023).toByteArray
private def bytes0360 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0200).toByteArray
private def bytes0361 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0200 ++ block0023).toByteArray
private def bytes0362 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0201).toByteArray
private def bytes0363 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0201 ++ block0023).toByteArray
private def bytes0364 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0202).toByteArray
private def bytes0365 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0202 ++ block0023).toByteArray
private def bytes0366 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0203).toByteArray
private def bytes0367 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0203 ++ block0023).toByteArray
private def bytes0368 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0204).toByteArray
private def bytes0369 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0204 ++ block0023).toByteArray
private def bytes0370 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0205).toByteArray
private def bytes0371 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0205 ++ block0023).toByteArray
private def bytes0372 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0206).toByteArray
private def bytes0373 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0206 ++ block0023).toByteArray
private def bytes0374 : ByteArray :=
  (block0010 ++ block0011 ++ block0012 ++ block0013 ++ block0014 ++ block0015 ++ block0016 ++
    block0017 ++ block0018 ++ block0019 ++ block0020 ++ block0207).toByteArray
private def bytes0375 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0207 ++ block0023).toByteArray
private def bytes0376 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0024 ++ block0024 ++ block0024 ++
    block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++
    block0024 ++ block0024 ++ block0023).toByteArray
private def bytes0377 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0025 ++ block0025 ++ block0025 ++
    block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++
    block0025 ++ block0025 ++ block0023).toByteArray
private def bytes0378 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0024).toByteArray
private def bytes0379 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0106).toByteArray
private def bytes0380 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0107).toByteArray
private def bytes0381 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0108).toByteArray
private def bytes0382 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0109).toByteArray
private def bytes0383 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0110).toByteArray
private def bytes0384 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0111).toByteArray
private def bytes0385 : ByteArray :=
  (block0000 ++ block0001 ++ block0002 ++ block0003 ++ block0004 ++ block0005 ++ block0006 ++
    block0007 ++ block0008 ++ block0009 ++ block0022 ++ block0010 ++ block0011 ++ block0012 ++
    block0013 ++ block0014 ++ block0015 ++ block0016 ++ block0017 ++ block0018 ++ block0019 ++
    block0020 ++ block0021 ++ block0025).toByteArray
private def bytes0386 : ByteArray :=
  (block0208 ++ block0209 ++ block0210).toByteArray
private def bytes0387 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0388 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0389 : ByteArray :=
  (block0024 ++ block0024 ++ block0225).toByteArray
private def bytes0390 : ByteArray :=
  (block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++
    block0024 ++ block0024 ++ block0225).toByteArray
private def bytes0391 : ByteArray :=
  (block0025 ++ block0025 ++ block0226).toByteArray
private def bytes0392 : ByteArray :=
  (block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++
    block0025 ++ block0025 ++ block0226).toByteArray
private def bytes0393 : ByteArray :=
  (block0227 ++ block0209 ++ block0210).toByteArray
private def bytes0394 : ByteArray :=
  (block0227 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0395 : ByteArray :=
  (block0228 ++ block0209 ++ block0210).toByteArray
private def bytes0396 : ByteArray :=
  (block0228 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0397 : ByteArray :=
  (block0229 ++ block0209 ++ block0210).toByteArray
private def bytes0398 : ByteArray :=
  (block0229 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0399 : ByteArray :=
  (block0230 ++ block0209 ++ block0210).toByteArray
private def bytes0400 : ByteArray :=
  (block0230 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0401 : ByteArray :=
  (block0231 ++ block0209 ++ block0210).toByteArray
private def bytes0402 : ByteArray :=
  (block0231 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0403 : ByteArray :=
  (block0232 ++ block0209 ++ block0210).toByteArray
private def bytes0404 : ByteArray :=
  (block0232 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0405 : ByteArray :=
  (block0233 ++ block0209 ++ block0210).toByteArray
private def bytes0406 : ByteArray :=
  (block0233 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0407 : ByteArray :=
  (block0234 ++ block0209 ++ block0210).toByteArray
private def bytes0408 : ByteArray :=
  (block0234 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0409 : ByteArray :=
  (block0208 ++ block0235 ++ block0210).toByteArray
private def bytes0410 : ByteArray :=
  (block0208 ++ block0235 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0411 : ByteArray :=
  (block0208 ++ block0236 ++ block0210).toByteArray
private def bytes0412 : ByteArray :=
  (block0208 ++ block0236 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0413 : ByteArray :=
  (block0208 ++ block0237 ++ block0210).toByteArray
private def bytes0414 : ByteArray :=
  (block0208 ++ block0237 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0415 : ByteArray :=
  (block0208 ++ block0238 ++ block0210).toByteArray
private def bytes0416 : ByteArray :=
  (block0208 ++ block0238 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0417 : ByteArray :=
  (block0208 ++ block0239 ++ block0210).toByteArray
private def bytes0418 : ByteArray :=
  (block0208 ++ block0239 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0419 : ByteArray :=
  (block0208 ++ block0240 ++ block0210).toByteArray
private def bytes0420 : ByteArray :=
  (block0208 ++ block0240 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0421 : ByteArray :=
  (block0208 ++ block0241 ++ block0210).toByteArray
private def bytes0422 : ByteArray :=
  (block0208 ++ block0241 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0423 : ByteArray :=
  (block0208 ++ block0242 ++ block0210).toByteArray
private def bytes0424 : ByteArray :=
  (block0208 ++ block0242 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0425 : ByteArray :=
  (block0208 ++ block0209 ++ block0243).toByteArray
private def bytes0426 : ByteArray :=
  (block0208 ++ block0209 ++ block0244 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0427 : ByteArray :=
  (block0208 ++ block0209 ++ block0245).toByteArray
private def bytes0428 : ByteArray :=
  (block0208 ++ block0209 ++ block0246 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0429 : ByteArray :=
  (block0208 ++ block0209 ++ block0247).toByteArray
private def bytes0430 : ByteArray :=
  (block0208 ++ block0209 ++ block0248 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0431 : ByteArray :=
  (block0208 ++ block0209 ++ block0249).toByteArray
private def bytes0432 : ByteArray :=
  (block0208 ++ block0209 ++ block0250 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0433 : ByteArray :=
  (block0024 ++ block0024 ++ block0251 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0434 : ByteArray :=
  (block0025 ++ block0025 ++ block0252 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0435 : ByteArray :=
  (block0253 ++ block0212 ++ block0213 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0436 : ByteArray :=
  (block0208 ++ block0209 ++ block0254 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0437 : ByteArray :=
  (block0255 ++ block0212 ++ block0213 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0438 : ByteArray :=
  (block0208 ++ block0209 ++ block0256 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0439 : ByteArray :=
  (block0257 ++ block0212 ++ block0213 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0440 : ByteArray :=
  (block0208 ++ block0209 ++ block0258 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0441 : ByteArray :=
  (block0259 ++ block0212 ++ block0213 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0442 : ByteArray :=
  (block0208 ++ block0209 ++ block0260 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0443 : ByteArray :=
  (block0261 ++ block0212 ++ block0213 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0444 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0262 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0445 : ByteArray :=
  (block0263 ++ block0212 ++ block0213 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0446 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0264 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0447 : ByteArray :=
  (block0265 ++ block0212 ++ block0213 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0448 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0266 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0449 : ByteArray :=
  (block0267 ++ block0212 ++ block0213 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0450 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0268 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0451 : ByteArray :=
  (block0211 ++ block0269 ++ block0213 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0452 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0270 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0453 : ByteArray :=
  (block0211 ++ block0271 ++ block0213 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0454 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0272 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0455 : ByteArray :=
  (block0211 ++ block0273 ++ block0213 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0456 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0274 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0457 : ByteArray :=
  (block0211 ++ block0275 ++ block0213 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0458 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0276 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0459 : ByteArray :=
  (block0211 ++ block0277 ++ block0213 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0460 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0278 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0461 : ByteArray :=
  (block0211 ++ block0279 ++ block0213 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0462 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0280 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0463 : ByteArray :=
  (block0211 ++ block0281 ++ block0213 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0464 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0282 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0465 : ByteArray :=
  (block0211 ++ block0283 ++ block0213 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0466 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0284 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0467 : ByteArray :=
  (block0211 ++ block0212 ++ block0285 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0468 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0286 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0469 : ByteArray :=
  (block0211 ++ block0212 ++ block0287 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0470 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0288 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0471 : ByteArray :=
  (block0211 ++ block0212 ++ block0289 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0472 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0290 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0473 : ByteArray :=
  (block0211 ++ block0212 ++ block0291 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0474 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0292 ++ block0220 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0475 : ByteArray :=
  (block0211 ++ block0212 ++ block0293 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0476 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0294 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0477 : ByteArray :=
  (block0211 ++ block0212 ++ block0295 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0478 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0296 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0479 : ByteArray :=
  (block0211 ++ block0212 ++ block0297 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0480 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0298 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0481 : ByteArray :=
  (block0211 ++ block0212 ++ block0299 ++ block0214 ++ block0215 ++ block0216).toByteArray
private def bytes0482 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0300 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0483 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0301 ++ block0215 ++ block0216).toByteArray
private def bytes0484 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0302 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0485 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0303 ++ block0215 ++ block0216).toByteArray
private def bytes0486 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0304 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0487 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0305 ++ block0215 ++ block0216).toByteArray
private def bytes0488 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0306 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0489 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0307 ++ block0215 ++ block0216).toByteArray
private def bytes0490 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0308 ++ block0221 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0491 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0309 ++ block0215 ++ block0216).toByteArray
private def bytes0492 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0310 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0493 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0311 ++ block0215 ++ block0216).toByteArray
private def bytes0494 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0312 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0495 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0313 ++ block0215 ++ block0216).toByteArray
private def bytes0496 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0314 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0497 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0315 ++ block0215 ++ block0216).toByteArray
private def bytes0498 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0316 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0499 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0214 ++ block0317 ++ block0216).toByteArray
private def bytes0500 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0318 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0501 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0214 ++ block0319 ++ block0216).toByteArray
private def bytes0502 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0320 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0503 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0214 ++ block0321 ++ block0216).toByteArray
private def bytes0504 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0322 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0505 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0214 ++ block0323 ++ block0216).toByteArray
private def bytes0506 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0324 ++
    block0222 ++ block0223 ++ block0224).toByteArray
private def bytes0507 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0214 ++ block0325 ++ block0216).toByteArray
private def bytes0508 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0326 ++ block0223 ++ block0224).toByteArray
private def bytes0509 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0214 ++ block0327 ++ block0216).toByteArray
private def bytes0510 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0328 ++ block0223 ++ block0224).toByteArray
private def bytes0511 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0214 ++ block0329 ++ block0216).toByteArray
private def bytes0512 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0330 ++ block0223 ++ block0224).toByteArray
private def bytes0513 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0214 ++ block0331 ++ block0216).toByteArray
private def bytes0514 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0332 ++ block0223 ++ block0224).toByteArray
private def bytes0515 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0214 ++ block0215 ++ block0333).toByteArray
private def bytes0516 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0334 ++ block0223 ++ block0224).toByteArray
private def bytes0517 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0214 ++ block0215 ++ block0335).toByteArray
private def bytes0518 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0336 ++ block0223 ++ block0224).toByteArray
private def bytes0519 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0214 ++ block0215 ++ block0337).toByteArray
private def bytes0520 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0338 ++ block0223 ++ block0224).toByteArray
private def bytes0521 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0214 ++ block0215 ++ block0339).toByteArray
private def bytes0522 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0340 ++ block0223 ++ block0224).toByteArray
private def bytes0523 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0214 ++ block0215 ++ block0341).toByteArray
private def bytes0524 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0342 ++ block0224).toByteArray
private def bytes0525 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0214 ++ block0215 ++ block0343).toByteArray
private def bytes0526 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0344 ++ block0224).toByteArray
private def bytes0527 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0214 ++ block0215 ++ block0345).toByteArray
private def bytes0528 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0346 ++ block0224).toByteArray
private def bytes0529 : ByteArray :=
  (block0211 ++ block0212 ++ block0213 ++ block0214 ++ block0215 ++ block0347).toByteArray
private def bytes0530 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0348 ++ block0224).toByteArray
private def bytes0531 : ByteArray :=
  (block0208 ++ block0209 ++ block0349 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++
    block0024 ++ block0350 ++ block0224).toByteArray
private def bytes0532 : ByteArray :=
  (block0208 ++ block0209 ++ block0351 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++
    block0025 ++ block0352 ++ block0224).toByteArray
private def bytes0533 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0353 ++ block0225).toByteArray
private def bytes0534 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0354 ++ block0225).toByteArray
private def bytes0535 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0355 ++ block0225).toByteArray
private def bytes0536 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0356 ++ block0225).toByteArray
private def bytes0537 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0357 ++ block0225).toByteArray
private def bytes0538 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0353 ++ block0358).toByteArray
private def bytes0539 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0353 ++ block0359).toByteArray
private def bytes0540 : ByteArray :=
  (block0208 ++ block0209 ++ block0217 ++ block0218 ++ block0219 ++ block0220 ++ block0221 ++
    block0222 ++ block0357 ++ block0226).toByteArray
private def bytes0541 : ByteArray :=
  (block0360 ++ block0361 ++ block0362).toByteArray
private def bytes0542 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0543 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0544 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0545 : ByteArray :=
  (block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++
    block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++
    block0225).toByteArray
private def bytes0546 : ByteArray :=
  (block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++
    block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++
    block0226).toByteArray
private def bytes0547 : ByteArray :=
  (block0388 ++ block0361 ++ block0362).toByteArray
private def bytes0548 : ByteArray :=
  (block0388 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0549 : ByteArray :=
  (block0389 ++ block0361 ++ block0362).toByteArray
private def bytes0550 : ByteArray :=
  (block0389 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0551 : ByteArray :=
  (block0390 ++ block0361 ++ block0362).toByteArray
private def bytes0552 : ByteArray :=
  (block0390 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0553 : ByteArray :=
  (block0391 ++ block0361 ++ block0362).toByteArray
private def bytes0554 : ByteArray :=
  (block0391 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0555 : ByteArray :=
  (block0392 ++ block0361 ++ block0362).toByteArray
private def bytes0556 : ByteArray :=
  (block0392 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0557 : ByteArray :=
  (block0393 ++ block0361 ++ block0362).toByteArray
private def bytes0558 : ByteArray :=
  (block0393 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0559 : ByteArray :=
  (block0394 ++ block0361 ++ block0362).toByteArray
private def bytes0560 : ByteArray :=
  (block0394 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0561 : ByteArray :=
  (block0395 ++ block0361 ++ block0362).toByteArray
private def bytes0562 : ByteArray :=
  (block0395 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0563 : ByteArray :=
  (block0360 ++ block0396 ++ block0362).toByteArray
private def bytes0564 : ByteArray :=
  (block0360 ++ block0396 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0565 : ByteArray :=
  (block0360 ++ block0397 ++ block0362).toByteArray
private def bytes0566 : ByteArray :=
  (block0360 ++ block0397 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0567 : ByteArray :=
  (block0360 ++ block0398 ++ block0362).toByteArray
private def bytes0568 : ByteArray :=
  (block0360 ++ block0398 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0569 : ByteArray :=
  (block0360 ++ block0399 ++ block0362).toByteArray
private def bytes0570 : ByteArray :=
  (block0360 ++ block0399 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0571 : ByteArray :=
  (block0360 ++ block0400 ++ block0362).toByteArray
private def bytes0572 : ByteArray :=
  (block0360 ++ block0400 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0573 : ByteArray :=
  (block0360 ++ block0401 ++ block0362).toByteArray
private def bytes0574 : ByteArray :=
  (block0360 ++ block0401 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0575 : ByteArray :=
  (block0360 ++ block0402 ++ block0362).toByteArray
private def bytes0576 : ByteArray :=
  (block0360 ++ block0402 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0577 : ByteArray :=
  (block0360 ++ block0403 ++ block0362).toByteArray
private def bytes0578 : ByteArray :=
  (block0360 ++ block0403 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0579 : ByteArray :=
  (block0360 ++ block0361 ++ block0404).toByteArray
private def bytes0580 : ByteArray :=
  (block0360 ++ block0361 ++ block0405 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0581 : ByteArray :=
  (block0360 ++ block0361 ++ block0406).toByteArray
private def bytes0582 : ByteArray :=
  (block0360 ++ block0361 ++ block0407 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0583 : ByteArray :=
  (block0360 ++ block0361 ++ block0408).toByteArray
private def bytes0584 : ByteArray :=
  (block0360 ++ block0361 ++ block0409 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0585 : ByteArray :=
  (block0360 ++ block0361 ++ block0410).toByteArray
private def bytes0586 : ByteArray :=
  (block0360 ++ block0361 ++ block0411 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0587 : ByteArray :=
  (block0024 ++ block0024 ++ block0412 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0588 : ByteArray :=
  (block0025 ++ block0025 ++ block0413 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0589 : ByteArray :=
  (block0414 ++ block0364 ++ block0365 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0590 : ByteArray :=
  (block0360 ++ block0361 ++ block0415 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0591 : ByteArray :=
  (block0416 ++ block0364 ++ block0365 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0592 : ByteArray :=
  (block0360 ++ block0361 ++ block0417 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0593 : ByteArray :=
  (block0418 ++ block0364 ++ block0365 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0594 : ByteArray :=
  (block0360 ++ block0361 ++ block0419 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0595 : ByteArray :=
  (block0420 ++ block0364 ++ block0365 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0596 : ByteArray :=
  (block0360 ++ block0361 ++ block0421 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0597 : ByteArray :=
  (block0422 ++ block0364 ++ block0365 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0598 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0423 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0599 : ByteArray :=
  (block0424 ++ block0364 ++ block0365 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0600 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0425 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0601 : ByteArray :=
  (block0426 ++ block0364 ++ block0365 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0602 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0427 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0603 : ByteArray :=
  (block0428 ++ block0364 ++ block0365 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0604 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0429 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0605 : ByteArray :=
  (block0363 ++ block0430 ++ block0365 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0606 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0431 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0607 : ByteArray :=
  (block0363 ++ block0432 ++ block0365 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0608 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0433 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0609 : ByteArray :=
  (block0363 ++ block0434 ++ block0365 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0610 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0435 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0611 : ByteArray :=
  (block0363 ++ block0436 ++ block0365 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0612 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0437 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0613 : ByteArray :=
  (block0363 ++ block0438 ++ block0365 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0614 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0439 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0615 : ByteArray :=
  (block0363 ++ block0440 ++ block0365 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0616 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0441 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0617 : ByteArray :=
  (block0363 ++ block0442 ++ block0365 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0618 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0443 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0619 : ByteArray :=
  (block0363 ++ block0444 ++ block0365 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0620 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0445 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0621 : ByteArray :=
  (block0363 ++ block0364 ++ block0446 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0622 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0447 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0623 : ByteArray :=
  (block0363 ++ block0364 ++ block0448 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0624 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0449 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0625 : ByteArray :=
  (block0363 ++ block0364 ++ block0450 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0626 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0451 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0627 : ByteArray :=
  (block0363 ++ block0364 ++ block0452 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0628 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0453 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0629 : ByteArray :=
  (block0363 ++ block0364 ++ block0454 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0630 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0455 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0631 : ByteArray :=
  (block0363 ++ block0364 ++ block0456 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0632 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0457 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0633 : ByteArray :=
  (block0363 ++ block0364 ++ block0458 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0634 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0459 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0635 : ByteArray :=
  (block0363 ++ block0364 ++ block0460 ++ block0366 ++ block0367 ++ block0368).toByteArray
private def bytes0636 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0461 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0637 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0462 ++ block0367 ++ block0368).toByteArray
private def bytes0638 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0463 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0639 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0464 ++ block0367 ++ block0368).toByteArray
private def bytes0640 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0465 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0641 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0466 ++ block0367 ++ block0368).toByteArray
private def bytes0642 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0467 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0643 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0468 ++ block0367 ++ block0368).toByteArray
private def bytes0644 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0469 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0645 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0470 ++ block0367 ++ block0368).toByteArray
private def bytes0646 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0471 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0647 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0472 ++ block0367 ++ block0368).toByteArray
private def bytes0648 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0473 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0649 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0474 ++ block0367 ++ block0368).toByteArray
private def bytes0650 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0475 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0651 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0476 ++ block0367 ++ block0368).toByteArray
private def bytes0652 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0477 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0653 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0366 ++ block0478 ++ block0368).toByteArray
private def bytes0654 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0479 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0655 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0366 ++ block0480 ++ block0368).toByteArray
private def bytes0656 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0481 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0657 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0366 ++ block0482 ++ block0368).toByteArray
private def bytes0658 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0483 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0659 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0366 ++ block0484 ++ block0368).toByteArray
private def bytes0660 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0485 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0661 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0366 ++ block0486 ++ block0368).toByteArray
private def bytes0662 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0487 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0663 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0366 ++ block0488 ++ block0368).toByteArray
private def bytes0664 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0489 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0665 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0366 ++ block0490 ++ block0368).toByteArray
private def bytes0666 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0491 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0667 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0366 ++ block0492 ++ block0368).toByteArray
private def bytes0668 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0493 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0669 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0366 ++ block0367 ++ block0494).toByteArray
private def bytes0670 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0495 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0671 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0366 ++ block0367 ++ block0496).toByteArray
private def bytes0672 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0497 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0673 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0366 ++ block0367 ++ block0498).toByteArray
private def bytes0674 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0499 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0675 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0366 ++ block0367 ++ block0500).toByteArray
private def bytes0676 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0501 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0677 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0366 ++ block0367 ++ block0502).toByteArray
private def bytes0678 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0503 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0679 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0366 ++ block0367 ++ block0504).toByteArray
private def bytes0680 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0505 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0681 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0366 ++ block0367 ++ block0506).toByteArray
private def bytes0682 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0507 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0683 : ByteArray :=
  (block0363 ++ block0364 ++ block0365 ++ block0366 ++ block0367 ++ block0508).toByteArray
private def bytes0684 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0509 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0685 : ByteArray :=
  (block0360 ++ block0361 ++ block0510 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++
    block0024 ++ block0511 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0686 : ByteArray :=
  (block0360 ++ block0361 ++ block0512 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++
    block0025 ++ block0513 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0687 : ByteArray :=
  (block0514 ++ block0370 ++ block0371 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0688 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0515 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0689 : ByteArray :=
  (block0516 ++ block0370 ++ block0371 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0690 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0517 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0691 : ByteArray :=
  (block0518 ++ block0370 ++ block0371 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0692 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0519 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0693 : ByteArray :=
  (block0520 ++ block0370 ++ block0371 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0694 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0521 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0695 : ByteArray :=
  (block0522 ++ block0370 ++ block0371 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0696 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0523 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0697 : ByteArray :=
  (block0524 ++ block0370 ++ block0371 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0698 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0525 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0699 : ByteArray :=
  (block0526 ++ block0370 ++ block0371 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0700 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0527 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0701 : ByteArray :=
  (block0528 ++ block0370 ++ block0371 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0702 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0529 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0703 : ByteArray :=
  (block0369 ++ block0530 ++ block0371 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0704 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0531 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0705 : ByteArray :=
  (block0369 ++ block0532 ++ block0371 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0706 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0533 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0707 : ByteArray :=
  (block0369 ++ block0534 ++ block0371 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0708 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0535 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0709 : ByteArray :=
  (block0369 ++ block0536 ++ block0371 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0710 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0537 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0711 : ByteArray :=
  (block0369 ++ block0538 ++ block0371 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0712 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0539 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0713 : ByteArray :=
  (block0369 ++ block0540 ++ block0371 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0714 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0541 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0715 : ByteArray :=
  (block0369 ++ block0542 ++ block0371 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0716 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0543 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0717 : ByteArray :=
  (block0369 ++ block0544 ++ block0371 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0718 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0545 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0719 : ByteArray :=
  (block0369 ++ block0370 ++ block0546 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0720 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0547 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0721 : ByteArray :=
  (block0369 ++ block0370 ++ block0548 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0722 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0549 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0723 : ByteArray :=
  (block0369 ++ block0370 ++ block0550 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0724 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0551 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0725 : ByteArray :=
  (block0369 ++ block0370 ++ block0552 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0726 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0553 ++ block0384 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0727 : ByteArray :=
  (block0369 ++ block0370 ++ block0554 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0728 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0555 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0729 : ByteArray :=
  (block0369 ++ block0370 ++ block0556 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0730 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0557 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0731 : ByteArray :=
  (block0369 ++ block0370 ++ block0558 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0732 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0559 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0733 : ByteArray :=
  (block0369 ++ block0370 ++ block0560 ++ block0372 ++ block0373 ++ block0374).toByteArray
private def bytes0734 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0561 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0735 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0562 ++ block0373 ++ block0374).toByteArray
private def bytes0736 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0563 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0737 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0564 ++ block0373 ++ block0374).toByteArray
private def bytes0738 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0565 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0739 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0566 ++ block0373 ++ block0374).toByteArray
private def bytes0740 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0567 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0741 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0568 ++ block0373 ++ block0374).toByteArray
private def bytes0742 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0569 ++ block0385 ++ block0386 ++
    block0387).toByteArray
private def bytes0743 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0570 ++ block0373 ++ block0374).toByteArray
private def bytes0744 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0571 ++ block0386 ++
    block0387).toByteArray
private def bytes0745 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0572 ++ block0373 ++ block0374).toByteArray
private def bytes0746 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0573 ++ block0386 ++
    block0387).toByteArray
private def bytes0747 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0574 ++ block0373 ++ block0374).toByteArray
private def bytes0748 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0575 ++ block0386 ++
    block0387).toByteArray
private def bytes0749 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0576 ++ block0373 ++ block0374).toByteArray
private def bytes0750 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0577 ++ block0386 ++
    block0387).toByteArray
private def bytes0751 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0372 ++ block0578 ++ block0374).toByteArray
private def bytes0752 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0579 ++ block0386 ++
    block0387).toByteArray
private def bytes0753 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0372 ++ block0580 ++ block0374).toByteArray
private def bytes0754 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0581 ++ block0386 ++
    block0387).toByteArray
private def bytes0755 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0372 ++ block0582 ++ block0374).toByteArray
private def bytes0756 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0583 ++ block0386 ++
    block0387).toByteArray
private def bytes0757 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0372 ++ block0584 ++ block0374).toByteArray
private def bytes0758 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0585 ++ block0386 ++
    block0387).toByteArray
private def bytes0759 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0372 ++ block0586 ++ block0374).toByteArray
private def bytes0760 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0587 ++
    block0387).toByteArray
private def bytes0761 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0372 ++ block0588 ++ block0374).toByteArray
private def bytes0762 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0589 ++
    block0387).toByteArray
private def bytes0763 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0372 ++ block0590 ++ block0374).toByteArray
private def bytes0764 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0591 ++
    block0387).toByteArray
private def bytes0765 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0372 ++ block0592 ++ block0374).toByteArray
private def bytes0766 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0593 ++
    block0387).toByteArray
private def bytes0767 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0372 ++ block0373 ++ block0594).toByteArray
private def bytes0768 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0595 ++
    block0387).toByteArray
private def bytes0769 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0372 ++ block0373 ++ block0596).toByteArray
private def bytes0770 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0597 ++
    block0387).toByteArray
private def bytes0771 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0372 ++ block0373 ++ block0598).toByteArray
private def bytes0772 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0599 ++
    block0387).toByteArray
private def bytes0773 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0372 ++ block0373 ++ block0600).toByteArray
private def bytes0774 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0601 ++
    block0387).toByteArray
private def bytes0775 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0372 ++ block0373 ++ block0602).toByteArray
private def bytes0776 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0603).toByteArray
private def bytes0777 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0372 ++ block0373 ++ block0604).toByteArray
private def bytes0778 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0605).toByteArray
private def bytes0779 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0372 ++ block0373 ++ block0606).toByteArray
private def bytes0780 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0607).toByteArray
private def bytes0781 : ByteArray :=
  (block0369 ++ block0370 ++ block0371 ++ block0372 ++ block0373 ++ block0608).toByteArray
private def bytes0782 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0381 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++ block0386 ++
    block0609).toByteArray
private def bytes0783 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0610 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++
    block0225).toByteArray
private def bytes0784 : ByteArray :=
  (block0360 ++ block0361 ++ block0375 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++
    block0380 ++ block0611 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++
    block0226).toByteArray
private def bytes0785 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0786 : ByteArray :=
  (block0618 ++ block0619 ++ block0620 ++ block0621).toByteArray
private def bytes0787 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes0788 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0789 : ByteArray :=
  (block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++
    block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++
    block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++
    block0024 ++ block0024).toByteArray
private def bytes0790 : ByteArray :=
  (block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++
    block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++
    block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++
    block0025 ++ block0025).toByteArray
private def bytes0791 : ByteArray :=
  (block0632 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0792 : ByteArray :=
  (block0632 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0793 : ByteArray :=
  (block0633 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0794 : ByteArray :=
  (block0633 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0795 : ByteArray :=
  (block0634 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0796 : ByteArray :=
  (block0634 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0797 : ByteArray :=
  (block0635 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0798 : ByteArray :=
  (block0635 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0799 : ByteArray :=
  (block0636 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0800 : ByteArray :=
  (block0636 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0801 : ByteArray :=
  (block0637 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0802 : ByteArray :=
  (block0637 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0803 : ByteArray :=
  (block0638 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0804 : ByteArray :=
  (block0638 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0805 : ByteArray :=
  (block0639 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0806 : ByteArray :=
  (block0639 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0807 : ByteArray :=
  (block0612 ++ block0640 ++ block0614 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0808 : ByteArray :=
  (block0612 ++ block0640 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0809 : ByteArray :=
  (block0612 ++ block0641 ++ block0614 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0810 : ByteArray :=
  (block0612 ++ block0641 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0811 : ByteArray :=
  (block0612 ++ block0642 ++ block0614 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0812 : ByteArray :=
  (block0612 ++ block0642 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0813 : ByteArray :=
  (block0612 ++ block0643 ++ block0614 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0814 : ByteArray :=
  (block0612 ++ block0643 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0815 : ByteArray :=
  (block0612 ++ block0644 ++ block0614 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0816 : ByteArray :=
  (block0612 ++ block0644 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0817 : ByteArray :=
  (block0612 ++ block0645 ++ block0614 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0818 : ByteArray :=
  (block0612 ++ block0645 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0819 : ByteArray :=
  (block0612 ++ block0646 ++ block0614 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0820 : ByteArray :=
  (block0612 ++ block0646 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0821 : ByteArray :=
  (block0612 ++ block0647 ++ block0614 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0822 : ByteArray :=
  (block0612 ++ block0647 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0823 : ByteArray :=
  (block0612 ++ block0613 ++ block0648 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0824 : ByteArray :=
  (block0612 ++ block0613 ++ block0648 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0825 : ByteArray :=
  (block0612 ++ block0613 ++ block0649 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0826 : ByteArray :=
  (block0612 ++ block0613 ++ block0649 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0827 : ByteArray :=
  (block0612 ++ block0613 ++ block0650 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0828 : ByteArray :=
  (block0612 ++ block0613 ++ block0650 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0829 : ByteArray :=
  (block0612 ++ block0613 ++ block0651 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0830 : ByteArray :=
  (block0612 ++ block0613 ++ block0651 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0831 : ByteArray :=
  (block0612 ++ block0613 ++ block0652 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0832 : ByteArray :=
  (block0612 ++ block0613 ++ block0652 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0833 : ByteArray :=
  (block0612 ++ block0613 ++ block0653 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0834 : ByteArray :=
  (block0612 ++ block0613 ++ block0653 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0835 : ByteArray :=
  (block0612 ++ block0613 ++ block0654 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0836 : ByteArray :=
  (block0612 ++ block0613 ++ block0654 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0837 : ByteArray :=
  (block0612 ++ block0613 ++ block0655 ++ block0615 ++ block0616 ++ block0617).toByteArray
private def bytes0838 : ByteArray :=
  (block0612 ++ block0613 ++ block0655 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0839 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0656 ++ block0616 ++ block0617).toByteArray
private def bytes0840 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0656 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0841 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0657 ++ block0616 ++ block0617).toByteArray
private def bytes0842 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0657 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0843 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0658 ++ block0616 ++ block0617).toByteArray
private def bytes0844 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0658 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0845 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0659 ++ block0616 ++ block0617).toByteArray
private def bytes0846 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0659 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0847 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0660 ++ block0616 ++ block0617).toByteArray
private def bytes0848 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0660 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0849 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0661 ++ block0616 ++ block0617).toByteArray
private def bytes0850 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0661 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0851 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0662 ++ block0616 ++ block0617).toByteArray
private def bytes0852 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0662 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0853 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0663 ++ block0616 ++ block0617).toByteArray
private def bytes0854 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0663 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0855 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0664 ++ block0617).toByteArray
private def bytes0856 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0664 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0857 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0665 ++ block0617).toByteArray
private def bytes0858 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0665 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0859 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0666 ++ block0617).toByteArray
private def bytes0860 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0666 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0861 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0667 ++ block0617).toByteArray
private def bytes0862 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0667 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0863 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0668 ++ block0617).toByteArray
private def bytes0864 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0668 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0865 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0669 ++ block0617).toByteArray
private def bytes0866 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0669 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0867 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0670 ++ block0617).toByteArray
private def bytes0868 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0670 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0869 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0671 ++ block0617).toByteArray
private def bytes0870 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0671 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0871 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0672).toByteArray
private def bytes0872 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0672 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0873 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0673).toByteArray
private def bytes0874 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0673 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0875 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0674).toByteArray
private def bytes0876 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0674 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0877 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0675).toByteArray
private def bytes0878 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0675 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0879 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0676).toByteArray
private def bytes0880 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0676 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0881 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0677).toByteArray
private def bytes0882 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0677 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0883 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0678).toByteArray
private def bytes0884 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0678 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0885 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0679).toByteArray
private def bytes0886 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0679 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0887 : ByteArray :=
  (block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0888 : ByteArray :=
  (block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0889 : ByteArray :=
  (block0680 ++ block0619 ++ block0620 ++ block0621).toByteArray
private def bytes0890 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0680 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0891 : ByteArray :=
  (block0681 ++ block0619 ++ block0620 ++ block0621).toByteArray
private def bytes0892 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0681 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0893 : ByteArray :=
  (block0682 ++ block0619 ++ block0620 ++ block0621).toByteArray
private def bytes0894 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0682 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0895 : ByteArray :=
  (block0683 ++ block0619 ++ block0620 ++ block0621).toByteArray
private def bytes0896 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0683 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0897 : ByteArray :=
  (block0684 ++ block0619 ++ block0620 ++ block0621).toByteArray
private def bytes0898 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0684 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0899 : ByteArray :=
  (block0685 ++ block0619 ++ block0620 ++ block0621).toByteArray
private def bytes0900 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0685 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0901 : ByteArray :=
  (block0686 ++ block0619 ++ block0620 ++ block0621).toByteArray
private def bytes0902 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0686 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0903 : ByteArray :=
  (block0687 ++ block0619 ++ block0620 ++ block0621).toByteArray
private def bytes0904 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0687 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0905 : ByteArray :=
  (block0618 ++ block0688 ++ block0620 ++ block0621).toByteArray
private def bytes0906 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0688 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0907 : ByteArray :=
  (block0618 ++ block0689 ++ block0620 ++ block0621).toByteArray
private def bytes0908 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0689 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0909 : ByteArray :=
  (block0618 ++ block0690 ++ block0620 ++ block0621).toByteArray
private def bytes0910 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0690 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0911 : ByteArray :=
  (block0618 ++ block0691 ++ block0620 ++ block0621).toByteArray
private def bytes0912 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0691 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0913 : ByteArray :=
  (block0618 ++ block0692 ++ block0620 ++ block0621).toByteArray
private def bytes0914 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0692 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0915 : ByteArray :=
  (block0618 ++ block0693 ++ block0620 ++ block0621).toByteArray
private def bytes0916 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0693 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0917 : ByteArray :=
  (block0618 ++ block0694 ++ block0620 ++ block0621).toByteArray
private def bytes0918 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0694 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0919 : ByteArray :=
  (block0618 ++ block0695 ++ block0620 ++ block0621).toByteArray
private def bytes0920 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0695 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0921 : ByteArray :=
  (block0618 ++ block0619 ++ block0696 ++ block0621).toByteArray
private def bytes0922 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0696 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0923 : ByteArray :=
  (block0618 ++ block0619 ++ block0697 ++ block0621).toByteArray
private def bytes0924 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0697 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0925 : ByteArray :=
  (block0618 ++ block0619 ++ block0698 ++ block0621).toByteArray
private def bytes0926 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0698 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0927 : ByteArray :=
  (block0618 ++ block0619 ++ block0699 ++ block0621).toByteArray
private def bytes0928 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0699 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0929 : ByteArray :=
  (block0618 ++ block0619 ++ block0700 ++ block0621).toByteArray
private def bytes0930 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0700 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0931 : ByteArray :=
  (block0618 ++ block0619 ++ block0701 ++ block0621).toByteArray
private def bytes0932 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0701 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0933 : ByteArray :=
  (block0618 ++ block0619 ++ block0702 ++ block0621).toByteArray
private def bytes0934 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0702 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0935 : ByteArray :=
  (block0618 ++ block0619 ++ block0703 ++ block0621).toByteArray
private def bytes0936 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0703 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0937 : ByteArray :=
  (block0618 ++ block0619 ++ block0620 ++ block0704).toByteArray
private def bytes0938 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0704 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0939 : ByteArray :=
  (block0618 ++ block0619 ++ block0620 ++ block0705).toByteArray
private def bytes0940 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0705 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0941 : ByteArray :=
  (block0618 ++ block0619 ++ block0620 ++ block0706).toByteArray
private def bytes0942 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0706 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0943 : ByteArray :=
  (block0618 ++ block0619 ++ block0620 ++ block0707).toByteArray
private def bytes0944 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0707 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0945 : ByteArray :=
  (block0618 ++ block0619 ++ block0620 ++ block0708).toByteArray
private def bytes0946 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0708 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0947 : ByteArray :=
  (block0618 ++ block0619 ++ block0620 ++ block0709).toByteArray
private def bytes0948 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0709 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0949 : ByteArray :=
  (block0618 ++ block0619 ++ block0620 ++ block0710).toByteArray
private def bytes0950 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0710 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0951 : ByteArray :=
  (block0618 ++ block0619 ++ block0620 ++ block0711).toByteArray
private def bytes0952 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0711 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0953 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0024 ++
    block0024 ++ block0024 ++ block0024 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0954 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0025 ++
    block0025 ++ block0025 ++ block0025 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0955 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0024 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0956 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0106 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0957 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0107 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0958 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0108 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0959 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0109 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0960 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0110 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0961 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0111 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0962 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0025 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0963 : ByteArray :=
  (block0712 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes0964 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0712 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0965 : ByteArray :=
  (block0713 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes0966 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0713 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0967 : ByteArray :=
  (block0714 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes0968 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0714 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0969 : ByteArray :=
  (block0715 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes0970 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0715 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0971 : ByteArray :=
  (block0716 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes0972 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0716 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0973 : ByteArray :=
  (block0717 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes0974 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0717 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0975 : ByteArray :=
  (block0718 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes0976 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0718 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0977 : ByteArray :=
  (block0719 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes0978 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0719 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0979 : ByteArray :=
  (block0622 ++ block0720 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes0980 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0720 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0981 : ByteArray :=
  (block0622 ++ block0721 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes0982 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0721 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0983 : ByteArray :=
  (block0622 ++ block0722 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes0984 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0722 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0985 : ByteArray :=
  (block0622 ++ block0723 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes0986 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0723 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0987 : ByteArray :=
  (block0622 ++ block0724 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes0988 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0724 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0989 : ByteArray :=
  (block0622 ++ block0725 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes0990 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0725 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0991 : ByteArray :=
  (block0622 ++ block0726 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes0992 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0726 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0993 : ByteArray :=
  (block0622 ++ block0727 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes0994 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0727 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0995 : ByteArray :=
  (block0622 ++ block0623 ++ block0728 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes0996 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0728 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0997 : ByteArray :=
  (block0622 ++ block0623 ++ block0729 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes0998 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0729 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes0999 : ByteArray :=
  (block0622 ++ block0623 ++ block0730 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1000 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0730 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1001 : ByteArray :=
  (block0622 ++ block0623 ++ block0731 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1002 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0731 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1003 : ByteArray :=
  (block0622 ++ block0623 ++ block0732 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1004 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0732 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1005 : ByteArray :=
  (block0622 ++ block0623 ++ block0733 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1006 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0733 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1007 : ByteArray :=
  (block0622 ++ block0623 ++ block0734 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1008 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0734 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1009 : ByteArray :=
  (block0622 ++ block0623 ++ block0735 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1010 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0735 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1011 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0736 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1012 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0736 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1013 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0737 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1014 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0737 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1015 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0738 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1016 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0738 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1017 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0739 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1018 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0739 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1019 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0740 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1020 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0740 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1021 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0741 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1022 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0741 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1023 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0742 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1024 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0742 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1025 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0743 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1026 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0743 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1027 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0744 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1028 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0744 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1029 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0745 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1030 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0745 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1031 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0746 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1032 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0746 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1033 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0747 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1034 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0747 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1035 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0748 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1036 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0748 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1037 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0749 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1038 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0749 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1039 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0750 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1040 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0750 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1041 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0751 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1042 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0751 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1043 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0752 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1044 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0752 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1045 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0753 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1046 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0753 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1047 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0754 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1048 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0754 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1049 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0755 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1050 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0755 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1051 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0756 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1052 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0756 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1053 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0757 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1054 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0757 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1055 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0758 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1056 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0758 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1057 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0759 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1058 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0759 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1059 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0760 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1060 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0760 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1061 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0761 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1062 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0761 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1063 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0762 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1064 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0762 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1065 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0763 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1066 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0763 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1067 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0764 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1068 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0764 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1069 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0765 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1070 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0765 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1071 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0766 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1072 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0766 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1073 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0767 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1074 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0767 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1075 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0278 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1076 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0278 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1077 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0280 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1078 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0280 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1079 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0282 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1080 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0282 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1081 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0284 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1082 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0284 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1083 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0286 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1084 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0286 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1085 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0288 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1086 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0288 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1087 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0290 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1088 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0290 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1089 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0292 ++ block0629 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1090 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0292 ++ block0629 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1091 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0768 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1092 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0768 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1093 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0769 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1094 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0769 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1095 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0770 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1096 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0770 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1097 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0771 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1098 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0771 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1099 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0772 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1100 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0772 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1101 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0773 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1102 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0773 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1103 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0774 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1104 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0774 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1105 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0775 ++ block0221 ++ block0222 ++ block0630).toByteArray
private def bytes1106 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0775 ++ block0221 ++
    block0222 ++ block0630).toByteArray
private def bytes1107 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0310 ++ block0222 ++ block0630).toByteArray
private def bytes1108 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0310 ++
    block0222 ++ block0630).toByteArray
private def bytes1109 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0312 ++ block0222 ++ block0630).toByteArray
private def bytes1110 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0312 ++
    block0222 ++ block0630).toByteArray
private def bytes1111 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0314 ++ block0222 ++ block0630).toByteArray
private def bytes1112 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0314 ++
    block0222 ++ block0630).toByteArray
private def bytes1113 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0316 ++ block0222 ++ block0630).toByteArray
private def bytes1114 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0316 ++
    block0222 ++ block0630).toByteArray
private def bytes1115 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0318 ++ block0222 ++ block0630).toByteArray
private def bytes1116 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0318 ++
    block0222 ++ block0630).toByteArray
private def bytes1117 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0320 ++ block0222 ++ block0630).toByteArray
private def bytes1118 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0320 ++
    block0222 ++ block0630).toByteArray
private def bytes1119 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0322 ++ block0222 ++ block0630).toByteArray
private def bytes1120 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0322 ++
    block0222 ++ block0630).toByteArray
private def bytes1121 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0324 ++ block0222 ++ block0630).toByteArray
private def bytes1122 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0324 ++
    block0222 ++ block0630).toByteArray
private def bytes1123 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0326 ++ block0630).toByteArray
private def bytes1124 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0326 ++ block0630).toByteArray
private def bytes1125 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0328 ++ block0630).toByteArray
private def bytes1126 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0328 ++ block0630).toByteArray
private def bytes1127 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0330 ++ block0630).toByteArray
private def bytes1128 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0330 ++ block0630).toByteArray
private def bytes1129 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0332 ++ block0630).toByteArray
private def bytes1130 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0332 ++ block0630).toByteArray
private def bytes1131 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0334 ++ block0630).toByteArray
private def bytes1132 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0334 ++ block0630).toByteArray
private def bytes1133 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0336 ++ block0630).toByteArray
private def bytes1134 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0336 ++ block0630).toByteArray
private def bytes1135 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0338 ++ block0630).toByteArray
private def bytes1136 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0338 ++ block0630).toByteArray
private def bytes1137 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0340 ++ block0630).toByteArray
private def bytes1138 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0340 ++ block0630).toByteArray
private def bytes1139 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0776).toByteArray
private def bytes1140 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0776).toByteArray
private def bytes1141 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0777).toByteArray
private def bytes1142 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0777).toByteArray
private def bytes1143 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0778).toByteArray
private def bytes1144 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0778).toByteArray
private def bytes1145 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0779).toByteArray
private def bytes1146 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0779).toByteArray
private def bytes1147 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0780).toByteArray
private def bytes1148 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0780).toByteArray
private def bytes1149 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0781).toByteArray
private def bytes1150 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0781).toByteArray
private def bytes1151 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0782).toByteArray
private def bytes1152 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0782).toByteArray
private def bytes1153 : ByteArray :=
  (block0622 ++ block0623 ++ block0624 ++ block0625 ++ block0626 ++ block0627 ++ block0628 ++
    block0219 ++ block0629 ++ block0221 ++ block0222 ++ block0783).toByteArray
private def bytes1154 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0622 ++ block0623 ++ block0624 ++
    block0625 ++ block0626 ++ block0627 ++ block0628 ++ block0219 ++ block0629 ++ block0221 ++
    block0222 ++ block0783).toByteArray
private def bytes1155 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0024 ++ block0024 ++ block0024 ++
    block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++
    block0024 ++ block0024).toByteArray
private def bytes1156 : ByteArray :=
  (block0612 ++ block0613 ++ block0614 ++ block0615 ++ block0616 ++ block0617 ++ block0618 ++
    block0619 ++ block0620 ++ block0621 ++ block0631 ++ block0025 ++ block0025 ++ block0025 ++
    block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++
    block0025 ++ block0025).toByteArray
private def bytes1157 : ByteArray :=
  (block0784 ++ block0785 ++ block0786).toByteArray
private def bytes1158 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1159 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1160 : ByteArray :=
  (block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++
    block0024 ++ block0225).toByteArray
private def bytes1161 : ByteArray :=
  (block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++
    block0025 ++ block0226).toByteArray
private def bytes1162 : ByteArray :=
  (block0800 ++ block0785 ++ block0786).toByteArray
private def bytes1163 : ByteArray :=
  (block0800 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1164 : ByteArray :=
  (block0801 ++ block0785 ++ block0786).toByteArray
private def bytes1165 : ByteArray :=
  (block0801 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1166 : ByteArray :=
  (block0802 ++ block0785 ++ block0786).toByteArray
private def bytes1167 : ByteArray :=
  (block0802 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1168 : ByteArray :=
  (block0803 ++ block0785 ++ block0786).toByteArray
private def bytes1169 : ByteArray :=
  (block0803 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1170 : ByteArray :=
  (block0804 ++ block0785 ++ block0786).toByteArray
private def bytes1171 : ByteArray :=
  (block0804 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1172 : ByteArray :=
  (block0805 ++ block0785 ++ block0786).toByteArray
private def bytes1173 : ByteArray :=
  (block0805 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1174 : ByteArray :=
  (block0806 ++ block0785 ++ block0786).toByteArray
private def bytes1175 : ByteArray :=
  (block0806 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1176 : ByteArray :=
  (block0807 ++ block0785 ++ block0786).toByteArray
private def bytes1177 : ByteArray :=
  (block0807 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1178 : ByteArray :=
  (block0784 ++ block0808 ++ block0786).toByteArray
private def bytes1179 : ByteArray :=
  (block0784 ++ block0808 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1180 : ByteArray :=
  (block0784 ++ block0809 ++ block0786).toByteArray
private def bytes1181 : ByteArray :=
  (block0784 ++ block0809 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1182 : ByteArray :=
  (block0784 ++ block0810 ++ block0786).toByteArray
private def bytes1183 : ByteArray :=
  (block0784 ++ block0810 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1184 : ByteArray :=
  (block0784 ++ block0811 ++ block0786).toByteArray
private def bytes1185 : ByteArray :=
  (block0784 ++ block0811 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1186 : ByteArray :=
  (block0784 ++ block0812 ++ block0786).toByteArray
private def bytes1187 : ByteArray :=
  (block0784 ++ block0812 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1188 : ByteArray :=
  (block0784 ++ block0813 ++ block0786).toByteArray
private def bytes1189 : ByteArray :=
  (block0784 ++ block0813 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1190 : ByteArray :=
  (block0784 ++ block0814 ++ block0786).toByteArray
private def bytes1191 : ByteArray :=
  (block0784 ++ block0814 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1192 : ByteArray :=
  (block0784 ++ block0815 ++ block0786).toByteArray
private def bytes1193 : ByteArray :=
  (block0784 ++ block0815 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1194 : ByteArray :=
  (block0784 ++ block0785 ++ block0816).toByteArray
private def bytes1195 : ByteArray :=
  (block0784 ++ block0785 ++ block0817 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1196 : ByteArray :=
  (block0784 ++ block0785 ++ block0818).toByteArray
private def bytes1197 : ByteArray :=
  (block0784 ++ block0785 ++ block0819 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1198 : ByteArray :=
  (block0784 ++ block0785 ++ block0820).toByteArray
private def bytes1199 : ByteArray :=
  (block0784 ++ block0785 ++ block0821 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1200 : ByteArray :=
  (block0784 ++ block0785 ++ block0822).toByteArray
private def bytes1201 : ByteArray :=
  (block0784 ++ block0785 ++ block0823 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1202 : ByteArray :=
  (block0024 ++ block0024 ++ block0824 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1203 : ByteArray :=
  (block0025 ++ block0025 ++ block0825 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1204 : ByteArray :=
  (block0826 ++ block0788 ++ block0789 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1205 : ByteArray :=
  (block0784 ++ block0785 ++ block0827 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1206 : ByteArray :=
  (block0828 ++ block0788 ++ block0789 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1207 : ByteArray :=
  (block0784 ++ block0785 ++ block0829 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1208 : ByteArray :=
  (block0830 ++ block0788 ++ block0789 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1209 : ByteArray :=
  (block0784 ++ block0785 ++ block0831 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1210 : ByteArray :=
  (block0832 ++ block0788 ++ block0789 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1211 : ByteArray :=
  (block0784 ++ block0785 ++ block0833 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1212 : ByteArray :=
  (block0834 ++ block0788 ++ block0789 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1213 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0835 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1214 : ByteArray :=
  (block0836 ++ block0788 ++ block0789 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1215 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0837 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1216 : ByteArray :=
  (block0838 ++ block0788 ++ block0789 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1217 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0839 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1218 : ByteArray :=
  (block0840 ++ block0788 ++ block0789 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1219 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0841 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1220 : ByteArray :=
  (block0787 ++ block0842 ++ block0789 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1221 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0843 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1222 : ByteArray :=
  (block0787 ++ block0844 ++ block0789 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1223 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0845 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1224 : ByteArray :=
  (block0787 ++ block0846 ++ block0789 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1225 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0847 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1226 : ByteArray :=
  (block0787 ++ block0848 ++ block0789 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1227 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0849 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1228 : ByteArray :=
  (block0787 ++ block0850 ++ block0789 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1229 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0851 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1230 : ByteArray :=
  (block0787 ++ block0852 ++ block0789 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1231 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0853 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1232 : ByteArray :=
  (block0787 ++ block0854 ++ block0789 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1233 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0855 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1234 : ByteArray :=
  (block0787 ++ block0856 ++ block0789 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1235 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0857 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1236 : ByteArray :=
  (block0787 ++ block0788 ++ block0858 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1237 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0859 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1238 : ByteArray :=
  (block0787 ++ block0788 ++ block0860 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1239 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0861 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1240 : ByteArray :=
  (block0787 ++ block0788 ++ block0862 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1241 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0863 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1242 : ByteArray :=
  (block0787 ++ block0788 ++ block0864 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1243 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0865 ++ block0796 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1244 : ByteArray :=
  (block0787 ++ block0788 ++ block0866 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1245 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0867 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1246 : ByteArray :=
  (block0787 ++ block0788 ++ block0868 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1247 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0869 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1248 : ByteArray :=
  (block0787 ++ block0788 ++ block0870 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1249 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0871 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1250 : ByteArray :=
  (block0787 ++ block0788 ++ block0872 ++ block0790 ++ block0791 ++ block0792).toByteArray
private def bytes1251 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0873 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1252 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0874 ++ block0791 ++ block0792).toByteArray
private def bytes1253 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0875 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1254 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0876 ++ block0791 ++ block0792).toByteArray
private def bytes1255 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0877 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1256 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0878 ++ block0791 ++ block0792).toByteArray
private def bytes1257 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0879 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1258 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0880 ++ block0791 ++ block0792).toByteArray
private def bytes1259 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0881 ++ block0797 ++
    block0798 ++ block0799).toByteArray
private def bytes1260 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0882 ++ block0791 ++ block0792).toByteArray
private def bytes1261 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0883 ++
    block0798 ++ block0799).toByteArray
private def bytes1262 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0884 ++ block0791 ++ block0792).toByteArray
private def bytes1263 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0885 ++
    block0798 ++ block0799).toByteArray
private def bytes1264 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0886 ++ block0791 ++ block0792).toByteArray
private def bytes1265 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0887 ++
    block0798 ++ block0799).toByteArray
private def bytes1266 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0888 ++ block0791 ++ block0792).toByteArray
private def bytes1267 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0889 ++
    block0798 ++ block0799).toByteArray
private def bytes1268 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0790 ++ block0890 ++ block0792).toByteArray
private def bytes1269 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0891 ++
    block0798 ++ block0799).toByteArray
private def bytes1270 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0790 ++ block0892 ++ block0792).toByteArray
private def bytes1271 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0893 ++
    block0798 ++ block0799).toByteArray
private def bytes1272 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0790 ++ block0894 ++ block0792).toByteArray
private def bytes1273 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0895 ++
    block0798 ++ block0799).toByteArray
private def bytes1274 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0790 ++ block0896 ++ block0792).toByteArray
private def bytes1275 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0897 ++
    block0798 ++ block0799).toByteArray
private def bytes1276 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0790 ++ block0898 ++ block0792).toByteArray
private def bytes1277 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0899 ++ block0799).toByteArray
private def bytes1278 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0790 ++ block0900 ++ block0792).toByteArray
private def bytes1279 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0901 ++ block0799).toByteArray
private def bytes1280 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0790 ++ block0902 ++ block0792).toByteArray
private def bytes1281 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0903 ++ block0799).toByteArray
private def bytes1282 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0790 ++ block0904 ++ block0792).toByteArray
private def bytes1283 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0905 ++ block0799).toByteArray
private def bytes1284 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0790 ++ block0791 ++ block0906).toByteArray
private def bytes1285 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0907 ++ block0799).toByteArray
private def bytes1286 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0790 ++ block0791 ++ block0908).toByteArray
private def bytes1287 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0909 ++ block0799).toByteArray
private def bytes1288 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0790 ++ block0791 ++ block0910).toByteArray
private def bytes1289 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0911 ++ block0799).toByteArray
private def bytes1290 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0790 ++ block0791 ++ block0912).toByteArray
private def bytes1291 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0913 ++ block0799).toByteArray
private def bytes1292 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0790 ++ block0791 ++ block0914).toByteArray
private def bytes1293 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0915).toByteArray
private def bytes1294 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0790 ++ block0791 ++ block0916).toByteArray
private def bytes1295 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0917).toByteArray
private def bytes1296 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0790 ++ block0791 ++ block0918).toByteArray
private def bytes1297 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0919).toByteArray
private def bytes1298 : ByteArray :=
  (block0787 ++ block0788 ++ block0789 ++ block0790 ++ block0791 ++ block0920).toByteArray
private def bytes1299 : ByteArray :=
  (block0784 ++ block0785 ++ block0793 ++ block0794 ++ block0795 ++ block0796 ++ block0797 ++
    block0798 ++ block0921).toByteArray
private def bytes1300 : ByteArray :=
  (block0784 ++ block0785 ++ block0922 ++ block0024 ++ block0024 ++ block0024 ++ block0024 ++
    block0024 ++ block0225).toByteArray
private def bytes1301 : ByteArray :=
  (block0784 ++ block0785 ++ block0923 ++ block0025 ++ block0025 ++ block0025 ++ block0025 ++
    block0025 ++ block0226).toByteArray
private def bytes1302 : ByteArray :=
  (block0360 ++ block0361 ++ block0924 ++ block0382 ++ block0383 ++ block0384 ++ block0385 ++
    block0386 ++ block0925 ++ block0376 ++ block0377 ++ block0378 ++ block0379 ++ block0380 ++
    block0926).toByteArray
private def bytes1303 : ByteArray :=
  (block0927 ++ block0798 ++ block0928 ++ block0929 ++ block0930 ++ block0931).toByteArray
private def bytes1304 : ByteArray :=
  (block0932 ++ block0933 ++ block0934 ++ block0935 ++ block0936 ++ block0937).toByteArray
private def bytes1305 : ByteArray :=
  (block0360 ++ block0361 ++ block0938 ++ block0791 ++ block0939 ++ block0940 ++ block0941 ++
    block0942 ++ block0943 ++ block0944 ++ block0945 ++ block0946 ++ block0947 ++ block0619 ++
    block0948).toByteArray
private def bytes1306 : ByteArray :=
  (block0949 ++ block0950 ++ block0951 ++ block0952 ++ block0953 ++ block0954).toByteArray
private def bytes1307 : ByteArray :=
  (block0955 ++ block0956 ++ block0957 ++ block0958 ++ block0959 ++ block0960).toByteArray
private def bytes1308 : ByteArray :=
  (block0360 ++ block0361 ++ block0961 ++ block0962 ++ block0963 ++ block0964 ++ block0965 ++
    block0966 ++ block0967 ++ block0968 ++ block0969 ++ block0970 ++ block0971 ++ block0972 ++
    block0973).toByteArray
private def bytes1309 : ByteArray :=
  (block0974 ++ block0975 ++ block0976 ++ block0977 ++ block0978 ++ block0979).toByteArray
private def bytes1310 : ByteArray :=
  (block0980 ++ block0981 ++ block0215 ++ block0982 ++ block0983 ++ block0984).toByteArray
private def bytes1311 : ByteArray :=
  (block0360 ++ block0361 ++ block0985 ++ block0986 ++ block0987 ++ block0988 ++ block0989 ++
    block0990 ++ block0991 ++ block0629 ++ block0221 ++ block0992 ++ block0993 ++ block0994 ++
    block0995).toByteArray

-- DepositRequest/asymmetric-baseline
private def case000 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0003)
#guard case000 == some true

-- DepositRequest/all-zero
private def case001 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0004)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0005)
  let amount ← U64.ofNat? 0
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0006)
  let index ← U64.ofNat? 0
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0004.data.toList, .inl bytes0005.data.toList, .inr 0, .inl bytes0006.data.toList,
      .inr 0]
    (.container [.bytes bytes0004, .bytes bytes0005, .uint 0, .bytes bytes0006, .uint 0])
    bytes0007)
#guard case001 == some true

-- DepositRequest/all-ff-max
private def case002 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0008)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0009)
  let amount ← U64.ofNat? 18446744073709551615
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0010)
  let index ← U64.ofNat? 18446744073709551615
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0008.data.toList, .inl bytes0009.data.toList, .inr 18446744073709551615,
      .inl bytes0010.data.toList, .inr 18446744073709551615]
    (.container [.bytes bytes0008, .bytes bytes0009, .uint 18446744073709551615,
      .bytes bytes0010, .uint 18446744073709551615]) bytes0011)
#guard case002 == some true

-- DepositRequest/position/pubkey/0
private def case003 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0012)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0012.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0012, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0013)
#guard case003 == some true

-- DepositRequest/position/pubkey/1
private def case004 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0014)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0014.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0014, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0015)
#guard case004 == some true

-- DepositRequest/position/pubkey/2
private def case005 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0016)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0016.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0016, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0017)
#guard case005 == some true

-- DepositRequest/position/pubkey/3
private def case006 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0018)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0018.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0018, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0019)
#guard case006 == some true

-- DepositRequest/position/pubkey/4
private def case007 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0020)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0020.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0020, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0021)
#guard case007 == some true

-- DepositRequest/position/pubkey/5
private def case008 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0022)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0022.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0022, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0023)
#guard case008 == some true

-- DepositRequest/position/pubkey/6
private def case009 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0024)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0024.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0024, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0025)
#guard case009 == some true

-- DepositRequest/position/pubkey/7
private def case010 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0026)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0026.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0026, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0027)
#guard case010 == some true

-- DepositRequest/position/pubkey/8
private def case011 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0028)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0028.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0028, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0029)
#guard case011 == some true

-- DepositRequest/position/pubkey/9
private def case012 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0030)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0030.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0030, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0031)
#guard case012 == some true

-- DepositRequest/position/pubkey/10
private def case013 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0032)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0032.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0032, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0033)
#guard case013 == some true

-- DepositRequest/position/pubkey/11
private def case014 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0034)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0034.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0034, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0035)
#guard case014 == some true

-- DepositRequest/position/pubkey/12
private def case015 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0036)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0036.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0036, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0037)
#guard case015 == some true

-- DepositRequest/position/pubkey/13
private def case016 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0038)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0038.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0038, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0039)
#guard case016 == some true

-- DepositRequest/position/pubkey/14
private def case017 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0040)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0040.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0040, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0041)
#guard case017 == some true

-- DepositRequest/position/pubkey/15
private def case018 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0042)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0042.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0042, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0043)
#guard case018 == some true

-- DepositRequest/position/pubkey/16
private def case019 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0044)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0044.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0044, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0045)
#guard case019 == some true

-- DepositRequest/position/pubkey/17
private def case020 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0046)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0046.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0046, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0047)
#guard case020 == some true

-- DepositRequest/position/pubkey/18
private def case021 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0048)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0048.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0048, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0049)
#guard case021 == some true

-- DepositRequest/position/pubkey/19
private def case022 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0050)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0050.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0050, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0051)
#guard case022 == some true

-- DepositRequest/position/pubkey/20
private def case023 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0052)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0052.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0052, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0053)
#guard case023 == some true

-- DepositRequest/position/pubkey/21
private def case024 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0054)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0054.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0054, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0055)
#guard case024 == some true

-- DepositRequest/position/pubkey/22
private def case025 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0056)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0056.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0056, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0057)
#guard case025 == some true

-- DepositRequest/position/pubkey/23
private def case026 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0058)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0058.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0058, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0059)
#guard case026 == some true

-- DepositRequest/position/pubkey/24
private def case027 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0060)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0060.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0060, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0061)
#guard case027 == some true

-- DepositRequest/position/pubkey/25
private def case028 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0062)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0062.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0062, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0063)
#guard case028 == some true

-- DepositRequest/position/pubkey/26
private def case029 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0064)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0064.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0064, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0065)
#guard case029 == some true

-- DepositRequest/position/pubkey/27
private def case030 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0066)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0066.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0066, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0067)
#guard case030 == some true

-- DepositRequest/position/pubkey/28
private def case031 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0068)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0068.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0068, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0069)
#guard case031 == some true

-- DepositRequest/position/pubkey/29
private def case032 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0070)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0070.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0070, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0071)
#guard case032 == some true

-- DepositRequest/position/pubkey/30
private def case033 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0072)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0072.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0072, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0073)
#guard case033 == some true

-- DepositRequest/position/pubkey/31
private def case034 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0074)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0074.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0074, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0075)
#guard case034 == some true

-- DepositRequest/position/pubkey/32
private def case035 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0076)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0076.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0076, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0077)
#guard case035 == some true

-- DepositRequest/position/pubkey/33
private def case036 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0078)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0078.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0078, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0079)
#guard case036 == some true

-- DepositRequest/position/pubkey/34
private def case037 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0080)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0080.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0080, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0081)
#guard case037 == some true

-- DepositRequest/position/pubkey/35
private def case038 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0082)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0082.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0082, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0083)
#guard case038 == some true

-- DepositRequest/position/pubkey/36
private def case039 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0084)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0084.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0084, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0085)
#guard case039 == some true

-- DepositRequest/position/pubkey/37
private def case040 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0086)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0086.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0086, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0087)
#guard case040 == some true

-- DepositRequest/position/pubkey/38
private def case041 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0088)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0088.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0088, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0089)
#guard case041 == some true

-- DepositRequest/position/pubkey/39
private def case042 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0090)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0090.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0090, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0091)
#guard case042 == some true

-- DepositRequest/position/pubkey/40
private def case043 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0092)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0092.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0092, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0093)
#guard case043 == some true

-- DepositRequest/position/pubkey/41
private def case044 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0094)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0094.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0094, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0095)
#guard case044 == some true

-- DepositRequest/position/pubkey/42
private def case045 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0096)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0096.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0096, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0097)
#guard case045 == some true

-- DepositRequest/position/pubkey/43
private def case046 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0098)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0098.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0098, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0099)
#guard case046 == some true

-- DepositRequest/position/pubkey/44
private def case047 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0100)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0100.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0100, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0101)
#guard case047 == some true

-- DepositRequest/position/pubkey/45
private def case048 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0102)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0102.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0102, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0103)
#guard case048 == some true

-- DepositRequest/position/pubkey/46
private def case049 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0104)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0104.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0104, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0105)
#guard case049 == some true

-- DepositRequest/position/pubkey/47
private def case050 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0106)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0106.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0106, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0107)
#guard case050 == some true

-- DepositRequest/whole-field/pubkey/0
private def case051 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0004)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0004.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0004, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0108)
#guard case051 == some true

-- DepositRequest/whole-field/pubkey/255
private def case052 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0008)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0008.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0008, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0109)
#guard case052 == some true

-- DepositRequest/position/withdrawalCredentials/0
private def case053 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0110)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0110.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0110, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0111)
#guard case053 == some true

-- DepositRequest/position/withdrawalCredentials/1
private def case054 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0112)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0112.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0112, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0113)
#guard case054 == some true

-- DepositRequest/position/withdrawalCredentials/2
private def case055 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0114)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0114.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0114, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0115)
#guard case055 == some true

-- DepositRequest/position/withdrawalCredentials/3
private def case056 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0116)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0116.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0116, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0117)
#guard case056 == some true

-- DepositRequest/position/withdrawalCredentials/4
private def case057 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0118)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0118.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0118, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0119)
#guard case057 == some true

-- DepositRequest/position/withdrawalCredentials/5
private def case058 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0120)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0120.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0120, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0121)
#guard case058 == some true

-- DepositRequest/position/withdrawalCredentials/6
private def case059 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0122)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0122.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0122, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0123)
#guard case059 == some true

-- DepositRequest/position/withdrawalCredentials/7
private def case060 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0124)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0124.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0124, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0125)
#guard case060 == some true

-- DepositRequest/position/withdrawalCredentials/8
private def case061 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0126)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0126.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0126, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0127)
#guard case061 == some true

-- DepositRequest/position/withdrawalCredentials/9
private def case062 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0128)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0128.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0128, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0129)
#guard case062 == some true

-- DepositRequest/position/withdrawalCredentials/10
private def case063 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0130)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0130.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0130, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0131)
#guard case063 == some true

-- DepositRequest/position/withdrawalCredentials/11
private def case064 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0132)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0132.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0132, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0133)
#guard case064 == some true

-- DepositRequest/position/withdrawalCredentials/12
private def case065 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0134)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0134.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0134, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0135)
#guard case065 == some true

-- DepositRequest/position/withdrawalCredentials/13
private def case066 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0136)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0136.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0136, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0137)
#guard case066 == some true

-- DepositRequest/position/withdrawalCredentials/14
private def case067 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0138)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0138.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0138, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0139)
#guard case067 == some true

-- DepositRequest/position/withdrawalCredentials/15
private def case068 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0140)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0140.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0140, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0141)
#guard case068 == some true

-- DepositRequest/position/withdrawalCredentials/16
private def case069 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0142)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0142.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0142, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0143)
#guard case069 == some true

-- DepositRequest/position/withdrawalCredentials/17
private def case070 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0144)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0144.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0144, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0145)
#guard case070 == some true

-- DepositRequest/position/withdrawalCredentials/18
private def case071 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0146)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0146.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0146, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0147)
#guard case071 == some true

-- DepositRequest/position/withdrawalCredentials/19
private def case072 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0148)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0148.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0148, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0149)
#guard case072 == some true

-- DepositRequest/position/withdrawalCredentials/20
private def case073 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0150)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0150.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0150, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0151)
#guard case073 == some true

-- DepositRequest/position/withdrawalCredentials/21
private def case074 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0152)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0152.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0152, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0153)
#guard case074 == some true

-- DepositRequest/position/withdrawalCredentials/22
private def case075 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0154)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0154.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0154, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0155)
#guard case075 == some true

-- DepositRequest/position/withdrawalCredentials/23
private def case076 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0156)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0156.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0156, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0157)
#guard case076 == some true

-- DepositRequest/position/withdrawalCredentials/24
private def case077 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0158)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0158.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0158, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0159)
#guard case077 == some true

-- DepositRequest/position/withdrawalCredentials/25
private def case078 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0160)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0160.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0160, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0161)
#guard case078 == some true

-- DepositRequest/position/withdrawalCredentials/26
private def case079 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0162)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0162.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0162, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0163)
#guard case079 == some true

-- DepositRequest/position/withdrawalCredentials/27
private def case080 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0164)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0164.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0164, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0165)
#guard case080 == some true

-- DepositRequest/position/withdrawalCredentials/28
private def case081 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0166)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0166.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0166, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0167)
#guard case081 == some true

-- DepositRequest/position/withdrawalCredentials/29
private def case082 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0168)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0168.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0168, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0169)
#guard case082 == some true

-- DepositRequest/position/withdrawalCredentials/30
private def case083 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0170)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0170.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0170, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0171)
#guard case083 == some true

-- DepositRequest/position/withdrawalCredentials/31
private def case084 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0172)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0172.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0172, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0173)
#guard case084 == some true

-- DepositRequest/whole-field/withdrawalCredentials/0
private def case085 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0005)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0005.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0005, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0174)
#guard case085 == some true

-- DepositRequest/whole-field/withdrawalCredentials/255
private def case086 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0009)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0009.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0009, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0175)
#guard case086 == some true

-- DepositRequest/uint/amount/0
private def case087 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 0
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 0, .inl bytes0002.data.toList,
      .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 0, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0176)
#guard case087 == some true

-- DepositRequest/uint/amount/1
private def case088 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1, .inl bytes0002.data.toList,
      .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0177)
#guard case088 == some true

-- DepositRequest/uint/amount/255
private def case089 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 255
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 255,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 255, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0178)
#guard case089 == some true

-- DepositRequest/uint/amount/256
private def case090 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 256
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 256,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 256, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0179)
#guard case090 == some true

-- DepositRequest/uint/amount/4294967295
private def case091 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 4294967295
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 4294967295,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 4294967295, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0180)
#guard case091 == some true

-- DepositRequest/uint/amount/4294967296
private def case092 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 4294967296
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 4294967296,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 4294967296, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0181)
#guard case092 == some true

-- DepositRequest/uint/amount/9223372036854775808
private def case093 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 9223372036854775808
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 9223372036854775808,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 9223372036854775808, .bytes bytes0002,
      .uint 1161981756646142084]) bytes0182)
#guard case093 == some true

-- DepositRequest/uint/amount/18446744073709551615
private def case094 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 18446744073709551615
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 18446744073709551615,
      .inl bytes0002.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 18446744073709551615,
      .bytes bytes0002, .uint 1161981756646142084]) bytes0183)
#guard case094 == some true

-- DepositRequest/position/signature/0
private def case095 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0184)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0184.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0184,
      .uint 1161981756646142084]) bytes0185)
#guard case095 == some true

-- DepositRequest/position/signature/1
private def case096 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0186)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0186.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0186,
      .uint 1161981756646142084]) bytes0187)
#guard case096 == some true

-- DepositRequest/position/signature/2
private def case097 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0188)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0188.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0188,
      .uint 1161981756646142084]) bytes0189)
#guard case097 == some true

-- DepositRequest/position/signature/3
private def case098 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0190)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0190.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0190,
      .uint 1161981756646142084]) bytes0191)
#guard case098 == some true

-- DepositRequest/position/signature/4
private def case099 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0192)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0192.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0192,
      .uint 1161981756646142084]) bytes0193)
#guard case099 == some true

-- DepositRequest/position/signature/5
private def case100 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0194)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0194.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0194,
      .uint 1161981756646142084]) bytes0195)
#guard case100 == some true

-- DepositRequest/position/signature/6
private def case101 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0196)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0196.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0196,
      .uint 1161981756646142084]) bytes0197)
#guard case101 == some true

-- DepositRequest/position/signature/7
private def case102 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0198)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0198.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0198,
      .uint 1161981756646142084]) bytes0199)
#guard case102 == some true

-- DepositRequest/position/signature/8
private def case103 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0200)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0200.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0200,
      .uint 1161981756646142084]) bytes0201)
#guard case103 == some true

-- DepositRequest/position/signature/9
private def case104 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0202)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0202.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0202,
      .uint 1161981756646142084]) bytes0203)
#guard case104 == some true

-- DepositRequest/position/signature/10
private def case105 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0204)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0204.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0204,
      .uint 1161981756646142084]) bytes0205)
#guard case105 == some true

-- DepositRequest/position/signature/11
private def case106 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0206)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0206.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0206,
      .uint 1161981756646142084]) bytes0207)
#guard case106 == some true

-- DepositRequest/position/signature/12
private def case107 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0208)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0208.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0208,
      .uint 1161981756646142084]) bytes0209)
#guard case107 == some true

-- DepositRequest/position/signature/13
private def case108 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0210)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0210.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0210,
      .uint 1161981756646142084]) bytes0211)
#guard case108 == some true

-- DepositRequest/position/signature/14
private def case109 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0212)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0212.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0212,
      .uint 1161981756646142084]) bytes0213)
#guard case109 == some true

-- DepositRequest/position/signature/15
private def case110 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0214)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0214.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0214,
      .uint 1161981756646142084]) bytes0215)
#guard case110 == some true

-- DepositRequest/position/signature/16
private def case111 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0216)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0216.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0216,
      .uint 1161981756646142084]) bytes0217)
#guard case111 == some true

-- DepositRequest/position/signature/17
private def case112 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0218)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0218.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0218,
      .uint 1161981756646142084]) bytes0219)
#guard case112 == some true

-- DepositRequest/position/signature/18
private def case113 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0220)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0220.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0220,
      .uint 1161981756646142084]) bytes0221)
#guard case113 == some true

-- DepositRequest/position/signature/19
private def case114 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0222)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0222.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0222,
      .uint 1161981756646142084]) bytes0223)
#guard case114 == some true

-- DepositRequest/position/signature/20
private def case115 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0224)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0224.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0224,
      .uint 1161981756646142084]) bytes0225)
#guard case115 == some true

-- DepositRequest/position/signature/21
private def case116 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0226)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0226.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0226,
      .uint 1161981756646142084]) bytes0227)
#guard case116 == some true

-- DepositRequest/position/signature/22
private def case117 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0228)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0228.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0228,
      .uint 1161981756646142084]) bytes0229)
#guard case117 == some true

-- DepositRequest/position/signature/23
private def case118 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0230)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0230.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0230,
      .uint 1161981756646142084]) bytes0231)
#guard case118 == some true

-- DepositRequest/position/signature/24
private def case119 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0232)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0232.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0232,
      .uint 1161981756646142084]) bytes0233)
#guard case119 == some true

-- DepositRequest/position/signature/25
private def case120 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0234)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0234.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0234,
      .uint 1161981756646142084]) bytes0235)
#guard case120 == some true

-- DepositRequest/position/signature/26
private def case121 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0236)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0236.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0236,
      .uint 1161981756646142084]) bytes0237)
#guard case121 == some true

-- DepositRequest/position/signature/27
private def case122 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0238)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0238.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0238,
      .uint 1161981756646142084]) bytes0239)
#guard case122 == some true

-- DepositRequest/position/signature/28
private def case123 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0240)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0240.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0240,
      .uint 1161981756646142084]) bytes0241)
#guard case123 == some true

-- DepositRequest/position/signature/29
private def case124 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0242)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0242.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0242,
      .uint 1161981756646142084]) bytes0243)
#guard case124 == some true

-- DepositRequest/position/signature/30
private def case125 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0244)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0244.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0244,
      .uint 1161981756646142084]) bytes0245)
#guard case125 == some true

-- DepositRequest/position/signature/31
private def case126 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0246)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0246.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0246,
      .uint 1161981756646142084]) bytes0247)
#guard case126 == some true

-- DepositRequest/position/signature/32
private def case127 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0248)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0248.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0248,
      .uint 1161981756646142084]) bytes0249)
#guard case127 == some true

-- DepositRequest/position/signature/33
private def case128 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0250)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0250.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0250,
      .uint 1161981756646142084]) bytes0251)
#guard case128 == some true

-- DepositRequest/position/signature/34
private def case129 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0252)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0252.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0252,
      .uint 1161981756646142084]) bytes0253)
#guard case129 == some true

-- DepositRequest/position/signature/35
private def case130 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0254)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0254.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0254,
      .uint 1161981756646142084]) bytes0255)
#guard case130 == some true

-- DepositRequest/position/signature/36
private def case131 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0256)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0256.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0256,
      .uint 1161981756646142084]) bytes0257)
#guard case131 == some true

-- DepositRequest/position/signature/37
private def case132 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0258)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0258.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0258,
      .uint 1161981756646142084]) bytes0259)
#guard case132 == some true

-- DepositRequest/position/signature/38
private def case133 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0260)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0260.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0260,
      .uint 1161981756646142084]) bytes0261)
#guard case133 == some true

-- DepositRequest/position/signature/39
private def case134 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0262)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0262.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0262,
      .uint 1161981756646142084]) bytes0263)
#guard case134 == some true

-- DepositRequest/position/signature/40
private def case135 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0264)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0264.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0264,
      .uint 1161981756646142084]) bytes0265)
#guard case135 == some true

-- DepositRequest/position/signature/41
private def case136 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0266)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0266.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0266,
      .uint 1161981756646142084]) bytes0267)
#guard case136 == some true

-- DepositRequest/position/signature/42
private def case137 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0268)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0268.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0268,
      .uint 1161981756646142084]) bytes0269)
#guard case137 == some true

-- DepositRequest/position/signature/43
private def case138 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0270)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0270.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0270,
      .uint 1161981756646142084]) bytes0271)
#guard case138 == some true

-- DepositRequest/position/signature/44
private def case139 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0272)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0272.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0272,
      .uint 1161981756646142084]) bytes0273)
#guard case139 == some true

-- DepositRequest/position/signature/45
private def case140 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0274)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0274.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0274,
      .uint 1161981756646142084]) bytes0275)
#guard case140 == some true

-- DepositRequest/position/signature/46
private def case141 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0276)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0276.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0276,
      .uint 1161981756646142084]) bytes0277)
#guard case141 == some true

-- DepositRequest/position/signature/47
private def case142 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0278)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0278.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0278,
      .uint 1161981756646142084]) bytes0279)
#guard case142 == some true

-- DepositRequest/position/signature/48
private def case143 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0280)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0280.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0280,
      .uint 1161981756646142084]) bytes0281)
#guard case143 == some true

-- DepositRequest/position/signature/49
private def case144 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0282)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0282.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0282,
      .uint 1161981756646142084]) bytes0283)
#guard case144 == some true

-- DepositRequest/position/signature/50
private def case145 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0284)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0284.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0284,
      .uint 1161981756646142084]) bytes0285)
#guard case145 == some true

-- DepositRequest/position/signature/51
private def case146 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0286)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0286.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0286,
      .uint 1161981756646142084]) bytes0287)
#guard case146 == some true

-- DepositRequest/position/signature/52
private def case147 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0288)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0288.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0288,
      .uint 1161981756646142084]) bytes0289)
#guard case147 == some true

-- DepositRequest/position/signature/53
private def case148 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0290)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0290.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0290,
      .uint 1161981756646142084]) bytes0291)
#guard case148 == some true

-- DepositRequest/position/signature/54
private def case149 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0292)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0292.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0292,
      .uint 1161981756646142084]) bytes0293)
#guard case149 == some true

-- DepositRequest/position/signature/55
private def case150 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0294)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0294.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0294,
      .uint 1161981756646142084]) bytes0295)
#guard case150 == some true

-- DepositRequest/position/signature/56
private def case151 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0296)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0296.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0296,
      .uint 1161981756646142084]) bytes0297)
#guard case151 == some true

-- DepositRequest/position/signature/57
private def case152 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0298)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0298.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0298,
      .uint 1161981756646142084]) bytes0299)
#guard case152 == some true

-- DepositRequest/position/signature/58
private def case153 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0300)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0300.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0300,
      .uint 1161981756646142084]) bytes0301)
#guard case153 == some true

-- DepositRequest/position/signature/59
private def case154 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0302)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0302.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0302,
      .uint 1161981756646142084]) bytes0303)
#guard case154 == some true

-- DepositRequest/position/signature/60
private def case155 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0304)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0304.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0304,
      .uint 1161981756646142084]) bytes0305)
#guard case155 == some true

-- DepositRequest/position/signature/61
private def case156 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0306)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0306.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0306,
      .uint 1161981756646142084]) bytes0307)
#guard case156 == some true

-- DepositRequest/position/signature/62
private def case157 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0308)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0308.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0308,
      .uint 1161981756646142084]) bytes0309)
#guard case157 == some true

-- DepositRequest/position/signature/63
private def case158 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0310)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0310.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0310,
      .uint 1161981756646142084]) bytes0311)
#guard case158 == some true

-- DepositRequest/position/signature/64
private def case159 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0312)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0312.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0312,
      .uint 1161981756646142084]) bytes0313)
#guard case159 == some true

-- DepositRequest/position/signature/65
private def case160 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0314)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0314.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0314,
      .uint 1161981756646142084]) bytes0315)
#guard case160 == some true

-- DepositRequest/position/signature/66
private def case161 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0316)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0316.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0316,
      .uint 1161981756646142084]) bytes0317)
#guard case161 == some true

-- DepositRequest/position/signature/67
private def case162 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0318)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0318.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0318,
      .uint 1161981756646142084]) bytes0319)
#guard case162 == some true

-- DepositRequest/position/signature/68
private def case163 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0320)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0320.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0320,
      .uint 1161981756646142084]) bytes0321)
#guard case163 == some true

-- DepositRequest/position/signature/69
private def case164 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0322)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0322.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0322,
      .uint 1161981756646142084]) bytes0323)
#guard case164 == some true

-- DepositRequest/position/signature/70
private def case165 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0324)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0324.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0324,
      .uint 1161981756646142084]) bytes0325)
#guard case165 == some true

-- DepositRequest/position/signature/71
private def case166 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0326)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0326.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0326,
      .uint 1161981756646142084]) bytes0327)
#guard case166 == some true

-- DepositRequest/position/signature/72
private def case167 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0328)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0328.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0328,
      .uint 1161981756646142084]) bytes0329)
#guard case167 == some true

-- DepositRequest/position/signature/73
private def case168 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0330)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0330.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0330,
      .uint 1161981756646142084]) bytes0331)
#guard case168 == some true

-- DepositRequest/position/signature/74
private def case169 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0332)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0332.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0332,
      .uint 1161981756646142084]) bytes0333)
#guard case169 == some true

-- DepositRequest/position/signature/75
private def case170 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0334)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0334.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0334,
      .uint 1161981756646142084]) bytes0335)
#guard case170 == some true

-- DepositRequest/position/signature/76
private def case171 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0336)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0336.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0336,
      .uint 1161981756646142084]) bytes0337)
#guard case171 == some true

-- DepositRequest/position/signature/77
private def case172 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0338)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0338.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0338,
      .uint 1161981756646142084]) bytes0339)
#guard case172 == some true

-- DepositRequest/position/signature/78
private def case173 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0340)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0340.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0340,
      .uint 1161981756646142084]) bytes0341)
#guard case173 == some true

-- DepositRequest/position/signature/79
private def case174 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0342)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0342.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0342,
      .uint 1161981756646142084]) bytes0343)
#guard case174 == some true

-- DepositRequest/position/signature/80
private def case175 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0344)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0344.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0344,
      .uint 1161981756646142084]) bytes0345)
#guard case175 == some true

-- DepositRequest/position/signature/81
private def case176 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0346)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0346.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0346,
      .uint 1161981756646142084]) bytes0347)
#guard case176 == some true

-- DepositRequest/position/signature/82
private def case177 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0348)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0348.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0348,
      .uint 1161981756646142084]) bytes0349)
#guard case177 == some true

-- DepositRequest/position/signature/83
private def case178 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0350)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0350.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0350,
      .uint 1161981756646142084]) bytes0351)
#guard case178 == some true

-- DepositRequest/position/signature/84
private def case179 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0352)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0352.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0352,
      .uint 1161981756646142084]) bytes0353)
#guard case179 == some true

-- DepositRequest/position/signature/85
private def case180 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0354)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0354.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0354,
      .uint 1161981756646142084]) bytes0355)
#guard case180 == some true

-- DepositRequest/position/signature/86
private def case181 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0356)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0356.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0356,
      .uint 1161981756646142084]) bytes0357)
#guard case181 == some true

-- DepositRequest/position/signature/87
private def case182 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0358)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0358.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0358,
      .uint 1161981756646142084]) bytes0359)
#guard case182 == some true

-- DepositRequest/position/signature/88
private def case183 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0360)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0360.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0360,
      .uint 1161981756646142084]) bytes0361)
#guard case183 == some true

-- DepositRequest/position/signature/89
private def case184 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0362)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0362.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0362,
      .uint 1161981756646142084]) bytes0363)
#guard case184 == some true

-- DepositRequest/position/signature/90
private def case185 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0364)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0364.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0364,
      .uint 1161981756646142084]) bytes0365)
#guard case185 == some true

-- DepositRequest/position/signature/91
private def case186 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0366)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0366.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0366,
      .uint 1161981756646142084]) bytes0367)
#guard case186 == some true

-- DepositRequest/position/signature/92
private def case187 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0368)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0368.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0368,
      .uint 1161981756646142084]) bytes0369)
#guard case187 == some true

-- DepositRequest/position/signature/93
private def case188 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0370)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0370.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0370,
      .uint 1161981756646142084]) bytes0371)
#guard case188 == some true

-- DepositRequest/position/signature/94
private def case189 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0372)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0372.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0372,
      .uint 1161981756646142084]) bytes0373)
#guard case189 == some true

-- DepositRequest/position/signature/95
private def case190 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0374)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0374.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0374,
      .uint 1161981756646142084]) bytes0375)
#guard case190 == some true

-- DepositRequest/whole-field/signature/0
private def case191 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0006)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0006.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0006,
      .uint 1161981756646142084]) bytes0376)
#guard case191 == some true

-- DepositRequest/whole-field/signature/255
private def case192 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0010)
  let index ← U64.ofNat? 1161981756646142084
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0010.data.toList, .inr 1161981756646142084]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0010,
      .uint 1161981756646142084]) bytes0377)
#guard case192 == some true

-- DepositRequest/uint/index/0
private def case193 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 0
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 0]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 0]) bytes0378)
#guard case193 == some true

-- DepositRequest/uint/index/1
private def case194 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 1
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 1]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 1]) bytes0379)
#guard case194 == some true

-- DepositRequest/uint/index/255
private def case195 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 255
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 255]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 255]) bytes0380)
#guard case195 == some true

-- DepositRequest/uint/index/256
private def case196 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 256
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 256]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 256]) bytes0381)
#guard case196 == some true

-- DepositRequest/uint/index/4294967295
private def case197 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 4294967295
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 4294967295]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 4294967295]) bytes0382)
#guard case197 == some true

-- DepositRequest/uint/index/4294967296
private def case198 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 4294967296
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 4294967296]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 4294967296]) bytes0383)
#guard case198 == some true

-- DepositRequest/uint/index/9223372036854775808
private def case199 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 9223372036854775808
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 9223372036854775808]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 9223372036854775808]) bytes0384)
#guard case199 == some true

-- DepositRequest/uint/index/18446744073709551615
private def case200 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0000)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0001)
  let amount ← U64.ofNat? 1161981756646133890
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0002)
  let index ← U64.ofNat? 18446744073709551615
  pure (DepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature, index⟩
    [.inl bytes0000.data.toList, .inl bytes0001.data.toList, .inr 1161981756646133890,
      .inl bytes0002.data.toList, .inr 18446744073709551615]
    (.container [.bytes bytes0000, .bytes bytes0001, .uint 1161981756646133890, .bytes bytes0002,
      .uint 18446744073709551615]) bytes0385)
#guard case200 == some true

-- WithdrawalRequest/asymmetric-baseline
private def case201 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0387, .uint 1161981756647186562]) bytes0388)
#guard case201 == some true

-- WithdrawalRequest/all-zero
private def case202 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0389)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0004)
  let amount ← U64.ofNat? 0
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0389.data.toList, .inl bytes0004.data.toList, .inr 0]
    (.container [.bytes bytes0389, .bytes bytes0004, .uint 0]) bytes0390)
#guard case202 == some true

-- WithdrawalRequest/all-ff-max
private def case203 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0391)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0008)
  let amount ← U64.ofNat? 18446744073709551615
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0391.data.toList, .inl bytes0008.data.toList, .inr 18446744073709551615]
    (.container [.bytes bytes0391, .bytes bytes0008, .uint 18446744073709551615]) bytes0392)
#guard case203 == some true

-- WithdrawalRequest/position/sourceAddress/0
private def case204 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0393)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0393.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0393, .bytes bytes0387, .uint 1161981756647186562]) bytes0394)
#guard case204 == some true

-- WithdrawalRequest/position/sourceAddress/1
private def case205 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0395)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0395.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0395, .bytes bytes0387, .uint 1161981756647186562]) bytes0396)
#guard case205 == some true

-- WithdrawalRequest/position/sourceAddress/2
private def case206 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0397)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0397.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0397, .bytes bytes0387, .uint 1161981756647186562]) bytes0398)
#guard case206 == some true

-- WithdrawalRequest/position/sourceAddress/3
private def case207 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0399)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0399.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0399, .bytes bytes0387, .uint 1161981756647186562]) bytes0400)
#guard case207 == some true

-- WithdrawalRequest/position/sourceAddress/4
private def case208 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0401)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0401.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0401, .bytes bytes0387, .uint 1161981756647186562]) bytes0402)
#guard case208 == some true

-- WithdrawalRequest/position/sourceAddress/5
private def case209 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0403)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0403.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0403, .bytes bytes0387, .uint 1161981756647186562]) bytes0404)
#guard case209 == some true

-- WithdrawalRequest/position/sourceAddress/6
private def case210 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0405)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0405.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0405, .bytes bytes0387, .uint 1161981756647186562]) bytes0406)
#guard case210 == some true

-- WithdrawalRequest/position/sourceAddress/7
private def case211 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0407)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0407.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0407, .bytes bytes0387, .uint 1161981756647186562]) bytes0408)
#guard case211 == some true

-- WithdrawalRequest/position/sourceAddress/8
private def case212 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0409)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0409.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0409, .bytes bytes0387, .uint 1161981756647186562]) bytes0410)
#guard case212 == some true

-- WithdrawalRequest/position/sourceAddress/9
private def case213 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0411)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0411.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0411, .bytes bytes0387, .uint 1161981756647186562]) bytes0412)
#guard case213 == some true

-- WithdrawalRequest/position/sourceAddress/10
private def case214 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0413)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0413.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0413, .bytes bytes0387, .uint 1161981756647186562]) bytes0414)
#guard case214 == some true

-- WithdrawalRequest/position/sourceAddress/11
private def case215 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0415)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0415.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0415, .bytes bytes0387, .uint 1161981756647186562]) bytes0416)
#guard case215 == some true

-- WithdrawalRequest/position/sourceAddress/12
private def case216 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0417)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0417.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0417, .bytes bytes0387, .uint 1161981756647186562]) bytes0418)
#guard case216 == some true

-- WithdrawalRequest/position/sourceAddress/13
private def case217 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0419)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0419.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0419, .bytes bytes0387, .uint 1161981756647186562]) bytes0420)
#guard case217 == some true

-- WithdrawalRequest/position/sourceAddress/14
private def case218 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0421)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0421.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0421, .bytes bytes0387, .uint 1161981756647186562]) bytes0422)
#guard case218 == some true

-- WithdrawalRequest/position/sourceAddress/15
private def case219 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0423)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0423.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0423, .bytes bytes0387, .uint 1161981756647186562]) bytes0424)
#guard case219 == some true

-- WithdrawalRequest/position/sourceAddress/16
private def case220 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0425)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0425.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0425, .bytes bytes0387, .uint 1161981756647186562]) bytes0426)
#guard case220 == some true

-- WithdrawalRequest/position/sourceAddress/17
private def case221 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0427)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0427.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0427, .bytes bytes0387, .uint 1161981756647186562]) bytes0428)
#guard case221 == some true

-- WithdrawalRequest/position/sourceAddress/18
private def case222 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0429)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0429.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0429, .bytes bytes0387, .uint 1161981756647186562]) bytes0430)
#guard case222 == some true

-- WithdrawalRequest/position/sourceAddress/19
private def case223 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0431)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0431.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0431, .bytes bytes0387, .uint 1161981756647186562]) bytes0432)
#guard case223 == some true

-- WithdrawalRequest/whole-field/sourceAddress/0
private def case224 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0389)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0389.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0389, .bytes bytes0387, .uint 1161981756647186562]) bytes0433)
#guard case224 == some true

-- WithdrawalRequest/whole-field/sourceAddress/255
private def case225 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0391)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0391.data.toList, .inl bytes0387.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0391, .bytes bytes0387, .uint 1161981756647186562]) bytes0434)
#guard case225 == some true

-- WithdrawalRequest/position/validatorPubkey/0
private def case226 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0435)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0435.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0435, .uint 1161981756647186562]) bytes0436)
#guard case226 == some true

-- WithdrawalRequest/position/validatorPubkey/1
private def case227 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0437)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0437.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0437, .uint 1161981756647186562]) bytes0438)
#guard case227 == some true

-- WithdrawalRequest/position/validatorPubkey/2
private def case228 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0439)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0439.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0439, .uint 1161981756647186562]) bytes0440)
#guard case228 == some true

-- WithdrawalRequest/position/validatorPubkey/3
private def case229 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0441)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0441.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0441, .uint 1161981756647186562]) bytes0442)
#guard case229 == some true

-- WithdrawalRequest/position/validatorPubkey/4
private def case230 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0443)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0443.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0443, .uint 1161981756647186562]) bytes0444)
#guard case230 == some true

-- WithdrawalRequest/position/validatorPubkey/5
private def case231 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0445)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0445.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0445, .uint 1161981756647186562]) bytes0446)
#guard case231 == some true

-- WithdrawalRequest/position/validatorPubkey/6
private def case232 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0447)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0447.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0447, .uint 1161981756647186562]) bytes0448)
#guard case232 == some true

-- WithdrawalRequest/position/validatorPubkey/7
private def case233 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0449)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0449.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0449, .uint 1161981756647186562]) bytes0450)
#guard case233 == some true

-- WithdrawalRequest/position/validatorPubkey/8
private def case234 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0451)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0451.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0451, .uint 1161981756647186562]) bytes0452)
#guard case234 == some true

-- WithdrawalRequest/position/validatorPubkey/9
private def case235 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0453)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0453.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0453, .uint 1161981756647186562]) bytes0454)
#guard case235 == some true

-- WithdrawalRequest/position/validatorPubkey/10
private def case236 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0455)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0455.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0455, .uint 1161981756647186562]) bytes0456)
#guard case236 == some true

-- WithdrawalRequest/position/validatorPubkey/11
private def case237 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0457)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0457.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0457, .uint 1161981756647186562]) bytes0458)
#guard case237 == some true

-- WithdrawalRequest/position/validatorPubkey/12
private def case238 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0459)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0459.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0459, .uint 1161981756647186562]) bytes0460)
#guard case238 == some true

-- WithdrawalRequest/position/validatorPubkey/13
private def case239 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0461)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0461.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0461, .uint 1161981756647186562]) bytes0462)
#guard case239 == some true

-- WithdrawalRequest/position/validatorPubkey/14
private def case240 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0463)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0463.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0463, .uint 1161981756647186562]) bytes0464)
#guard case240 == some true

-- WithdrawalRequest/position/validatorPubkey/15
private def case241 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0465)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0465.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0465, .uint 1161981756647186562]) bytes0466)
#guard case241 == some true

-- WithdrawalRequest/position/validatorPubkey/16
private def case242 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0467)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0467.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0467, .uint 1161981756647186562]) bytes0468)
#guard case242 == some true

-- WithdrawalRequest/position/validatorPubkey/17
private def case243 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0469)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0469.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0469, .uint 1161981756647186562]) bytes0470)
#guard case243 == some true

-- WithdrawalRequest/position/validatorPubkey/18
private def case244 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0471)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0471.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0471, .uint 1161981756647186562]) bytes0472)
#guard case244 == some true

-- WithdrawalRequest/position/validatorPubkey/19
private def case245 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0473)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0473.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0473, .uint 1161981756647186562]) bytes0474)
#guard case245 == some true

-- WithdrawalRequest/position/validatorPubkey/20
private def case246 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0475)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0475.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0475, .uint 1161981756647186562]) bytes0476)
#guard case246 == some true

-- WithdrawalRequest/position/validatorPubkey/21
private def case247 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0477)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0477.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0477, .uint 1161981756647186562]) bytes0478)
#guard case247 == some true

-- WithdrawalRequest/position/validatorPubkey/22
private def case248 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0479)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0479.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0479, .uint 1161981756647186562]) bytes0480)
#guard case248 == some true

-- WithdrawalRequest/position/validatorPubkey/23
private def case249 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0481)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0481.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0481, .uint 1161981756647186562]) bytes0482)
#guard case249 == some true

-- WithdrawalRequest/position/validatorPubkey/24
private def case250 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0483)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0483.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0483, .uint 1161981756647186562]) bytes0484)
#guard case250 == some true

-- WithdrawalRequest/position/validatorPubkey/25
private def case251 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0485)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0485.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0485, .uint 1161981756647186562]) bytes0486)
#guard case251 == some true

-- WithdrawalRequest/position/validatorPubkey/26
private def case252 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0487)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0487.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0487, .uint 1161981756647186562]) bytes0488)
#guard case252 == some true

-- WithdrawalRequest/position/validatorPubkey/27
private def case253 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0489)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0489.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0489, .uint 1161981756647186562]) bytes0490)
#guard case253 == some true

-- WithdrawalRequest/position/validatorPubkey/28
private def case254 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0491)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0491.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0491, .uint 1161981756647186562]) bytes0492)
#guard case254 == some true

-- WithdrawalRequest/position/validatorPubkey/29
private def case255 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0493)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0493.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0493, .uint 1161981756647186562]) bytes0494)
#guard case255 == some true

-- WithdrawalRequest/position/validatorPubkey/30
private def case256 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0495)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0495.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0495, .uint 1161981756647186562]) bytes0496)
#guard case256 == some true

-- WithdrawalRequest/position/validatorPubkey/31
private def case257 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0497)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0497.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0497, .uint 1161981756647186562]) bytes0498)
#guard case257 == some true

-- WithdrawalRequest/position/validatorPubkey/32
private def case258 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0499)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0499.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0499, .uint 1161981756647186562]) bytes0500)
#guard case258 == some true

-- WithdrawalRequest/position/validatorPubkey/33
private def case259 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0501)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0501.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0501, .uint 1161981756647186562]) bytes0502)
#guard case259 == some true

-- WithdrawalRequest/position/validatorPubkey/34
private def case260 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0503)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0503.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0503, .uint 1161981756647186562]) bytes0504)
#guard case260 == some true

-- WithdrawalRequest/position/validatorPubkey/35
private def case261 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0505)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0505.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0505, .uint 1161981756647186562]) bytes0506)
#guard case261 == some true

-- WithdrawalRequest/position/validatorPubkey/36
private def case262 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0507)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0507.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0507, .uint 1161981756647186562]) bytes0508)
#guard case262 == some true

-- WithdrawalRequest/position/validatorPubkey/37
private def case263 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0509)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0509.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0509, .uint 1161981756647186562]) bytes0510)
#guard case263 == some true

-- WithdrawalRequest/position/validatorPubkey/38
private def case264 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0511)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0511.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0511, .uint 1161981756647186562]) bytes0512)
#guard case264 == some true

-- WithdrawalRequest/position/validatorPubkey/39
private def case265 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0513)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0513.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0513, .uint 1161981756647186562]) bytes0514)
#guard case265 == some true

-- WithdrawalRequest/position/validatorPubkey/40
private def case266 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0515)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0515.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0515, .uint 1161981756647186562]) bytes0516)
#guard case266 == some true

-- WithdrawalRequest/position/validatorPubkey/41
private def case267 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0517)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0517.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0517, .uint 1161981756647186562]) bytes0518)
#guard case267 == some true

-- WithdrawalRequest/position/validatorPubkey/42
private def case268 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0519)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0519.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0519, .uint 1161981756647186562]) bytes0520)
#guard case268 == some true

-- WithdrawalRequest/position/validatorPubkey/43
private def case269 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0521)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0521.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0521, .uint 1161981756647186562]) bytes0522)
#guard case269 == some true

-- WithdrawalRequest/position/validatorPubkey/44
private def case270 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0523)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0523.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0523, .uint 1161981756647186562]) bytes0524)
#guard case270 == some true

-- WithdrawalRequest/position/validatorPubkey/45
private def case271 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0525)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0525.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0525, .uint 1161981756647186562]) bytes0526)
#guard case271 == some true

-- WithdrawalRequest/position/validatorPubkey/46
private def case272 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0527)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0527.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0527, .uint 1161981756647186562]) bytes0528)
#guard case272 == some true

-- WithdrawalRequest/position/validatorPubkey/47
private def case273 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0529)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0529.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0529, .uint 1161981756647186562]) bytes0530)
#guard case273 == some true

-- WithdrawalRequest/whole-field/validatorPubkey/0
private def case274 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0004)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0004.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0004, .uint 1161981756647186562]) bytes0531)
#guard case274 == some true

-- WithdrawalRequest/whole-field/validatorPubkey/255
private def case275 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0008)
  let amount ← U64.ofNat? 1161981756647186562
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0008.data.toList, .inr 1161981756647186562]
    (.container [.bytes bytes0386, .bytes bytes0008, .uint 1161981756647186562]) bytes0532)
#guard case275 == some true

-- WithdrawalRequest/uint/amount/0
private def case276 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 0
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0387.data.toList, .inr 0]
    (.container [.bytes bytes0386, .bytes bytes0387, .uint 0]) bytes0533)
#guard case276 == some true

-- WithdrawalRequest/uint/amount/1
private def case277 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 1
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0387.data.toList, .inr 1]
    (.container [.bytes bytes0386, .bytes bytes0387, .uint 1]) bytes0534)
#guard case277 == some true

-- WithdrawalRequest/uint/amount/255
private def case278 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 255
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0387.data.toList, .inr 255]
    (.container [.bytes bytes0386, .bytes bytes0387, .uint 255]) bytes0535)
#guard case278 == some true

-- WithdrawalRequest/uint/amount/256
private def case279 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 256
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0387.data.toList, .inr 256]
    (.container [.bytes bytes0386, .bytes bytes0387, .uint 256]) bytes0536)
#guard case279 == some true

-- WithdrawalRequest/uint/amount/4294967295
private def case280 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 4294967295
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0387.data.toList, .inr 4294967295]
    (.container [.bytes bytes0386, .bytes bytes0387, .uint 4294967295]) bytes0537)
#guard case280 == some true

-- WithdrawalRequest/uint/amount/4294967296
private def case281 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 4294967296
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0387.data.toList, .inr 4294967296]
    (.container [.bytes bytes0386, .bytes bytes0387, .uint 4294967296]) bytes0538)
#guard case281 == some true

-- WithdrawalRequest/uint/amount/9223372036854775808
private def case282 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 9223372036854775808
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0387.data.toList, .inr 9223372036854775808]
    (.container [.bytes bytes0386, .bytes bytes0387, .uint 9223372036854775808]) bytes0539)
#guard case282 == some true

-- WithdrawalRequest/uint/amount/18446744073709551615
private def case283 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0386)
  let validatorPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0387)
  let amount ← U64.ofNat? 18446744073709551615
  pure (WithdrawalRequest.check ⟨sourceAddress, validatorPubkey, amount⟩
    [.inl bytes0386.data.toList, .inl bytes0387.data.toList, .inr 18446744073709551615]
    (.container [.bytes bytes0386, .bytes bytes0387, .uint 18446744073709551615]) bytes0540)
#guard case283 == some true

-- ConsolidationRequest/asymmetric-baseline
private def case284 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0543]) bytes0544)
#guard case284 == some true

-- ConsolidationRequest/all-zero
private def case285 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0389)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0004)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0004)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0389.data.toList, .inl bytes0004.data.toList, .inl bytes0004.data.toList]
    (.container [.bytes bytes0389, .bytes bytes0004, .bytes bytes0004]) bytes0545)
#guard case285 == some true

-- ConsolidationRequest/all-ff-max
private def case286 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0391)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0008)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0008)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0391.data.toList, .inl bytes0008.data.toList, .inl bytes0008.data.toList]
    (.container [.bytes bytes0391, .bytes bytes0008, .bytes bytes0008]) bytes0546)
#guard case286 == some true

-- ConsolidationRequest/position/sourceAddress/0
private def case287 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0547)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0547.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0547, .bytes bytes0542, .bytes bytes0543]) bytes0548)
#guard case287 == some true

-- ConsolidationRequest/position/sourceAddress/1
private def case288 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0549)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0549.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0549, .bytes bytes0542, .bytes bytes0543]) bytes0550)
#guard case288 == some true

-- ConsolidationRequest/position/sourceAddress/2
private def case289 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0551)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0551.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0551, .bytes bytes0542, .bytes bytes0543]) bytes0552)
#guard case289 == some true

-- ConsolidationRequest/position/sourceAddress/3
private def case290 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0553)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0553.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0553, .bytes bytes0542, .bytes bytes0543]) bytes0554)
#guard case290 == some true

-- ConsolidationRequest/position/sourceAddress/4
private def case291 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0555)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0555.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0555, .bytes bytes0542, .bytes bytes0543]) bytes0556)
#guard case291 == some true

-- ConsolidationRequest/position/sourceAddress/5
private def case292 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0557)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0557.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0557, .bytes bytes0542, .bytes bytes0543]) bytes0558)
#guard case292 == some true

-- ConsolidationRequest/position/sourceAddress/6
private def case293 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0559)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0559.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0559, .bytes bytes0542, .bytes bytes0543]) bytes0560)
#guard case293 == some true

-- ConsolidationRequest/position/sourceAddress/7
private def case294 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0561)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0561.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0561, .bytes bytes0542, .bytes bytes0543]) bytes0562)
#guard case294 == some true

-- ConsolidationRequest/position/sourceAddress/8
private def case295 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0563)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0563.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0563, .bytes bytes0542, .bytes bytes0543]) bytes0564)
#guard case295 == some true

-- ConsolidationRequest/position/sourceAddress/9
private def case296 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0565)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0565.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0565, .bytes bytes0542, .bytes bytes0543]) bytes0566)
#guard case296 == some true

-- ConsolidationRequest/position/sourceAddress/10
private def case297 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0567)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0567.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0567, .bytes bytes0542, .bytes bytes0543]) bytes0568)
#guard case297 == some true

-- ConsolidationRequest/position/sourceAddress/11
private def case298 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0569)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0569.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0569, .bytes bytes0542, .bytes bytes0543]) bytes0570)
#guard case298 == some true

-- ConsolidationRequest/position/sourceAddress/12
private def case299 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0571)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0571.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0571, .bytes bytes0542, .bytes bytes0543]) bytes0572)
#guard case299 == some true

-- ConsolidationRequest/position/sourceAddress/13
private def case300 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0573)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0573.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0573, .bytes bytes0542, .bytes bytes0543]) bytes0574)
#guard case300 == some true

-- ConsolidationRequest/position/sourceAddress/14
private def case301 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0575)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0575.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0575, .bytes bytes0542, .bytes bytes0543]) bytes0576)
#guard case301 == some true

-- ConsolidationRequest/position/sourceAddress/15
private def case302 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0577)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0577.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0577, .bytes bytes0542, .bytes bytes0543]) bytes0578)
#guard case302 == some true

-- ConsolidationRequest/position/sourceAddress/16
private def case303 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0579)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0579.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0579, .bytes bytes0542, .bytes bytes0543]) bytes0580)
#guard case303 == some true

-- ConsolidationRequest/position/sourceAddress/17
private def case304 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0581)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0581.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0581, .bytes bytes0542, .bytes bytes0543]) bytes0582)
#guard case304 == some true

-- ConsolidationRequest/position/sourceAddress/18
private def case305 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0583)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0583.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0583, .bytes bytes0542, .bytes bytes0543]) bytes0584)
#guard case305 == some true

-- ConsolidationRequest/position/sourceAddress/19
private def case306 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0585)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0585.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0585, .bytes bytes0542, .bytes bytes0543]) bytes0586)
#guard case306 == some true

-- ConsolidationRequest/whole-field/sourceAddress/0
private def case307 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0389)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0389.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0389, .bytes bytes0542, .bytes bytes0543]) bytes0587)
#guard case307 == some true

-- ConsolidationRequest/whole-field/sourceAddress/255
private def case308 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0391)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0391.data.toList, .inl bytes0542.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0391, .bytes bytes0542, .bytes bytes0543]) bytes0588)
#guard case308 == some true

-- ConsolidationRequest/position/sourcePubkey/0
private def case309 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0589)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0589.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0589, .bytes bytes0543]) bytes0590)
#guard case309 == some true

-- ConsolidationRequest/position/sourcePubkey/1
private def case310 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0591)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0591.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0591, .bytes bytes0543]) bytes0592)
#guard case310 == some true

-- ConsolidationRequest/position/sourcePubkey/2
private def case311 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0593)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0593.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0593, .bytes bytes0543]) bytes0594)
#guard case311 == some true

-- ConsolidationRequest/position/sourcePubkey/3
private def case312 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0595)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0595.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0595, .bytes bytes0543]) bytes0596)
#guard case312 == some true

-- ConsolidationRequest/position/sourcePubkey/4
private def case313 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0597)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0597.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0597, .bytes bytes0543]) bytes0598)
#guard case313 == some true

-- ConsolidationRequest/position/sourcePubkey/5
private def case314 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0599)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0599.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0599, .bytes bytes0543]) bytes0600)
#guard case314 == some true

-- ConsolidationRequest/position/sourcePubkey/6
private def case315 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0601)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0601.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0601, .bytes bytes0543]) bytes0602)
#guard case315 == some true

-- ConsolidationRequest/position/sourcePubkey/7
private def case316 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0603)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0603.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0603, .bytes bytes0543]) bytes0604)
#guard case316 == some true

-- ConsolidationRequest/position/sourcePubkey/8
private def case317 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0605)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0605.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0605, .bytes bytes0543]) bytes0606)
#guard case317 == some true

-- ConsolidationRequest/position/sourcePubkey/9
private def case318 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0607)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0607.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0607, .bytes bytes0543]) bytes0608)
#guard case318 == some true

-- ConsolidationRequest/position/sourcePubkey/10
private def case319 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0609)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0609.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0609, .bytes bytes0543]) bytes0610)
#guard case319 == some true

-- ConsolidationRequest/position/sourcePubkey/11
private def case320 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0611)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0611.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0611, .bytes bytes0543]) bytes0612)
#guard case320 == some true

-- ConsolidationRequest/position/sourcePubkey/12
private def case321 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0613)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0613.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0613, .bytes bytes0543]) bytes0614)
#guard case321 == some true

-- ConsolidationRequest/position/sourcePubkey/13
private def case322 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0615)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0615.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0615, .bytes bytes0543]) bytes0616)
#guard case322 == some true

-- ConsolidationRequest/position/sourcePubkey/14
private def case323 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0617)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0617.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0617, .bytes bytes0543]) bytes0618)
#guard case323 == some true

-- ConsolidationRequest/position/sourcePubkey/15
private def case324 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0619)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0619.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0619, .bytes bytes0543]) bytes0620)
#guard case324 == some true

-- ConsolidationRequest/position/sourcePubkey/16
private def case325 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0621)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0621.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0621, .bytes bytes0543]) bytes0622)
#guard case325 == some true

-- ConsolidationRequest/position/sourcePubkey/17
private def case326 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0623)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0623.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0623, .bytes bytes0543]) bytes0624)
#guard case326 == some true

-- ConsolidationRequest/position/sourcePubkey/18
private def case327 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0625)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0625.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0625, .bytes bytes0543]) bytes0626)
#guard case327 == some true

-- ConsolidationRequest/position/sourcePubkey/19
private def case328 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0627)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0627.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0627, .bytes bytes0543]) bytes0628)
#guard case328 == some true

-- ConsolidationRequest/position/sourcePubkey/20
private def case329 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0629)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0629.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0629, .bytes bytes0543]) bytes0630)
#guard case329 == some true

-- ConsolidationRequest/position/sourcePubkey/21
private def case330 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0631)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0631.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0631, .bytes bytes0543]) bytes0632)
#guard case330 == some true

-- ConsolidationRequest/position/sourcePubkey/22
private def case331 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0633)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0633.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0633, .bytes bytes0543]) bytes0634)
#guard case331 == some true

-- ConsolidationRequest/position/sourcePubkey/23
private def case332 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0635)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0635.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0635, .bytes bytes0543]) bytes0636)
#guard case332 == some true

-- ConsolidationRequest/position/sourcePubkey/24
private def case333 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0637)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0637.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0637, .bytes bytes0543]) bytes0638)
#guard case333 == some true

-- ConsolidationRequest/position/sourcePubkey/25
private def case334 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0639)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0639.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0639, .bytes bytes0543]) bytes0640)
#guard case334 == some true

-- ConsolidationRequest/position/sourcePubkey/26
private def case335 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0641)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0641.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0641, .bytes bytes0543]) bytes0642)
#guard case335 == some true

-- ConsolidationRequest/position/sourcePubkey/27
private def case336 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0643)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0643.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0643, .bytes bytes0543]) bytes0644)
#guard case336 == some true

-- ConsolidationRequest/position/sourcePubkey/28
private def case337 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0645)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0645.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0645, .bytes bytes0543]) bytes0646)
#guard case337 == some true

-- ConsolidationRequest/position/sourcePubkey/29
private def case338 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0647)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0647.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0647, .bytes bytes0543]) bytes0648)
#guard case338 == some true

-- ConsolidationRequest/position/sourcePubkey/30
private def case339 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0649)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0649.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0649, .bytes bytes0543]) bytes0650)
#guard case339 == some true

-- ConsolidationRequest/position/sourcePubkey/31
private def case340 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0651)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0651.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0651, .bytes bytes0543]) bytes0652)
#guard case340 == some true

-- ConsolidationRequest/position/sourcePubkey/32
private def case341 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0653)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0653.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0653, .bytes bytes0543]) bytes0654)
#guard case341 == some true

-- ConsolidationRequest/position/sourcePubkey/33
private def case342 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0655)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0655.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0655, .bytes bytes0543]) bytes0656)
#guard case342 == some true

-- ConsolidationRequest/position/sourcePubkey/34
private def case343 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0657)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0657.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0657, .bytes bytes0543]) bytes0658)
#guard case343 == some true

-- ConsolidationRequest/position/sourcePubkey/35
private def case344 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0659)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0659.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0659, .bytes bytes0543]) bytes0660)
#guard case344 == some true

-- ConsolidationRequest/position/sourcePubkey/36
private def case345 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0661)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0661.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0661, .bytes bytes0543]) bytes0662)
#guard case345 == some true

-- ConsolidationRequest/position/sourcePubkey/37
private def case346 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0663)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0663.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0663, .bytes bytes0543]) bytes0664)
#guard case346 == some true

-- ConsolidationRequest/position/sourcePubkey/38
private def case347 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0665)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0665.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0665, .bytes bytes0543]) bytes0666)
#guard case347 == some true

-- ConsolidationRequest/position/sourcePubkey/39
private def case348 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0667)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0667.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0667, .bytes bytes0543]) bytes0668)
#guard case348 == some true

-- ConsolidationRequest/position/sourcePubkey/40
private def case349 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0669)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0669.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0669, .bytes bytes0543]) bytes0670)
#guard case349 == some true

-- ConsolidationRequest/position/sourcePubkey/41
private def case350 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0671)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0671.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0671, .bytes bytes0543]) bytes0672)
#guard case350 == some true

-- ConsolidationRequest/position/sourcePubkey/42
private def case351 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0673)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0673.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0673, .bytes bytes0543]) bytes0674)
#guard case351 == some true

-- ConsolidationRequest/position/sourcePubkey/43
private def case352 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0675)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0675.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0675, .bytes bytes0543]) bytes0676)
#guard case352 == some true

-- ConsolidationRequest/position/sourcePubkey/44
private def case353 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0677)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0677.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0677, .bytes bytes0543]) bytes0678)
#guard case353 == some true

-- ConsolidationRequest/position/sourcePubkey/45
private def case354 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0679)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0679.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0679, .bytes bytes0543]) bytes0680)
#guard case354 == some true

-- ConsolidationRequest/position/sourcePubkey/46
private def case355 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0681)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0681.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0681, .bytes bytes0543]) bytes0682)
#guard case355 == some true

-- ConsolidationRequest/position/sourcePubkey/47
private def case356 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0683)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0683.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0683, .bytes bytes0543]) bytes0684)
#guard case356 == some true

-- ConsolidationRequest/whole-field/sourcePubkey/0
private def case357 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0004)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0004.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0004, .bytes bytes0543]) bytes0685)
#guard case357 == some true

-- ConsolidationRequest/whole-field/sourcePubkey/255
private def case358 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0008)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0008.data.toList, .inl bytes0543.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0008, .bytes bytes0543]) bytes0686)
#guard case358 == some true

-- ConsolidationRequest/position/targetPubkey/0
private def case359 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0687)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0687.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0687]) bytes0688)
#guard case359 == some true

-- ConsolidationRequest/position/targetPubkey/1
private def case360 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0689)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0689.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0689]) bytes0690)
#guard case360 == some true

-- ConsolidationRequest/position/targetPubkey/2
private def case361 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0691)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0691.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0691]) bytes0692)
#guard case361 == some true

-- ConsolidationRequest/position/targetPubkey/3
private def case362 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0693)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0693.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0693]) bytes0694)
#guard case362 == some true

-- ConsolidationRequest/position/targetPubkey/4
private def case363 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0695)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0695.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0695]) bytes0696)
#guard case363 == some true

-- ConsolidationRequest/position/targetPubkey/5
private def case364 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0697)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0697.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0697]) bytes0698)
#guard case364 == some true

-- ConsolidationRequest/position/targetPubkey/6
private def case365 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0699)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0699.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0699]) bytes0700)
#guard case365 == some true

-- ConsolidationRequest/position/targetPubkey/7
private def case366 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0701)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0701.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0701]) bytes0702)
#guard case366 == some true

-- ConsolidationRequest/position/targetPubkey/8
private def case367 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0703)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0703.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0703]) bytes0704)
#guard case367 == some true

-- ConsolidationRequest/position/targetPubkey/9
private def case368 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0705)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0705.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0705]) bytes0706)
#guard case368 == some true

-- ConsolidationRequest/position/targetPubkey/10
private def case369 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0707)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0707.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0707]) bytes0708)
#guard case369 == some true

-- ConsolidationRequest/position/targetPubkey/11
private def case370 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0709)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0709.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0709]) bytes0710)
#guard case370 == some true

-- ConsolidationRequest/position/targetPubkey/12
private def case371 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0711)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0711.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0711]) bytes0712)
#guard case371 == some true

-- ConsolidationRequest/position/targetPubkey/13
private def case372 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0713)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0713.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0713]) bytes0714)
#guard case372 == some true

-- ConsolidationRequest/position/targetPubkey/14
private def case373 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0715)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0715.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0715]) bytes0716)
#guard case373 == some true

-- ConsolidationRequest/position/targetPubkey/15
private def case374 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0717)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0717.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0717]) bytes0718)
#guard case374 == some true

-- ConsolidationRequest/position/targetPubkey/16
private def case375 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0719)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0719.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0719]) bytes0720)
#guard case375 == some true

-- ConsolidationRequest/position/targetPubkey/17
private def case376 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0721)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0721.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0721]) bytes0722)
#guard case376 == some true

-- ConsolidationRequest/position/targetPubkey/18
private def case377 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0723)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0723.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0723]) bytes0724)
#guard case377 == some true

-- ConsolidationRequest/position/targetPubkey/19
private def case378 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0725)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0725.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0725]) bytes0726)
#guard case378 == some true

-- ConsolidationRequest/position/targetPubkey/20
private def case379 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0727)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0727.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0727]) bytes0728)
#guard case379 == some true

-- ConsolidationRequest/position/targetPubkey/21
private def case380 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0729)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0729.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0729]) bytes0730)
#guard case380 == some true

-- ConsolidationRequest/position/targetPubkey/22
private def case381 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0731)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0731.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0731]) bytes0732)
#guard case381 == some true

-- ConsolidationRequest/position/targetPubkey/23
private def case382 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0733)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0733.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0733]) bytes0734)
#guard case382 == some true

-- ConsolidationRequest/position/targetPubkey/24
private def case383 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0735)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0735.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0735]) bytes0736)
#guard case383 == some true

-- ConsolidationRequest/position/targetPubkey/25
private def case384 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0737)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0737.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0737]) bytes0738)
#guard case384 == some true

-- ConsolidationRequest/position/targetPubkey/26
private def case385 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0739)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0739.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0739]) bytes0740)
#guard case385 == some true

-- ConsolidationRequest/position/targetPubkey/27
private def case386 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0741)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0741.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0741]) bytes0742)
#guard case386 == some true

-- ConsolidationRequest/position/targetPubkey/28
private def case387 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0743)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0743.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0743]) bytes0744)
#guard case387 == some true

-- ConsolidationRequest/position/targetPubkey/29
private def case388 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0745)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0745.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0745]) bytes0746)
#guard case388 == some true

-- ConsolidationRequest/position/targetPubkey/30
private def case389 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0747)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0747.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0747]) bytes0748)
#guard case389 == some true

-- ConsolidationRequest/position/targetPubkey/31
private def case390 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0749)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0749.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0749]) bytes0750)
#guard case390 == some true

-- ConsolidationRequest/position/targetPubkey/32
private def case391 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0751)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0751.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0751]) bytes0752)
#guard case391 == some true

-- ConsolidationRequest/position/targetPubkey/33
private def case392 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0753)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0753.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0753]) bytes0754)
#guard case392 == some true

-- ConsolidationRequest/position/targetPubkey/34
private def case393 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0755)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0755.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0755]) bytes0756)
#guard case393 == some true

-- ConsolidationRequest/position/targetPubkey/35
private def case394 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0757)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0757.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0757]) bytes0758)
#guard case394 == some true

-- ConsolidationRequest/position/targetPubkey/36
private def case395 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0759)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0759.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0759]) bytes0760)
#guard case395 == some true

-- ConsolidationRequest/position/targetPubkey/37
private def case396 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0761)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0761.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0761]) bytes0762)
#guard case396 == some true

-- ConsolidationRequest/position/targetPubkey/38
private def case397 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0763)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0763.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0763]) bytes0764)
#guard case397 == some true

-- ConsolidationRequest/position/targetPubkey/39
private def case398 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0765)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0765.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0765]) bytes0766)
#guard case398 == some true

-- ConsolidationRequest/position/targetPubkey/40
private def case399 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0767)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0767.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0767]) bytes0768)
#guard case399 == some true

-- ConsolidationRequest/position/targetPubkey/41
private def case400 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0769)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0769.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0769]) bytes0770)
#guard case400 == some true

-- ConsolidationRequest/position/targetPubkey/42
private def case401 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0771)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0771.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0771]) bytes0772)
#guard case401 == some true

-- ConsolidationRequest/position/targetPubkey/43
private def case402 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0773)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0773.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0773]) bytes0774)
#guard case402 == some true

-- ConsolidationRequest/position/targetPubkey/44
private def case403 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0775)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0775.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0775]) bytes0776)
#guard case403 == some true

-- ConsolidationRequest/position/targetPubkey/45
private def case404 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0777)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0777.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0777]) bytes0778)
#guard case404 == some true

-- ConsolidationRequest/position/targetPubkey/46
private def case405 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0779)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0779.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0779]) bytes0780)
#guard case405 == some true

-- ConsolidationRequest/position/targetPubkey/47
private def case406 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0781)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0781.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0781]) bytes0782)
#guard case406 == some true

-- ConsolidationRequest/whole-field/targetPubkey/0
private def case407 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0004)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0004.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0004]) bytes0783)
#guard case407 == some true

-- ConsolidationRequest/whole-field/targetPubkey/255
private def case408 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0008)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0542.data.toList, .inl bytes0008.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0542, .bytes bytes0008]) bytes0784)
#guard case408 == some true

-- BuilderDepositRequest/asymmetric-baseline
private def case409 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0788)
#guard case409 == some true

-- BuilderDepositRequest/all-zero
private def case410 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0004)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0005)
  let amount ← U64.ofNat? 0
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0006)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0004.data.toList, .inl bytes0005.data.toList, .inr 0, .inl bytes0006.data.toList]
    (.container [.bytes bytes0004, .bytes bytes0005, .uint 0, .bytes bytes0006]) bytes0789)
#guard case410 == some true

-- BuilderDepositRequest/all-ff-max
private def case411 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0008)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0009)
  let amount ← U64.ofNat? 18446744073709551615
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0010)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0008.data.toList, .inl bytes0009.data.toList, .inr 18446744073709551615,
      .inl bytes0010.data.toList]
    (.container [.bytes bytes0008, .bytes bytes0009, .uint 18446744073709551615,
      .bytes bytes0010]) bytes0790)
#guard case411 == some true

-- BuilderDepositRequest/position/pubkey/0
private def case412 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0791)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0791.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0791, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0792)
#guard case412 == some true

-- BuilderDepositRequest/position/pubkey/1
private def case413 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0793)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0793.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0793, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0794)
#guard case413 == some true

-- BuilderDepositRequest/position/pubkey/2
private def case414 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0795)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0795.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0795, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0796)
#guard case414 == some true

-- BuilderDepositRequest/position/pubkey/3
private def case415 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0797)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0797.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0797, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0798)
#guard case415 == some true

-- BuilderDepositRequest/position/pubkey/4
private def case416 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0799)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0799.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0799, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0800)
#guard case416 == some true

-- BuilderDepositRequest/position/pubkey/5
private def case417 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0801)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0801.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0801, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0802)
#guard case417 == some true

-- BuilderDepositRequest/position/pubkey/6
private def case418 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0803)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0803.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0803, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0804)
#guard case418 == some true

-- BuilderDepositRequest/position/pubkey/7
private def case419 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0805)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0805.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0805, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0806)
#guard case419 == some true

-- BuilderDepositRequest/position/pubkey/8
private def case420 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0807)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0807.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0807, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0808)
#guard case420 == some true

-- BuilderDepositRequest/position/pubkey/9
private def case421 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0809)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0809.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0809, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0810)
#guard case421 == some true

-- BuilderDepositRequest/position/pubkey/10
private def case422 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0811)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0811.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0811, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0812)
#guard case422 == some true

-- BuilderDepositRequest/position/pubkey/11
private def case423 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0813)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0813.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0813, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0814)
#guard case423 == some true

-- BuilderDepositRequest/position/pubkey/12
private def case424 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0815)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0815.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0815, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0816)
#guard case424 == some true

-- BuilderDepositRequest/position/pubkey/13
private def case425 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0817)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0817.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0817, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0818)
#guard case425 == some true

-- BuilderDepositRequest/position/pubkey/14
private def case426 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0819)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0819.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0819, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0820)
#guard case426 == some true

-- BuilderDepositRequest/position/pubkey/15
private def case427 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0821)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0821.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0821, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0822)
#guard case427 == some true

-- BuilderDepositRequest/position/pubkey/16
private def case428 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0823)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0823.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0823, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0824)
#guard case428 == some true

-- BuilderDepositRequest/position/pubkey/17
private def case429 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0825)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0825.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0825, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0826)
#guard case429 == some true

-- BuilderDepositRequest/position/pubkey/18
private def case430 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0827)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0827.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0827, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0828)
#guard case430 == some true

-- BuilderDepositRequest/position/pubkey/19
private def case431 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0829)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0829.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0829, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0830)
#guard case431 == some true

-- BuilderDepositRequest/position/pubkey/20
private def case432 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0831)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0831.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0831, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0832)
#guard case432 == some true

-- BuilderDepositRequest/position/pubkey/21
private def case433 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0833)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0833.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0833, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0834)
#guard case433 == some true

-- BuilderDepositRequest/position/pubkey/22
private def case434 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0835)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0835.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0835, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0836)
#guard case434 == some true

-- BuilderDepositRequest/position/pubkey/23
private def case435 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0837)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0837.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0837, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0838)
#guard case435 == some true

-- BuilderDepositRequest/position/pubkey/24
private def case436 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0839)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0839.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0839, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0840)
#guard case436 == some true

-- BuilderDepositRequest/position/pubkey/25
private def case437 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0841)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0841.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0841, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0842)
#guard case437 == some true

-- BuilderDepositRequest/position/pubkey/26
private def case438 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0843)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0843.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0843, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0844)
#guard case438 == some true

-- BuilderDepositRequest/position/pubkey/27
private def case439 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0845)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0845.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0845, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0846)
#guard case439 == some true

-- BuilderDepositRequest/position/pubkey/28
private def case440 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0847)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0847.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0847, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0848)
#guard case440 == some true

-- BuilderDepositRequest/position/pubkey/29
private def case441 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0849)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0849.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0849, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0850)
#guard case441 == some true

-- BuilderDepositRequest/position/pubkey/30
private def case442 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0851)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0851.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0851, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0852)
#guard case442 == some true

-- BuilderDepositRequest/position/pubkey/31
private def case443 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0853)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0853.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0853, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0854)
#guard case443 == some true

-- BuilderDepositRequest/position/pubkey/32
private def case444 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0855)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0855.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0855, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0856)
#guard case444 == some true

-- BuilderDepositRequest/position/pubkey/33
private def case445 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0857)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0857.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0857, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0858)
#guard case445 == some true

-- BuilderDepositRequest/position/pubkey/34
private def case446 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0859)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0859.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0859, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0860)
#guard case446 == some true

-- BuilderDepositRequest/position/pubkey/35
private def case447 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0861)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0861.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0861, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0862)
#guard case447 == some true

-- BuilderDepositRequest/position/pubkey/36
private def case448 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0863)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0863.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0863, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0864)
#guard case448 == some true

-- BuilderDepositRequest/position/pubkey/37
private def case449 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0865)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0865.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0865, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0866)
#guard case449 == some true

-- BuilderDepositRequest/position/pubkey/38
private def case450 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0867)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0867.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0867, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0868)
#guard case450 == some true

-- BuilderDepositRequest/position/pubkey/39
private def case451 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0869)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0869.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0869, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0870)
#guard case451 == some true

-- BuilderDepositRequest/position/pubkey/40
private def case452 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0871)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0871.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0871, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0872)
#guard case452 == some true

-- BuilderDepositRequest/position/pubkey/41
private def case453 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0873)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0873.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0873, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0874)
#guard case453 == some true

-- BuilderDepositRequest/position/pubkey/42
private def case454 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0875)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0875.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0875, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0876)
#guard case454 == some true

-- BuilderDepositRequest/position/pubkey/43
private def case455 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0877)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0877.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0877, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0878)
#guard case455 == some true

-- BuilderDepositRequest/position/pubkey/44
private def case456 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0879)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0879.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0879, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0880)
#guard case456 == some true

-- BuilderDepositRequest/position/pubkey/45
private def case457 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0881)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0881.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0881, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0882)
#guard case457 == some true

-- BuilderDepositRequest/position/pubkey/46
private def case458 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0883)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0883.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0883, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0884)
#guard case458 == some true

-- BuilderDepositRequest/position/pubkey/47
private def case459 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0885)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0885.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0885, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0886)
#guard case459 == some true

-- BuilderDepositRequest/whole-field/pubkey/0
private def case460 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0004)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0004.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0004, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0887)
#guard case460 == some true

-- BuilderDepositRequest/whole-field/pubkey/255
private def case461 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0008)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0008.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0008, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0888)
#guard case461 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/0
private def case462 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0889)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0889.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0889, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0890)
#guard case462 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/1
private def case463 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0891)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0891.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0891, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0892)
#guard case463 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/2
private def case464 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0893)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0893.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0893, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0894)
#guard case464 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/3
private def case465 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0895)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0895.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0895, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0896)
#guard case465 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/4
private def case466 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0897)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0897.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0897, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0898)
#guard case466 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/5
private def case467 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0899)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0899.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0899, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0900)
#guard case467 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/6
private def case468 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0901)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0901.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0901, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0902)
#guard case468 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/7
private def case469 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0903)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0903.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0903, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0904)
#guard case469 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/8
private def case470 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0905)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0905.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0905, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0906)
#guard case470 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/9
private def case471 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0907)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0907.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0907, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0908)
#guard case471 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/10
private def case472 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0909)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0909.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0909, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0910)
#guard case472 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/11
private def case473 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0911)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0911.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0911, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0912)
#guard case473 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/12
private def case474 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0913)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0913.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0913, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0914)
#guard case474 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/13
private def case475 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0915)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0915.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0915, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0916)
#guard case475 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/14
private def case476 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0917)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0917.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0917, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0918)
#guard case476 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/15
private def case477 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0919)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0919.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0919, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0920)
#guard case477 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/16
private def case478 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0921)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0921.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0921, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0922)
#guard case478 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/17
private def case479 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0923)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0923.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0923, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0924)
#guard case479 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/18
private def case480 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0925)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0925.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0925, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0926)
#guard case480 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/19
private def case481 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0927)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0927.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0927, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0928)
#guard case481 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/20
private def case482 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0929)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0929.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0929, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0930)
#guard case482 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/21
private def case483 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0931)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0931.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0931, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0932)
#guard case483 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/22
private def case484 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0933)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0933.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0933, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0934)
#guard case484 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/23
private def case485 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0935)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0935.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0935, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0936)
#guard case485 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/24
private def case486 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0937)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0937.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0937, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0938)
#guard case486 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/25
private def case487 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0939)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0939.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0939, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0940)
#guard case487 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/26
private def case488 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0941)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0941.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0941, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0942)
#guard case488 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/27
private def case489 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0943)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0943.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0943, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0944)
#guard case489 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/28
private def case490 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0945)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0945.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0945, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0946)
#guard case490 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/29
private def case491 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0947)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0947.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0947, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0948)
#guard case491 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/30
private def case492 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0949)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0949.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0949, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0950)
#guard case492 == some true

-- BuilderDepositRequest/position/withdrawalCredentials/31
private def case493 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0951)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0951.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0951, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0952)
#guard case493 == some true

-- BuilderDepositRequest/whole-field/withdrawalCredentials/0
private def case494 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0005)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0005.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0005, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0953)
#guard case494 == some true

-- BuilderDepositRequest/whole-field/withdrawalCredentials/255
private def case495 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0009)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0009.data.toList, .inr 1161981756649291906,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0009, .uint 1161981756649291906,
      .bytes bytes0787]) bytes0954)
#guard case495 == some true

-- BuilderDepositRequest/uint/amount/0
private def case496 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 0
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 0, .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 0, .bytes bytes0787]) bytes0955)
#guard case496 == some true

-- BuilderDepositRequest/uint/amount/1
private def case497 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1, .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1, .bytes bytes0787]) bytes0956)
#guard case497 == some true

-- BuilderDepositRequest/uint/amount/255
private def case498 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 255
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 255, .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 255, .bytes bytes0787]) bytes0957)
#guard case498 == some true

-- BuilderDepositRequest/uint/amount/256
private def case499 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 256
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 256, .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 256, .bytes bytes0787]) bytes0958)
#guard case499 == some true

-- BuilderDepositRequest/uint/amount/4294967295
private def case500 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 4294967295
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 4294967295,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 4294967295, .bytes bytes0787])
    bytes0959)
#guard case500 == some true

-- BuilderDepositRequest/uint/amount/4294967296
private def case501 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 4294967296
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 4294967296,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 4294967296, .bytes bytes0787])
    bytes0960)
#guard case501 == some true

-- BuilderDepositRequest/uint/amount/9223372036854775808
private def case502 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 9223372036854775808
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 9223372036854775808,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 9223372036854775808,
      .bytes bytes0787]) bytes0961)
#guard case502 == some true

-- BuilderDepositRequest/uint/amount/18446744073709551615
private def case503 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 18446744073709551615
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0787)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 18446744073709551615,
      .inl bytes0787.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 18446744073709551615,
      .bytes bytes0787]) bytes0962)
#guard case503 == some true

-- BuilderDepositRequest/position/signature/0
private def case504 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0963)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0963.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0963]) bytes0964)
#guard case504 == some true

-- BuilderDepositRequest/position/signature/1
private def case505 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0965)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0965.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0965]) bytes0966)
#guard case505 == some true

-- BuilderDepositRequest/position/signature/2
private def case506 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0967)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0967.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0967]) bytes0968)
#guard case506 == some true

-- BuilderDepositRequest/position/signature/3
private def case507 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0969)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0969.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0969]) bytes0970)
#guard case507 == some true

-- BuilderDepositRequest/position/signature/4
private def case508 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0971)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0971.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0971]) bytes0972)
#guard case508 == some true

-- BuilderDepositRequest/position/signature/5
private def case509 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0973)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0973.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0973]) bytes0974)
#guard case509 == some true

-- BuilderDepositRequest/position/signature/6
private def case510 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0975)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0975.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0975]) bytes0976)
#guard case510 == some true

-- BuilderDepositRequest/position/signature/7
private def case511 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0977)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0977.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0977]) bytes0978)
#guard case511 == some true

-- BuilderDepositRequest/position/signature/8
private def case512 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0979)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0979.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0979]) bytes0980)
#guard case512 == some true

-- BuilderDepositRequest/position/signature/9
private def case513 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0981)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0981.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0981]) bytes0982)
#guard case513 == some true

-- BuilderDepositRequest/position/signature/10
private def case514 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0983)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0983.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0983]) bytes0984)
#guard case514 == some true

-- BuilderDepositRequest/position/signature/11
private def case515 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0985)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0985.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0985]) bytes0986)
#guard case515 == some true

-- BuilderDepositRequest/position/signature/12
private def case516 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0987)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0987.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0987]) bytes0988)
#guard case516 == some true

-- BuilderDepositRequest/position/signature/13
private def case517 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0989)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0989.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0989]) bytes0990)
#guard case517 == some true

-- BuilderDepositRequest/position/signature/14
private def case518 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0991)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0991.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0991]) bytes0992)
#guard case518 == some true

-- BuilderDepositRequest/position/signature/15
private def case519 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0993)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0993.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0993]) bytes0994)
#guard case519 == some true

-- BuilderDepositRequest/position/signature/16
private def case520 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0995)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0995.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0995]) bytes0996)
#guard case520 == some true

-- BuilderDepositRequest/position/signature/17
private def case521 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0997)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0997.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0997]) bytes0998)
#guard case521 == some true

-- BuilderDepositRequest/position/signature/18
private def case522 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0999)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0999.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0999]) bytes1000)
#guard case522 == some true

-- BuilderDepositRequest/position/signature/19
private def case523 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1001)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1001.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1001]) bytes1002)
#guard case523 == some true

-- BuilderDepositRequest/position/signature/20
private def case524 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1003)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1003.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1003]) bytes1004)
#guard case524 == some true

-- BuilderDepositRequest/position/signature/21
private def case525 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1005)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1005.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1005]) bytes1006)
#guard case525 == some true

-- BuilderDepositRequest/position/signature/22
private def case526 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1007)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1007.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1007]) bytes1008)
#guard case526 == some true

-- BuilderDepositRequest/position/signature/23
private def case527 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1009)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1009.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1009]) bytes1010)
#guard case527 == some true

-- BuilderDepositRequest/position/signature/24
private def case528 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1011)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1011.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1011]) bytes1012)
#guard case528 == some true

-- BuilderDepositRequest/position/signature/25
private def case529 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1013)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1013.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1013]) bytes1014)
#guard case529 == some true

-- BuilderDepositRequest/position/signature/26
private def case530 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1015)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1015.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1015]) bytes1016)
#guard case530 == some true

-- BuilderDepositRequest/position/signature/27
private def case531 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1017)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1017.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1017]) bytes1018)
#guard case531 == some true

-- BuilderDepositRequest/position/signature/28
private def case532 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1019)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1019.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1019]) bytes1020)
#guard case532 == some true

-- BuilderDepositRequest/position/signature/29
private def case533 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1021)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1021.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1021]) bytes1022)
#guard case533 == some true

-- BuilderDepositRequest/position/signature/30
private def case534 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1023)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1023.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1023]) bytes1024)
#guard case534 == some true

-- BuilderDepositRequest/position/signature/31
private def case535 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1025)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1025.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1025]) bytes1026)
#guard case535 == some true

-- BuilderDepositRequest/position/signature/32
private def case536 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1027)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1027.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1027]) bytes1028)
#guard case536 == some true

-- BuilderDepositRequest/position/signature/33
private def case537 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1029)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1029.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1029]) bytes1030)
#guard case537 == some true

-- BuilderDepositRequest/position/signature/34
private def case538 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1031)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1031.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1031]) bytes1032)
#guard case538 == some true

-- BuilderDepositRequest/position/signature/35
private def case539 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1033)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1033.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1033]) bytes1034)
#guard case539 == some true

-- BuilderDepositRequest/position/signature/36
private def case540 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1035)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1035.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1035]) bytes1036)
#guard case540 == some true

-- BuilderDepositRequest/position/signature/37
private def case541 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1037)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1037.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1037]) bytes1038)
#guard case541 == some true

-- BuilderDepositRequest/position/signature/38
private def case542 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1039)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1039.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1039]) bytes1040)
#guard case542 == some true

-- BuilderDepositRequest/position/signature/39
private def case543 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1041)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1041.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1041]) bytes1042)
#guard case543 == some true

-- BuilderDepositRequest/position/signature/40
private def case544 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1043)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1043.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1043]) bytes1044)
#guard case544 == some true

-- BuilderDepositRequest/position/signature/41
private def case545 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1045)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1045.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1045]) bytes1046)
#guard case545 == some true

-- BuilderDepositRequest/position/signature/42
private def case546 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1047)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1047.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1047]) bytes1048)
#guard case546 == some true

-- BuilderDepositRequest/position/signature/43
private def case547 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1049)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1049.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1049]) bytes1050)
#guard case547 == some true

-- BuilderDepositRequest/position/signature/44
private def case548 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1051)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1051.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1051]) bytes1052)
#guard case548 == some true

-- BuilderDepositRequest/position/signature/45
private def case549 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1053)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1053.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1053]) bytes1054)
#guard case549 == some true

-- BuilderDepositRequest/position/signature/46
private def case550 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1055)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1055.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1055]) bytes1056)
#guard case550 == some true

-- BuilderDepositRequest/position/signature/47
private def case551 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1057)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1057.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1057]) bytes1058)
#guard case551 == some true

-- BuilderDepositRequest/position/signature/48
private def case552 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1059)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1059.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1059]) bytes1060)
#guard case552 == some true

-- BuilderDepositRequest/position/signature/49
private def case553 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1061)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1061.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1061]) bytes1062)
#guard case553 == some true

-- BuilderDepositRequest/position/signature/50
private def case554 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1063)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1063.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1063]) bytes1064)
#guard case554 == some true

-- BuilderDepositRequest/position/signature/51
private def case555 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1065)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1065.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1065]) bytes1066)
#guard case555 == some true

-- BuilderDepositRequest/position/signature/52
private def case556 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1067)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1067.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1067]) bytes1068)
#guard case556 == some true

-- BuilderDepositRequest/position/signature/53
private def case557 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1069)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1069.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1069]) bytes1070)
#guard case557 == some true

-- BuilderDepositRequest/position/signature/54
private def case558 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1071)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1071.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1071]) bytes1072)
#guard case558 == some true

-- BuilderDepositRequest/position/signature/55
private def case559 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1073)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1073.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1073]) bytes1074)
#guard case559 == some true

-- BuilderDepositRequest/position/signature/56
private def case560 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1075)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1075.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1075]) bytes1076)
#guard case560 == some true

-- BuilderDepositRequest/position/signature/57
private def case561 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1077)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1077.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1077]) bytes1078)
#guard case561 == some true

-- BuilderDepositRequest/position/signature/58
private def case562 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1079)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1079.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1079]) bytes1080)
#guard case562 == some true

-- BuilderDepositRequest/position/signature/59
private def case563 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1081)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1081.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1081]) bytes1082)
#guard case563 == some true

-- BuilderDepositRequest/position/signature/60
private def case564 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1083)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1083.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1083]) bytes1084)
#guard case564 == some true

-- BuilderDepositRequest/position/signature/61
private def case565 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1085)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1085.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1085]) bytes1086)
#guard case565 == some true

-- BuilderDepositRequest/position/signature/62
private def case566 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1087)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1087.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1087]) bytes1088)
#guard case566 == some true

-- BuilderDepositRequest/position/signature/63
private def case567 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1089)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1089.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1089]) bytes1090)
#guard case567 == some true

-- BuilderDepositRequest/position/signature/64
private def case568 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1091)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1091.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1091]) bytes1092)
#guard case568 == some true

-- BuilderDepositRequest/position/signature/65
private def case569 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1093)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1093.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1093]) bytes1094)
#guard case569 == some true

-- BuilderDepositRequest/position/signature/66
private def case570 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1095)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1095.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1095]) bytes1096)
#guard case570 == some true

-- BuilderDepositRequest/position/signature/67
private def case571 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1097)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1097.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1097]) bytes1098)
#guard case571 == some true

-- BuilderDepositRequest/position/signature/68
private def case572 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1099)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1099.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1099]) bytes1100)
#guard case572 == some true

-- BuilderDepositRequest/position/signature/69
private def case573 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1101)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1101.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1101]) bytes1102)
#guard case573 == some true

-- BuilderDepositRequest/position/signature/70
private def case574 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1103)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1103.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1103]) bytes1104)
#guard case574 == some true

-- BuilderDepositRequest/position/signature/71
private def case575 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1105)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1105.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1105]) bytes1106)
#guard case575 == some true

-- BuilderDepositRequest/position/signature/72
private def case576 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1107)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1107.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1107]) bytes1108)
#guard case576 == some true

-- BuilderDepositRequest/position/signature/73
private def case577 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1109)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1109.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1109]) bytes1110)
#guard case577 == some true

-- BuilderDepositRequest/position/signature/74
private def case578 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1111)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1111.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1111]) bytes1112)
#guard case578 == some true

-- BuilderDepositRequest/position/signature/75
private def case579 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1113)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1113.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1113]) bytes1114)
#guard case579 == some true

-- BuilderDepositRequest/position/signature/76
private def case580 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1115)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1115.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1115]) bytes1116)
#guard case580 == some true

-- BuilderDepositRequest/position/signature/77
private def case581 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1117)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1117.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1117]) bytes1118)
#guard case581 == some true

-- BuilderDepositRequest/position/signature/78
private def case582 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1119)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1119.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1119]) bytes1120)
#guard case582 == some true

-- BuilderDepositRequest/position/signature/79
private def case583 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1121)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1121.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1121]) bytes1122)
#guard case583 == some true

-- BuilderDepositRequest/position/signature/80
private def case584 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1123)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1123.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1123]) bytes1124)
#guard case584 == some true

-- BuilderDepositRequest/position/signature/81
private def case585 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1125)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1125.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1125]) bytes1126)
#guard case585 == some true

-- BuilderDepositRequest/position/signature/82
private def case586 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1127)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1127.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1127]) bytes1128)
#guard case586 == some true

-- BuilderDepositRequest/position/signature/83
private def case587 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1129)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1129.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1129]) bytes1130)
#guard case587 == some true

-- BuilderDepositRequest/position/signature/84
private def case588 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1131)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1131.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1131]) bytes1132)
#guard case588 == some true

-- BuilderDepositRequest/position/signature/85
private def case589 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1133)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1133.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1133]) bytes1134)
#guard case589 == some true

-- BuilderDepositRequest/position/signature/86
private def case590 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1135)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1135.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1135]) bytes1136)
#guard case590 == some true

-- BuilderDepositRequest/position/signature/87
private def case591 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1137)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1137.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1137]) bytes1138)
#guard case591 == some true

-- BuilderDepositRequest/position/signature/88
private def case592 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1139)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1139.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1139]) bytes1140)
#guard case592 == some true

-- BuilderDepositRequest/position/signature/89
private def case593 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1141)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1141.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1141]) bytes1142)
#guard case593 == some true

-- BuilderDepositRequest/position/signature/90
private def case594 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1143)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1143.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1143]) bytes1144)
#guard case594 == some true

-- BuilderDepositRequest/position/signature/91
private def case595 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1145)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1145.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1145]) bytes1146)
#guard case595 == some true

-- BuilderDepositRequest/position/signature/92
private def case596 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1147)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1147.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1147]) bytes1148)
#guard case596 == some true

-- BuilderDepositRequest/position/signature/93
private def case597 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1149)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1149.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1149]) bytes1150)
#guard case597 == some true

-- BuilderDepositRequest/position/signature/94
private def case598 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1151)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1151.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1151]) bytes1152)
#guard case598 == some true

-- BuilderDepositRequest/position/signature/95
private def case599 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes1153)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes1153.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes1153]) bytes1154)
#guard case599 == some true

-- BuilderDepositRequest/whole-field/signature/0
private def case600 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0006)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0006.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0006]) bytes1155)
#guard case600 == some true

-- BuilderDepositRequest/whole-field/signature/255
private def case601 : Option Bool := do
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0785)
  let withdrawalCredentials ← FixedBytes.ofBytes? (n := 32) (Bytes.ofByteArray bytes0786)
  let amount ← U64.ofNat? 1161981756649291906
  let signature ← FixedBytes.ofBytes? (n := 96) (Bytes.ofByteArray bytes0010)
  pure (BuilderDepositRequest.check ⟨pubkey, withdrawalCredentials, amount, signature⟩
    [.inl bytes0785.data.toList, .inl bytes0786.data.toList, .inr 1161981756649291906,
      .inl bytes0010.data.toList]
    (.container [.bytes bytes0785, .bytes bytes0786, .uint 1161981756649291906,
      .bytes bytes0010]) bytes1156)
#guard case601 == some true

-- BuilderExitRequest/asymmetric-baseline
private def case602 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1158]) bytes1159)
#guard case602 == some true

-- BuilderExitRequest/all-zero
private def case603 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0389)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0004)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes0389.data.toList, .inl bytes0004.data.toList]
    (.container [.bytes bytes0389, .bytes bytes0004]) bytes1160)
#guard case603 == some true

-- BuilderExitRequest/all-ff-max
private def case604 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0391)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0008)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes0391.data.toList, .inl bytes0008.data.toList]
    (.container [.bytes bytes0391, .bytes bytes0008]) bytes1161)
#guard case604 == some true

-- BuilderExitRequest/position/sourceAddress/0
private def case605 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1162)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1162.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes1162, .bytes bytes1158]) bytes1163)
#guard case605 == some true

-- BuilderExitRequest/position/sourceAddress/1
private def case606 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1164)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1164.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes1164, .bytes bytes1158]) bytes1165)
#guard case606 == some true

-- BuilderExitRequest/position/sourceAddress/2
private def case607 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1166)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1166.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes1166, .bytes bytes1158]) bytes1167)
#guard case607 == some true

-- BuilderExitRequest/position/sourceAddress/3
private def case608 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1168)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1168.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes1168, .bytes bytes1158]) bytes1169)
#guard case608 == some true

-- BuilderExitRequest/position/sourceAddress/4
private def case609 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1170)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1170.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes1170, .bytes bytes1158]) bytes1171)
#guard case609 == some true

-- BuilderExitRequest/position/sourceAddress/5
private def case610 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1172)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1172.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes1172, .bytes bytes1158]) bytes1173)
#guard case610 == some true

-- BuilderExitRequest/position/sourceAddress/6
private def case611 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1174)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1174.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes1174, .bytes bytes1158]) bytes1175)
#guard case611 == some true

-- BuilderExitRequest/position/sourceAddress/7
private def case612 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1176)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1176.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes1176, .bytes bytes1158]) bytes1177)
#guard case612 == some true

-- BuilderExitRequest/position/sourceAddress/8
private def case613 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1178)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1178.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes1178, .bytes bytes1158]) bytes1179)
#guard case613 == some true

-- BuilderExitRequest/position/sourceAddress/9
private def case614 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1180)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1180.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes1180, .bytes bytes1158]) bytes1181)
#guard case614 == some true

-- BuilderExitRequest/position/sourceAddress/10
private def case615 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1182)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1182.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes1182, .bytes bytes1158]) bytes1183)
#guard case615 == some true

-- BuilderExitRequest/position/sourceAddress/11
private def case616 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1184)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1184.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes1184, .bytes bytes1158]) bytes1185)
#guard case616 == some true

-- BuilderExitRequest/position/sourceAddress/12
private def case617 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1186)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1186.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes1186, .bytes bytes1158]) bytes1187)
#guard case617 == some true

-- BuilderExitRequest/position/sourceAddress/13
private def case618 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1188)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1188.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes1188, .bytes bytes1158]) bytes1189)
#guard case618 == some true

-- BuilderExitRequest/position/sourceAddress/14
private def case619 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1190)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1190.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes1190, .bytes bytes1158]) bytes1191)
#guard case619 == some true

-- BuilderExitRequest/position/sourceAddress/15
private def case620 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1192)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1192.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes1192, .bytes bytes1158]) bytes1193)
#guard case620 == some true

-- BuilderExitRequest/position/sourceAddress/16
private def case621 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1194)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1194.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes1194, .bytes bytes1158]) bytes1195)
#guard case621 == some true

-- BuilderExitRequest/position/sourceAddress/17
private def case622 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1196)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1196.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes1196, .bytes bytes1158]) bytes1197)
#guard case622 == some true

-- BuilderExitRequest/position/sourceAddress/18
private def case623 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1198)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1198.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes1198, .bytes bytes1158]) bytes1199)
#guard case623 == some true

-- BuilderExitRequest/position/sourceAddress/19
private def case624 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1200)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1200.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes1200, .bytes bytes1158]) bytes1201)
#guard case624 == some true

-- BuilderExitRequest/whole-field/sourceAddress/0
private def case625 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0389)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes0389.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes0389, .bytes bytes1158]) bytes1202)
#guard case625 == some true

-- BuilderExitRequest/whole-field/sourceAddress/255
private def case626 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0391)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1158)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes0391.data.toList, .inl bytes1158.data.toList]
    (.container [.bytes bytes0391, .bytes bytes1158]) bytes1203)
#guard case626 == some true

-- BuilderExitRequest/position/pubkey/0
private def case627 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1204)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1204.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1204]) bytes1205)
#guard case627 == some true

-- BuilderExitRequest/position/pubkey/1
private def case628 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1206)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1206.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1206]) bytes1207)
#guard case628 == some true

-- BuilderExitRequest/position/pubkey/2
private def case629 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1208)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1208.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1208]) bytes1209)
#guard case629 == some true

-- BuilderExitRequest/position/pubkey/3
private def case630 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1210)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1210.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1210]) bytes1211)
#guard case630 == some true

-- BuilderExitRequest/position/pubkey/4
private def case631 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1212)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1212.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1212]) bytes1213)
#guard case631 == some true

-- BuilderExitRequest/position/pubkey/5
private def case632 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1214)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1214.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1214]) bytes1215)
#guard case632 == some true

-- BuilderExitRequest/position/pubkey/6
private def case633 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1216)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1216.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1216]) bytes1217)
#guard case633 == some true

-- BuilderExitRequest/position/pubkey/7
private def case634 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1218)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1218.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1218]) bytes1219)
#guard case634 == some true

-- BuilderExitRequest/position/pubkey/8
private def case635 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1220)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1220.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1220]) bytes1221)
#guard case635 == some true

-- BuilderExitRequest/position/pubkey/9
private def case636 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1222)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1222.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1222]) bytes1223)
#guard case636 == some true

-- BuilderExitRequest/position/pubkey/10
private def case637 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1224)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1224.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1224]) bytes1225)
#guard case637 == some true

-- BuilderExitRequest/position/pubkey/11
private def case638 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1226)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1226.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1226]) bytes1227)
#guard case638 == some true

-- BuilderExitRequest/position/pubkey/12
private def case639 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1228)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1228.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1228]) bytes1229)
#guard case639 == some true

-- BuilderExitRequest/position/pubkey/13
private def case640 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1230)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1230.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1230]) bytes1231)
#guard case640 == some true

-- BuilderExitRequest/position/pubkey/14
private def case641 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1232)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1232.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1232]) bytes1233)
#guard case641 == some true

-- BuilderExitRequest/position/pubkey/15
private def case642 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1234)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1234.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1234]) bytes1235)
#guard case642 == some true

-- BuilderExitRequest/position/pubkey/16
private def case643 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1236)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1236.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1236]) bytes1237)
#guard case643 == some true

-- BuilderExitRequest/position/pubkey/17
private def case644 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1238)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1238.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1238]) bytes1239)
#guard case644 == some true

-- BuilderExitRequest/position/pubkey/18
private def case645 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1240)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1240.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1240]) bytes1241)
#guard case645 == some true

-- BuilderExitRequest/position/pubkey/19
private def case646 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1242)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1242.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1242]) bytes1243)
#guard case646 == some true

-- BuilderExitRequest/position/pubkey/20
private def case647 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1244)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1244.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1244]) bytes1245)
#guard case647 == some true

-- BuilderExitRequest/position/pubkey/21
private def case648 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1246)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1246.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1246]) bytes1247)
#guard case648 == some true

-- BuilderExitRequest/position/pubkey/22
private def case649 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1248)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1248.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1248]) bytes1249)
#guard case649 == some true

-- BuilderExitRequest/position/pubkey/23
private def case650 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1250)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1250.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1250]) bytes1251)
#guard case650 == some true

-- BuilderExitRequest/position/pubkey/24
private def case651 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1252)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1252.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1252]) bytes1253)
#guard case651 == some true

-- BuilderExitRequest/position/pubkey/25
private def case652 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1254)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1254.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1254]) bytes1255)
#guard case652 == some true

-- BuilderExitRequest/position/pubkey/26
private def case653 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1256)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1256.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1256]) bytes1257)
#guard case653 == some true

-- BuilderExitRequest/position/pubkey/27
private def case654 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1258)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1258.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1258]) bytes1259)
#guard case654 == some true

-- BuilderExitRequest/position/pubkey/28
private def case655 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1260)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1260.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1260]) bytes1261)
#guard case655 == some true

-- BuilderExitRequest/position/pubkey/29
private def case656 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1262)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1262.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1262]) bytes1263)
#guard case656 == some true

-- BuilderExitRequest/position/pubkey/30
private def case657 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1264)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1264.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1264]) bytes1265)
#guard case657 == some true

-- BuilderExitRequest/position/pubkey/31
private def case658 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1266)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1266.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1266]) bytes1267)
#guard case658 == some true

-- BuilderExitRequest/position/pubkey/32
private def case659 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1268)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1268.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1268]) bytes1269)
#guard case659 == some true

-- BuilderExitRequest/position/pubkey/33
private def case660 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1270)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1270.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1270]) bytes1271)
#guard case660 == some true

-- BuilderExitRequest/position/pubkey/34
private def case661 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1272)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1272.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1272]) bytes1273)
#guard case661 == some true

-- BuilderExitRequest/position/pubkey/35
private def case662 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1274)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1274.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1274]) bytes1275)
#guard case662 == some true

-- BuilderExitRequest/position/pubkey/36
private def case663 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1276)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1276.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1276]) bytes1277)
#guard case663 == some true

-- BuilderExitRequest/position/pubkey/37
private def case664 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1278)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1278.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1278]) bytes1279)
#guard case664 == some true

-- BuilderExitRequest/position/pubkey/38
private def case665 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1280)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1280.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1280]) bytes1281)
#guard case665 == some true

-- BuilderExitRequest/position/pubkey/39
private def case666 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1282)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1282.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1282]) bytes1283)
#guard case666 == some true

-- BuilderExitRequest/position/pubkey/40
private def case667 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1284)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1284.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1284]) bytes1285)
#guard case667 == some true

-- BuilderExitRequest/position/pubkey/41
private def case668 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1286)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1286.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1286]) bytes1287)
#guard case668 == some true

-- BuilderExitRequest/position/pubkey/42
private def case669 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1288)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1288.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1288]) bytes1289)
#guard case669 == some true

-- BuilderExitRequest/position/pubkey/43
private def case670 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1290)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1290.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1290]) bytes1291)
#guard case670 == some true

-- BuilderExitRequest/position/pubkey/44
private def case671 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1292)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1292.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1292]) bytes1293)
#guard case671 == some true

-- BuilderExitRequest/position/pubkey/45
private def case672 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1294)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1294.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1294]) bytes1295)
#guard case672 == some true

-- BuilderExitRequest/position/pubkey/46
private def case673 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1296)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1296.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1296]) bytes1297)
#guard case673 == some true

-- BuilderExitRequest/position/pubkey/47
private def case674 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1298)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes1298.data.toList]
    (.container [.bytes bytes1157, .bytes bytes1298]) bytes1299)
#guard case674 == some true

-- BuilderExitRequest/whole-field/pubkey/0
private def case675 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0004)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes0004.data.toList]
    (.container [.bytes bytes1157, .bytes bytes0004]) bytes1300)
#guard case675 == some true

-- BuilderExitRequest/whole-field/pubkey/255
private def case676 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes1157)
  let pubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0008)
  pure (BuilderExitRequest.check ⟨sourceAddress, pubkey⟩
    [.inl bytes1157.data.toList, .inl bytes0008.data.toList]
    (.container [.bytes bytes1157, .bytes bytes0008]) bytes1301)
#guard case676 == some true

-- ConsolidationRequest/source-target-swap/0
private def case677 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0543)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes0542)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes0543.data.toList, .inl bytes0542.data.toList]
    (.container [.bytes bytes0541, .bytes bytes0543, .bytes bytes0542]) bytes1302)
#guard case677 == some true

-- ConsolidationRequest/source-target-swap/1
private def case678 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1303)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1304)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes1303.data.toList, .inl bytes1304.data.toList]
    (.container [.bytes bytes0541, .bytes bytes1303, .bytes bytes1304]) bytes1305)
#guard case678 == some true

-- ConsolidationRequest/source-target-swap/2
private def case679 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1306)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1307)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes1306.data.toList, .inl bytes1307.data.toList]
    (.container [.bytes bytes0541, .bytes bytes1306, .bytes bytes1307]) bytes1308)
#guard case679 == some true

-- ConsolidationRequest/source-target-swap/3
private def case680 : Option Bool := do
  let sourceAddress ← Address.ofBytes? (Bytes.ofByteArray bytes0541)
  let sourcePubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1309)
  let targetPubkey ← FixedBytes.ofBytes? (n := 48) (Bytes.ofByteArray bytes1310)
  pure (ConsolidationRequest.check ⟨sourceAddress, sourcePubkey, targetPubkey⟩
    [.inl bytes0541.data.toList, .inl bytes1309.data.toList, .inl bytes1310.data.toList]
    (.container [.bytes bytes0541, .bytes bytes1309, .bytes bytes1310]) bytes1311)
#guard case680 == some true

end STFSpec.Conformance.Stateless.RequestItemSszWireControls
