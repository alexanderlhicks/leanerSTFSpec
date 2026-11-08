/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless
import STFSpec.Codec.SszCountRecoverable

/-!
# Actual stateless input schema clients

Library `EthConformance`. Private facade clients check actual providers, complete
models and the exact three certificates. Count and layout are separate domains.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Stateless.InputSszCallerProofs

open STFSpec.Stateless STFSpec.Base STFSpec.Codec

private abbrev actual : SszSchema StatelessInput := StatelessInput.instSszSchema

private theorem inferred : (inferInstance : SszSchema StatelessInput) = actual := rfl

private theorem descriptor : actual.type = .container [NewPayloadRequest.instSszSchema.type,
    ExecutionWitness.instSszSchema.type, .uint 8] := rfl

private theorem names : actual.fieldNames = ["new_payload_request", "witness", "chain_id"] := rfl

private theorem validity (a : StatelessInput) : actual.valid a ↔
    NewPayloadRequest.instSszSchema.valid a.newPayloadRequest ∧
      ExecutionWitness.instSszSchema.valid a.witness := Iff.rfl

private theorem complete_model (a : StatelessInput) : actual.toValue a = .container [
    NewPayloadRequest.instSszSchema.toValue a.newPayloadRequest,
    ExecutionWitness.instSszSchema.toValue a.witness, .uint a.chainId.toNat] := rfl

private theorem wf : actual.type.WellFormed := StatelessInput.ssz_type_wellFormed

private theorem forward : ∀ a : StatelessInput, actual.valid a →
    actual.ofValue? (actual.toValue a) = some a ∧
      SszValue.WellTyped actual.type (actual.toValue a) := StatelessInput.ssz_ofValue_toValue

private theorem reverse : ∀ (v : SszValue) (a : StatelessInput),
    SszValue.WellTyped actual.type v ∧ actual.ofValue? v = some a →
      actual.valid a ∧ actual.toValue a = v := StatelessInput.ssz_toValue_ofValue

private theorem arbitrary_construction (r : NewPayloadRequest) (w : ExecutionWitness) (c : U64)
    (hr : NewPayloadRequest.instSszSchema.valid r)
    (hw : ExecutionWitness.instSszSchema.valid w) :
    actual.ofValue? (.container [NewPayloadRequest.instSszSchema.toValue r,
      ExecutionWitness.instSszSchema.toValue w, .uint c.toNat]) = some (StatelessInput.mk r w c) ∧
    SszValue.WellTyped actual.type (actual.toValue (StatelessInput.mk r w c)) :=
  forward (StatelessInput.mk r w c) ⟨hr, hw⟩

private theorem recovered_reforward (v : SszValue) (a : StatelessInput)
    (ht : SszValue.WellTyped actual.type v) (hs : actual.ofValue? v = some a) :
    actual.valid a ∧ actual.toValue a = v := reverse v a ⟨ht, hs⟩

private theorem whole_recovery (a : StatelessInput) (hv : actual.valid a) :
    (actual.ofValue? (actual.toValue a)).map (fun b ↦
      (b.newPayloadRequest, b.witness, b.chainId)) =
      some (a.newPayloadRequest, a.witness, a.chainId) := by
  rw [(forward a hv).1]
  rfl

private theorem head_slots :
    (match actual.type with
    | .container fs => fs.map (fun f ↦ f.fixedSize?.getD 4)
    | _ => []) = [4, 4, 8] := by decide

private theorem head_size : ([4, 4, 8] : List Nat).sum = 16 := by decide

private theorem emitted_starts (r w : Nat) :
    (([NewPayloadRequest.instSszSchema.type, ExecutionWitness.instSszSchema.type,
      .uint 8].zip [r, w, 8]).foldl
      (fun (s : Nat × List Nat) q ↦ match q.1.fixedSize? with
        | some _ => s
        | none => (s.1 + q.2, s.2 ++ [s.1])) (16, [])).2 = [16, 16 + r] := rfl

private theorem outer_start_bound (r : Nat) :
    (∀ o ∈ [16, 16 + r], o < 2 ^ 32) ↔ 16 + r < 2 ^ 32 := by
  constructor
  · intro h
    exact h (16 + r) (by simp)
  · intro h o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · decide
    · exact h

-- The final witness end is absent from this condition; child support stays separate.
private theorem unbounded_final_end (w : Nat) :
    (∀ o ∈ [16, 16 + (2 ^ 32 - 17)], o < 2 ^ 32) ∧
      16 + (2 ^ 32 - 17) + (w + 1) ≥ 2 ^ 32 := by
  constructor
  · decide
  · omega

private theorem rejected_second_start :
    ¬ (∀ o ∈ [16, 16 + (2 ^ 32 - 16)], o < 2 ^ 32) := by decide

private theorem count_recovery (a : StatelessInput) :
    Ssz.CountRecoverable actual.type (actual.toValue a) := by
  dsimp only [actual, SszSchema.type, SszSchema.toValue, StatelessInput.instSszSchema,
    NewPayloadRequest.instSszSchema, ExecutionWitness.instSszSchema,
    ExecutionPayload.instSszSchema, ExecutionRequests.instSszSchema,
    DepositRequest.instSszSchema, WithdrawalRequest.instSszSchema,
    ConsolidationRequest.instSszSchema, BuilderDepositRequest.instSszSchema,
    BuilderExitRequest.instSszSchema]
  simp [Ssz.countRecoverable_iff (.container _) (.container _),
    Ssz.countRecoverable_iff (.progressiveContainer _ _) (.container _),
    Ssz.countRecoverable_iff (.progressiveList _) (.list _),
    Ssz.countRecoverable_iff (.list _ _) (.list _),
    Ssz.countRecoverable_iff (.uint _) (.uint _),
    Ssz.countRecoverable_iff (.byteVector _) (.bytes _),
    Ssz.countRecoverable_iff (.byteList _) (.bytes _),
    Ssz.countRecoverable_iff (.progressiveByteList) (.bytes _),
    SszType.fixedSize?_eq (.progressiveByteList), SszType.fixedSize?_eq (.byteList _),
    SszType.fixedSize?_eq (.container _),
    SszType.fixedSize?_eq (.uint _), SszType.fixedSize?_eq (.byteVector _)]

private noncomputable def logicalSize : SszType → SszValue → Nat := fun t v ↦
    SszValue.rec (motive_1 := fun _ ↦ SszType → Nat)
      (motive_2 := fun _ ↦ List (SszType → Nat))
      (fun _ t ↦ match t with | .uint w => w | _ => 0)
      (fun _ t ↦ match t with | .bool => 1 | _ => 0)
      (fun b t ↦ match t with
        | .byteVector _ | .byteList _ | .progressiveByteList => b.size
        | _ => 0)
      (fun xs lengths t ↦ match t with
        | .list e _ | .progressiveList e =>
          match SszType.fixedSize? e with
          | some w => w * xs.length
          | none => 4 * xs.length + (lengths.map (fun k ↦ k e)).sum
        | _ => 0)
      (fun _ lengths t ↦ match t with
        | .container fs | .progressiveContainer _ fs =>
          ((fs.zip lengths).map (fun (f, k) ↦
            match SszType.fixedSize? f with | some w => w | none => 4 + k f)).sum
        | _ => 0)
      [] (fun _ _ child rest ↦ child :: rest) v t

private noncomputable def logicalChildren (xs : List SszValue) : List (SszType → Nat) :=
  SszValue.rec_1 (motive_1 := fun _ ↦ SszType → Nat)
      (motive_2 := fun _ ↦ List (SszType → Nat))
      (fun _ t ↦ match t with | .uint w => w | _ => 0)
      (fun _ t ↦ match t with | .bool => 1 | _ => 0)
      (fun b t ↦ match t with
        | .byteVector _ | .byteList _ | .progressiveByteList => b.size
        | _ => 0)
      (fun xs lengths t ↦ match t with
        | .list e _ | .progressiveList e =>
          match SszType.fixedSize? e with
          | some w => w * xs.length
          | none => 4 * xs.length + (lengths.map (fun k ↦ k e)).sum
        | _ => 0)
      (fun _ lengths t ↦ match t with
        | .container fs | .progressiveContainer _ fs =>
          ((fs.zip lengths).map (fun (f, k) ↦
            match SszType.fixedSize? f with | some w => w | none => 4 + k f)).sum
        | _ => 0)
      [] (fun _ _ child rest ↦ child :: rest) xs

private theorem logicalChildren_eq (xs : List SszValue) :
    logicalChildren xs = xs.map (fun x t ↦ logicalSize t x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (fun t ↦ logicalSize t x) :: logicalChildren xs = _
    rw [ih]
    rfl

private theorem logicalSize_recurrence (t : SszType) (v : SszValue) :
  logicalSize t v = match t, v with
    | .uint w, .uint _ => w
    | .bool, .bool _ => 1
    | .byteVector _, .bytes b => b.size
    | .byteList _, .bytes b => b.size
    | .progressiveByteList, .bytes b => b.size
    | .list e _, .list xs | .progressiveList e, .list xs =>
      match SszType.fixedSize? e with
      | some w => w * xs.length
      | none => 4 * xs.length + (xs.map (fun x ↦ logicalSize e x)).sum
    | .container fs, .container xs | .progressiveContainer _ fs, .container xs =>
      ((fs.zip xs).map (fun (f, x) ↦
        match SszType.fixedSize? f with | some w => w | none => 4 + logicalSize f x)).sum
    | _, _ => 0 := by
  cases v with
  | uint n => cases t <;> rfl
  | bool b => cases t <;> rfl
  | bytes b => cases t <;> rfl
  | list xs =>
    cases t with
    | list e limit =>
      change (match SszType.fixedSize? e with
        | some w => w * xs.length
        | none => 4 * xs.length +
          ((logicalChildren xs).map (fun (k : SszType → Nat) ↦ k e)).sum) = _
      rw [logicalChildren_eq]
      simp only [List.map_map]
      rfl
    | progressiveList e =>
      change (match SszType.fixedSize? e with
        | some w => w * xs.length
        | none => 4 * xs.length +
          ((logicalChildren xs).map (fun (k : SszType → Nat) ↦ k e)).sum) = _
      rw [logicalChildren_eq]
      simp only [List.map_map]
      rfl
    | _ => rfl
  | container xs =>
    cases t with
    | container fs =>
      change (((fs.zip (logicalChildren xs)).map (fun (f, k) ↦
        match SszType.fixedSize? f with | some w => w | none => 4 + k f)).sum) = _
      rw [logicalChildren_eq, List.zip_map_right, List.map_map]
      rfl
    | progressiveContainer mask fs =>
      change (((fs.zip (logicalChildren xs)).map (fun (f, k) ↦
        match SszType.fixedSize? f with | some w => w | none => 4 + k f)).sum) = _
      rw [logicalChildren_eq, List.zip_map_right, List.map_map]
      rfl
    | _ => rfl

/-! ### Private size consequences of the public SSZ laws -/

private def littleEndian (w n : Nat) : List UInt8 :=
  (List.range w).map (fun i ↦ UInt8.ofNat ((n / 256 ^ i) % 256))

private def layoutStep (s : Nat × List UInt8 × List UInt8)
    (q : (SszType × SszValue) × ByteArray) : Nat × List UInt8 × List UInt8 :=
  match q.1.1.fixedSize? with
  | some _ => (s.1, s.2.1 ++ q.2.data.toList, s.2.2)
  | none => (s.1 + q.2.size, s.2.1 ++ littleEndian 4 s.1,
      s.2.2 ++ q.2.data.toList)

private def layout (ps : List (SszType × SszValue)) (bs : List ByteArray) : List UInt8 :=
  let s := (ps.zip bs).foldl layoutStep
    ((ps.map (fun p ↦ p.1.fixedSize?.getD 4)).sum, [], [])
  s.2.1 ++ s.2.2

private def Certificate (ps : List (SszType × SszValue)) (bs : List ByteArray) : Prop :=
  ps.length = bs.length ∧ ∀ q ∈ ps.zip bs,
    ∀ hc : Ssz.Serializable q.1.1 q.1.2, Ssz.encode q.1.1 q.1.2 hc = q.2

private theorem layout_fold_length (qs : List ((SszType × SszValue) × ByteArray))
    (s : Nat × List UInt8 × List UInt8) :
    let r := qs.foldl layoutStep s
    r.2.1.length + r.2.2.length = s.2.1.length + s.2.2.length +
      (qs.map (fun q ↦ q.2.size + if q.1.1.fixedSize?.isSome then 0 else 4)).sum := by
  induction qs generalizing s with
  | nil => simp
  | cons q qs ih =>
    simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]
    cases hf : q.1.1.fixedSize? <;>
      simp only [layoutStep, hf, List.length_append, littleEndian, List.length_map,
        List.length_range, Array.length_toList, ByteArray.size_data, Option.isSome,
        Bool.false_eq_true, ↓reduceIte, Nat.add_zero] <;> omega

private theorem layout_length (ps : List (SszType × SszValue)) (bs : List ByteArray) :
    (layout ps bs).length = ((ps.zip bs).map
      (fun q ↦ q.2.size + if q.1.1.fixedSize?.isSome then 0 else 4)).sum := by
  have h := layout_fold_length (ps.zip bs)
    ((ps.map (fun p ↦ p.1.fixedSize?.getD 4)).sum, [], [])
  simpa only [layout, List.length_append, List.length_nil, Nat.zero_add] using h

private def fixedFold (fs : List SszType) : Option Nat :=
  fs.foldr (fun f acc ↦ match f.fixedSize?, acc with
    | some n, some m => some (n + m)
    | _, _ => none) (some 0)

private theorem fixed_fields_size (fs : List SszType) (xs : List SszValue)
    (hlen : fs.length = xs.length) (n : Nat) (hf : fixedFold fs = some n) :
    ((fs.zip xs).map (fun (f, x) ↦
      match f.fixedSize? with | some w => w | none => 4 + logicalSize f x)).sum = n := by
  induction fs generalizing xs n with
  | nil =>
    cases xs with
    | nil => cases hf; rfl
    | cons x xs => simp at hlen
  | cons f fs ih =>
    cases xs with
    | nil => simp at hlen
    | cons x xs =>
      change (match f.fixedSize?, fixedFold fs with
        | some n, some m => some (n + m)
        | _, _ => none) = some n at hf
      cases hw : f.fixedSize? <;> cases hm : fixedFold fs <;>
        simp only [hw, hm, reduceCtorEq, Option.some.injEq] at hf
      subst n
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, hw]
      rw [ih xs (by simpa using hlen) _ hm]

-- Fixed field widths determine the sum once arity agrees; zero widths are allowed.
private theorem logicalSize_fixed (t : SszType) (v : SszValue)
    (h : Ssz.Serializable t v) (n : Nat) (hn : t.fixedSize? = some n) :
    logicalSize t v = n := by
  have hs := (Ssz.serializable_iff t v).mp h
  rw [SszType.fixedSize?_eq t] at hn
  rw [logicalSize_recurrence]
  cases t <;> cases v <;> dsimp only at hs hn ⊢ <;>
    first | contradiction | skip
  all_goals first
    | cases hn; rfl
    | cases hn; exact hs
    | exact fixed_fields_size _ _ hs.1 n hn

-- Each occurrence receives its own actual bytes. Proof irrelevance lets the
-- certificate quantify over every support proof, including a different one.
private theorem child_certificate (ps : List (SszType × SszValue))
    (hs : ∀ p ∈ ps, Ssz.Serializable p.1 p.2) :
    ∃ bs, Certificate ps bs := by
  induction ps with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons p ps ih =>
    obtain ⟨bs, hb⟩ := ih (fun q hq ↦ hs q (List.mem_cons_of_mem p hq))
    refine ⟨Ssz.encode p.1 p.2 (hs p (by simp)) :: bs, ?_, ?_⟩
    · simp only [List.length_cons, hb.1]
    · intro q hq hc
      rcases List.mem_cons.mp hq with rfl | hq
      · rfl
      · exact hb.2 q hq hc

private theorem certified_layout_length (ps : List (SszType × SszValue))
    (bs : List ByteArray) (hc : Certificate ps bs)
    (hs : ∀ p ∈ ps, Ssz.Serializable p.1 p.2)
    (hi : ∀ p ∈ ps, ∀ h : Ssz.Serializable p.1 p.2,
      (Ssz.encode p.1 p.2 h).size = logicalSize p.1 p.2) :
    (layout ps bs).length = ((ps.map (fun p ↦
      match p.1.fixedSize? with | some w => w | none => 4 + logicalSize p.1 p.2))).sum := by
  rw [layout_length]
  induction ps generalizing bs with
  | nil => cases bs <;> simp_all [Certificate]
  | cons p ps ih =>
    cases bs with
    | nil => exact False.elim (by simpa [Certificate] using hc.1)
    | cons b bs =>
      have hp := hs p (by simp)
      have he := hc.2 (p, b) (by simp) hp
      dsimp only at he
      have hn : b.size = logicalSize p.1 p.2 := by
        rw [← he]
        exact hi p (by simp) hp
      have htail : Certificate ps bs := ⟨by simpa using hc.1,
        fun q hq h ↦ hc.2 q (by simp only [List.zip_cons_cons, List.mem_cons]; exact Or.inr hq) h⟩
      have ht := ih bs htail (fun q hq ↦ hs q (by simp [hq]))
        (fun q hq ↦ hi q (by simp [hq]))
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
      rw [ht, hn]
      cases hf : p.1.fixedSize? with
      | none => simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte]; omega
      | some w =>
        rw [logicalSize_fixed p.1 p.2 hp w hf]
        rfl

private theorem encoded_layout_size (t : SszType) (v : SszValue)
    (h : Ssz.Serializable t v) (ps : List (SszType × SszValue))
    (he : ∀ bs, Certificate ps bs → (Ssz.encode t v h).data.toList = layout ps bs)
    (hs : ∀ p ∈ ps, Ssz.Serializable p.1 p.2)
    (hi : ∀ p ∈ ps, ∀ hc : Ssz.Serializable p.1 p.2,
      (Ssz.encode p.1 p.2 hc).size = logicalSize p.1 p.2) :
    (Ssz.encode t v h).size = (ps.map (fun p ↦
      match p.1.fixedSize? with | some w => w | none => 4 + logicalSize p.1 p.2)).sum := by
  obtain ⟨bs, hc⟩ := child_certificate ps hs
  have hh := congrArg List.length (he bs hc)
  rw [certified_layout_length ps bs hc hs hi] at hh
  simpa only [Array.length_toList, ByteArray.size_data] using hh

private theorem values_size_sum (e : SszType) (xs : List SszValue) :
    ((xs.map (fun x ↦ (e, x))).map (fun p ↦
      match p.1.fixedSize? with | some w => w | none => 4 + logicalSize p.1 p.2)).sum =
    match e.fixedSize? with
    | some w => w * xs.length
    | none => 4 * xs.length + (xs.map (fun x ↦ logicalSize e x)).sum := by
  cases hf : e.fixedSize? <;> induction xs with
  | nil => simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.mul_zero, Nat.add_zero]
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, hf,
      Nat.mul_add, Nat.mul_one] at ih ⊢
    rw [ih]
    simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem encoded_values_size (t : SszType) (xs : List SszValue)
    (h : Ssz.Serializable t (.list xs)) (e : SszType)
    (he : ∀ bs, Certificate (xs.map (fun x ↦ (e, x))) bs →
      (Ssz.encode t (.list xs) h).data.toList = layout (xs.map (fun x ↦ (e, x))) bs)
    (hs : ∀ x ∈ xs, Ssz.Serializable e x)
    (ih : ∀ x ∈ xs, ∀ (t : SszType) (hc : Ssz.Serializable t x),
      (Ssz.encode t x hc).size = logicalSize t x) :
    (Ssz.encode t (.list xs) h).size =
      match e.fixedSize? with
      | some w => w * xs.length
      | none => 4 * xs.length + (xs.map (fun x ↦ logicalSize e x)).sum := by
  have hp : ∀ p ∈ xs.map (fun x ↦ (e, x)), Ssz.Serializable p.1 p.2 := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    exact hs x hx
  have hi : ∀ p ∈ xs.map (fun x ↦ (e, x)), ∀ hc : Ssz.Serializable p.1 p.2,
      (Ssz.encode p.1 p.2 hc).size = logicalSize p.1 p.2 := by
    intro p hp hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    exact ih x hx e hc
  rw [encoded_layout_size _ _ h _ he hp hi, values_size_sum]

private theorem encode_size_model (v : SszValue) :
    ∀ (t : SszType) (h : Ssz.Serializable t v),
      (Ssz.encode t v h).size = logicalSize t v := by
  induction v using SszValue.rec
    (motive_2 := fun xs ↦ ∀ x ∈ xs, ∀ (t : SszType) (h : Ssz.Serializable t x),
      (Ssz.encode t x h).size = logicalSize t x) with
  | uint k =>
    intro t h
    have he := Ssz.encode_eq t (.uint k) h
    cases t <;> dsimp only at he
    all_goals first
      | contradiction
      | have hh := congrArg List.length he
        simpa only [logicalSize_recurrence, List.length_map, List.length_range,
          Array.length_toList, ByteArray.size_data, Nat.zero_add] using hh
  | bool b =>
    intro t h
    have he := Ssz.encode_eq t (.bool b) h
    cases t <;> dsimp only at he
    all_goals first
      | contradiction
      | have hh := congrArg List.length he
        simpa only [logicalSize_recurrence, List.length_cons, List.length_nil,
          Array.length_toList, ByteArray.size_data, Nat.zero_add] using hh
  | bytes b =>
    intro t h
    have he := Ssz.encode_eq t (.bytes b) h
    cases t <;> dsimp only at he
    all_goals first
      | contradiction
      | have hh := congrArg List.length he
        simpa only [logicalSize_recurrence, Array.length_toList, ByteArray.size_data,
          Nat.zero_add] using hh
  | list xs ih =>
    intro t h
    have he := Ssz.encode_eq t (.list xs) h
    have hs := (Ssz.serializable_iff t (.list xs)).mp h
    cases t with
    | list e limit =>
      rw [logicalSize_recurrence]
      exact encoded_values_size _ xs h e he hs.2.1 ih
    | progressiveList e =>
      rw [logicalSize_recurrence]
      exact encoded_values_size _ xs h e he hs.1 ih
    | _ => contradiction
  | container xs ih =>
    intro t h
    have he := Ssz.encode_eq t (.container xs) h
    have hs := (Ssz.serializable_iff t (.container xs)).mp h
    cases t <;> dsimp only at he hs
    all_goals first | contradiction | skip
    all_goals
      have hh := encoded_layout_size _ _ h _ he hs.2.1
        (fun p hp hc ↦ ih p.2 (List.of_mem_zip hp).2 p.1 hc)
      rw [hh, logicalSize_recurrence]
  | nil => contradiction
  | cons x xs hx hxs =>
    rename_i y hy t h
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx t h
    · exact hxs y hy t h

private theorem encode_fixed_size (t : SszType) (v : SszValue)
    (h : Ssz.Serializable t v) (n : Nat) (hn : t.fixedSize? = some n) :
    (Ssz.encode t v h).size = n :=
  (encode_size_model v t h).trans (logicalSize_fixed t v h n hn)

private theorem certified_child_width (ps : List (SszType × SszValue))
    (bs : List ByteArray) (hc : Certificate ps bs)
    (hs : ∀ p ∈ ps, Ssz.Serializable p.1 p.2)
    (q : (SszType × SszValue) × ByteArray) (hq : q ∈ ps.zip bs)
    (n : Nat) (hn : q.1.1.fixedSize? = some n) : q.2.size = n := by
  have hp := hs q.1 (List.of_mem_zip hq).1
  rw [← hc.2 q hq hp]
  exact encode_fixed_size q.1.1 q.1.2 hp n hn

private theorem certified_layout_width (ps : List (SszType × SszValue))
    (bs : List ByteArray) (hc : Certificate ps bs)
    (hs : ∀ p ∈ ps, Ssz.Serializable p.1 p.2) :
    (layout ps bs).length = ((ps.zip bs).map (fun q ↦
      match q.1.1.fixedSize? with | some n => n | none => 4 + q.2.size)).sum := by
  rw [layout_length]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q hq
  cases hn : q.1.1.fixedSize? with
  | none => simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_comm]
  | some n =>
    rw [certified_child_width ps bs hc hs q hq n hn]
    rfl

private theorem final_tail_support (b : ByteArray) :
    Ssz.Serializable (.container [.progressiveByteList]) (.container [.bytes b]) := by
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  · intro p hp
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    subst p
    exact (Ssz.serializable_iff .progressiveByteList (.bytes b)).mpr trivial
  · change ∀ o ∈ [4], o < 2 ^ 32
    intro o ho
    have : o = 4 := by simpa using ho
    subst o
    decide

private theorem final_tail_size (b : ByteArray)
    (h : Ssz.Serializable (.container [.progressiveByteList]) (.container [.bytes b])) :
    (Ssz.encode _ _ h).size = 4 + b.size := by
  rw [encode_size_model, logicalSize_recurrence]
  simp only [List.zip_cons_cons, List.zip_nil_left, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, SszType.fixedSize?_eq .progressiveByteList,
    logicalSize_recurrence .progressiveByteList (.bytes b), Nat.add_zero]

private theorem final_tail_no_cap (b : ByteArray) (hb : 2 ^ 32 ≤ b.size) :
    ∃ h : Ssz.Serializable (.container [.progressiveByteList]) (.container [.bytes b]),
      2 ^ 32 < (Ssz.encode _ _ h).size := by
  refine ⟨final_tail_support b, ?_⟩
  rw [final_tail_size]
  omega

private theorem unsupported_width (n : Nat) : ¬ Ssz.Serializable (.uint 3) (.uint n) := by
  rw [Ssz.serializable_iff]
  intro h
  have : ¬ (3 = 1 ∨ 3 = 2 ∨ 3 = 4 ∨ 3 = 8 ∨ 3 = 16 ∨ 3 = 32) := by decide
  exact this h.1

private theorem unsupported_tags (t : SszType) (v : SszValue)
    (hu : (match t, v with
      | .uint _, .uint _ | .bool, .bool _ | .byteVector _, .bytes _
      | .byteList _, .bytes _ | .progressiveByteList, .bytes _
      | .list _ _, .list _ | .progressiveList _, .list _
      | .container _, .container _ | .progressiveContainer _ _, .container _ => False
      | _, _ => True)) : ¬ Ssz.Serializable t v := by
  rw [Ssz.serializable_iff]
  cases t <;> cases v <;> first | contradiction | exact id

private theorem over_limit_bytes :
    ¬ Ssz.Serializable (.byteList 1) (.bytes (ByteArray.mk #[0, 1])) := by
  rw [Ssz.serializable_iff]
  decide

private theorem wrong_vector_size :
    ¬ Ssz.Serializable (.byteVector 0) (.bytes (ByteArray.mk #[0])) := by
  rw [Ssz.serializable_iff]
  decide





/-! ### Complete private raw size controls -/

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private abbrev sizeType00 : SszType := (.uint 1)

private def sizeValue00 : SszValue := (.uint 0)

private theorem sizeSupport00 : Ssz.Serializable sizeType00 sizeValue00 := by
  change Ssz.Serializable (.uint 1) (.uint 0)
  apply (Ssz.serializable_iff _ _).mpr
  decide

private def sizeWire00 : List UInt8 := [0]

private theorem sizeModel00 : logicalSize sizeType00 sizeValue00 = 1 := by
  decide

private theorem sizeActual00 : (Ssz.encode sizeType00 sizeValue00 sizeSupport00).size = 1 :=
  (encode_size_model sizeValue00 sizeType00 sizeSupport00).trans sizeModel00

#guard (Ssz.encode sizeType00 sizeValue00 sizeSupport00).data.toList = sizeWire00
#guard (Ssz.encode sizeType00 sizeValue00 sizeSupport00).size = 1

private abbrev sizeType01 : SszType := (.uint 1)

private def sizeValue01 : SszValue := (.uint 255)

private theorem sizeSupport01 : Ssz.Serializable sizeType01 sizeValue01 := by
  change Ssz.Serializable (.uint 1) (.uint 255)
  apply (Ssz.serializable_iff _ _).mpr
  decide

private def sizeWire01 : List UInt8 := [255]

private theorem sizeModel01 : logicalSize sizeType01 sizeValue01 = 1 := by
  decide

private theorem sizeActual01 : (Ssz.encode sizeType01 sizeValue01 sizeSupport01).size = 1 :=
  (encode_size_model sizeValue01 sizeType01 sizeSupport01).trans sizeModel01

#guard (Ssz.encode sizeType01 sizeValue01 sizeSupport01).data.toList = sizeWire01
#guard (Ssz.encode sizeType01 sizeValue01 sizeSupport01).size = 1

private abbrev sizeType02 : SszType := (.uint 2)

private def sizeValue02 : SszValue := (.uint 513)

private theorem sizeSupport02 : Ssz.Serializable sizeType02 sizeValue02 := by
  change Ssz.Serializable (.uint 2) (.uint 513)
  apply (Ssz.serializable_iff _ _).mpr
  decide

private def sizeWire02 : List UInt8 := [1, 2]

private theorem sizeModel02 : logicalSize sizeType02 sizeValue02 = 2 := by
  decide

private theorem sizeActual02 : (Ssz.encode sizeType02 sizeValue02 sizeSupport02).size = 2 :=
  (encode_size_model sizeValue02 sizeType02 sizeSupport02).trans sizeModel02

#guard (Ssz.encode sizeType02 sizeValue02 sizeSupport02).data.toList = sizeWire02
#guard (Ssz.encode sizeType02 sizeValue02 sizeSupport02).size = 2

private abbrev sizeType03 : SszType := (.uint 4)

private def sizeValue03 : SszValue := (.uint 16909060)

private theorem sizeSupport03 : Ssz.Serializable sizeType03 sizeValue03 := by
  change Ssz.Serializable (.uint 4) (.uint 16909060)
  apply (Ssz.serializable_iff _ _).mpr
  decide

private def sizeWire03 : List UInt8 := [4, 3, 2, 1]

private theorem sizeModel03 : logicalSize sizeType03 sizeValue03 = 4 := by
  decide

private theorem sizeActual03 : (Ssz.encode sizeType03 sizeValue03 sizeSupport03).size = 4 :=
  (encode_size_model sizeValue03 sizeType03 sizeSupport03).trans sizeModel03

#guard (Ssz.encode sizeType03 sizeValue03 sizeSupport03).data.toList = sizeWire03
#guard (Ssz.encode sizeType03 sizeValue03 sizeSupport03).size = 4

private abbrev sizeType04 : SszType := (.uint 8)

private def sizeValue04 : SszValue := (.uint 72623859790382856)

private theorem sizeSupport04 : Ssz.Serializable sizeType04 sizeValue04 := by
  change Ssz.Serializable (.uint 8) (.uint 72623859790382856)
  apply (Ssz.serializable_iff _ _).mpr
  decide

private def sizeWire04 : List UInt8 := [8, 7, 6, 5, 4, 3, 2, 1]

private theorem sizeModel04 : logicalSize sizeType04 sizeValue04 = 8 := by
  decide

private theorem sizeActual04 : (Ssz.encode sizeType04 sizeValue04 sizeSupport04).size = 8 :=
  (encode_size_model sizeValue04 sizeType04 sizeSupport04).trans sizeModel04

#guard (Ssz.encode sizeType04 sizeValue04 sizeSupport04).data.toList = sizeWire04
#guard (Ssz.encode sizeType04 sizeValue04 sizeSupport04).size = 8

private abbrev sizeType05 : SszType := (.uint 16)

private def sizeValue05 : SszValue := (.uint 1)

private theorem sizeSupport05 : Ssz.Serializable sizeType05 sizeValue05 := by
  change Ssz.Serializable (.uint 16) (.uint 1)
  apply (Ssz.serializable_iff _ _).mpr
  decide

private def sizeWire05 : List UInt8 := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem sizeModel05 : logicalSize sizeType05 sizeValue05 = 16 := by
  decide

private theorem sizeActual05 : (Ssz.encode sizeType05 sizeValue05 sizeSupport05).size = 16 :=
  (encode_size_model sizeValue05 sizeType05 sizeSupport05).trans sizeModel05

#guard (Ssz.encode sizeType05 sizeValue05 sizeSupport05).data.toList = sizeWire05
#guard (Ssz.encode sizeType05 sizeValue05 sizeSupport05).size = 16

private abbrev sizeType06 : SszType := (.uint 32)

private def sizeValue06 : SszValue :=
  (.uint 115792089237316195423570985008687907853269984665640564039457584007913129639935)

private theorem sizeSupport06 : Ssz.Serializable sizeType06 sizeValue06 := by
  change Ssz.Serializable
    (.uint 32)
    (.uint 115792089237316195423570985008687907853269984665640564039457584007913129639935)
  apply (Ssz.serializable_iff _ _).mpr
  decide

private def sizeWire06 : List UInt8 :=
  [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]

private theorem sizeModel06 : logicalSize sizeType06 sizeValue06 = 32 := by
  decide

private theorem sizeActual06 : (Ssz.encode sizeType06 sizeValue06 sizeSupport06).size = 32 :=
  (encode_size_model sizeValue06 sizeType06 sizeSupport06).trans sizeModel06

#guard (Ssz.encode sizeType06 sizeValue06 sizeSupport06).data.toList = sizeWire06
#guard (Ssz.encode sizeType06 sizeValue06 sizeSupport06).size = 32

private abbrev sizeType07 : SszType := .bool

private def sizeValue07 : SszValue := (.bool false)

private theorem sizeSupport07 : Ssz.Serializable sizeType07 sizeValue07 := by
  change Ssz.Serializable .bool (.bool false)
  apply (Ssz.serializable_iff _ _).mpr
  decide

private def sizeWire07 : List UInt8 := [0]

private theorem sizeModel07 : logicalSize sizeType07 sizeValue07 = 1 := by
  decide

private theorem sizeActual07 : (Ssz.encode sizeType07 sizeValue07 sizeSupport07).size = 1 :=
  (encode_size_model sizeValue07 sizeType07 sizeSupport07).trans sizeModel07

#guard (Ssz.encode sizeType07 sizeValue07 sizeSupport07).data.toList = sizeWire07
#guard (Ssz.encode sizeType07 sizeValue07 sizeSupport07).size = 1

private abbrev sizeType08 : SszType := .bool

private def sizeValue08 : SszValue := (.bool true)

private theorem sizeSupport08 : Ssz.Serializable sizeType08 sizeValue08 := by
  change Ssz.Serializable .bool (.bool true)
  apply (Ssz.serializable_iff _ _).mpr
  decide

private def sizeWire08 : List UInt8 := [1]

private theorem sizeModel08 : logicalSize sizeType08 sizeValue08 = 1 := by
  decide

private theorem sizeActual08 : (Ssz.encode sizeType08 sizeValue08 sizeSupport08).size = 1 :=
  (encode_size_model sizeValue08 sizeType08 sizeSupport08).trans sizeModel08

#guard (Ssz.encode sizeType08 sizeValue08 sizeSupport08).data.toList = sizeWire08
#guard (Ssz.encode sizeType08 sizeValue08 sizeSupport08).size = 1

private abbrev sizeType09 : SszType := (.byteVector 0)

private def sizeValue09 : SszValue := (.bytes (ByteArray.mk #[]))

private theorem sizeSupport09 : Ssz.Serializable sizeType09 sizeValue09 := by
  change Ssz.Serializable (.byteVector 0) (.bytes (ByteArray.mk #[]))
  apply (Ssz.serializable_iff _ _).mpr
  decide

private def sizeWire09 : List UInt8 := []

private theorem sizeModel09 : logicalSize sizeType09 sizeValue09 = 0 := by
  decide

private theorem sizeActual09 : (Ssz.encode sizeType09 sizeValue09 sizeSupport09).size = 0 :=
  (encode_size_model sizeValue09 sizeType09 sizeSupport09).trans sizeModel09

#guard (Ssz.encode sizeType09 sizeValue09 sizeSupport09).data.toList = sizeWire09
#guard (Ssz.encode sizeType09 sizeValue09 sizeSupport09).size = 0

private abbrev sizeType10 : SszType := (.byteVector 3)

private def sizeValue10 : SszValue := (.bytes (ByteArray.mk #[0, 255, 0]))

private theorem sizeSupport10 : Ssz.Serializable sizeType10 sizeValue10 := by
  change Ssz.Serializable (.byteVector 3) (.bytes (ByteArray.mk #[0, 255, 0]))
  apply (Ssz.serializable_iff _ _).mpr
  decide

private def sizeWire10 : List UInt8 := [0, 255, 0]

private theorem sizeModel10 : logicalSize sizeType10 sizeValue10 = 3 := by
  decide

private theorem sizeActual10 : (Ssz.encode sizeType10 sizeValue10 sizeSupport10).size = 3 :=
  (encode_size_model sizeValue10 sizeType10 sizeSupport10).trans sizeModel10

#guard (Ssz.encode sizeType10 sizeValue10 sizeSupport10).data.toList = sizeWire10
#guard (Ssz.encode sizeType10 sizeValue10 sizeSupport10).size = 3

private abbrev sizeType11 : SszType := (.byteList 0)

private def sizeValue11 : SszValue := (.bytes (ByteArray.mk #[]))

private theorem sizeSupport11 : Ssz.Serializable sizeType11 sizeValue11 := by
  change Ssz.Serializable (.byteList 0) (.bytes (ByteArray.mk #[]))
  apply (Ssz.serializable_iff _ _).mpr
  decide

private def sizeWire11 : List UInt8 := []

private theorem sizeModel11 : logicalSize sizeType11 sizeValue11 = 0 := by
  decide

private theorem sizeActual11 : (Ssz.encode sizeType11 sizeValue11 sizeSupport11).size = 0 :=
  (encode_size_model sizeValue11 sizeType11 sizeSupport11).trans sizeModel11

#guard (Ssz.encode sizeType11 sizeValue11 sizeSupport11).data.toList = sizeWire11
#guard (Ssz.encode sizeType11 sizeValue11 sizeSupport11).size = 0

private abbrev sizeType12 : SszType := (.byteList 3)

private def sizeValue12 : SszValue := (.bytes (ByteArray.mk #[1, 0, 255]))

private theorem sizeSupport12 : Ssz.Serializable sizeType12 sizeValue12 := by
  change Ssz.Serializable (.byteList 3) (.bytes (ByteArray.mk #[1, 0, 255]))
  apply (Ssz.serializable_iff _ _).mpr
  decide

private def sizeWire12 : List UInt8 := [1, 0, 255]

private theorem sizeModel12 : logicalSize sizeType12 sizeValue12 = 3 := by
  decide

private theorem sizeActual12 : (Ssz.encode sizeType12 sizeValue12 sizeSupport12).size = 3 :=
  (encode_size_model sizeValue12 sizeType12 sizeSupport12).trans sizeModel12

#guard (Ssz.encode sizeType12 sizeValue12 sizeSupport12).data.toList = sizeWire12
#guard (Ssz.encode sizeType12 sizeValue12 sizeSupport12).size = 3

private abbrev sizeType13 : SszType := .progressiveByteList

private def sizeValue13 : SszValue := (.bytes (ByteArray.mk #[7, 0, 8]))

private theorem sizeSupport13 : Ssz.Serializable sizeType13 sizeValue13 := by
  change Ssz.Serializable .progressiveByteList (.bytes (ByteArray.mk #[7, 0, 8]))
  apply (Ssz.serializable_iff _ _).mpr
  decide

private def sizeWire13 : List UInt8 := [7, 0, 8]

private theorem sizeModel13 : logicalSize sizeType13 sizeValue13 = 3 := by
  decide

private theorem sizeActual13 : (Ssz.encode sizeType13 sizeValue13 sizeSupport13).size = 3 :=
  (encode_size_model sizeValue13 sizeType13 sizeSupport13).trans sizeModel13

#guard (Ssz.encode sizeType13 sizeValue13 sizeSupport13).data.toList = sizeWire13
#guard (Ssz.encode sizeType13 sizeValue13 sizeSupport13).size = 3

private abbrev sizeType14 : SszType := (.list (.uint 1) 0)

private def sizeValue14 : SszValue := (.list [])

private theorem sizeSupport14 : Ssz.Serializable sizeType14 sizeValue14 := by
  change Ssz.Serializable (.list (.uint 1) 0) (.list [])
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, ?_⟩
  · intro x hx
    exact False.elim (List.not_mem_nil hx)
  · decide

private def sizeWire14 : List UInt8 := []

private theorem sizeModel14 : logicalSize sizeType14 sizeValue14 = 0 := by
  decide

private theorem sizeActual14 : (Ssz.encode sizeType14 sizeValue14 sizeSupport14).size = 0 :=
  (encode_size_model sizeValue14 sizeType14 sizeSupport14).trans sizeModel14

#guard (Ssz.encode sizeType14 sizeValue14 sizeSupport14).data.toList = sizeWire14
#guard (Ssz.encode sizeType14 sizeValue14 sizeSupport14).size = 0

private abbrev sizeType15 : SszType := (.list (.uint 2) 3)

private def sizeValue15 : SszValue := (.list [(.uint 1), (.uint 513)])

private theorem sizeSupport15 : Ssz.Serializable sizeType15 sizeValue15 := by
  change Ssz.Serializable (.list (.uint 2) 3) (.list [(.uint 1), (.uint 513)])
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · apply (Ssz.serializable_iff _ _).mpr
      decide
    · apply (Ssz.serializable_iff _ _).mpr
      decide
  · decide

private def sizeWire15 : List UInt8 := [1, 0, 1, 2]

private theorem sizeModel15 : logicalSize sizeType15 sizeValue15 = 4 := by
  decide

private theorem sizeActual15 : (Ssz.encode sizeType15 sizeValue15 sizeSupport15).size = 4 :=
  (encode_size_model sizeValue15 sizeType15 sizeSupport15).trans sizeModel15

#guard (Ssz.encode sizeType15 sizeValue15 sizeSupport15).data.toList = sizeWire15
#guard (Ssz.encode sizeType15 sizeValue15 sizeSupport15).size = 4

private abbrev sizeType16 : SszType := (.progressiveList .bool)

private def sizeValue16 : SszValue := (.list [(.bool true), (.bool false), (.bool true)])

private theorem sizeSupport16 : Ssz.Serializable sizeType16 sizeValue16 := by
  change Ssz.Serializable (.progressiveList .bool)
    (.list [(.bool true), (.bool false), (.bool true)])
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · apply (Ssz.serializable_iff _ _).mpr
      decide
    · apply (Ssz.serializable_iff _ _).mpr
      decide
    · apply (Ssz.serializable_iff _ _).mpr
      decide
  · decide

private def sizeWire16 : List UInt8 := [1, 0, 1]

private theorem sizeModel16 : logicalSize sizeType16 sizeValue16 = 3 := by
  decide

private theorem sizeActual16 : (Ssz.encode sizeType16 sizeValue16 sizeSupport16).size = 3 :=
  (encode_size_model sizeValue16 sizeType16 sizeSupport16).trans sizeModel16

#guard (Ssz.encode sizeType16 sizeValue16 sizeSupport16).data.toList = sizeWire16
#guard (Ssz.encode sizeType16 sizeValue16 sizeSupport16).size = 3

private abbrev sizeType17 : SszType := (.list (.byteVector 0) 3)

private def sizeValue17 : SszValue :=
  (.list [(.bytes (ByteArray.mk #[])), (.bytes (ByteArray.mk #[])), (.bytes (ByteArray.mk #[]))])

private theorem sizeSupport17 : Ssz.Serializable sizeType17 sizeValue17 := by
  change Ssz.Serializable (.list (.byteVector 0) 3)
    (.list [(.bytes (ByteArray.mk #[])), (.bytes (ByteArray.mk #[])),
      (.bytes (ByteArray.mk #[]))])
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · apply (Ssz.serializable_iff _ _).mpr
      decide
    · apply (Ssz.serializable_iff _ _).mpr
      decide
    · apply (Ssz.serializable_iff _ _).mpr
      decide
  · decide

private def sizeWire17 : List UInt8 := []

private theorem sizeModel17 : logicalSize sizeType17 sizeValue17 = 0 := by
  decide

private theorem sizeActual17 : (Ssz.encode sizeType17 sizeValue17 sizeSupport17).size = 0 :=
  (encode_size_model sizeValue17 sizeType17 sizeSupport17).trans sizeModel17

#guard (Ssz.encode sizeType17 sizeValue17 sizeSupport17).data.toList = sizeWire17
#guard (Ssz.encode sizeType17 sizeValue17 sizeSupport17).size = 0

private abbrev sizeType18 : SszType := (.progressiveList (.container []))

private def sizeValue18 : SszValue := (.list [(.container []), (.container [])])

private theorem sizeSupport18 : Ssz.Serializable sizeType18 sizeValue18 := by
  change Ssz.Serializable (.progressiveList (.container []))
    (.list [(.container []), (.container [])])
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · apply (Ssz.serializable_iff _ _).mpr
      refine ⟨rfl, ?_, ?_⟩
      · intro x hx
        exact False.elim (List.not_mem_nil hx)
      · decide
    · apply (Ssz.serializable_iff _ _).mpr
      refine ⟨rfl, ?_, ?_⟩
      · intro x hx
        exact False.elim (List.not_mem_nil hx)
      · decide
  · decide

private def sizeWire18 : List UInt8 := []

private theorem sizeModel18 : logicalSize sizeType18 sizeValue18 = 0 := by
  decide

private theorem sizeActual18 : (Ssz.encode sizeType18 sizeValue18 sizeSupport18).size = 0 :=
  (encode_size_model sizeValue18 sizeType18 sizeSupport18).trans sizeModel18

#guard (Ssz.encode sizeType18 sizeValue18 sizeSupport18).data.toList = sizeWire18
#guard (Ssz.encode sizeType18 sizeValue18 sizeSupport18).size = 0

private abbrev sizeType19 : SszType := (.progressiveList .progressiveByteList)

private def sizeValue19 : SszValue :=
  (.list [(.bytes (ByteArray.mk #[])), (.bytes (ByteArray.mk #[9])), (.bytes (ByteArray.mk #[]))])

private theorem sizeSupport19 : Ssz.Serializable sizeType19 sizeValue19 := by
  change Ssz.Serializable (.progressiveList .progressiveByteList)
    (.list [(.bytes (ByteArray.mk #[])), (.bytes (ByteArray.mk #[9])),
      (.bytes (ByteArray.mk #[]))])
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · apply (Ssz.serializable_iff _ _).mpr
      decide
    · apply (Ssz.serializable_iff _ _).mpr
      decide
    · apply (Ssz.serializable_iff _ _).mpr
      decide
  · decide

private def sizeWire19 : List UInt8 := [12, 0, 0, 0, 12, 0, 0, 0, 13, 0, 0, 0, 9]

private theorem sizeModel19 : logicalSize sizeType19 sizeValue19 = 13 := by
  decide

private theorem sizeActual19 : (Ssz.encode sizeType19 sizeValue19 sizeSupport19).size = 13 :=
  (encode_size_model sizeValue19 sizeType19 sizeSupport19).trans sizeModel19

#guard (Ssz.encode sizeType19 sizeValue19 sizeSupport19).data.toList = sizeWire19
#guard (Ssz.encode sizeType19 sizeValue19 sizeSupport19).size = 13

private abbrev sizeType20 : SszType := (.container [])

private def sizeValue20 : SszValue := (.container [])

private theorem sizeSupport20 : Ssz.Serializable sizeType20 sizeValue20 := by
  change Ssz.Serializable (.container []) (.container [])
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  · intro x hx
    exact False.elim (List.not_mem_nil hx)
  · decide

private def sizeWire20 : List UInt8 := []

private theorem sizeModel20 : logicalSize sizeType20 sizeValue20 = 0 := by
  decide

private theorem sizeActual20 : (Ssz.encode sizeType20 sizeValue20 sizeSupport20).size = 0 :=
  (encode_size_model sizeValue20 sizeType20 sizeSupport20).trans sizeModel20

#guard (Ssz.encode sizeType20 sizeValue20 sizeSupport20).data.toList = sizeWire20
#guard (Ssz.encode sizeType20 sizeValue20 sizeSupport20).size = 0

private abbrev sizeType21 : SszType := (.progressiveContainer [] [])

private def sizeValue21 : SszValue := (.container [])

private theorem sizeSupport21 : Ssz.Serializable sizeType21 sizeValue21 := by
  change Ssz.Serializable (.progressiveContainer [] []) (.container [])
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  · intro x hx
    exact False.elim (List.not_mem_nil hx)
  · decide

private def sizeWire21 : List UInt8 := []

private theorem sizeModel21 : logicalSize sizeType21 sizeValue21 = 0 := by
  decide

private theorem sizeActual21 : (Ssz.encode sizeType21 sizeValue21 sizeSupport21).size = 0 :=
  (encode_size_model sizeValue21 sizeType21 sizeSupport21).trans sizeModel21

#guard (Ssz.encode sizeType21 sizeValue21 sizeSupport21).data.toList = sizeWire21
#guard (Ssz.encode sizeType21 sizeValue21 sizeSupport21).size = 0

private abbrev sizeType22 : SszType := (.container [(.uint 1), (.byteList 5), (.byteVector 2)])

private def sizeValue22 : SszValue :=
  (.container [(.uint 7), (.bytes (ByteArray.mk #[9, 8])), (.bytes (ByteArray.mk #[3, 4]))])

private theorem sizeSupport22 : Ssz.Serializable sizeType22 sizeValue22 := by
  change Ssz.Serializable (.container [(.uint 1), (.byteList 5), (.byteVector 2)])
    (.container [(.uint 7), (.bytes (ByteArray.mk #[9, 8])), (.bytes (ByteArray.mk #[3, 4]))])
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  · intro x hx
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · apply (Ssz.serializable_iff _ _).mpr
      decide
    · apply (Ssz.serializable_iff _ _).mpr
      decide
    · apply (Ssz.serializable_iff _ _).mpr
      decide
  · decide

private def sizeWire22 : List UInt8 := [7, 7, 0, 0, 0, 3, 4, 9, 8]

private theorem sizeModel22 : logicalSize sizeType22 sizeValue22 = 9 := by
  decide

private theorem sizeActual22 : (Ssz.encode sizeType22 sizeValue22 sizeSupport22).size = 9 :=
  (encode_size_model sizeValue22 sizeType22 sizeSupport22).trans sizeModel22

#guard (Ssz.encode sizeType22 sizeValue22 sizeSupport22).data.toList = sizeWire22
#guard (Ssz.encode sizeType22 sizeValue22 sizeSupport22).size = 9

private abbrev sizeType23 : SszType := (.progressiveContainer [false] [(.uint 1), (.byteList 2)])

private def sizeValue23 : SszValue := (.container [(.uint 2), (.bytes (ByteArray.mk #[5, 6]))])

private theorem sizeSupport23 : Ssz.Serializable sizeType23 sizeValue23 := by
  change Ssz.Serializable (.progressiveContainer [false] [(.uint 1), (.byteList 2)])
    (.container [(.uint 2), (.bytes (ByteArray.mk #[5, 6]))])
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  · intro x hx
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · apply (Ssz.serializable_iff _ _).mpr
      decide
    · apply (Ssz.serializable_iff _ _).mpr
      decide
  · decide

private def sizeWire23 : List UInt8 := [2, 5, 0, 0, 0, 5, 6]

private theorem sizeModel23 : logicalSize sizeType23 sizeValue23 = 7 := by
  decide

private theorem sizeActual23 : (Ssz.encode sizeType23 sizeValue23 sizeSupport23).size = 7 :=
  (encode_size_model sizeValue23 sizeType23 sizeSupport23).trans sizeModel23

#guard (Ssz.encode sizeType23 sizeValue23 sizeSupport23).data.toList = sizeWire23
#guard (Ssz.encode sizeType23 sizeValue23 sizeSupport23).size = 7

private abbrev sizeType24 : SszType := (.container [(.progressiveList (.byteList 4)), .bool])

private def sizeValue24 : SszValue :=
  (.container [(.list [(.bytes (ByteArray.mk #[1, 2])), (.bytes (ByteArray.mk #[]))]),
    (.bool true)])

private theorem sizeSupport24 : Ssz.Serializable sizeType24 sizeValue24 := by
  change Ssz.Serializable (.container [(.progressiveList (.byteList 4)), .bool])
    (.container [(.list [(.bytes (ByteArray.mk #[1, 2])), (.bytes (ByteArray.mk #[]))]),
      (.bool true)])
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  · intro x hx
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · apply (Ssz.serializable_iff _ _).mpr
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · apply (Ssz.serializable_iff _ _).mpr
          decide
        · apply (Ssz.serializable_iff _ _).mpr
          decide
      · decide
    · apply (Ssz.serializable_iff _ _).mpr
      decide
  · decide

private def sizeWire24 : List UInt8 := [5, 0, 0, 0, 1, 8, 0, 0, 0, 10, 0, 0, 0, 1, 2]

private theorem sizeModel24 : logicalSize sizeType24 sizeValue24 = 15 := by
  decide

private theorem sizeActual24 : (Ssz.encode sizeType24 sizeValue24 sizeSupport24).size = 15 :=
  (encode_size_model sizeValue24 sizeType24 sizeSupport24).trans sizeModel24

#guard (Ssz.encode sizeType24 sizeValue24 sizeSupport24).data.toList = sizeWire24
#guard (Ssz.encode sizeType24 sizeValue24 sizeSupport24).size = 15

private abbrev sizeType25 : SszType := (.container [(.byteList 0), (.byteList 3)])

private def sizeValue25 : SszValue :=
  (.container [(.bytes (ByteArray.mk #[])), (.bytes (ByteArray.mk #[0, 4]))])

private theorem sizeSupport25 : Ssz.Serializable sizeType25 sizeValue25 := by
  change Ssz.Serializable (.container [(.byteList 0), (.byteList 3)])
    (.container [(.bytes (ByteArray.mk #[])), (.bytes (ByteArray.mk #[0, 4]))])
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  · intro x hx
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · apply (Ssz.serializable_iff _ _).mpr
      decide
    · apply (Ssz.serializable_iff _ _).mpr
      decide
  · decide

private def sizeWire25 : List UInt8 := [8, 0, 0, 0, 8, 0, 0, 0, 0, 4]

private theorem sizeModel25 : logicalSize sizeType25 sizeValue25 = 10 := by
  decide

private theorem sizeActual25 : (Ssz.encode sizeType25 sizeValue25 sizeSupport25).size = 10 :=
  (encode_size_model sizeValue25 sizeType25 sizeSupport25).trans sizeModel25

#guard (Ssz.encode sizeType25 sizeValue25 sizeSupport25).data.toList = sizeWire25
#guard (Ssz.encode sizeType25 sizeValue25 sizeSupport25).size = 10

private abbrev sizeType26 : SszType := (.container [(.byteVector 0), (.uint 1)])

private def sizeValue26 : SszValue := (.container [(.bytes (ByteArray.mk #[])), (.uint 9)])

private theorem sizeSupport26 : Ssz.Serializable sizeType26 sizeValue26 := by
  change Ssz.Serializable (.container [(.byteVector 0),
    (.uint 1)]) (.container [(.bytes (ByteArray.mk #[])), (.uint 9)])
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  · intro x hx
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · apply (Ssz.serializable_iff _ _).mpr
      decide
    · apply (Ssz.serializable_iff _ _).mpr
      decide
  · decide

private def sizeWire26 : List UInt8 := [9]

private theorem sizeModel26 : logicalSize sizeType26 sizeValue26 = 1 := by
  decide

private theorem sizeActual26 : (Ssz.encode sizeType26 sizeValue26 sizeSupport26).size = 1 :=
  (encode_size_model sizeValue26 sizeType26 sizeSupport26).trans sizeModel26

#guard (Ssz.encode sizeType26 sizeValue26 sizeSupport26).data.toList = sizeWire26
#guard (Ssz.encode sizeType26 sizeValue26 sizeSupport26).size = 1

private abbrev sizeType27 : SszType := (.list (.container [(.byteVector 0)]) 2)

private def sizeValue27 : SszValue :=
  (.list [(.container [(.bytes (ByteArray.mk #[]))]), (.container [(.bytes (ByteArray.mk #[]))])])

private theorem sizeSupport27 : Ssz.Serializable sizeType27 sizeValue27 := by
  change Ssz.Serializable (.list (.container [(.byteVector 0)]) 2)
    (.list [(.container [(.bytes (ByteArray.mk #[]))]),
      (.container [(.bytes (ByteArray.mk #[]))])])
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · apply (Ssz.serializable_iff _ _).mpr
      refine ⟨rfl, ?_, ?_⟩
      · intro x hx
        simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
          List.not_mem_nil, or_false] at hx
        subst x
        apply (Ssz.serializable_iff _ _).mpr
        decide
      · decide
    · apply (Ssz.serializable_iff _ _).mpr
      refine ⟨rfl, ?_, ?_⟩
      · intro x hx
        simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
          List.not_mem_nil, or_false] at hx
        subst x
        apply (Ssz.serializable_iff _ _).mpr
        decide
      · decide
  · decide

private def sizeWire27 : List UInt8 := []

private theorem sizeModel27 : logicalSize sizeType27 sizeValue27 = 0 := by
  decide

private theorem sizeActual27 : (Ssz.encode sizeType27 sizeValue27 sizeSupport27).size = 0 :=
  (encode_size_model sizeValue27 sizeType27 sizeSupport27).trans sizeModel27

#guard (Ssz.encode sizeType27 sizeValue27 sizeSupport27).data.toList = sizeWire27
#guard (Ssz.encode sizeType27 sizeValue27 sizeSupport27).size = 0

private abbrev sizeType28 : SszType := (.list (.byteList 1) 3)

private def sizeValue28 : SszValue :=
  (.list [(.bytes (ByteArray.mk #[1])), (.bytes (ByteArray.mk #[])), (.bytes (ByteArray.mk #[2]))])

private theorem sizeSupport28 : Ssz.Serializable sizeType28 sizeValue28 := by
  change Ssz.Serializable (.list (.byteList 1) 3)
    (.list [(.bytes (ByteArray.mk #[1])), (.bytes (ByteArray.mk #[])),
      (.bytes (ByteArray.mk #[2]))])
  apply (Ssz.serializable_iff _ _).mpr
  refine ⟨by decide, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · apply (Ssz.serializable_iff _ _).mpr
      decide
    · apply (Ssz.serializable_iff _ _).mpr
      decide
    · apply (Ssz.serializable_iff _ _).mpr
      decide
  · decide

private def sizeWire28 : List UInt8 := [12, 0, 0, 0, 13, 0, 0, 0, 13, 0, 0, 0, 1, 2]

private theorem sizeModel28 : logicalSize sizeType28 sizeValue28 = 14 := by
  decide

private theorem sizeActual28 : (Ssz.encode sizeType28 sizeValue28 sizeSupport28).size = 14 :=
  (encode_size_model sizeValue28 sizeType28 sizeSupport28).trans sizeModel28

#guard (Ssz.encode sizeType28 sizeValue28 sizeSupport28).data.toList = sizeWire28
#guard (Ssz.encode sizeType28 sizeValue28 sizeSupport28).size = 14

private abbrev sizeType29 : SszType := (.uint 32)

private def sizeValue29 : SszValue := (.uint 0)

private theorem sizeSupport29 : Ssz.Serializable sizeType29 sizeValue29 := by
  change Ssz.Serializable (.uint 32) (.uint 0)
  apply (Ssz.serializable_iff _ _).mpr
  decide

private def sizeWire29 : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem sizeModel29 : logicalSize sizeType29 sizeValue29 = 32 := by
  decide

private theorem sizeActual29 : (Ssz.encode sizeType29 sizeValue29 sizeSupport29).size = 32 :=
  (encode_size_model sizeValue29 sizeType29 sizeSupport29).trans sizeModel29

#guard (Ssz.encode sizeType29 sizeValue29 sizeSupport29).data.toList = sizeWire29
#guard (Ssz.encode sizeType29 sizeValue29 sizeSupport29).size = 32


private theorem fixed_zero_count_boundary :
    Ssz.Serializable sizeType17 sizeValue17 ∧
      ¬ Ssz.CountRecoverable sizeType17 sizeValue17 := by
  refine ⟨sizeSupport17, ?_⟩
  rw [Ssz.countRecoverable_iff]
  intro h
  exact h.1 rfl

/-! ### Private actual request sizes and inherited support -/

private def transactionSize (transactions : Array ByteArray) : Nat :=
  4 * transactions.size + (transactions.toList.map ByteArray.size).sum

private def payloadSize (p : ExecutionPayload) : Nat :=
  540 + p.extraData.size + transactionSize p.transactions + 44 * p.withdrawals.size +
    p.blockAccessList.size

private def requestsSize (a : ExecutionRequests) : Nat :=
  20 + 192 * a.deposits.size + 76 * a.withdrawals.size + 116 * a.consolidations.size +
    184 * a.builderDeposits.size + 68 * a.builderExits.size

private def requestSize (q : NewPayloadRequest) : Nat :=
  44 + payloadSize q.executionPayload + 32 * q.versionedHashes.size +
    requestsSize q.executionRequests

private theorem withdrawal_fixed_size :
    STFSpec.Block.Withdrawal.instSszSchema.type.fixedSize? = some 44 := by
  dsimp only [SszSchema.type, STFSpec.Block.Withdrawal.instSszSchema]
  simp [SszType.fixedSize?_eq (.container _),
    SszType.fixedSize?_eq (.byteVector _), SszType.fixedSize?_eq (.uint _)]

private theorem deposit_fixed_size : DepositRequest.instSszSchema.type.fixedSize? = some 192 := by
  dsimp only [SszSchema.type, DepositRequest.instSszSchema]
  simp [SszType.fixedSize?_eq (.container _),
    SszType.fixedSize?_eq (.byteVector _), SszType.fixedSize?_eq (.uint _)]

private theorem withdrawal_request_fixed_size :
    WithdrawalRequest.instSszSchema.type.fixedSize? = some 76 := by
  dsimp only [SszSchema.type, WithdrawalRequest.instSszSchema]
  simp [SszType.fixedSize?_eq (.container _),
    SszType.fixedSize?_eq (.byteVector _), SszType.fixedSize?_eq (.uint _)]

private theorem consolidation_fixed_size :
    ConsolidationRequest.instSszSchema.type.fixedSize? = some 116 := by
  dsimp only [SszSchema.type, ConsolidationRequest.instSszSchema]
  simp [SszType.fixedSize?_eq (.container _),
    SszType.fixedSize?_eq (.byteVector _)]

private theorem builder_deposit_fixed_size :
    BuilderDepositRequest.instSszSchema.type.fixedSize? = some 184 := by
  dsimp only [SszSchema.type, BuilderDepositRequest.instSszSchema]
  simp [SszType.fixedSize?_eq (.container _),
    SszType.fixedSize?_eq (.byteVector _), SszType.fixedSize?_eq (.uint _)]

private theorem builder_exit_fixed_size :
    BuilderExitRequest.instSszSchema.type.fixedSize? = some 68 := by
  dsimp only [SszSchema.type, BuilderExitRequest.instSszSchema]
  simp [SszType.fixedSize?_eq (.container _),
    SszType.fixedSize?_eq (.byteVector _)]

private theorem payload_variable_size : ExecutionPayload.instSszSchema.type.fixedSize? = none := by
  dsimp only [SszSchema.type, ExecutionPayload.instSszSchema]
  simp [SszType.fixedSize?_eq (.progressiveContainer _ _),
    SszType.fixedSize?_eq (.byteVector _), SszType.fixedSize?_eq (.uint _),
    SszType.fixedSize?_eq (.byteList _), SszType.fixedSize?_eq (.progressiveList _),
    SszType.fixedSize?_eq .progressiveByteList]

private theorem requests_variable_size :
    ExecutionRequests.instSszSchema.type.fixedSize? = none := by
  dsimp only [SszSchema.type, ExecutionRequests.instSszSchema]
  simp [SszType.fixedSize?_eq (.progressiveContainer _ _),
    SszType.fixedSize?_eq (.progressiveList _)]

private theorem transactions_logical_size (transactions : Array ByteArray) :
    logicalSize (.progressiveList .progressiveByteList)
      (.list (transactions.toList.map SszValue.bytes)) = transactionSize transactions := by
  rw [logicalSize_recurrence]
  simp only [SszType.fixedSize?_eq .progressiveByteList, List.length_map,
    Array.length_toList, List.map_map, Function.comp_def,
    logicalSize_recurrence .progressiveByteList (.bytes _), transactionSize]

private theorem payload_logical_size (p : ExecutionPayload) :
    logicalSize ExecutionPayload.instSszSchema.type
      (ExecutionPayload.instSszSchema.toValue p) = payloadSize p := by
  change logicalSize (.progressiveContainer (List.replicate 19 true) [
    .byteVector 32, .byteVector 20, .byteVector 32, .byteVector 32,
    .byteVector 256, .byteVector 32, .uint 8, .uint 8, .uint 8, .uint 8,
    .byteList maxExtraDataBytes, .uint 32, .byteVector 32,
    .progressiveList .progressiveByteList,
    .progressiveList STFSpec.Block.Withdrawal.instSszSchema.type,
    .uint 8, .uint 8, .progressiveByteList, .uint 8]) (.container [
      .bytes p.parentHash.toBytes.toByteArray, .bytes p.feeRecipient.toBytes.toByteArray,
      .bytes p.stateRoot.toBytes.toByteArray, .bytes p.receiptsRoot.toBytes.toByteArray,
      .bytes p.logsBloom.toBytes.toByteArray, .bytes p.prevRandao.toBytes.toByteArray,
      .uint p.blockNumber.toNat, .uint p.gasLimit.toNat, .uint p.gasUsed.toNat,
      .uint p.timestamp.toNat, .bytes p.extraData, .uint p.baseFeePerGas.toNat,
      .bytes p.blockHash.toBytes.toByteArray,
      .list (p.transactions.toList.map SszValue.bytes),
      .list (p.withdrawals.toList.map STFSpec.Block.Withdrawal.instSszSchema.toValue),
      .uint p.blobGasUsed.toNat, .uint p.excessBlobGas.toNat, .bytes p.blockAccessList,
      .uint p.slotNumber.toNat]) = _
  rw [logicalSize_recurrence]
  simp only [List.zip_cons_cons, List.zip_nil_left, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, SszType.fixedSize?_eq (.byteVector _),
    SszType.fixedSize?_eq (.uint _), SszType.fixedSize?_eq (.byteList _),
    SszType.fixedSize?_eq (.progressiveList _),
    SszType.fixedSize?_eq .progressiveByteList,
    logicalSize_recurrence (.byteList _) (.bytes _),
    logicalSize_recurrence .progressiveByteList (.bytes _),
    transactions_logical_size, logicalSize_recurrence
      (.progressiveList STFSpec.Block.Withdrawal.instSszSchema.type) (.list _),
    withdrawal_fixed_size, List.length_map, Array.length_toList, payloadSize]
  omega

private theorem requests_logical_size (a : ExecutionRequests) :
    logicalSize ExecutionRequests.instSszSchema.type
      (ExecutionRequests.instSszSchema.toValue a) = requestsSize a := by
  change logicalSize (.progressiveContainer [true, true, true, true, true] [
    .progressiveList DepositRequest.instSszSchema.type,
    .progressiveList WithdrawalRequest.instSszSchema.type,
    .progressiveList ConsolidationRequest.instSszSchema.type,
    .progressiveList BuilderDepositRequest.instSszSchema.type,
    .progressiveList BuilderExitRequest.instSszSchema.type]) (.container [
      .list (a.deposits.toList.map DepositRequest.instSszSchema.toValue),
      .list (a.withdrawals.toList.map WithdrawalRequest.instSszSchema.toValue),
      .list (a.consolidations.toList.map ConsolidationRequest.instSszSchema.toValue),
      .list (a.builderDeposits.toList.map BuilderDepositRequest.instSszSchema.toValue),
      .list (a.builderExits.toList.map BuilderExitRequest.instSszSchema.toValue)]) = _
  rw [logicalSize_recurrence]
  simp only [List.zip_cons_cons, List.zip_nil_left, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, SszType.fixedSize?_eq (.progressiveList _),
    logicalSize_recurrence (.progressiveList _) (.list _), deposit_fixed_size,
    withdrawal_request_fixed_size, consolidation_fixed_size, builder_deposit_fixed_size,
    builder_exit_fixed_size, List.length_map, Array.length_toList, requestsSize]
  omega

private theorem request_logical_size (q : NewPayloadRequest) :
    logicalSize NewPayloadRequest.instSszSchema.type
      (NewPayloadRequest.instSszSchema.toValue q) = requestSize q := by
  change logicalSize (.container [ExecutionPayload.instSszSchema.type,
    .progressiveList (.byteVector 32), .byteVector 32, ExecutionRequests.instSszSchema.type])
    (.container [ExecutionPayload.instSszSchema.toValue q.executionPayload,
      .list (q.versionedHashes.toList.map (fun h ↦ .bytes h.toBytes.toByteArray)),
      .bytes q.parentBeaconBlockRoot.toBytes.toByteArray,
      ExecutionRequests.instSszSchema.toValue q.executionRequests]) = _
  rw [logicalSize_recurrence]
  simp only [List.zip_cons_cons, List.zip_nil_left, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, payload_variable_size, requests_variable_size,
    SszType.fixedSize?_eq (.progressiveList _), SszType.fixedSize?_eq (.byteVector _),
    payload_logical_size, requests_logical_size,
    logicalSize_recurrence (.progressiveList _) (.list _),
    List.length_map, Array.length_toList, requestSize]
  omega

private theorem transactions_encoded_size (transactions : Array ByteArray)
    (h : Ssz.Serializable (.progressiveList .progressiveByteList)
      (.list (transactions.toList.map SszValue.bytes))) :
    (Ssz.encode _ _ h).size = transactionSize transactions :=
  (encode_size_model _ _ h).trans (transactions_logical_size transactions)

private theorem payload_encoded_size (p : ExecutionPayload)
    (h : Ssz.Serializable ExecutionPayload.instSszSchema.type
      (ExecutionPayload.instSszSchema.toValue p)) :
    (Ssz.encode _ _ h).size = payloadSize p :=
  (encode_size_model _ _ h).trans (payload_logical_size p)

private theorem requests_encoded_size (a : ExecutionRequests)
    (h : Ssz.Serializable ExecutionRequests.instSszSchema.type
      (ExecutionRequests.instSszSchema.toValue a)) :
    (Ssz.encode _ _ h).size = requestsSize a :=
  (encode_size_model _ _ h).trans (requests_logical_size a)

private theorem request_encoded_size (q : NewPayloadRequest)
    (h : Ssz.Serializable NewPayloadRequest.instSszSchema.type
      (NewPayloadRequest.instSszSchema.toValue q)) :
    (Ssz.encode _ _ h).size = requestSize q :=
  (encode_size_model _ _ h).trans (request_logical_size q)

private theorem withdrawal_encoded_size (a : STFSpec.Block.Withdrawal)
    (h : Ssz.Serializable STFSpec.Block.Withdrawal.instSszSchema.type
      (STFSpec.Block.Withdrawal.instSszSchema.toValue a)) :
    (Ssz.encode _ _ h).size = 44 :=
  encode_fixed_size _ _ h 44 withdrawal_fixed_size

private theorem deposit_encoded_size (a : DepositRequest)
    (h : Ssz.Serializable DepositRequest.instSszSchema.type
      (DepositRequest.instSszSchema.toValue a)) :
    (Ssz.encode _ _ h).size = 192 :=
  encode_fixed_size _ _ h 192 deposit_fixed_size

private theorem withdrawal_request_encoded_size (a : WithdrawalRequest)
    (h : Ssz.Serializable WithdrawalRequest.instSszSchema.type
      (WithdrawalRequest.instSszSchema.toValue a)) :
    (Ssz.encode _ _ h).size = 76 :=
  encode_fixed_size _ _ h 76 withdrawal_request_fixed_size

private theorem consolidation_encoded_size (a : ConsolidationRequest)
    (h : Ssz.Serializable ConsolidationRequest.instSszSchema.type
      (ConsolidationRequest.instSszSchema.toValue a)) :
    (Ssz.encode _ _ h).size = 116 :=
  encode_fixed_size _ _ h 116 consolidation_fixed_size

private theorem builder_deposit_encoded_size (a : BuilderDepositRequest)
    (h : Ssz.Serializable BuilderDepositRequest.instSszSchema.type
      (BuilderDepositRequest.instSszSchema.toValue a)) :
    (Ssz.encode _ _ h).size = 184 :=
  encode_fixed_size _ _ h 184 builder_deposit_fixed_size

private theorem builder_exit_encoded_size (a : BuilderExitRequest)
    (h : Ssz.Serializable BuilderExitRequest.instSszSchema.type
      (BuilderExitRequest.instSszSchema.toValue a)) :
    (Ssz.encode _ _ h).size = 68 :=
  encode_fixed_size _ _ h 68 builder_exit_fixed_size

private theorem request_children_serializable (q : NewPayloadRequest)
    (h : Ssz.Serializable NewPayloadRequest.instSszSchema.type
      (NewPayloadRequest.instSszSchema.toValue q)) :
    Ssz.Serializable ExecutionPayload.instSszSchema.type
      (ExecutionPayload.instSszSchema.toValue q.executionPayload) ∧
    Ssz.Serializable (.progressiveList (.byteVector 32))
      (.list (q.versionedHashes.toList.map (fun h ↦ .bytes h.toBytes.toByteArray))) ∧
    Ssz.Serializable (.byteVector 32) (.bytes q.parentBeaconBlockRoot.toBytes.toByteArray) ∧
    Ssz.Serializable ExecutionRequests.instSszSchema.type
      (ExecutionRequests.instSszSchema.toValue q.executionRequests) := by
  have hs := ((Ssz.serializable_iff _ _).mp h).2.1
  refine ⟨hs (ExecutionPayload.instSszSchema.type,
      ExecutionPayload.instSszSchema.toValue q.executionPayload) ?_,
    hs (.progressiveList (.byteVector 32), .list (q.versionedHashes.toList.map
      (fun h ↦ .bytes h.toBytes.toByteArray))) ?_,
    hs (.byteVector 32, .bytes q.parentBeaconBlockRoot.toBytes.toByteArray) ?_,
    hs (ExecutionRequests.instSszSchema.type,
      ExecutionRequests.instSszSchema.toValue q.executionRequests) ?_⟩ <;>
    simp

private theorem payload_children_serializable (p : ExecutionPayload)
    (h : Ssz.Serializable ExecutionPayload.instSszSchema.type
      (ExecutionPayload.instSszSchema.toValue p)) :
    Ssz.Serializable (.progressiveList .progressiveByteList)
      (.list (p.transactions.toList.map SszValue.bytes)) ∧
    Ssz.Serializable (.progressiveList STFSpec.Block.Withdrawal.instSszSchema.type)
      (.list (p.withdrawals.toList.map STFSpec.Block.Withdrawal.instSszSchema.toValue)) ∧
    Ssz.Serializable (.byteList maxExtraDataBytes) (.bytes p.extraData) ∧
    Ssz.Serializable .progressiveByteList (.bytes p.blockAccessList) := by
  have hs := ((Ssz.serializable_iff _ _).mp h).2.1
  refine ⟨hs (.progressiveList .progressiveByteList,
      .list (p.transactions.toList.map SszValue.bytes)) ?_,
    hs (.progressiveList STFSpec.Block.Withdrawal.instSszSchema.type,
      .list (p.withdrawals.toList.map STFSpec.Block.Withdrawal.instSszSchema.toValue)) ?_,
    hs (.byteList maxExtraDataBytes, .bytes p.extraData) ?_,
    hs (.progressiveByteList, .bytes p.blockAccessList) ?_⟩ <;>
    simp

private theorem requests_children_serializable (a : ExecutionRequests)
    (h : Ssz.Serializable ExecutionRequests.instSszSchema.type
      (ExecutionRequests.instSszSchema.toValue a)) :
    Ssz.Serializable (.progressiveList DepositRequest.instSszSchema.type)
      (.list (a.deposits.toList.map DepositRequest.instSszSchema.toValue)) ∧
    Ssz.Serializable (.progressiveList WithdrawalRequest.instSszSchema.type)
      (.list (a.withdrawals.toList.map WithdrawalRequest.instSszSchema.toValue)) ∧
    Ssz.Serializable (.progressiveList ConsolidationRequest.instSszSchema.type)
      (.list (a.consolidations.toList.map ConsolidationRequest.instSszSchema.toValue)) ∧
    Ssz.Serializable (.progressiveList BuilderDepositRequest.instSszSchema.type)
      (.list (a.builderDeposits.toList.map BuilderDepositRequest.instSszSchema.toValue)) ∧
    Ssz.Serializable (.progressiveList BuilderExitRequest.instSszSchema.type)
      (.list (a.builderExits.toList.map BuilderExitRequest.instSszSchema.toValue)) := by
  have hs := ((Ssz.serializable_iff _ _).mp h).2.1
  refine ⟨hs (.progressiveList DepositRequest.instSszSchema.type,
      .list (a.deposits.toList.map DepositRequest.instSszSchema.toValue)) ?_,
    hs (.progressiveList WithdrawalRequest.instSszSchema.type,
      .list (a.withdrawals.toList.map WithdrawalRequest.instSszSchema.toValue)) ?_,
    hs (.progressiveList ConsolidationRequest.instSszSchema.type,
      .list (a.consolidations.toList.map ConsolidationRequest.instSszSchema.toValue)) ?_,
    hs (.progressiveList BuilderDepositRequest.instSszSchema.type,
      .list (a.builderDeposits.toList.map BuilderDepositRequest.instSszSchema.toValue)) ?_,
    hs (.progressiveList BuilderExitRequest.instSszSchema.type,
      .list (a.builderExits.toList.map BuilderExitRequest.instSszSchema.toValue)) ?_⟩ <;>
    simp

private theorem progressive_members_serializable {α : Type} (t : SszType)
    (model : α → SszValue) (xs : List α)
    (h : Ssz.Serializable (.progressiveList t) (.list (xs.map model))) :
    ∀ x ∈ xs, Ssz.Serializable t (model x) := by
  have hs := ((Ssz.serializable_iff _ _).mp h).1
  intro x hx
  exact hs _ (List.mem_map.mpr ⟨x, hx, rfl⟩)

private theorem request_hashes_serializable (q : NewPayloadRequest)
    (h : Ssz.Serializable NewPayloadRequest.instSszSchema.type
      (NewPayloadRequest.instSszSchema.toValue q)) :
    ∀ b ∈ q.versionedHashes.toList,
      Ssz.Serializable (.byteVector 32) (.bytes b.toBytes.toByteArray) :=
  progressive_members_serializable _ _ _ (request_children_serializable q h).2.1

private theorem payload_members_serializable (p : ExecutionPayload)
    (h : Ssz.Serializable ExecutionPayload.instSszSchema.type
      (ExecutionPayload.instSszSchema.toValue p)) :
    (∀ b ∈ p.transactions.toList, Ssz.Serializable .progressiveByteList (.bytes b)) ∧
    (∀ w ∈ p.withdrawals.toList, Ssz.Serializable STFSpec.Block.Withdrawal.instSszSchema.type
      (STFSpec.Block.Withdrawal.instSszSchema.toValue w)) := by
  have hs := payload_children_serializable p h
  exact ⟨progressive_members_serializable _ _ _ hs.1,
    progressive_members_serializable _ _ _ hs.2.1⟩

private theorem requests_members_serializable (a : ExecutionRequests)
    (h : Ssz.Serializable ExecutionRequests.instSszSchema.type
      (ExecutionRequests.instSszSchema.toValue a)) :
    (∀ d ∈ a.deposits.toList, Ssz.Serializable DepositRequest.instSszSchema.type
      (DepositRequest.instSszSchema.toValue d)) ∧
    (∀ w ∈ a.withdrawals.toList, Ssz.Serializable WithdrawalRequest.instSszSchema.type
      (WithdrawalRequest.instSszSchema.toValue w)) ∧
    (∀ c ∈ a.consolidations.toList, Ssz.Serializable ConsolidationRequest.instSszSchema.type
      (ConsolidationRequest.instSszSchema.toValue c)) ∧
    (∀ b ∈ a.builderDeposits.toList, Ssz.Serializable BuilderDepositRequest.instSszSchema.type
      (BuilderDepositRequest.instSszSchema.toValue b)) ∧
    (∀ b ∈ a.builderExits.toList, Ssz.Serializable BuilderExitRequest.instSszSchema.type
      (BuilderExitRequest.instSszSchema.toValue b)) := by
  have hs := requests_children_serializable a h
  exact ⟨progressive_members_serializable _ _ _ hs.1,
    progressive_members_serializable _ _ _ hs.2.1,
    progressive_members_serializable _ _ _ hs.2.2.1,
    progressive_members_serializable _ _ _ hs.2.2.2.1,
    progressive_members_serializable _ _ _ hs.2.2.2.2⟩

/-! ### Symbolic actual-size probes -/

private theorem empty_transactions_logical_size (n : Nat) :
    logicalSize (.progressiveList .progressiveByteList)
      (.list (List.replicate n (.bytes (ByteArray.mk #[])))) = 4 * n := by
  rw [logicalSize_recurrence]
  simp [SszType.fixedSize?_eq .progressiveByteList,
    logicalSize_recurrence .progressiveByteList (.bytes _),
    show (ByteArray.mk #[]).size = 0 from rfl]

private theorem final_transaction_logical_size (n : Nat) (b : ByteArray) :
    logicalSize (.progressiveList .progressiveByteList)
      (.list (List.replicate n (.bytes (ByteArray.mk #[])) ++ [.bytes b])) =
        4 * (n + 1) + b.size := by
  rw [logicalSize_recurrence]
  simp [SszType.fixedSize?_eq .progressiveByteList,
    logicalSize_recurrence .progressiveByteList (.bytes _),
    show (ByteArray.mk #[]).size = 0 from rfl]

private theorem payload_bal_replacement_size (p : ExecutionPayload) (b : ByteArray) :
    logicalSize ExecutionPayload.instSszSchema.type
      (ExecutionPayload.instSszSchema.toValue { p with blockAccessList := b }) +
        p.blockAccessList.size =
    logicalSize ExecutionPayload.instSszSchema.type (ExecutionPayload.instSszSchema.toValue p) +
      b.size := by
  rw [payload_logical_size, payload_logical_size]
  simp only [payloadSize]
  omega

-- This raw equation includes b.size above the extra-data wire limit; it makes no encoder call.
private theorem payload_extra_data_replacement_size (p : ExecutionPayload) (b : ByteArray) :
    logicalSize ExecutionPayload.instSszSchema.type
      (ExecutionPayload.instSszSchema.toValue { p with extraData := b }) + p.extraData.size =
    logicalSize ExecutionPayload.instSszSchema.type (ExecutionPayload.instSszSchema.toValue p) +
      b.size := by
  rw [payload_logical_size, payload_logical_size]
  simp only [payloadSize]
  omega

private theorem deposit_append_logical_size (a : ExecutionRequests) (x : DepositRequest) :
    logicalSize ExecutionRequests.instSszSchema.type
      (ExecutionRequests.instSszSchema.toValue { a with deposits := a.deposits.push x }) =
    logicalSize ExecutionRequests.instSszSchema.type (ExecutionRequests.instSszSchema.toValue a) +
      192 := by
  rw [requests_logical_size, requests_logical_size]
  simp only [requestsSize, Array.size_push]
  omega

private theorem withdrawal_request_append_logical_size (a : ExecutionRequests)
    (x : WithdrawalRequest) :
    logicalSize ExecutionRequests.instSszSchema.type
      (ExecutionRequests.instSszSchema.toValue { a with withdrawals := a.withdrawals.push x }) =
    logicalSize ExecutionRequests.instSszSchema.type (ExecutionRequests.instSszSchema.toValue a) +
      76 := by
  rw [requests_logical_size, requests_logical_size]
  simp only [requestsSize, Array.size_push]
  omega

private theorem consolidation_append_logical_size (a : ExecutionRequests)
    (x : ConsolidationRequest) :
    logicalSize ExecutionRequests.instSszSchema.type
      (ExecutionRequests.instSszSchema.toValue
        { a with consolidations := a.consolidations.push x }) =
    logicalSize ExecutionRequests.instSszSchema.type (ExecutionRequests.instSszSchema.toValue a) +
      116 := by
  rw [requests_logical_size, requests_logical_size]
  simp only [requestsSize, Array.size_push]
  omega

private theorem builder_deposit_append_logical_size (a : ExecutionRequests)
    (x : BuilderDepositRequest) :
    logicalSize ExecutionRequests.instSszSchema.type
      (ExecutionRequests.instSszSchema.toValue
        { a with builderDeposits := a.builderDeposits.push x }) =
    logicalSize ExecutionRequests.instSszSchema.type (ExecutionRequests.instSszSchema.toValue a) +
      184 := by
  rw [requests_logical_size, requests_logical_size]
  simp only [requestsSize, Array.size_push]
  omega

private theorem builder_exit_append_logical_size (a : ExecutionRequests) (x : BuilderExitRequest) :
    logicalSize ExecutionRequests.instSszSchema.type
      (ExecutionRequests.instSszSchema.toValue { a with builderExits := a.builderExits.push x }) =
    logicalSize ExecutionRequests.instSszSchema.type (ExecutionRequests.instSszSchema.toValue a) +
      68 := by
  rw [requests_logical_size, requests_logical_size]
  simp only [requestsSize, Array.size_push]
  omega

end STFSpec.Conformance.Stateless.InputSszCallerProofs
