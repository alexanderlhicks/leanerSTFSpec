/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec
import Init.Data.List.Monadic

/-!
# Generic list RLP public-law callers

Library `EthConformance`. Ten private caller groups use public model contracts.
Value equations do not assert callback execution traces or resource bounds.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Conformance.Codec.RlpListCallerProofs
open STFSpec.Codec STFSpec.Codec.Rlp

-- CP01: Complete ordered encoder model and every encoded byte.
private theorem encoder {α : Type} [RlpEncode α] (xs : List α) :
    RlpEncode.toRlp xs = .list (xs.map RlpEncode.toRlp) := rfl
private theorem wire_model {α : Type} [RlpEncode α] (xs : List α) :
    (encodeOf xs).data.toList = encodeModel (.list (xs.map RlpEncode.toRlp)) :=
  toList_encode _
private theorem wire_list_model {α : Type} [RlpEncode α] (xs : List α) :
    (encodeOf xs).data.toList =
      lengthPrefixModel 192 247 (encodePayloadModel (xs.map RlpEncode.toRlp)).length ++
        encodePayloadModel (xs.map RlpEncode.toRlp) := toList_encode_list _

-- CP02: Public shape/bind/mapM composition and public core traversal equations.
private theorem decoder {α : Type} [RlpDecode α] (item : RlpItem) :
    RlpDecode.ofRlp (α := List α) item = (toList item).bind
      (fun children => children.mapM (RlpDecode.ofRlp (α := α))) := rfl
private theorem decoder_bytes {α : Type} [RlpDecode α] (b : ByteArray) :
    RlpDecode.ofRlp (α := List α) (.bytes b) = .error (.shape "list") := rfl
private theorem decoder_nil {α : Type} [RlpDecode α] :
    RlpDecode.ofRlp (α := List α) (.list []) = .ok [] := by
  change [].mapM (RlpDecode.ofRlp (α := α)) = .ok []
  rw [List.mapM_nil]; rfl
private theorem decoder_cons {α : Type} [RlpDecode α] (x : RlpItem) (xs : List RlpItem) :
    RlpDecode.ofRlp (α := List α) (.list (x :: xs)) =
      (RlpDecode.ofRlp (α := α) x).bind (fun a =>
        (RlpDecode.ofRlp (α := List α) (.list xs)).bind (fun rest => .ok (a :: rest))) := by
  change (x :: xs).mapM (RlpDecode.ofRlp (α := α)) = _
  rw [List.mapM_cons]
  rfl

-- CP03: Actual-member agreement, with no Encodable premise.
private theorem model_inverse {α : Type} [RlpEncode α] [RlpDecode α] (xs : List α)
    (hElements : ∀ a ∈ xs, RlpDecode.ofRlp (RlpEncode.toRlp a) =
      (Except.ok a : Except RlpError α)) :
    RlpDecode.ofRlp (RlpEncode.toRlp xs) = (Except.ok xs : Except RlpError (List α)) :=
  ofRlp_toRlp_list xs hElements
private theorem global_restricts {α : Type} [RlpEncode α] [RlpDecode α] (xs : List α)
    (hAll : ∀ a : α, RlpDecode.ofRlp (RlpEncode.toRlp a) = .ok a) :
    RlpDecode.ofRlp (RlpEncode.toRlp xs) = (Except.ok xs : Except RlpError (List α)) :=
  ofRlp_toRlp_list xs (fun a _ => hAll a)

-- CP04: The same local premise and the complete assembled wire domain.
private theorem wire_inverse {α : Type} [RlpEncode α] [RlpDecode α] (xs : List α)
    (hElements : ∀ a ∈ xs, RlpDecode.ofRlp (RlpEncode.toRlp a) =
      (Except.ok a : Except RlpError α))
    (h : Encodable (.list (xs.map RlpEncode.toRlp))) :
    decodeTo (encodeOf xs) = (Except.ok xs : Except RlpError (List α)) :=
  decodeTo_encodeOf_list xs hElements h
private theorem whole_domain {α : Type} [RlpEncode α] (xs : List α) :
    Encodable (.list (xs.map RlpEncode.toRlp)) ↔
      (∀ x ∈ xs.map RlpEncode.toRlp, Encodable x) ∧
      (encodePayloadModel (xs.map RlpEncode.toRlp)).length < 2 ^ 64 :=
  encodable_list_iff _

-- CP05: Recursively reuse the PUBLIC model law, without any wire-domain detour.
private theorem nested_model {α : Type} [RlpEncode α] [RlpDecode α] (xss : List (List α))
    (hElements : ∀ xs ∈ xss, ∀ a ∈ xs, RlpDecode.ofRlp (RlpEncode.toRlp a) =
      (Except.ok a : Except RlpError α)) :
    RlpDecode.ofRlp (RlpEncode.toRlp xss) =
      (Except.ok xss : Except RlpError (List (List α))) :=
  ofRlp_toRlp_list xss (fun xs hxs => ofRlp_toRlp_list xs (hElements xs hxs))
private theorem nested_nat :
    RlpDecode.ofRlp (RlpEncode.toRlp ([[0],[1,0]] : List (List Nat))) =
      (Except.ok [[0],[1,0]] : Except RlpError (List (List Nat))) :=
  ofRlp_toRlp_list _ (fun xs _ => ofRlp_toRlp_list xs (fun a _ => toNat_ofNat a))

-- CP06: Vacuous membership supports unrelated instances even with a failing decoder.
private structure Fail where
  value : Nat
private instance : RlpEncode Fail := ⟨fun x => ofNat x.value⟩
private instance : RlpDecode Fail := ⟨fun _ => .error (.shape "always")⟩
private theorem empty_model :
    RlpDecode.ofRlp (RlpEncode.toRlp ([] : List Fail)) =
      (Except.ok [] : Except RlpError (List Fail)) :=
  ofRlp_toRlp_list [] (fun _ h => nomatch h)
private theorem empty_domain : Encodable (.list []) := by
  rw [encodable_list_iff]
  constructor
  · intro x h; cases h
  · change 0 < 2 ^ 64
    decide
private theorem empty_wire : decodeTo (encodeOf ([] : List Fail)) =
    (Except.ok [] : Except RlpError (List Fail)) :=
  decodeTo_encodeOf_list [] (fun _ h => nomatch h) empty_domain

-- CP07: Complete arbitrary first-error VALUES, with arbitrary later callbacks.
private theorem first_error {α : Type} [RlpDecode α] (x : RlpItem) (xs : List RlpItem)
    (e : RlpError) (hx : RlpDecode.ofRlp (α := α) x = .error e) :
    RlpDecode.ofRlp (α := List α) (.list (x :: xs)) = .error e := by
  rw [decoder_cons, hx]; rfl
private theorem late_error {α : Type} [RlpDecode α] (x y : RlpItem)
    (xs : List RlpItem) (a : α) (e : RlpError)
    (hx : RlpDecode.ofRlp x = .ok a) (hy : RlpDecode.ofRlp (α := α) y = .error e) :
    RlpDecode.ofRlp (α := List α) (.list (x :: y :: xs)) = .error e := by
  rw [decoder_cons, hx, first_error y xs e hy]; rfl
private theorem competing_errors {α : Type} [RlpDecode α] (x y : RlpItem)
    (xs : List RlpItem) (e f : RlpError) (_hne : e ≠ f)
    (hx : RlpDecode.ofRlp (α := α) x = .error e)
    (_hy : RlpDecode.ofRlp (α := α) y = .error f) :
    RlpDecode.ofRlp (α := List α) (.list (x :: y :: xs)) = .error e :=
  first_error x (y :: xs) e hx

-- CP08: Complete raw failure precedes every list callback.
private theorem raw_first {α : Type} [RlpDecode α] (wire : ByteArray) (e : RlpError)
    (h : decode wire = .error e) : decodeTo (α := List α) wire = .error e := by
  unfold decodeTo; rw [h]
private theorem raw_trailing {α : Type} [RlpDecode α]
    (h : decode ⟨#[193,0,0]⟩ = .error .trailing) :
    decodeTo (α := List α) ⟨#[193,0,0]⟩ = .error .trailing :=
  raw_first _ _ h
private theorem raw_later_truncated {α : Type} [RlpDecode α]
    (h : decode ⟨#[194,0,129]⟩ = .error .truncated) :
    decodeTo (α := List α) ⟨#[194,0,129]⟩ = .error .truncated :=
  raw_first _ _ h
private theorem raw_later_canonical {α : Type} [RlpDecode α]
    (h : decode ⟨#[195,0,129,1]⟩ = .error (.nonCanonical "prefixed single byte")) :
    decodeTo (α := List α) ⟨#[195,0,129,1]⟩ =
      .error (.nonCanonical "prefixed single byte") := raw_first _ _ h

-- CP09: Independent classes do not promise generic inversion or value recovery.
private structure Const where
  value : Nat
private structure Local where
  value : Nat
private instance : RlpEncode Const := ⟨fun x => ofNat x.value⟩
private instance : RlpDecode Const := ⟨fun _ => .ok ⟨0⟩⟩
private instance : RlpEncode Local := ⟨fun x => ofNat x.value⟩
private instance : RlpDecode Local := ⟨fun item => (toNat item).bind
  (fun n => if n = 0 then .ok ⟨0⟩ else .error (.shape "absent two"))⟩
private theorem nonempty_failure :
    RlpDecode.ofRlp (RlpEncode.toRlp ([⟨0⟩] : List Fail)) =
      (Except.error (.shape "always") : Except RlpError (List Fail)) := by
  rw [encoder, List.map_cons, decoder_cons]
  rfl
private theorem no_nonempty_inverse :
    RlpDecode.ofRlp (RlpEncode.toRlp ([⟨0⟩] : List Fail)) ≠
      (Except.ok [⟨0⟩] : Except RlpError (List Fail)) := by
  rw [nonempty_failure]; intro h; cases h
private theorem constant_success :
    decodeTo (α := List Const) ⟨#[193,1]⟩ = .ok [⟨0⟩] := by
  have hp : encodePayloadModel [.bytes ⟨#[1]⟩] = [1] := by
    rw [encodePayloadModel_cons, encodePayloadModel_nil, ← toList_encodeBytes,
      encodeBytes_single _ 1 (by decide) (by decide) (by decide)]
    rfl
  have he : encode (.list [.bytes ⟨#[1]⟩]) = (⟨#[193,1]⟩ : ByteArray) := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [toList_encode_list, hp, lengthPrefixModel_short _ _ _ (by decide)]
    rfl
  have hd : decode ⟨#[193,1]⟩ = .ok (.list [.bytes ⟨#[1]⟩]) := by
    rw [← he]
    apply decode_encode
    rw [encodable_list_iff]
    constructor
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst x
      rw [encodable_bytes_iff]; decide
    · rw [hp]
      decide
  unfold decodeTo
  rw [hd]
  change RlpDecode.ofRlp (α := List Const) (.list [.bytes ⟨#[1]⟩]) = .ok [⟨0⟩]
  rw [decoder_cons, decoder_nil]
  rfl
private theorem constant_changes_wire :
    encodeOf ([⟨0⟩] : List Const) ≠ (⟨#[193,1]⟩ : ByteArray) := by
  have hb : (STFSpec.Base.Uint.toBeBytes 0).toByteArray = (⟨#[]⟩ : ByteArray) := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [STFSpec.Base.Bytes.toList_toByteArray, STFSpec.Base.Uint.toBeBytes_zero,
      STFSpec.Base.Bytes.toList_empty]
  have hx : RlpEncode.toRlp (⟨0⟩ : Const) = .bytes (⟨#[]⟩ : ByteArray) := by
    change ofNat 0 = _
    unfold ofNat
    rw [hb]
  have hp : encodePayloadModel [RlpEncode.toRlp (⟨0⟩ : Const)] = [128] := by
    rw [hx, encodePayloadModel_cons, encodePayloadModel_nil, ← toList_encodeBytes,
      encodeBytes_short _ (by decide) (by decide)]
    rfl
  intro h
  have hm := congrArg (fun b : ByteArray => b.data.toList) h
  rw [wire_list_model, List.map_cons, List.map_nil, hp,
    lengthPrefixModel_short _ _ _ (by decide)] at hm
  have hne : ([193,128] : List UInt8) ≠ [193,1] := by decide
  exact hne hm
private theorem local_members : ∀ a ∈ ([⟨0⟩,⟨0⟩] : List Local),
    RlpDecode.ofRlp (RlpEncode.toRlp a) = (Except.ok a : Except RlpError Local) := by
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at ha
  subst a
  change (toNat (ofNat 0)).bind _ = _
  rw [toNat_ofNat]; rfl
private theorem local_model :
    RlpDecode.ofRlp (RlpEncode.toRlp ([⟨0⟩,⟨0⟩] : List Local)) =
      (Except.ok [⟨0⟩,⟨0⟩] : Except RlpError (List Local)) :=
  ofRlp_toRlp_list _ local_members
private theorem absent_failure :
    RlpDecode.ofRlp (RlpEncode.toRlp (⟨2⟩ : Local)) =
      (Except.error (.shape "absent two") : Except RlpError Local) := by
  change (toNat (ofNat 2)).bind _ = _
  rw [toNat_ofNat]; rfl
private theorem local_not_global : ¬ (∀ a : Local,
    RlpDecode.ofRlp (RlpEncode.toRlp a) = (Except.ok a : Except RlpError Local)) := by
  intro h
  have hx := h ⟨2⟩
  rw [absent_failure] at hx
  cases hx

-- CP10: Public Nat/byte/list accept sets keep shape and minimality distinct.
private theorem nat_acceptance (item : RlpItem) (n : Nat) :
    RlpDecode.ofRlp (α := Nat) item = .ok n ↔ item = ofNat n :=
  toNat_eq_ok_iff item n
private theorem bytes_acceptance (item : RlpItem) (b : ByteArray) :
    RlpDecode.ofRlp (α := ByteArray) item = .ok b ↔ item = .bytes b :=
  toBytes_eq_ok_iff item b
private theorem lists_acceptance (item : RlpItem) (xs : List RlpItem) :
    toList item = .ok xs ↔ item = .list xs := toList_eq_ok_iff item xs
private theorem nat_list_no_success (items : List RlpItem) (n : Nat) :
    RlpDecode.ofRlp (α := Nat) (.list items) ≠ .ok n := by
  intro h
  have hx := (toNat_eq_ok_iff _ n).mp h
  cases hx
private theorem bytes_zero_success :
    RlpDecode.ofRlp (α := List ByteArray) (.list [.bytes ⟨#[0]⟩]) =
      .ok [⟨#[0]⟩] := by
  rw [decoder_cons, decoder_nil]; rfl
private theorem nat_zero_no_success (n : Nat) :
    RlpDecode.ofRlp (α := Nat) (.bytes ⟨#[0]⟩) ≠ .ok n := by
  intro h
  have hn := (toNat_eq_ok_bytes_iff _ n).mp h
  exact hn.1 rfl
private theorem byte_not_list (b : ByteArray) (xs : List RlpItem) :
    toList (.bytes b) ≠ .ok xs := by
  intro h
  have hx := (toList_eq_ok_iff _ xs).mp h
  cases hx
private theorem nested_empty :
    RlpDecode.ofRlp (α := List (List Nat)) (.list [.list []]) = .ok [[]] := by
  rw [decoder_cons, decoder_nil, decoder_nil]; rfl

end STFSpec.Conformance.Codec.RlpListCallerProofs
