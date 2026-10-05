/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit.Account
import STFSpec.State.WitnessError

/-!
# Lenient account-leaf decoding

Library `EthStateCommit`. Complete strict RLP parsing precedes the ordered nonce,
balance, root and code conversions. Only the supplied empty-root/code defaults
are observed. The packed balance fold has an ordinary checked-reference proof.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` §§3–7/10.
-/

namespace STFSpec.StateCommit
open Base Codec State

/-! ### Bounded balance folding and reference equality -/

private def checkedBalanceReference (bs : ByteArray) : Option U256 :=
  U256.ofNat? (Uint.ofBeBytes (Bytes.ofByteArray bs))

private def boundedNat (n : Nat) : Option Nat :=
  if n < 2 ^ 256 then some n else none

private def balanceStep : Option Nat → UInt8 → Option Nat
  | none, _ => none
  | some n, byte => if n < 2 ^ 248 then some (256 * n + byte.toNat) else none

private theorem byte_lt (byte : UInt8) : byte.toNat < 256 := by
  have h := Uint.ofBeBytes_lt (Bytes.ofList [byte])
  rw [Uint.ofBeBytes_eq_fold, Bytes.toList_ofList, Bytes.size_ofList] at h
  simpa only [List.foldl_cons, List.foldl_nil, Nat.mul_zero, Nat.zero_add,
    List.length_cons, List.length_nil] using h

set_option exponentiation.threshold 300 in
private theorem balance_threshold (n : Nat) (byte : UInt8) :
    256 * n + byte.toNat < 2 ^ 256 ↔ n < 2 ^ 248 := by
  have hb := byte_lt byte
  have hm : 2 ^ 256 = 256 * (2 ^ 248) := Nat.pow_add 2 8 248
  rw [hm]
  omega

private theorem balanceStep_commutes (n : Nat) (byte : UInt8) :
    balanceStep (boundedNat n) byte = boundedNat (256 * n + byte.toNat) := by
  unfold boundedNat
  by_cases hn : n < 2 ^ 256
  · simp only [hn, ite_true, balanceStep]
    simp only [balance_threshold]
  · have hg : ¬ 256 * n + byte.toNat < 2 ^ 256 := by omega
    simp only [hn, hg, ite_false, balanceStep]

private theorem balanceFold_commutes (xs : List UInt8) (n : Nat) :
    xs.foldl balanceStep (boundedNat n) =
      boundedNat (xs.foldl (fun acc byte ↦ 256 * acc + byte.toNat) n) := by
  induction xs generalizing n with
  | nil => rfl
  | cons byte xs ih =>
    simp only [List.foldl_cons, balanceStep_commutes]
    exact ih _

private theorem balanceFold_absorbing (xs : List UInt8) :
    xs.foldl balanceStep none = none := by
  induction xs with
  | nil => rfl
  | cons byte xs ih => simpa only [List.foldl_cons, balanceStep] using ih

private theorem balancePacked_absorbing (bs : Bytes) :
    bs.foldl balanceStep none = none := by
  rw [Bytes.foldl_eq]
  exact balanceFold_absorbing _

private theorem balanceStep_retained_lt (state : Option Nat) (byte : UInt8) (n : Nat)
    (h : balanceStep state byte = some n) : n < 2 ^ 256 := by
  cases state with
  | none => simp [balanceStep] at h
  | some acc =>
    simp only [balanceStep] at h
    split at h
    · next ha =>
      have he := Option.some.inj h
      rw [← he]
      exact (balance_threshold _ _).mpr ha
    · contradiction

private theorem balancePrefix_invariant (xs : List UInt8) (n : Nat) :
    (∀ v, xs.foldl balanceStep (boundedNat n) = some v ↔
      xs.foldl (fun acc byte ↦ 256 * acc + byte.toNat) n < 2 ^ 256 ∧
      v = xs.foldl (fun acc byte ↦ 256 * acc + byte.toNat) n) ∧
    (xs.foldl balanceStep (boundedNat n) = none ↔
      2 ^ 256 ≤ xs.foldl (fun acc byte ↦ 256 * acc + byte.toNat) n) := by
  rw [balanceFold_commutes]
  unfold boundedNat
  split <;> simp_all [eq_comm, Nat.not_lt]

private def checkedBalance (bs : ByteArray) : Option U256 :=
  ((Bytes.ofByteArray bs).foldl balanceStep (some 0)).bind U256.ofNat?

private theorem checkedBalance_eq_reference (bs : ByteArray) :
    checkedBalance bs = checkedBalanceReference bs := by
  have hz : boundedNat 0 = some 0 := by simp [boundedNat]
  unfold checkedBalance checkedBalanceReference
  rw [Bytes.foldl_eq, ← hz, balanceFold_commutes, ← Uint.ofBeBytes_eq_fold]
  generalize Uint.ofBeBytes (Bytes.ofByteArray bs) = n
  unfold boundedNat
  split
  · rfl
  · next h => simp only [Option.bind_none, (U256.ofNat?_eq_none_iff n).mpr (by omega)]

/-! ### Lenient field interpretation -/

private def nonceField : RlpItem → Except WitnessError Nat
  | .bytes bs => .ok (Uint.ofBeBytes (Bytes.ofByteArray bs))
  | .list [] => .ok 0
  | .list (_ :: _) => .error (.malformed .leaf)

private def balanceField : RlpItem → Except WitnessError U256
  | .bytes bs =>
    match checkedBalance bs with
    | some v => .ok v
    | none => .error (.malformed .leaf)
  | .list [] => .ok U256.zero
  | .list (_ :: _) => .error (.malformed .leaf)

private def hashField (default : Hash32) : RlpItem → Except WitnessError Hash32
  | .bytes bs =>
    if bs = ByteArray.empty then .ok default else
      match Hash32.ofBytes? (Bytes.ofByteArray bs) with
      | some v => .ok v
      | none => .error (.malformed .leaf)
  | .list [] => .ok default
  | .list (_ :: _) => .error (.malformed .leaf)

private theorem bytes_ne_list (bs : ByteArray) (xs : List RlpItem) :
    (RlpItem.bytes bs) ≠ .list xs := by
  intro h
  cases h

private theorem nonceField_ok (item : RlpItem) (v : Nat) :
    nonceField item = .ok v ↔
      (∃ bs : ByteArray, item = .bytes bs ∧ Uint.ofBeBytes (Bytes.ofByteArray bs) = v) ∨
      (item = .list [] ∧ v = 0) := by
  cases item with
  | bytes bs => simp [nonceField, bytes_ne_list]
  | list xs => cases xs <;> simp [nonceField, eq_comm]

private theorem balanceField_ok (item : RlpItem) (v : U256) :
    balanceField item = .ok v ↔
      (∃ bs : ByteArray, item = .bytes bs ∧
        Uint.ofBeBytes (Bytes.ofByteArray bs) = v.toNat) ∨
      (item = .list [] ∧ v = U256.zero) := by
  cases item with
  | bytes bs =>
    simp only [balanceField, checkedBalance_eq_reference, checkedBalanceReference]
    cases h : U256.ofNat? (Uint.ofBeBytes (Bytes.ofByteArray bs)) with
    | none =>
      have hn := (U256.ofNat?_eq_none_iff _).mp h
      have hv := U256.toNat_lt v
      simp [bytes_ne_list]
      omega
    | some x =>
      have hx := (U256.ofNat?_eq_some_iff _ _).mp h
      simp [bytes_ne_list]
      rw [← hx.2, U256.toNat_inj]
  | list xs => cases xs <;> simp [balanceField, eq_comm]

private theorem hashBytes_ne_empty (v : Hash32) : v.toBytes.toByteArray ≠ ByteArray.empty := by
  intro h
  have hs := congrArg ByteArray.size h
  rw [Bytes.size_toByteArray, Hash32.size_toBytes, ByteArray.size_empty] at hs
  omega

private theorem hashField_ok (default v : Hash32) (item : RlpItem) :
    hashField default item = .ok v ↔
      (((item = .bytes ByteArray.empty) ∨ (item = .list [])) ∧ v = default) ∨
      item = .bytes v.toBytes.toByteArray := by
  cases item with
  | list xs => cases xs <;> simp [hashField, eq_comm]
  | bytes bs =>
    by_cases he : bs = ByteArray.empty
    · subst bs
      simp [hashField, Ne.symm (hashBytes_ne_empty v), eq_comm]
    · simp only [hashField, he, ite_false]
      simp only [RlpItem.bytes.injEq, bytes_ne_list, he, or_false, false_and, false_or]
      have hb : Hash32.ofBytes? (Bytes.ofByteArray bs) = some v ↔
          bs = v.toBytes.toByteArray := by
        constructor
        · intro h
          have hh := (Hash32.ofBytes?_eq_some_iff.mp h).2
          simpa only [Bytes.toByteArray_ofByteArray] using
            (congrArg Bytes.toByteArray hh).symm
        · intro h
          rw [h, Bytes.ofByteArray_toByteArray, Hash32.ofBytes?_toBytes]
      cases h : Hash32.ofBytes? (Bytes.ofByteArray bs) with
      | none => simpa only [h, reduceCtorEq] using hb
      | some x => simpa only [h, Option.some.injEq, Except.ok.injEq] using hb

section
variable (consts : HashConsts)
local notation "EMPTY_CODE_HASH" => consts.emptyCodeHash
local notation "EMPTY_TRIE_ROOT" => consts.emptyTrieRoot

private def accountFields (n b r c : RlpItem) : Except WitnessError (Account × Hash32) := do
  let nonce ← nonceField n
  let balance ← balanceField b
  let root ← hashField EMPTY_TRIE_ROOT r
  let code ← hashField EMPTY_CODE_HASH c
  return (Account.mk nonce balance code, root)

/-- EELS `src/ethereum/forks/amsterdam/witness_state.py:103–127`: complete strict
RLP first, exact four-field list next, then nonce, balance, root and code (SC5). -/
def decodeAccountLeaf (leaf : ByteArray) : Except WitnessError (Account × Hash32) :=
  match Rlp.decode leaf with
  | .ok (.list [n, b, r, c]) => accountFields consts n b r c
  | _ => .error (.malformed .leaf)

end

/-! ### Account result characterization -/

private theorem account_mk_eq (nonce : Nat) (balance : U256) (code : Hash32)
    (acc : Account) : Account.mk nonce balance code = acc ↔
      nonce = acc.nonce ∧ balance = acc.balance ∧ code = acc.codeHash := by
  cases acc
  simp only [Account.mk.injEq]

private theorem accountFields_ok (consts : HashConsts) (n b r c : RlpItem)
    (acc : Account) (root : Hash32) :
    accountFields consts n b r c = .ok (acc, root) ↔
      nonceField n = .ok acc.nonce ∧ balanceField b = .ok acc.balance ∧
      hashField consts.emptyTrieRoot r = .ok root ∧
      hashField consts.emptyCodeHash c = .ok acc.codeHash := by
  cases hn : nonceField n <;> cases hb : balanceField b <;>
    cases hr : hashField consts.emptyTrieRoot r <;>
    cases hc : hashField consts.emptyCodeHash c <;>
    simp [accountFields, hn, hb, hr, hc, bind, pure, Except.bind, Except.pure,
      account_mk_eq, and_assoc, and_left_comm, and_comm]

private theorem decodeAccountLeaf_fields_iff
    (consts : HashConsts) (leaf : ByteArray) (acc : Account) (root : Hash32) :
    decodeAccountLeaf consts leaf = .ok (acc, root) ↔
      ∃ n b r c : RlpItem,
        Rlp.decode leaf = .ok (.list [n, b, r, c]) ∧
        nonceField n = .ok acc.nonce ∧ balanceField b = .ok acc.balance ∧
        hashField consts.emptyTrieRoot r = .ok root ∧
        hashField consts.emptyCodeHash c = .ok acc.codeHash := by
  constructor
  · intro h
    unfold decodeAccountLeaf at h
    split at h
    · next n b r c hp => exact ⟨n, b, r, c, hp, (accountFields_ok _ _ _ _ _ _ _).mp h⟩
    · contradiction
  · rintro ⟨n, b, r, c, hp, hn, hb, hr, hc⟩
    simp only [decodeAccountLeaf, hp]
    exact (accountFields_ok _ _ _ _ _ _ _).mpr ⟨hn, hb, hr, hc⟩

/-! ### Public success contract -/

/-- Complete characterization of accepted fields and their full values (SC5).
The balance model equality imposes its numerical range without a byte-count cap. -/
theorem decodeAccountLeaf_eq_ok_iff
    (consts : HashConsts) (leaf : ByteArray) (acc : Account) (storageRoot : Hash32) :
    decodeAccountLeaf consts leaf = .ok (acc, storageRoot) ↔
      ∃ n b r c : RlpItem,
        Rlp.decode leaf = .ok (.list [n, b, r, c]) ∧
        ((∃ bs : ByteArray,
            n = .bytes bs ∧ Uint.ofBeBytes (Bytes.ofByteArray bs) = acc.nonce) ∨
          (n = .list [] ∧ acc.nonce = 0)) ∧
        ((∃ bs : ByteArray,
            b = .bytes bs ∧ Uint.ofBeBytes (Bytes.ofByteArray bs) = acc.balance.toNat) ∨
          (b = .list [] ∧ acc.balance = U256.zero)) ∧
        ((((r = .bytes ByteArray.empty) ∨ (r = .list [])) ∧
            storageRoot = consts.emptyTrieRoot) ∨
          r = .bytes storageRoot.toBytes.toByteArray) ∧
        ((((c = .bytes ByteArray.empty) ∨ (c = .list [])) ∧
            acc.codeHash = consts.emptyCodeHash) ∨
          c = .bytes acc.codeHash.toBytes.toByteArray) := by
  simp only [decodeAccountLeaf_fields_iff, nonceField_ok, balanceField_ok, hashField_ok]

/-! ### Coarse error characterization -/

private theorem nonceField_error (item : RlpItem) (e : WitnessError)
    (h : nonceField item = .error e) : e = .malformed .leaf := by
  cases item with
  | bytes bs => simp [nonceField] at h
  | list xs => cases xs <;> simp_all [nonceField]

private theorem balanceField_error (item : RlpItem) (e : WitnessError)
    (h : balanceField item = .error e) : e = .malformed .leaf := by
  cases item with
  | bytes bs =>
    simp only [balanceField] at h
    split at h <;> simp_all
  | list xs => cases xs <;> simp_all [balanceField]

private theorem hashField_error (default : Hash32) (item : RlpItem) (e : WitnessError)
    (h : hashField default item = .error e) : e = .malformed .leaf := by
  cases item with
  | bytes bs =>
    simp only [hashField] at h
    split at h
    · simp at h
    · split at h <;> simp_all
  | list xs => cases xs <;> simp_all [hashField]

private theorem accountFields_error (consts : HashConsts) (n b r c : RlpItem)
    (e : WitnessError) (h : accountFields consts n b r c = .error e) :
    e = .malformed .leaf := by
  cases hn : nonceField n with
  | error en =>
    have he := nonceField_error _ _ hn
    simpa only [accountFields, hn, bind, Except.bind, Except.error.injEq, ← he] using h.symm
  | ok vn =>
    cases hb : balanceField b with
    | error eb =>
      have he := balanceField_error _ _ hb
      simpa only [accountFields, hn, hb, bind, Except.bind, Except.error.injEq, ← he]
        using h.symm
    | ok vb =>
      cases hr : hashField consts.emptyTrieRoot r with
      | error er =>
        have he := hashField_error _ _ _ hr
        simpa only [accountFields, hn, hb, hr, bind, Except.bind, Except.error.injEq, ← he]
          using h.symm
      | ok vr =>
        cases hc : hashField consts.emptyCodeHash c with
        | error ec =>
          have he := hashField_error _ _ _ hc
          simpa only [accountFields, hn, hb, hr, hc, bind, Except.bind,
            Except.error.injEq, ← he] using h.symm
        | ok vc => simp [accountFields, hn, hb, hr, hc, bind, pure, Except.bind,
            Except.pure] at h

/-! ### Public rejection, roundtrip and constants contracts -/

/-- Every rejection is precisely the existing coarse malformed-leaf error;
no absent, unresolved or field-specific diagnostic is returned. -/
theorem decodeAccountLeaf_eq_error_iff (consts : HashConsts) (leaf : ByteArray) :
    decodeAccountLeaf consts leaf = .error (.malformed .leaf) ↔
      ¬ ∃ acc : Account, ∃ storageRoot : Hash32,
        decodeAccountLeaf consts leaf = .ok (acc, storageRoot) := by
  constructor
  · intro h
    rintro ⟨acc, root, hs⟩
    rw [h] at hs
    cases hs
  · intro h
    cases hd : decodeAccountLeaf consts leaf with
    | ok pair => exact False.elim (h ⟨pair.1, pair.2, hd⟩)
    | error e =>
      have he : e = .malformed .leaf := by
        unfold decodeAccountLeaf at hd
        split at hd
        · exact accountFields_error _ _ _ _ _ _ hd
        · simpa only [Except.error.injEq] using hd.symm
      rw [he]

/-- Raw empty input fails in the strict parser before field interpretation. -/
theorem decodeAccountLeaf_empty (consts : HashConsts) :
    decodeAccountLeaf consts ByteArray.empty = .error (.malformed .leaf) := by
  simp only [decodeAccountLeaf, Rlp.decode_empty]

/-- Canonical account wires reconstruct all four values on the complete assembled
Q47 domain, for every supplied constants record, including explicit all-zero hashes. -/
theorem decodeAccountLeaf_encodeAccount
    (consts : HashConsts) (acc : Account) (storageRoot : Hash32)
    (h : Rlp.Encodable (.list [Rlp.ofNat acc.nonce, Rlp.ofNat acc.balance.toNat,
      .bytes storageRoot.toBytes.toByteArray, .bytes acc.codeHash.toBytes.toByteArray])) :
    decodeAccountLeaf consts (encodeAccount acc storageRoot) = .ok (acc, storageRoot) := by
  apply (decodeAccountLeaf_eq_ok_iff _ _ _ _).mpr
  refine ⟨_, _, _, _, Rlp.decode_encode _ h, ?_, ?_, ?_, ?_⟩
  · exact Or.inl ⟨_, rfl, by rw [Bytes.ofByteArray_toByteArray,
      Uint.ofBeBytes_toBeBytes]⟩
  · exact Or.inl ⟨_, rfl, by rw [Bytes.ofByteArray_toByteArray,
      Uint.ofBeBytes_toBeBytes]⟩
  · exact Or.inr rfl
  · exact Or.inr rfl

/-- The decoder observes only the supplied empty trie root and empty code hash. -/
theorem decodeAccountLeaf_congr_consts
    (consts₁ consts₂ : HashConsts) (leaf : ByteArray)
    (hroot : consts₁.emptyTrieRoot = consts₂.emptyTrieRoot)
    (hcode : consts₁.emptyCodeHash = consts₂.emptyCodeHash) :
    decodeAccountLeaf consts₁ leaf = decodeAccountLeaf consts₂ leaf := by
  unfold decodeAccountLeaf
  split
  · simp only [accountFields, hroot, hcode]
  · rfl

end STFSpec.StateCommit
