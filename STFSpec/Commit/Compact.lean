/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit.Nibbles
import STFSpec.Commit.TrieError

/-!
# Lenient compact trie path decoding

Library `EthCommit`. Pinned EELS
`src/ethereum/forks/amsterdam/incremental_mpt.py:859–889`.
The first byte supplies leaf/parity through bits 1/0 of its high nibble;
unused high bits and even padding are ignored. Only raw empty input fails.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§2.1/3/5/7.
-/

namespace STFSpec.Commit

/-- Read bit 1 of the high nibble, ignoring flag bits 2–3.
EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:878–879`. -/
def compactIsLeaf (first : UInt8) : Bool := first.toNat / 32 % 2 == 1

/-- Read bit 0 of the high nibble, ignoring flag bits 1–3.
EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:878–880`. -/
def compactIsOdd (first : UInt8) : Bool := first.toNat / 16 % 2 == 1

/-- Legible model of EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:878–889`:
retain the odd first digit, then high/low suffix digits. -/
def compactToNibblesModel : List UInt8 → Except TrieError (List (Fin 16) × Bool)
  | [] => .error (.malformed .compactEmpty)
  | first :: rest => .ok
      ((if compactIsOdd first then [lowNibble first] else []) ++ bytesToNibbleListModel rest,
        compactIsLeaf first)

private def compactSkip (first : UInt8) : Nat := if compactIsOdd first then 1 else 2

private def compactDigit (b : ByteArray) (skip i : Nat) : Fin 16 :=
  if h : (i + skip) / 2 < b.size then
    if (i + skip) % 2 = 0 then highNibble b[(i + skip) / 2]
    else lowNibble b[(i + skip) / 2]
  else 0

/-- EELS `src/ethereum/forks/amsterdam/incremental_mpt.py:878–889`,
with Q48's exact first-byte diagnostic.
The indexed digit list is copied through the public `Nibbles.ofList` boundary;
its temporary lists and packed copy are recorded in the D18 debt register. -/
def compactToNibbles (b : ByteArray) : Except TrieError (Nibbles × Bool) :=
  if h : 0 < b.size then
    let first := b[0]
    let skip := compactSkip first
    .ok (Nibbles.ofList (List.ofFn (fun i : Fin (2 * b.size - skip) ↦
      compactDigit b skip i.val)), compactIsLeaf first)
  else .error (.malformed .compactEmpty)

private theorem compactDigit_split (b : ByteArray) (skip i : Nat)
    (hi : i + skip < 2 * b.size) :
    compactDigit b skip i =
      (bytesToNibbleList b).get ⟨i + skip, by rw [size_bytesToNibbleList]; exact hi⟩ := by
  have hb : (i + skip) / 2 < b.size := by omega
  simp only [compactDigit, dite_eq_left hb]
  split
  · next he =>
    have hv : i + skip = 2 * ((i + skip) / 2) := by omega
    have hg := get_bytesToNibbleList_high b _ hb
    have heq : (⟨i + skip, by rw [size_bytesToNibbleList]; exact hi⟩ :
        Fin (bytesToNibbleList b).size) =
          ⟨2 * ((i + skip) / 2), by rw [size_bytesToNibbleList]; omega⟩ := Fin.ext hv
    rw [heq]
    exact hg.symm
  · next he =>
    have hv : i + skip = 2 * ((i + skip) / 2) + 1 := by omega
    have hg := get_bytesToNibbleList_low b _ hb
    have heq : (⟨i + skip, by rw [size_bytesToNibbleList]; exact hi⟩ :
        Fin (bytesToNibbleList b).size) =
          ⟨2 * ((i + skip) / 2) + 1, by rw [size_bytesToNibbleList]; omega⟩ := Fin.ext hv
    rw [heq]
    exact hg.symm

private theorem decodedDigits_split (b : ByteArray) (skip : Nat) :
    List.ofFn (fun i : Fin (2 * b.size - skip) ↦ compactDigit b skip i.val) =
      (bytesToNibbleList b).toList.drop skip := by
  apply List.ext_getElem
  · simp [Nibbles.length_toList, size_bytesToNibbleList]
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_drop]
    have hb : skip + i < (bytesToNibbleList b).size := by
      rw [size_bytesToNibbleList]
      simp only [List.length_ofFn] at hi
      omega
    rw [Nibbles.getElem_toList _ _ hb]
    simpa only [Nat.add_comm] using compactDigit_split b skip i (by
      simp only [List.length_ofFn] at hi
      omega)

/-- Ordinary all-input correspondence, preserving both diagnostics and leaf flags. -/
theorem compactToNibbles_eq_model (b : ByteArray) :
    (compactToNibbles b).map (fun p ↦ (p.1.toList, p.2)) =
      compactToNibblesModel b.data.toList := by
  unfold compactToNibbles
  split
  · next hb =>
    rw [Except.map, Nibbles.toList_ofList, decodedDigits_split, toList_bytesToNibbleList]
    have hl : b.data.toList = b[0] :: b.data.toList.drop 1 := by
      have ht := List.getElem_cons_drop (as := b.data.toList) (i := 0) (by
        simpa only [Array.length_toList, ByteArray.size_data] using hb)
      simpa [ByteArray.getElem_eq_getElem_data] using ht.symm
    rw [hl]
    simp only [compactToNibblesModel, compactSkip]
    unfold bytesToNibbleListModel
    simp only [List.flatMap]
    split <;> simp
  · next hb =>
    have hl : b.data.toList = [] := List.eq_nil_of_length_eq_zero (by
      change b.size = 0; omega)
    rw [hl]
    rfl

/-- Empty input has the approved diagnostic, before any decoded path exists. -/
theorem compactToNibbles_empty :
    compactToNibbles ByteArray.empty = .error (.malformed .compactEmpty) := rfl

/-- This is the only error, and it occurs exactly on raw empty input. -/
theorem compactToNibbles_error_iff (b : ByteArray) (error : TrieError) :
    compactToNibbles b = .error error ↔
      b.size = 0 ∧ error = .malformed .compactEmpty := by
  by_cases hb : 0 < b.size
  · have hz : b.size ≠ 0 := by omega
    simp [compactToNibbles, hb, hz]
  · have hz : b.size = 0 := by omega
    simp [compactToNibbles, hz, eq_comm]

/-- Successful path/leaf values are characterized exactly by the public List model. -/
theorem compactToNibbles_ok_iff (b : ByteArray) (path : Nibbles) (leaf : Bool) :
    compactToNibbles b = .ok (path, leaf) ↔
      compactToNibblesModel b.data.toList = .ok (path.toList, leaf) := by
  rw [← compactToNibbles_eq_model]
  cases hr : compactToNibbles b with
  | error error => simp [Except.map]
  | ok pair =>
    rcases pair with ⟨p, l⟩
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨hp, hl⟩
      exact ⟨congrArg Nibbles.toList hp, hl⟩
    · rintro ⟨hp, hl⟩
      exact ⟨Nibbles.ext hp, hl⟩

/-- Every nonempty input succeeds; no flag or padding check can reject it. -/
theorem compactToNibbles_success_iff (b : ByteArray) :
    (∃ path leaf, compactToNibbles b = .ok (path, leaf)) ↔ 0 < b.size := by
  unfold compactToNibbles
  split
  · next hb => exact ⟨fun _ ↦ hb, fun _ ↦ ⟨_, _, rfl⟩⟩
  · next hb => simp [hb]

/-- The successful leaf flag is exactly bit 1 of the high nibble. -/
theorem compactToNibbles_leaf (b : ByteArray) (path : Nibbles) (leaf : Bool)
    (h : compactToNibbles b = .ok (path, leaf)) (hb : 0 < b.size) :
    leaf = compactIsLeaf b[0] := by
  unfold compactToNibbles at h
  rw [dite_eq_left hb] at h
  exact (congrArg Prod.snd (Except.ok.inj h)).symm

/-- Successful decoding has two suffix digits per byte and one odd first digit. -/
theorem compactToNibbles_size (b : ByteArray) (path : Nibbles) (leaf : Bool)
    (h : compactToNibbles b = .ok (path, leaf)) (hb : 0 < b.size) :
    path.size = 2 * (b.size - 1) + if compactIsOdd b[0] then 1 else 0 := by
  unfold compactToNibbles at h
  rw [dite_eq_left hb] at h
  have hp := congrArg (fun p ↦ p.1.size) (Except.ok.inj h)
  simp only [Nibbles.size_ofList, List.length_ofFn, compactSkip] at hp
  cases ho : compactIsOdd b[0] <;>
    simp only [ho, Bool.false_eq_true, ite_false, ite_true] at hp ⊢ <;> omega

/-- Every successful decoded position indexes an existing raw compact byte. -/
theorem compactToNibbles_index_lt (b : ByteArray) (path : Nibbles) (leaf : Bool)
    (h : compactToNibbles b = .ok (path, leaf)) (hb : 0 < b.size)
    (i : Nat) (hi : i < path.size) :
    (i + (if compactIsOdd b[0] then 1 else 2)) / 2 < b.size := by
  have hs := compactToNibbles_size b path leaf h hb
  cases ho : compactIsOdd b[0] <;>
    simp only [ho, Bool.false_eq_true, ite_false, ite_true] at hs ⊢ <;> omega

/-- Ordered output positions split the remaining raw digits high before low. -/
theorem compactToNibbles_get (b : ByteArray) (path : Nibbles) (leaf : Bool)
    (h : compactToNibbles b = .ok (path, leaf)) (hb : 0 < b.size)
    (i : Nat) (hi : i < path.size) :
    let skip := if compactIsOdd b[0] then 1 else 2
    path.get ⟨i, hi⟩ =
      if (i + skip) % 2 = 0 then
        highNibble (b[(i + skip) / 2]'(compactToNibbles_index_lt b path leaf h hb i hi))
      else lowNibble (b[(i + skip) / 2]'(compactToNibbles_index_lt b path leaf h hb i hi)) := by
  have hr := h
  unfold compactToNibbles at hr
  rw [dite_eq_left hb] at hr
  have hl := congrArg (fun p ↦ p.1.toList) (Except.ok.inj hr)
  dsimp only at hl
  rw [Nibbles.toList_ofList] at hl
  have he := congrArg (fun xs ↦ xs[i]?.getD 0) hl
  have hn : i < 2 * b.size - compactSkip b[0] := by
    have hs := congrArg List.length hl
    rw [List.length_ofFn, Nibbles.length_toList] at hs
    omega
  rw [List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hn),
    List.getElem?_eq_getElem (by rw [Nibbles.length_toList]; exact hi),
    Option.getD_some, List.getElem_ofFn, Nibbles.getElem_toList _ _ hi] at he
  simp only [Option.getD_some] at he
  rw [← he]
  dsimp only
  unfold compactDigit compactSkip
  rw [dite_eq_left (compactToNibbles_index_lt b path leaf h hb i hi)]

private theorem canonical_leaf (x : Nibbles) (leaf : Bool) :
    compactIsLeaf ((nibbleListToCompact x leaf)[0]'(nibbleListToCompact_nonempty x leaf)) =
      leaf := by
  have hf := nibbleListToCompact_flag x leaf
  cases leaf
  · simp only [Bool.false_eq_true, ite_false] at hf
    have hd : ((nibbleListToCompact x false)[0]'
        (nibbleListToCompact_nonempty x false)).toNat / 32 = 0 := by omega
    simp only [compactIsLeaf, hd]
    rfl
  · simp only [ite_true] at hf
    have hd : ((nibbleListToCompact x true)[0]'
        (nibbleListToCompact_nonempty x true)).toNat / 32 = 1 := by omega
    simp only [compactIsLeaf, hd]
    rfl

private theorem canonical_odd (x : Nibbles) (leaf : Bool) :
    compactIsOdd ((nibbleListToCompact x leaf)[0]'(nibbleListToCompact_nonempty x leaf)) =
      (x.size % 2 == 1) := by
  have hf := nibbleListToCompact_flag x leaf
  unfold compactIsOdd
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  cases leaf <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hf <;> omega

/-- Decoding every canonical compact encoding recovers the full bounded path and leaf flag. -/
theorem compactToNibbles_nibbleListToCompact (x : Nibbles) (leaf : Bool) :
    compactToNibbles (nibbleListToCompact x leaf) = .ok (x, leaf) := by
  let b := nibbleListToCompact x leaf
  have hb : 0 < b.size := nibbleListToCompact_nonempty x leaf
  obtain ⟨path, l, hd⟩ := (compactToNibbles_success_iff b).mpr hb
  have hl : l = leaf := (compactToNibbles_leaf b path l hd hb).trans (canonical_leaf x leaf)
  have ho : compactIsOdd b[0] = (x.size % 2 == 1) := canonical_odd x leaf
  have hs : path.size = x.size := by
    have hs := compactToNibbles_size b path l hd hb
    rw [ho, size_nibbleListToCompact] at hs
    have hm := Nat.mod_lt x.size (by decide : 0 < 2)
    by_cases he : x.size % 2 = 1
    · simp only [he, beq_self_eq_true, ite_true] at hs
      omega
    · have hz : x.size % 2 = 0 := by omega
      simp only [hz] at hs
      simp at hs
      omega
  have hp : path = x := by
    apply Nibbles.ext
    apply List.ext_getElem
    · rw [Nibbles.length_toList, Nibbles.length_toList, hs]
    · intro i hi hj
      have hip : i < path.size := by rwa [Nibbles.length_toList] at hi
      have hix : i < x.size := by rwa [Nibbles.length_toList] at hj
      rw [Nibbles.getElem_toList _ _ hip, Nibbles.getElem_toList _ _ hix]
      have hx : x.toList[i]?.getD 0 = x.get ⟨i, hix⟩ := by
        rw [List.getElem?_eq_getElem (by rw [Nibbles.length_toList]; exact hix),
          Option.getD_some, Nibbles.getElem_toList _ _ hix]
      have hg := compactToNibbles_get b path l hd hb i hip
      simp only [ho] at hg
      let skip := if x.size % 2 == 1 then 1 else 2
      have hk : (i + skip) / 2 < b.size := by
        simpa only [ho] using compactToNibbles_index_lt b path l hd hb i hip
      have hm : x.size % 2 < 2 := Nat.mod_lt _ (by decide)
      have hskip : skip = 2 - x.size % 2 := by
        dsimp only [skip]
        split
        · next he =>
          simp only [beq_iff_eq] at he
          omega
        · next he =>
          simp only [beq_iff_eq] at he
          omega
      change path.get ⟨i, hip⟩ = if (i + skip) % 2 = 0 then
        highNibble b[(i + skip) / 2] else lowNibble b[(i + skip) / 2] at hg
      by_cases hz : (i + skip) / 2 = 0
      · have hp : x.size % 2 = 1 ∧ i = 0 ∧ skip = 1 := by
          omega
        rcases hp with ⟨hp, rfl, hsone⟩
        have hf := nibbleListToCompact_first x leaf
        rw [hp] at hf
        simp only [Nat.one_ne_zero, ite_false] at hf
        apply Fin.ext
        have he : path.get ⟨0, hip⟩ = lowNibble b[0] := by
          simpa only [hsone, Nat.zero_add, Nat.one_mod, Nat.one_ne_zero,
            ite_false, Nat.div_self] using hg
        rw [he]
        change (b[0]).toNat % 16 = (x.get ⟨0, hix⟩).val
        rw [hf, List.getElem?_eq_getElem (by rw [Nibbles.length_toList]; exact hix),
          Option.getD_some, Nibbles.getElem_toList _ _ hix]
      · have hj : (i + skip) / 2 - 1 < x.size / 2 := by
          rw [size_nibbleListToCompact] at hk
          omega
        have hp := nibbleListToCompact_pair x leaf ((i + skip) / 2 - 1) hj
        have hk' : (i + skip) / 2 = ((i + skip) / 2 - 1) + 1 := by omega
        have hdigit : 2 * ((i + skip) / 2 - 1) + x.size % 2 +
            (if (i + skip) % 2 = 0 then 0 else 1) = i := by
          split <;> omega
        apply Fin.ext
        rw [hg]
        split
        · next he =>
          have hpos : 2 * ((i + skip) / 2 - 1) + x.size % 2 = i := by
            simpa only [he, ite_true, Nat.add_zero] using hdigit
          have hebyte : b[(i + skip) / 2] =
              packNibbles (x.toList[i]?.getD 0)
                (x.toList[2 * ((i + skip) / 2 - 1) + x.size % 2 + 1]?.getD 0) := by
            simpa only [← hk', hpos] using hp
          change (b[(i + skip) / 2]).toNat / 16 = _
          rw [hebyte, toNat_packNibbles, hx]
          have := (x.toList[2 * ((i + skip) / 2 - 1) + x.size % 2 + 1]?.getD (0 : Fin 16)).isLt
          omega
        · next he =>
          have hpos : 2 * ((i + skip) / 2 - 1) + x.size % 2 + 1 = i := by
            simpa only [he, ite_false] using hdigit
          have hebyte : b[(i + skip) / 2] =
              packNibbles (x.toList[2 * ((i + skip) / 2 - 1) + x.size % 2]?.getD 0)
                (x.toList[i]?.getD 0) := by
            simpa only [← hk', hpos] using hp
          change (b[(i + skip) / 2]).toNat % 16 = _
          rw [hebyte, toNat_packNibbles, hx]
          have := (x.get ⟨i, hix⟩).isLt
          omega
  rw [hd, hp, hl]

/-- Canonical compact bytes bind the path and leaf flag through the proved inverse. -/
theorem nibbleListToCompact_inj (x y : Nibbles) (leaf otherLeaf : Bool) :
    nibbleListToCompact x leaf = nibbleListToCompact y otherLeaf ↔
      x = y ∧ leaf = otherLeaf := by
  constructor
  · intro h
    have hd := congrArg compactToNibbles h
    rw [compactToNibbles_nibbleListToCompact, compactToNibbles_nibbleListToCompact] at hd
    exact Prod.mk.inj (Except.ok.inj hd)
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Reencoding an accepted wire normalizes it and preserves its decoded value. -/
theorem compactToNibbles_normalization (b : ByteArray) (path : Nibbles) (leaf : Bool)
    (h : compactToNibbles b = .ok (path, leaf)) :
    compactToNibbles (nibbleListToCompact path leaf) = compactToNibbles b := by
  rw [compactToNibbles_nibbleListToCompact, h]

/-- Accepted-wire reencoding is byte identity exactly on the canonical encoder image. -/
theorem nibbleListToCompact_decode_eq_iff (b : ByteArray) (path : Nibbles) (leaf : Bool)
    (h : compactToNibbles b = .ok (path, leaf)) :
    nibbleListToCompact path leaf = b ↔
      ∃ canonicalPath canonicalLeaf, b = nibbleListToCompact canonicalPath canonicalLeaf := by
  constructor
  · intro he
    exact ⟨path, leaf, he.symm⟩
  · rintro ⟨p, l, rfl⟩
    rw [compactToNibbles_nibbleListToCompact] at h
    have he := Except.ok.inj h
    rcases Prod.mk.inj he with ⟨rfl, rfl⟩
    rfl

end STFSpec.Commit
