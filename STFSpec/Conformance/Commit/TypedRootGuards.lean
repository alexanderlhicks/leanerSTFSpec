/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Conformance.Commit.MathRootGuards

/-!
# Complete typed-root observations

Library `EthConformance`. Test-local lawful keys and nonempty encoded values
exercise the actual safe unsecured frontend. Every query, answer, original error
and carried state is observed. These instances are finite instrumentation only.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/4/7.0.3; Q53.
-/

namespace STFSpec.Conformance.Commit.TypedRootGuards

open STFSpec.Base STFSpec.Codec STFSpec.Hash STFSpec.Commit

-- Ordinary core byte observation bridge; no STFspec container internals are unfolded.
private theorem core_toList_loop (b : ByteArray) (n i : Nat) (r : List UInt8)
    (h : n + i = b.size) :
    ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i := by
  induction n generalizing i r with
  | zero =>
    have hi : ¬ i < b.size := by omega
    rw [ByteArray.toList.loop, ite_eq_right hi]
    rw [List.drop_of_length_le
      (by simp only [Array.length_toList, ByteArray.size] at *; omega), List.append_nil]
  | succ n ih =>
    have hi : i < b.size := by omega
    rw [ByteArray.toList.loop, ite_eq_left hi, ih (i + 1) _ (by omega)]
    rw [List.reverse_cons, List.append_assoc]
    congr 1
    rw (occs := [2]) [← List.getElem_cons_drop
      (by simpa only [Array.length_toList, ByteArray.size] using hi)]
    simp only [List.singleton_append, ByteArray.get!, Array.getElem!_eq_getD,
      Array.getD_eq_getD_getElem?, getElem?_pos b.data i hi, Option.getD_some,
      Array.getElem_toList]

private theorem core_toList (b : ByteArray) : b.toList = b.data.toList :=
  core_toList_loop b b.size 0 [] (Nat.add_zero _)

-- A test-local adapter for the existing core List model only.
local instance listKeyBytes : KeyBytes (List UInt8) where
  toBytes := List.toByteArray
  toBytes_injective := by
    intro a b h
    have hl := congrArg (fun x : ByteArray => x.data.toList) h
    simpa only [List.data_toByteArray, List.toList_toArray] using hl
  compare_toBytes a b := by
    simp only [core_toList, List.data_toByteArray, List.toList_toArray]

/-- Distinct test values may have identical complete encoding. -/
structure SampleValue where
  bytes : {b : ByteArray // b ≠ ByteArray.empty}
  tag : Bool

local instance : TrieValue SampleValue where
  encode v := v.bytes.val
  Valid _ := True
  encode_ne_empty v _ := v.bytes.property

/-- Build a supported finite sample with nonempty encoding. -/
def value (n : Nat) (width : Nat := 1) : SampleValue :=
  ⟨⟨(UInt8.ofNat n :: List.replicate width (UInt8.ofNat n)).toByteArray, by
      intro h
      have hs := congrArg ByteArray.size h
      simp at hs⟩, false⟩

/-- Actual stored rows, without setter default erasure or encoding replacement. -/
def trie (rows : List (List UInt8 × SampleValue)) : Trie (List UInt8) SampleValue :=
  ⟨false, value 99, Std.ExtTreeMap.ofList rows compare⟩

/-- All test values are supported regardless of tag or the supplied default. -/
theorem safe (t : Trie (List UInt8) SampleValue) : t.PrepareSafe := by
  intro _ _ _
  trivial

/-- Complete root digest and carried query state. -/
def recorded (t : Trie (List UInt8) SampleValue) (unsecured : t.secured = false)
    (emptyRoot : Hash32) (state : RootBranchGuards.Trace) :
    List UInt8 × RootBranchGuards.Trace :=
  let (answer, next) :=
    (root (m := RootBranchGuards.TestState) emptyRoot t unsecured (safe t)).run state
  (answer.toBytes.toByteArray.data.toList, next)

/-- Original complete errors and carried state, including the failing query. -/
def failed (t : Trie (List UInt8) SampleValue) (unsecured : t.secured = false)
    (state : RootBranchGuards.Trace) :
    Except RootBranchGuards.Failure (List UInt8) × RootBranchGuards.Trace :=
  let (answer, next) := (root (m := RootBranchGuards.TestFailure) MathRootGuards.supplied
    t unsecured (safe t)).run.run state
  (answer.map (fun h ↦ h.toBytes.toByteArray.data.toList), next)

/-- Test complete descendant and top queries across all sixteen child positions. -/
def branch : Trie (List UInt8) SampleValue := trie ((List.range 16).map
  fun d ↦ ([UInt8.ofNat (d * 16)], value d (26 + d % 3)))

/-- Include empty keys, strict prefixes, long paths and threshold payloads. -/
def nested : Trie (List UInt8) SampleValue := trie
  [([], value 1), ([0], value 2 28), ([0, 1], value 3 29),
    ([0, 2], value 4 30), (List.replicate 100 0 ++ [255], value 5 56)]

/-- Directly stored valid supplied default remains present in the root computation. -/
def storedDefault : Trie (List UInt8) SampleValue := trie [([0], value 99)]

/-- There is deliberately no NoDefault premise for this supported trie. -/
theorem storedDefault_has_default : ¬ storedDefault.NoDefault := by
  intro h
  exact h [0] (value 99) (Std.ExtTreeMap.getElem?_ofList_of_mem
    (Std.ReflCmp.compare_self) (by simp) (by simp)) rfl

/-- Full sequential reference is exercised on the lawful recording monad. -/
def sequenced (t : Trie (List UInt8) SampleValue) (unsecured : t.secured = false)
    (state : RootBranchGuards.Trace) :
    List UInt8 × RootBranchGuards.Trace :=
  let (answer, next) := (do
    let prepared ← prepareTrie (m := RootBranchGuards.TestState) t unsecured (safe t)
    mathRoot MathRootGuards.supplied prepared).run state
  (answer.toBytes.toByteArray.data.toList, next)

/-- The unsecured proof is carried through finite sample enumeration. -/
def samples : List {t : Trie (List UInt8) SampleValue // t.secured = false} :=
  [⟨trie [], rfl⟩, ⟨branch, rfl⟩, ⟨nested, rfl⟩, ⟨storedDefault, rfl⟩]

/-- Full finite observations; comparisons retain every byte and state field. -/
def cases : List (String × Bool) := [
  ("nonliteral empty root zero queries even with failing oracle",
    failed (trie []) rfl {(MathRootGuards.seeded 7) with failQueryAt := some 7} ==
      (.ok MathRootGuards.supplied.toBytes.toByteArray.data.toList,
        {(MathRootGuards.seeded 7) with failQueryAt := some 7})),
  ("all complete C8 queries answers and seeded states forwarded",
    samples.all fun t ↦ [7, 1000000].all fun start ↦
      recorded t.val t.property MathRootGuards.supplied (MathRootGuards.seeded start) ==
        MathRootGuards.recorded (prepareTrieModel t.val) MathRootGuards.supplied
          (MathRootGuards.seeded start)),
  ("original descendant and final-query errors forwarded completely",
    samples.all fun t ↦ [7, 1000000].all fun start ↦
      let state := MathRootGuards.seeded start
      let queries := (recorded t.val t.property MathRootGuards.supplied state).2.queries - start
      (List.range (queries + 1)).all fun offset ↦
        let failing := {state with failQueryAt := some (start + offset)}
        failed t.val t.property failing == MathRootGuards.failed (prepareTrieModel t.val)
          MathRootGuards.supplied failing),
  ("lawful separately sequenced action complete observations",
    samples.all fun t ↦ [7, 1000000].all fun start ↦
      recorded t.val t.property MathRootGuards.supplied (MathRootGuards.seeded start) ==
        sequenced t.val t.property (MathRootGuards.seeded start)),
  ("retained valid supplied default contributes a real top query",
    (prepareTrieModel storedDefault).size == 1 &&
      (recorded storedDefault rfl MathRootGuards.supplied {}).2.queries == 1),
  ("noninjective value encoding preserves complete root effects",
    let a := value 7
    recorded (trie [([0], a)]) rfl MathRootGuards.supplied (MathRootGuards.seeded 7) ==
      recorded (trie [([0], {a with tag := true})]) rfl MathRootGuards.supplied
        (MathRootGuards.seeded 7))]

#guard cases.all Prod.snd

/-- Print complete roots, query streams and every original failure for native checks. -/
def printComplete : IO UInt32 := do
  for t in samples do
    for start in [7, 1000000] do
      let state := MathRootGuards.seeded start
      let result := recorded t.val t.property MathRootGuards.supplied state
      IO.println s!"typed root={reprStr result}"
      for offset in List.range (result.2.queries - start + 1) do
        IO.println s!"typed error={reprStr (failed t.val t.property
          {state with failQueryAt := some (start + offset)})}"
  let mut failures := 0
  for (name, result) in cases do
    IO.println s!"typed root {name}: {result}"
    if !result then failures := failures + 1
  return failures

/-! Finite source instrumentation preserves raw-byte versus integer dispatch and
all-value setter/default semantics. No production instance is adopted. -/

/-- Interpret the supported concrete finite source fixtures, with None outside safety. -/
inductive SourceValue
  | none
  | raw (bytes : ByteArray)
  | integer (number : Nat)
  deriving DecidableEq

/-- Exact source identity/RLP dispatch for finite fixture values. -/
def sourceEncode : SourceValue → ByteArray
  | .none => ByteArray.empty
  | .raw b => b
  | .integer n => Rlp.encode (Rlp.ofNat n)

local instance : TrieValue SourceValue where
  encode := sourceEncode
  Valid v := v ≠ .none ∧ sourceEncode v ≠ ByteArray.empty
  encode_ne_empty _ h := h.2

/-- Validity is decidable for these concrete finite supported values. -/
instance sourceValidDecidable (v : SourceValue) : Decidable (TrieValue.Valid v) :=
  inferInstanceAs (Decidable (v ≠ .none ∧ sourceEncode v ≠ ByteArray.empty))

private def sourceWrites (t : Trie (List UInt8) SourceValue) :
    List (List UInt8 × SourceValue) → Trie (List UInt8) SourceValue
  | [] => t
  | (k, v) :: rows => sourceWrites (trieSet t k v) rows

private theorem sourceWrites_safe (t : Trie (List UInt8) SourceValue)
    (safe : t.PrepareSafe) (rows : List (List UInt8 × SourceValue))
    (valid : ∀ row ∈ rows, row.2 = t.default ∨ TrieValue.Valid row.2) :
    (sourceWrites t rows).PrepareSafe := by
  induction rows generalizing t with
  | nil => exact safe
  | cons row rows ih =>
    apply ih (trieSet t row.1 row.2)
    · exact (trieSet_prepareSafe_iff t row.1 row.2 safe).mpr (valid row (by simp))
    · intro r h
      exact valid r (by simp [h])

private theorem sourceWrites_unsecured (t : Trie (List UInt8) SourceValue)
    (rows : List (List UInt8 × SourceValue)) :
    (sourceWrites t rows).secured = t.secured := by
  induction rows generalizing t with
  | nil => rfl
  | cons row rows ih => exact ih (trieSet t row.1 row.2)

/-- Whole prepared-map and concrete root/query observations from actual typed setters.
Safe writes are a proof premise; unsuccessful source preparations get no local error. -/
def sourceTrace (default : SourceValue) (rows : List (List UInt8 × SourceValue))
    (valid : ∀ row ∈ rows, row.2 = default ∨ TrieValue.Valid row.2) :
    List (List Nat × List UInt8) × List UInt8 × List (List UInt8 × List UInt8) :=
  let empty : Trie (List UInt8) SourceValue := ⟨false, default, ∅⟩
  let t := sourceWrites empty rows
  let safe := sourceWrites_safe empty (Trie.prepareSafe_empty false default) rows valid
  let unsecured : t.secured = false := sourceWrites_unsecured empty rows
  letI : KeccakQuery (StateM (List (List UInt8 × List UInt8))) :=
    ⟨fun preimage state ↦
      let answer := keccak256 preimage
      (answer, state ++ [(preimage.data.toList, answer.toBytes.toByteArray.data.toList)])⟩
  let (answer, trace) :=
    (root (m := StateM (List (List UInt8 × List UInt8)))
      HashConsts.literals.emptyTrieRoot t unsecured safe).run []
  ((prepareTrieModel t).toList.map (fun (k, v) ↦ (k.toList.map Fin.val, v.data.toList)),
    answer.toBytes.toByteArray.data.toList, trace)

/-- Replay complete original answers while retaining every actual preimage/answer.
Exhaustion is visible in the full remaining/count comparison; fallback is instrumentation. -/
def sourceReplay (default : SourceValue) (rows : List (List UInt8 × SourceValue))
    (valid : ∀ row ∈ rows, row.2 = default ∨ TrieValue.Valid row.2)
    (answers : List Hash32) : List UInt8 × List (List UInt8 × List UInt8) × Nat :=
  let empty : Trie (List UInt8) SourceValue := ⟨false, default, ∅⟩
  let t := sourceWrites empty rows
  let safe := sourceWrites_safe empty (Trie.prepareSafe_empty false default) rows valid
  let unsecured : t.secured = false := sourceWrites_unsecured empty rows
  letI : KeccakQuery (StateM (List Hash32 × List (List UInt8 × List UInt8))) :=
    ⟨fun wire (remaining, trace) ↦
      let answer := remaining.headD (Hash32.ofBytes32 (FixedBytes.ofNat 0))
      (answer, (remaining.drop 1,
        trace ++ [(wire.data.toList, answer.toBytes.toByteArray.data.toList)]))⟩
  let (answer, (remaining, trace)) :=
    (root (m := StateM (List Hash32 × List (List UInt8 × List UInt8)))
      HashConsts.literals.emptyTrieRoot t unsecured safe).run (answers, [])
  (answer.toBytes.toByteArray.data.toList, trace, remaining.length)

end STFSpec.Conformance.Commit.TypedRootGuards
