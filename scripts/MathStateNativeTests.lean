/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Conformance.State.MathStateGuards

/-!
# Complete native mathematical-state comparisons

Library `EthConformance`: finite association-list oracle and full raw/query observations.
This executable measures no cost and enumerates no `WF` universe.
Spec guidance: `STFSpec/informal/modules/EthState.md`.

Run `lake exe math-state-native-tests`. Interpret the same complete checks with
`lake env lean --run scripts/MathStateNativeTests.lean`.
-/

open STFSpec.Base STFSpec.State
open STFSpec.Conformance.State.MathStateGuards

private structure Model where
  accounts : List (Address × Account)
  storage : List (Address × List (Bytes32 × U256))
  code : List (Hash32 × ByteArray)

private def normalize {K V : Type} [Ord K] [DecidableEq K] (xs : List (K × V)) :
    List (K × V) :=
  (xs.foldl (fun acc (k, v) ↦ acc.filter (fun p ↦ decide (p.1 ≠ k)) ++ [(k, v)]) []).mergeSort
    (fun x y ↦ compare x.1 y.1 != .gt)

private def lookup {K V : Type} [DecidableEq K] (xs : List (K × V)) (k : K) : Option V :=
  (xs.find? (fun p ↦ decide (p.1 = k))).map Prod.snd

private def canonical (m : Model) : Model :=
  ⟨normalize m.accounts, normalize m.storage |>.map (fun (a, vs) ↦ (a, normalize vs)),
    normalize m.code⟩

private def build (m : Model) : MathState :=
  ⟨m.accounts.foldl (fun acc (a, x) ↦ acc.insert a x) ∅,
    m.storage.foldl (fun acc (a, vs) ↦
      acc.insert a (vs.foldl (fun slots (k, v) ↦ slots.insert k v) ∅)) ∅,
    m.code.foldl (fun acc (h, b) ↦ acc.insert h b) ∅⟩

private def reference (input : Model) (consts : HashConsts) := Id.run do
  let m := canonical input
  let raw := (m.accounts.map (fun (a, x) ↦ (a.toBytes.toList, observeAccount x)),
    m.storage.map (fun (a, vs) ↦
      (a.toBytes.toList, vs.map (fun (kv : Bytes32 × U256) ↦ (kv.1.toBytes.toList, kv.2.toNat)))),
    m.code.map (fun (h, b) ↦ (h.toBytes.toList, b.toList)))
  return (raw, addresses.map (fun a ↦ (lookup m.accounts a).map observeAccount),
    addresses.map (fun a ↦ slots.map (fun k ↦
      ((lookup m.storage a).bind (fun vs ↦ lookup vs k)).getD U256.zero |>.toNat)),
    hashes.map (fun h ↦ if h = consts.emptyCodeHash then some []
      else (lookup m.code h).map ByteArray.toList))

private def bytes (xs : List UInt8) : ByteArray := (Bytes.ofList xs).toByteArray
private def h (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def a (n : Nat) : Address := Address.ofNat n
private def k (n : Nat) : Bytes32 := FixedBytes.ofNat n
private def huge : Account := ⟨2 ^ 1024 + 17, U256.max, h (2 ^ 248)⟩
private def base : Model :=
  ⟨[(a 1, emptyAccount constants), (a (2 ^ 152), huge)],
    [(a 1, [(k 1, U256.one), (k (2 ^ 248), U256.max)])],
    [(h 0, ByteArray.empty), (h (2 ^ 248), bytes [0, 128, 255, 0])]⟩
private def left : Model :=
  ⟨base.accounts ++ [(a 0, huge)], base.storage ++ [(a 0, [(k 0, U256.zero)])],
    base.code ++ [(constants.emptyCodeHash, bytes [255, 128, 1])]⟩
private def right : Model :=
  ⟨base.accounts, base.storage ++ [(a (2 ^ 160 - 1), [])],
    base.code ++ [(h (2 ^ 256 - 1), bytes (List.range 256 |>.map UInt8.ofNat))]⟩
private def full : Model :=
  ⟨addresses.zip hashes |>.map (fun (address, hash) ↦
      (address, ⟨2 ^ 1024 + 17, U256.max, hash⟩)),
    addresses.map (fun address ↦ (address, slots.zipIdx |>.map (fun (key, i) ↦
      (key, U256.ofNat (if i = 0 then 0 else 2 ^ (8 * i) + i))))),
    hashes.zipIdx |>.map (fun (hash, i) ↦
      (hash, bytes ([0, 128, 255] ++ (List.range (33 + i)).map UInt8.ofNat)))⟩
private def models : List Model :=
  [⟨[], [], []⟩, base, left, right, base, left, right, full,
    ⟨full.accounts.reverse, full.storage.reverse |>.map (fun (a, vs) ↦ (a, vs.reverse)),
      full.code.reverse⟩,
    ⟨[], [(a 1, [(k 1, U256.one)])], []⟩,
    ⟨[], [], [(constants.emptyCodeHash, ByteArray.empty)]⟩,
    ⟨[], [], [(constants.emptyCodeHash, bytes [1, 2, 255])]⟩,
    ⟨base.accounts ++ [(a 1, huge), (a 1, emptyAccount constants)],
      base.storage ++ [(a 1, []), (a 1, [(k 1, U256.zero), (k 1, U256.max)])],
      base.code ++ [(h 0, bytes [255]), (h 0, ByteArray.empty)]⟩]

private def observeReconstructed (σ : MathState) (consts : HashConsts) :=
  (observeRaw σ,
    addresses.map (fun a ↦ (σ.account? (Address.ofNat a.toNat)).map observeAccount),
    addresses.map (fun a ↦ slots.map (fun k ↦
      (σ.storageAt (Address.ofNat a.toNat) (FixedBytes.ofNat k.toNat)).toNat)),
    hashes.map (fun h ↦
      (σ.code? consts (Hash32.ofBytes32 (FixedBytes.ofNat h.toNat))).map ByteArray.toList))

/-- Compare and print every complete finite state and query answer against the list oracle. -/
def main : IO Unit := do
  let constsCases := [constants,
    HashConsts.mk constants.emptyCodeHash (h 99) (h 100) (h 101),
    HashConsts.mk (h 0) (h 99) (h 100) (h 101), HashConsts.literals]
  for (model, i) in models.zipIdx do
    let σ := build model
    let rebuilt : MathState := ⟨σ.accounts, σ.storage, σ.code⟩
    for (consts, j) in constsCases.zipIdx do
      let actual := observe σ consts
      let expected := reference model consts
      unless actual == expected && observe rebuilt consts == expected &&
          observeReconstructed σ consts == expected do
        throw (IO.userError s!"complete MathState mismatch at {i}/{j}")
      IO.println s!"math-state/{i}/{j} {repr actual}"
  unless observeRaw (build full) == observeRaw (build
      ⟨full.accounts.reverse, full.storage.reverse |>.map (fun (a, vs) ↦ (a, vs.reverse)),
        full.code.reverse⟩) do
    throw (IO.userError "raw insertion-order equality failed")
  let retainedModels : List Model := models.take 7 ++
    [⟨[], [], [(constants.emptyCodeHash, ByteArray.empty)]⟩, ⟨[], base.storage, []⟩]
  unless samples.length == retainedModels.length do
    throw (IO.userError "retained fixture/model lengths differ")
  for (σ, model) in samples.zip retainedModels do
    let actual := observe σ constants
    unless actual == reference model constants do
      throw (IO.userError "retained parent/sibling mismatch")
    IO.println s!"retained {repr actual}"
  IO.println "complete MathState list oracle, retained parent/siblings and reconstructed keys PASS"
