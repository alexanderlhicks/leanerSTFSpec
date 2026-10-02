/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base.FixedBytes
import STFSpec.Base.BytesOrder

/-!
# Compiled byte regression checks

Library `EthBase`. Spec guidance: `STFSpec/informal/modules/EthBase.md` §3.

Run `lake build bytes-native-tests --wfail && lake exe bytes-native-tests`.
These exercise the compiled packed operations against their list models, including
natural offsets whose low machine bits look like valid indices. Ordinary model
theorems prove the Lean equations; `#guard` supplies evaluated regression tests.
This standalone executable adds end-to-end compiled regression coverage.
-/

open STFSpec.Base

private def require (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

private def checkSlices : IO Nat := do
  let mut count := 0
  let offsets := [0, 1, 2, 3, 4, 2 ^ 64, 2 ^ 64 + 1, 2 ^ 256,
    2 ^ 256 + 1, 2 ^ 4096]
  for xs in [[], [255], [1, 2, 255]] do
    let b := Bytes.ofList xs
    for start in offsets do
      for stop in offsets do
        require s!"extract size={xs.length} start={start} stop={stop}"
          ((b.extract start stop).toList == (xs.drop start).take (stop - start))
        count := count + 1
      for len in [0, 1, 2, 3, 8] do
        let available := (xs.drop start).take len
        let expected := available ++ List.replicate (len - available.length) 0
        require s!"extractPadded size={xs.length} start={start} len={len}"
          ((b.extractPadded start len).toList == expected)
        count := count + 1
  return count

private def checkConstruction : IO Nat := do
  let mut count := 0
  for n in [0, 1, 2, 20, 32, 65, 256] do
    let xs := (List.range n).map (fun i ↦ UInt8.ofNat (i * 37 + 255))
    let b := Bytes.generate n (fun i ↦ UInt8.ofNat (i * 37 + 255))
    require s!"packed export {n}" (b.toByteArray.data.toList == xs)
    require s!"packed roundtrip {n}" (Bytes.ofByteArray b.toByteArray == b)
    require s!"generate {n}" (b.toList == xs)
    require s!"zeros {n}" ((Bytes.empty.rightPadZero n).toList == List.replicate n 0)
    require s!"fold {n}" (b.foldl (fun a v ↦ a * 256 + v.toNat) 0 ==
      xs.foldl (fun a v ↦ a * 256 + v.toNat) 0)
    let some fixed := FixedBytes.ofBytes? (n := n) b
      | throw (IO.userError s!"ofBytes? {n}")
    require s!"roundtrip {n}" (fixed.toBytes == b)
    require s!"wrong length {n}" ((FixedBytes.ofBytes? (n := n + 1) b).isNone)
    count := count + 7
  require "huge width rejects early"
    ((FixedBytes.ofBytes? (n := 2 ^ 4096) Bytes.empty).isNone)
  return count + 1

private def checkOrdering : IO Nat := do
  let mut count := 0
  for i in List.range 256 do
    for j in List.range 256 do
      let a := Bytes.ofList [UInt8.ofNat i]
      let b := Bytes.ofList [UInt8.ofNat j]
      require s!"unsigned ordering {i} {j}" (compare a b == compare i j)
      count := count + 1
  let shared := List.replicate 4096 (255 : UInt8)
  let patterns := [[], [0], [0, 0], [0, 1], [1], [127], [128], [255],
    [1, 255], [2], shared, shared ++ [0], shared ++ [1], 0 :: shared, 1 :: shared]
  for xs in patterns do
    let a := Bytes.ofList xs
    require s!"core packed list {xs.length}" (a.toByteArray.toList == xs)
    for ys in patterns do
      let b := Bytes.ofList ys
      require s!"ordering model {xs.length} {ys.length}"
        (compare a b == compare xs ys && Bytes.compare a b == Bytes.compareReference a b)
      require s!"ordering equality {xs.length} {ys.length}"
        ((compare a b == .eq) == decide (a = b))
      count := count + 2
    count := count + 1
  require "RLP ordinal zero sorts after one"
    (compare (Bytes.ofList [128]) (Bytes.ofList [1]) == .gt)
  return count + 1

/-- Isolated compiled regression entry point; not part of the library API. -/
def main : IO UInt32 := do
  try
    let slices ← checkSlices
    let construction ← checkConstruction
    let ordering ← checkOrdering
    (← IO.getStdout).putStrLn s!"PASS {slices + construction + ordering} compiled byte checks"
    return 0
  catch error =>
    (← IO.getStderr).putStrLn s!"FAIL {error}"
    return 1
