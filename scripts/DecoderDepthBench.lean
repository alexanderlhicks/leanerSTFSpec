/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Commit

/-!
# Witness-decoder depth diagnostic

Library `EthCommit`. Spec guidance: `STFSpec/informal/modules/EthCommit.md` C17;
evidence in `STFSpec/informal/DISCREPANCIES.md` DISC-001.

Arguments: `chain|wide N plain|secured`. `chain N` decodes a chain of N branch nodes; each
has a hashed child at slot 0 (the next node) and a stub at slot 1 that is absent from the
database, and the chain ends in a leaf. `wide N` decodes a root branch over 16 subtrees of
branches with N branch nodes in all, at most ⌈log₁₆ N⌉ + 1 deep, as a node-count control.
Database keys are synthetic full-width 256-bit values (a bijection of the index), and the
query oracle answers a constant: this measures the decoder's own traversal and path
bookkeeping, not Keccak. Construction precedes the clock. The decode result is checked
against the expected outcome (chain plain: `ok`; chain secured with N > 63 and wide
secured: `securedPathLength`; otherwise only reported), and a mismatch exits 1 before any
time is printed. The program prints the outcome, the entry count and the decode time;
inspect the generated C (`lake env lean -c`) to confirm the decode sits between the two
clock reads, since nothing fences it.
Measure peak memory externally from the process's maximum resident set size. This is a
local cost diagnostic, built and audited in CI but not run there. Reproduce from the
repository root:

```sh
lake build decoder-depth-bench --wfail
.lake/build/bin/decoder-depth-bench chain 10000 secured
```
-/

open STFSpec.Base STFSpec.Hash STFSpec.Codec STFSpec.Commit

/-- Odd multiplier: `n ↦ (n K + 2²⁵⁵) mod 2²⁵⁶` is a bijection onto full-width values. -/
private def keyMultiplier : Nat :=
  0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95
private def key (n : Nat) : Hash32 :=
  Hash32.ofBytes32 (FixedBytes.ofNat ((n * keyMultiplier + 2 ^ 255) % 2 ^ 256))
private def hashItem (n : Nat) : RlpItem := .bytes (key n).toBytes.toByteArray
private def emptyItem : RlpItem := .bytes ByteArray.empty
private def stubKey : Nat := 1
private def emptyRootKey : Nat := 2
private def firstKey : Nat := 16

private def branchRaw (children : List RlpItem) : ByteArray :=
  Rlp.encode (.list (children ++ List.replicate (16 - children.length) emptyItem ++ [emptyItem]))

private def leafRaw : ByteArray :=
  Rlp.encode (.list [.bytes (ByteArray.mk #[0x31]), .bytes (ByteArray.mk (Array.replicate 32 1))])

/-- Keys `firstKey + i` for `i < n`, then the leaf. -/
private def chain (n : Nat) : NodeDB := Id.run do
  let mut map : Std.HashMap Hash32 ByteArray := {}
  for i in [0:n] do
    map := map.insert (key (firstKey + i)) (branchRaw [hashItem (firstKey + i + 1), hashItem stubKey])
  map := map.insert (key (firstKey + n)) leafRaw
  pure ⟨map⟩

/-- Breadth-first: node `i` has children `16 i + 1 … 16 i + 16` below `n`, else leaves. -/
private def wide (n : Nat) : NodeDB := Id.run do
  let mut map : Std.HashMap Hash32 ByteArray := {}
  for i in [0:n] do
    let children := (List.range 16).map fun j => hashItem (firstKey + 16 * i + j + 1)
    map := map.insert (key (firstKey + i)) (branchRaw children)
  for i in [n:16 * n + 1] do
    map := map.insert (key (firstKey + i)) leafRaw
  pure ⟨map⟩

instance constantOracle : KeccakQuery Id := ⟨fun _ => key 3⟩

private def outcome : Except TrieError IncrementalMPT → String
  | .ok _ => "ok"
  | .error (.malformed .securedPathLength) => "securedPathLength"
  | .error (.malformed .cycle) => "cycle"
  | .error _ => "other error"

def main (args : List String) : IO UInt32 := do
  match args with
  | [shape, count, mode] =>
    let some n := count.toNat? | IO.eprintln "N must be a natural number"; pure 2
    let db ← match shape with
      | "chain" => pure (chain n)
      | "wide" => pure (wide n)
      | _ => do IO.eprintln "shape must be chain or wide"; pure ⟨{}⟩
    if db.map.isEmpty then return 2
    let secured ← match mode with
      | "secured" => pure true
      | "plain" => pure false
      | _ => do IO.eprintln "mode must be plain or secured"; return 2
    IO.println s!"{shape} {n} {mode}: {db.map.size} entries"
    let start ← IO.monoMsNow
    let result := decodeWitnessToMpt (m := Id) (key emptyRootKey) db (key firstKey) secured
    let observed := outcome result
    let stop ← IO.monoMsNow
    let expected : Option String := match shape, secured with
      | "chain", false => some "ok"
      | "chain", true => if 63 < n then some "securedPathLength" else none
      | _, true => some "securedPathLength"
      | _, false => none
    IO.println s!"outcome {observed}"
    if let some e := expected then
      if observed != e then
        IO.eprintln s!"expected {e}"
        return 1
    IO.println s!"decode {stop - start} ms"
    pure 0
  | _ => IO.eprintln "usage: decoder-depth-bench chain|wide N plain|secured"; pure 2
