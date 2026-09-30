/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Base

/-!
# Fixed little-endian output diagnostic

Library `EthBase`. Spec guidance: `STFSpec/informal/modules/EthBase.md` §3.

Compile and run as described there. Arguments: `u64|u256 current|direct INPUT COUNT`.
INPUT contains one in-range decimal natural per line. Both paths construct complete
packed byte outputs. Inputs and correctness checks precede the clocks; outputs are
retained until after timing, when their checksum is computed. This is a local cost
diagnostic, not a CI gate or an opcode/guest benchmark. Output cleanup is outside
this construction-only timing. Reproduce from the repository root:

```sh
lake build EthBase:static --wfail
lake env lean -c /tmp/stfspec-fixed-endian.c scripts/FixedEndianBench.lean
lake env leanc -O3 -o /tmp/stfspec-fixed-endian /tmp/stfspec-fixed-endian.c \
  .lake/build/lib/libstfspec_EthBase.a
python3 - <<'PY'
import random
from pathlib import Path
for bits in (64, 256):
    rng = random.Random(83173 + bits)
    values = [0, 1, 2, (1 << bits) - 1] + [1 << i for i in range(bits)]
    values += [int.from_bytes(bytes(range(bits // 8)), "little")]
    values += [rng.getrandbits(bits) for _ in range(256)]
    Path(f"/tmp/stfspec-fixed-{bits}.txt").write_text(
        "".join(f"{value}\n" for value in values))
PY
for sample in 1 2 3 4 5; do
  for bits in 256 64; do
    if [ "$((sample % 2))" -eq 1 ]; then modes='current direct'; else modes='direct current'; fi
    for mode in $modes; do
      /usr/bin/time -f 'peak-rss-kib=%M' /tmp/stfspec-fixed-endian \
        "u$bits" "$mode" "/tmp/stfspec-fixed-$bits.txt" 200000
    done
  done
done
```

Inspect the generated C: correctness precedes the first `lean_io_mono_ms_now`,
`batch` calls the encoder and pushes each output before returning, the second clock
precedes the checksum fold. Peak RSS includes runtime, loaded inputs, retained output
buffers and their pointer array; it does not measure total allocation or a guest peak.
-/

open STFSpec.Base

private def direct (width value : Nat) : Bytes :=
  Bytes.generate width (fun i ↦ UInt8.ofNat (value >>> (8 * i)))

private def load (path : System.FilePath) (bits : Nat) : IO (Array Nat) := do
  let mut values := #[]
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.isEmpty then continue
    let some value := line.toNat?
      | throw (IO.userError "input is not a decimal natural")
    unless value < 2 ^ bits do
      throw (IO.userError "input exceeds the selected width")
    values := values.push value
  if values.isEmpty then throw (IO.userError "input is empty")
  return values

-- An IO boundary prevents pure output construction from moving beyond the clocks.
@[noinline] private def batch {α : Type} (inputs : Array α) (encode : α → Bytes)
    (count : Nat) : IO (Array Bytes) := do
  let mut outputs := Array.emptyWithCapacity count
  for i in [:count] do
    let some input := inputs[i % inputs.size]?
      | throw (IO.userError "missing input")
    outputs := outputs.push (encode input)
  return outputs

private def runMeasurement {α : Type} (inputs : Array α) (current baseline : α → Bytes)
    (decode : Bytes → Nat) (observe : α → Nat) (width count : Nat)
    (mode : String) : IO Unit := do
  for input in inputs do
    let actual := current input
    unless actual == baseline input && actual.size == width &&
        decode actual == observe input do
      throw (IO.userError "complete-output correctness gate failed")
  let encode := if mode == "current" then current else baseline
  let before ← IO.monoMsNow
  let outputs ← batch inputs encode count
  let after ← IO.monoMsNow
  let checksum := outputs.foldl (fun acc bytes ↦
    bytes.foldl (fun sum byte ↦ sum + byte.toNat) acc) 0
  unless outputs.size == count do throw (IO.userError "wrong output count")
  (← IO.getStdout).putStrLn
    (s!"PASS inputs={inputs.size} outputs={count} bytes={count * width} " ++
      s!"elapsed-ms={after - before} checksum={checksum}")

/-- Run the local complete-output comparison; reject malformed arguments and inputs. -/
def main (args : List String) : IO UInt32 := do
  try
    let [kind, mode, path, countText] := args
      | throw (IO.userError "expected: u64|u256 current|direct INPUT COUNT")
    unless mode == "current" || mode == "direct" do
      throw (IO.userError "unknown output mode")
    let some count := countText.toNat?
      | throw (IO.userError "COUNT must be a natural")
    if count == 0 then throw (IO.userError "COUNT must be positive")
    if kind == "u256" then
      let inputs := (← load path 256).map U256.ofNat
      runMeasurement inputs (fun x ↦ (U256.toLeBytes32 x).toBytes)
        (fun x ↦ direct 32 x.toNat) Uint.ofLeBytes U256.toNat 32 count mode
    else if kind == "u64" then
      let inputs := (← load path 64).map U64.ofNat
      runMeasurement inputs (fun x ↦ (U64.toLeBytes8 x).toBytes)
        (fun x ↦ direct 8 x.toNat) Uint.ofLeBytes U64.toNat 8 count mode
    else
      throw (IO.userError "unknown integer kind")
    return 0
  catch error =>
    (← IO.getStderr).putStrLn s!"FAIL {error}"
    return 1
