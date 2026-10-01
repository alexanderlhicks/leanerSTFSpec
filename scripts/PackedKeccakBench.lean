/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash

/-!
# Complete packed/reference Keccak native cost diagnostic

Built and declaration-audited in CI; run manually with `lake exe packed-keccak-bench`.
Expected bytes below are supplemental finite observations of actual pinned EELS
`src/ethereum/crypto/hash.py:62,80`, commit
`e1a316a06fc3d3e0a5da36fdc78580811e9d8a36`, CPython 3.13.7,
ethereum-types 0.4.1 and pycryptodome 3.23.0. They are not published primary KATs;
those remain in `PackedKeccakGuards.lean`. Regenerate observations with
`STFSpec/Conformance/Hash/packed_keccak_differential.py` using frozen Python `-I -B`.
Input pattern is `(17*i+131)%256`, generated outside timing. Full digest values are
checked before and after clocks. All public endpoint/output conversions, padding,
block operations and retained-output replacement are timed; no checksum or
comparison occurs in the loop. Replaced outputs are released there; the last
fixed-width result is retained for the outside-clock correctness gate.
Local native timings do not establish D4 acceptance, target/client throughput,
allocation volume/peak-live space or whole-guest cost. Inspect generated C and
assembly to verify the digest call remains inside every repeated timed iteration.
Spec guidance: `STFSpec/informal/modules/EthHash.md` §§3,6,10.
-/

open STFSpec.Base
namespace PackedKeccakBench

private def hexDigit (c : Char) : Nat :=
  if c ≤ '9' then c.toNat - 48 else c.toNat - 87

private def hexLoop : List Char → ByteArray → ByteArray
  | a :: b :: rest, out => hexLoop rest
    (out.push (UInt8.ofNat (16 * hexDigit a + hexDigit b)))
  | _, out => out

private def fromHex (s : String) : ByteArray := hexLoop s.toList ByteArray.empty

/-- Construct the asymmetric patterned input outside the timed digest loop. -/
def workload (n : Nat) : ByteArray :=
  (Bytes.generate n (fun i ↦ UInt8.ofNat ((17 * i + 131) % 256))).toByteArray

/-- Complete retained reference Keccak-256 endpoint plus public byte conversion. -/
def reference256 (b : ByteArray) : ByteArray :=
  (STFSpec.Hash.keccak256 b).toBytes.toByteArray

/-- Complete retained reference Keccak-512 endpoint plus public byte conversion. -/
def reference512 (b : ByteArray) : ByteArray :=
  (STFSpec.Hash.keccak512 b).toBytes.toByteArray

/-- Complete packed candidate Keccak-256 endpoint plus public byte conversion. -/
def packed256 (b : ByteArray) : ByteArray :=
  (STFSpec.Hash.PackedKeccak.keccak256 b).toBytes.toByteArray

/-- Complete packed candidate Keccak-512 endpoint plus public byte conversion. -/
def packed512 (b : ByteArray) : ByteArray :=
  (STFSpec.Hash.PackedKeccak.keccak512 b).toBytes.toByteArray

/-- Time repeated complete digests and output replacement, with full outside-clock gates. -/
def measure (mode : String) (bits n reps trial : Nat) (f : ByteArray → ByteArray)
    (msg expected : ByteArray) : IO Unit := do
  if f msg != expected then throw (IO.userError "pre-timing complete digest mismatch")
  let retained ← IO.mkRef ByteArray.empty
  let start ← IO.monoNanosNow
  for _ in [:reps] do
    retained.set (f msg)
  let finish ← IO.monoNanosNow
  let result ← retained.get
  if result != expected then throw (IO.userError "post-timing complete digest mismatch")
  IO.println ("{\"mode\":\"" ++ mode ++ "\",\"bits\":" ++ toString bits ++
    ",\"length\":" ++ toString n ++ ",\"repetitions\":" ++ toString reps ++
    ",\"trial\":" ++ toString trial ++ ",\"elapsed_ns\":" ++ toString (finish-start) ++
    ",\"full_result_gates\":true}")

/-- Three alternating-order trials for one digest width/workload. -/
def runCase (bits n : Nat) (expectedHex : String) : IO Unit := do
  let msg := workload n
  let expected := fromHex expectedHex
  let reps := if n ≥ 1048576 then 1 else if n ≥ 4096 then 10 else 100
  let ref := if bits = 256 then reference256 else reference512
  let packed := if bits = 256 then packed256 else packed512
  for trial in [:3] do
    if trial % 2 = 0 then
      measure "reference" bits n reps trial ref msg expected
      measure "packed" bits n reps trial packed msg expected
    else
      measure "packed" bits n reps trial packed msg expected
      measure "reference" bits n reps trial ref msg expected

/-- The bounded paired native digest workloads; CI builds/audits without running timings. -/
def run : IO Unit := do
  runCase 256 0 "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
  runCase 512 0
    ("0eab42de4c3ceb9235fc91acffe746b29c29a8c366b7c60e4e67c466f36a4304" ++
      "c00fa9caf9d87976ba469bcbe06713b435f091ef2769fb160cdab33d3670680e")
  runCase 256 32 "594ddbaf47c2d7c09d97643a184269a75f199f47d765fd90a5b42a4b8f27bb5b"
  runCase 512 32
    ("0b6619f3f4405c06863a2d1c21b86426699c6ab4d657a17a48c636c8be045364" ++
      "dfdaf6cd3f1f1dd5c22ef3380c32b4819429e2c818fbad62b55101259c464118")
  runCase 256 64 "9d4f0186875e14b9d37b7109f92d2157e3bc9acaa74e3832fa903a1a353f5edd"
  runCase 512 64
    ("07fa0bc79798ea3b464c432c660ccc0be9c8a108149a3aa3d6b93a9e93cee2aa" ++
      "31751ff5bc2eaddbeaf3e16a31cb7db831aab2a568ed39bbb55908685412a266")
  runCase 256 135 "5ac40ed225db542ab2f57da9c668f027f601cf4c1655fa99ed21a44dd4b63842"
  runCase 512 135
    ("cc4a7de7abd809142ca2d8b8cbb931a1f372d7cfdeb2b4725c36d469abaa3057" ++
      "cfb1c14452eb8efb2bad93ace7bf66983105ba9806ba5b5179c7853ae0ac4f25")
  runCase 256 136 "11d83b94a27d43ba2be716a3492595e4d5ecab16d08582beb0b348fcd6a743c4"
  runCase 512 136
    ("9c0b3862dd8f8292dae090ae2322ad87105495eb49ae440275580279d9b08600" ++
      "3f8edb19a6c9b5cab159067dbb1fd0649d77bdf9c2a36a1b02c68148d109a42e")
  runCase 256 137 "39eb27a82680db6c5207dfaf5c9f4519cdd793a2db21c9eea1a8eaabb0cf0518"
  runCase 512 137
    ("923d5cb82495b2b1741ce327c6777069e222672ac765be64a3e054833149d93e" ++
      "7c33498bc583e7f3bcaf5a86b1e41083f28fc0948737d878b7add850099f9374")
  runCase 256 71 "6df33198be4965c7ac4edb37b1e40be72d1599704d4dfb3037662866d84cbb44"
  runCase 512 71
    ("417b5d7e41c051a16dbc73555e08c25ecb964fe61ee803a5f5ea3641f27144b5" ++
      "39db2339360d5ee42e8548b1fc5535eb5e434bd0129c75ed911f3780e57d8b88")
  runCase 256 72 "3875a52b53a2672606a3ad8c3381ef3fd2da33d878fdb773a3f8a1b28f4682a1"
  runCase 512 72
    ("46f355b0588082b847a8558f124676ded3e49cb9cae3a68c34882838fb3c6b11" ++
      "299bc0726096db68763f7aac2e1b471e2f2ea7110d3a0da4fccb863adbc529b9")
  runCase 256 73 "7c6c2a89d6187f5e6276773acc7e3d02ca555b4b5b434cde491a34742e3834d8"
  runCase 512 73
    ("cc400db4d72a9b0ea95513bf7f6db6271c2d846a17c42a26d51cbb52a0b1af01" ++
      "2e9b96470175d2f8d5b4516b34affe2faf39098023c913119a42e6883b7f6443")
  runCase 256 4096 "e594771494797fca06ab4b52053f2c06f4a4c0de6ebb980e6dd6a3c3f69c76b8"
  runCase 512 4096
    ("f1e36179c4660a6403e444e068b15f9288c8bfe1d01fca2505e824f5ec466105" ++
      "fb0edc2f6d64caac73b527d3fd2e4bdb9086ce7e3cbd3d781c5ac336190cb867")
  runCase 256 1048576 "02d11aa48fdf35d794c7771e19c119787d9f812d35def9af7c4a2107f24599c2"
  runCase 512 1048576
    ("f2e3c0be262aedc200ec7d099e50f37d0d845b4a4d34bdbf824a2a066e21e4d4" ++
      "43226ac9703a323d557452b686d1abbf1493408c1658071daea694bfa372b2ee")

end PackedKeccakBench

/-- Entry point for the standalone native cost diagnostic. -/
def main : IO Unit := PackedKeccakBench.run
