# Technical-debt register (D18)

**Status (2026-10-01):** current register under D18. The outstanding entries below record local performance exceptions. Known candidate: per-query storage-trie decoding in the witness backend, pending the memo design (DECISIONS F6).

Use one entry per local, correct and complete implementation whose data structure or algorithm is **not** performance-appropriate, justified on grounds of legibility or drastic proof-friendliness (D18). Missing semantics, proof holes required for release, unproved fuel sufficiency and protocol deviations are not performance debt. Protocol discrepancies belong in [`STFSpec/informal/DISCREPANCIES.md`](DISCREPANCIES.md).

Each entry records:

- Identifier, status, owning component and responsible maintainer.
- Preserved public contract and correctness/equivalence theorem.
- Expected workload, complexity, measured limitation (exact reproducer or benchmark, source/toolchain commits) and the reason for the exception.
- Affected consumers and why the limitation remains local.
- Replacement criterion, review/removal milestone and migration procedure.
- Decision authorizing acceptance and evidence closing the item.

Review outstanding entries when releasing, changing the owning component or updating the fork. Keep closed entries with links to their replacement evidence so that later regressions can be recognized.


## DEBT-U64-CHECKED — Nat intermediates in checked bounds

**Status:** open, 2026-09-30. **Owner:** EthBase maintainers. **Authority:** D18;
D1's native `UInt64` storage requirement remains satisfied.

`U64.checkedAdd`, `checkedSub` and `checkedMul` retain their exact success/failure
contracts and ordinary `*_eq_some_iff` / `*_eq_none_iff` theorems in
`STFSpec/Base/U64.lean`. Their bounds tests observe operands as `Nat`; successful
values use the native wrapping operations. The exception preserves readable
mathematical bounds and their direct proofs while consumer implementations and
aggregate R4 cost evidence remain pending.

The expected consumer is parent-header blob-gas arithmetic: pinned EELS
`forks/amsterdam/vm/gas.py:901–949`, called by `fork.py:473`, performs a bounded
number of additions, multiplication and subtraction per header. Its full `U64`
input domain includes malformed or adversarial headers; upper-half values are
not asserted to be common. This is local to checked operations, not native
storage, wrapping operations or all narrow-word arithmetic. On a 64-bit host,
`U8`/`U16` inputs and products fit immediate `Nat`; `U32` products can box, but
its inputs and sums fit immediate `Nat`.

The limitation is constant heap work, not unbounded arithmetic: conversions can
box operands at or above `2^63`, addition needs at most 65 bits and multiplication
128 bits. Reproduce the generated-code evidence with
`lake build EthBase --wfail`, then inspect `checkedAdd`, `checkedSub` and
`checkedMul` in `.lake/build/ir/STFSpec/Base/U64.c`: each converts both operands
with `lean_uint64_to_nat`; add/mul then use `lean_nat_add`/`lean_nat_mul`.
The pinned Lean runtime's `lean/lean.h` defines the immediate limit as
`SIZE_MAX >> 1` and delegates larger operands to `lean_big_uint64_to_nat`.

A local native diagnostic on Lean 4.34.0 (compiler
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`), U64 source SHA-256
`aea85624347269ab0f45eccc9fae45bcd6f77e5986c84bbb7598f24dbe8441ff`,
counted heap-valued conversion/arithmetic returns after 300 correctness cases.
Per call with `a=2^63+17`, `b=2^63+3`, add/mul returned two heap operand
conversions and one heap arithmetic result; sub returned two conversions.
With `17,3`, all these counts were zero. These are diagnostic return counts,
not total allocator bytes, throughput or a guest benchmark; the generated-code
inspection above is the repository reproducer.

Review before implementing the header consumer, at release and when updating
the pin. Replace the bounds tests if a representative consumer profile or target
cost check makes their allocation material. The replacement must avoid these
Nat temporaries, preserve the existing contracts with ordinary equality proofs,
and pass boundary, differential and native correctness gates. Record comparable
consumer measurements before closing this entry; no narrower input limit or
change to error behavior is permitted.

## DEBT-BYTES-ZEROS — packed zero-builder peak memory

**Status:** open, 2026-09-30. **Owner:** EthBase maintainers. **Authority:** D18.

`Bytes.zeros` uses geometrically increasing packed copies to build zeros; padding
and `extractPadded` can make a final append copy. The ordinary `toList_zeros`,
`toList_leftPadZero`, `toList_rightPadZero` and `toList_extractPadded_window`
theorems preserve the complete byte model. Time and copied bytes are O(result
length), with no boxed byte-list or pointer-array intermediate. Peak live storage
can nevertheless exceed a single result buffer. The [independent review of
6289e57](https://github.com/alexanderlhicks/leanerSTFSpec/pull/3#pullrequestreview-5365566565)
reports 257–310 MB peak for a 100 MB padded result on Lean 4.34.0. This is a local
allocation measurement, not a target guest cost or a maximum resource guarantee.

Reproduce the copy structure with `lake build EthBase --wfail` and inspect
`zeros`, `rightPadZero` and `extractPadded` in
`.lake/build/ir/STFSpec/Base/Bytes.c`: doubling retains the shared half while
appending it, odd lengths add a final push, and the read may append its copied
window to the zeros. The exception keeps the small well-founded builder and its
replicated-list proof while byte-consumer profiles remain pending. Already
sufficient padding returns its input; unavailable offsets are checked as Nat
before slicing, so offset magnitude does not drive the allocation.

Expected consumers are VM padded calldata/code reads and precompile input
padding, listed in EthBase §3. The limitation is local to constructing requested
padding; byte export, fixed-byte conversion and existing-buffer access do not
require this builder. Review before integrating those consumers, at release and
when updating Lean. Replace it with a single-buffer construction if representative
profiles or C1–C4 make peak storage material; preserve the ordinary model laws,
check native huge-offset/zero-length behavior, and measure both small reads and
large results before closing this entry. No input restriction or host-error rule
is adopted by this exception.

## DEBT-HASH-REFERENCE — boxed reference rounds

**Status:** open, 2026-09-30. **Owner:** EthHash maintainers. **Authority:** D4/D18.

The legible `keccakF1600` and `sha256Compress` references preserve their coordinate
and word-model contracts through `keccakToModel_f1600` and `sha256Compress_model`.
The exception is local to fixed-size rounds: Keccak executes 24 rounds and SHA
compression 64; the digest providers multiply this cost by the message block count.
Expected consumers are witness/trie and code hashing, SSZ/request roots and the
SHA precompile. No digest or guest cost is established by this reference work.

Reproduce the code-shape evidence on the pinned Lean 4.34.0 with
`lake build EthHash --wfail`, then inspect `keccakOfLanes`, the five step functions
and `keccakRounds` in `.lake/build/ir/STFSpec/Hash/KeccakPermutation.c`, and
`scheduleStep`, `round`, `rounds` and `feedForward` in
`.lake/build/ir/STFSpec/Hash/Sha256Compression.c`. Native word arithmetic does not
imply unboxed storage: Keccak's `Array.ofFn` callbacks box UInt64 results and
coordinate construction uses closure dispatch; theta builds two five-lane arrays
and each of the five steps builds a 25-lane result. SHA rounds build eight-word
arrays and schedule updates use array-set operations. Nat calls implement bounded
indices/rotation amounts; executable word arithmetic uses UInt64/UInt32 operations.
The separately executable bit-vector models contain Nat arithmetic too and must
not be included when inspecting the native call path. There is no List builder
in either executable round path. These are static observations, not dynamic
allocation totals.

The BLAKE2b F reference additionally carries variable-round cost: its UInt32
round count selects O(rounds) work, with no semantic truncation or new bound.
The ordinary `compress_model` proof preserves all counts, flags, counter words
and serialized bytes. Expected use is the BLAKE2F precompile after successful gas
charging; gas-before-evaluation and host/zkVM resource adequacy remain obligations
of that consumer and O12, not exceptions supplied by this debt entry.

Reproduce its static evidence with `lake build EthHash --wfail` and inspect
`rotr`, `G`, `initState`, `round`, `rounds`, `feedForward`, `outputByte`,
`serializeWords` and the specialised packed generator in
`.lake/build/ir/STFSpec/Hash/Blake2Compression.c`. Word arithmetic uses
`lean_uint64_add`, `lean_uint64_xor` and native shift/or operations; output uses
`lean_uint64_to_uint8`. `G` has eight `lean_array_fset` calls and eight explicit
UInt64 result boxes; each round calls G eight times, giving 64 explicit boxing
and 64 array-write calls per executed round through those sites. This does not count allocator calls:
array uniqueness governs copying/reuse, and callbacks, reference counts and
closure allocation remain relevant. Initialization builds sixteen boxed words
and feed-forward eight; both use `Array.ofFn` callbacks. The count-decreasing
`rounds` function and the exactly-64-byte packed serializer compile to tail
`goto _start` iteration. Byte generation uses `lean_byte_array_push`, with no
boxed per-byte temporary array. Native round execution calls no List builder,
BitVec model or Nat word arithmetic; Nat operations serve counts, sigma/index
arithmetic and rotation amounts only. These are code-shape observations, not a
benchmark, dynamic allocation total or C1–C4 result.

This bounded implementation exception keeps the sequential G definition and
ordinary alias-aware proof legible. Review before integrating the precompile,
at release and after toolchain/pin updates. Replace or refine the reference under
D25 if representative variable-round precompile/composition measurements make
boxing material; preserve arbitrary-index G simulation, ascending sigma/split
laws, full UInt32-domain compression and exact little-endian bytes. Measure
allocation and complete lifetime costs with correctness outside timing before
closing this exception. No speed claim or maximum-count runtime experiment is
supported by this entry.

The [independent review of `deded43`](https://github.com/alexanderlhicks/leanerSTFSpec/pull/8#pullrequestreview-5369643733)
reported 270–385 µs per permutation, approximately 6,000 allocations per permutation,
and 13–19 µs per SHA compression on its local host. These are historical reviewer
diagnostics of the original reference tree, not reproduced measurements of the
wrapped state or evidence satisfying C1–C4; the review supplies no committed timed
reproducer. The generated-C procedure above is the reproducible evidence here.

The exception keeps the reference steps and ordinary proofs readable under D4.
Review before integrating the digest consumers, at release and on toolchain/pin
updates. Attach a proved faster definition or replace private storage under D25
when representative digest/composition measurements make the allocation material.
Preserve all coordinate/word-model laws and failure-free domains; rerun primary
KATs, public callers and independent differentials. Measure with correctness outside
timing and report allocation, conversions and composed costs before closing this
entry. No digest readiness or whole-guest performance claim is authorized.

## DEBT-KECCAK-DIGEST — reference sponge cost

**Status:** open, 2026-09-30. **Owner:** EthHash maintainers. **Authority:** D4/D18.

`keccak256` and `keccak512` preserve their pure, total byte/model contracts on
all finite inputs ([EthHash §3](modules/EthHash.md#3-eels-source-map)). This entry
owns digest-level padding, block traversal and conversion costs;
[DEBT-HASH-REFERENCE](#debt-hash-reference--boxed-reference-rounds) owns the
permutation's boxed rounds and allocation exception. No input limit, rejection,
host-error policy or hash/oracle semantics changes.

Expected workloads include short trie keys/nodes and `HashConsts` preimages,
bounded differential messages, and large messages such as the 1 MiB diagnostic
below. Padding adds between one byte and a full rate block, copies the message
once and performs `n / rateBytes + 1` permutations. Padding byte work and ordered
block traversal are O(n). The executable path uses packed Base bytes and a
forward tail-recursive block loop. Native lane arithmetic does not establish
unboxed state storage; consult DEBT-HASH-REFERENCE for that cost. No dynamic
allocation volume or whole-guest measurement is established here.

The retained local diagnostic used Lean 4.34.0, x86_64 release compiler commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, private-state reference basis
`47d46bbd29dd2ff7b8bc815e06d15b13c989d40e`, sponge source SHA-256
`651fb1a07145e1759a6eec339b7bb2e682cfe631acb784cba3ef4b1073d63509`, and
permutation source SHA-256
`8bd477bfa1cf3207f3a031db767c201d7685b89d8c5a5556fd6212b7aa36f75b`.
Three complete 1 MiB digest samples passed full-output correctness gates at
2236/2224/2209 ms for Keccak-256 and 4788/4354/4297 ms for Keccak-512.
The native executable SHA-256 was
`8ba6853d14e3a92a97eca3e92c8ff50be84358c497c21bda2a8405924491198f`.
These are historical measurements of the named source bytes, preceding the
present formatting pass. Shared-host samples establish neither a target ceiling,
a native-client speed ratio nor dynamic allocation totals.

To reproduce the procedure, build a temporary native Lean executable importing
`STFSpec.Hash` through a local package dependency. Build with
`lake build <executable> --wfail` and run its native binary. Construct the input
outside timing as
`(Bytes.generate 1048576 (fun i ↦ UInt8.ofNat (17 * i + 131))).toByteArray`.
The measured functions return `(keccak256 b).toBytes.toByteArray` and
`(keccak512 b).toBytes.toByteArray`. First compare each complete result against
these supplemental actual pinned-EELS values (not published KATs):

- Keccak-256: `02d11aa48fdf35d794c7771e19c119787d9f812d35def9af7c4a2107f24599c2`.
- Keccak-512: `f2e3c0be262aedc200ec7d099e50f37d0d845b4a4d34bdbf824a2a066e21e4d443226ac9703a323d557452b686d1abbf1493408c1658071daea694bfa372b2ee`.

For each of three samples per function, read `IO.monoMsNow`, evaluate a complete
digest and store its full ByteArray in an `IO.Ref`, then read `IO.monoMsNow` again.
Compare the stored full bytes and print after the second clock read. Input and
expected-value construction and comparisons stay outside timing; padding,
permutation composition, squeeze, public conversions and the result store stay
inside. No checksum is timed. Inspect the executable's generated C to verify
the digest call lies between clock reads. Reproduce digest code shape with
`lake build EthHash --wfail` and inspect `pad`, `decodeAux`, `xorBlock`, `absorb`
and `squeeze` in `.lake/build/ir/STFSpec/Hash/KeccakSponge.c`; inspect the
permutation separately using DEBT-HASH-REFERENCE's procedure.

The separate `PackedKeccak` candidate now proves ordinary observer, step,
prefix/permutation, block absorption, squeeze and all-input fixed-rate endpoint
correspondence beside the retained reference ([EthHash §3](modules/EthHash.md#3-eels-source-map)).
The reference defaults and caller sources are retained; D4 remains provisional
and this entry stays open. `scripts/PackedKeccakBench.lean` is a committed,
warning-strict native diagnostic, separately built and declaration-audited in CI.
Run `lake build packed-keccak-bench --wfail`, then the native binary
`.lake/build/bin/packed-keccak-bench`. The benchmark source records supplemental
actual pinned-host expected values; primary KATs remain in the conformance suite.

The historical pre-wrapper candidate diagnostic used Base parent
`60cba4ad145d669c2cad1e3bf860d0a987b37f9c`, Lean 4.34.0 release commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, clang 22.1.4 with
`-O3 -DNDEBUG -DLEAN_EXPORTING` and no LTO, on an Intel Core Ultra 7 165U x86_64
shared Linux host. Candidate permutation/sponge source SHA-256 values are
`32257ffae3c42c2da051ef6f16bb8597831be9aedb83660bf57b287c1890495c` and
`4ef4296608b8a690009a86353c9939eaf7873449423881ce091d6d1f52a3bed9`; native binary SHA-256 is
`c93094352b661c94b9a39abef009c679a3645f3e1eb44729436546edaaf69f60`.
The reference algorithm source hashes above are unchanged; Base byte/fixed-byte
source SHA-256 values are
`40750891e503b9ff1aaeff9e742a346f465ad71fcddee37ec8e2fae01ff2ede4` and
`929b44724047f9439e03ae0bb026defa2f1d1fa7453ead6783deee6626c24779`.

Both endpoint sizes are measured at lengths 0,32,64,135,136,137,71,72,73,4096 and
1 MiB using `(17*i+131)%256`. Three trials alternate reference/candidate order,
with 100 repetitions for small inputs, 10 for 4096 and one for 1 MiB. Complete
expected outputs are checked before and after the nanosecond clocks. The loop
retains/replaces full outputs, releasing earlier results inside timing; its last
fixed-width output remains for the outside-clock gate and is then released.
Padding, block decode, permutation, squeeze and public output conversions are
included. C and native assembly confirm the digest call and retained-output store
within each repeated timed iteration, with no checksum or equality in that loop.

The historical pre-wrapper three-sample diagnostic yielded:

| Digest / 1 MiB | Reference ms | Packed candidate ms | Median reference/candidate |
|---|---|---|---|
| Keccak-256 | 2184.1/2250.2/3097.4 | 97.9/113.4/107.6 | 20.92× |
| Keccak-512 | 4201.8/4114.4/2659.6 | 166.4/186.9/151.2 | 24.73× |

These comparisons are local diagnostics against the retained Lean reference,
not a native-client baseline or target ceiling. Host contention/frequency/affinity
were not controlled. Generated C shows 25 scalar `uint64_t` fields at offsets
0,8,…,192, 200-byte record constructors and exclusive-record reuse branches. The
candidate digest's own hot-function graph has no UInt64 lane boxing, observer
conversion or coordinate-model calls. Startup round constants remain boxed once,
and byte callback adapters, Nat operations, closures, padding/output allocation
and runtime lifetimes remain. These source/code-shape observations are not dynamic
allocated-volume or peak-live-space profiles. No standalone hash measurement
claims to discharge all C1–C4; their relevant obligations arise in the future
consumer composition. The existing replacement criteria below remain unchanged.

### Historical 2026-09-30 wrapped-reference candidate diagnostic

The historical 2026-09-30 remeasurement used the private `KeccakState` coordinate API at
reference parent `47d46bbd29dd2ff7b8bc815e06d15b13c989d40e`, Lean 4.34.0 release
commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, clang 22.1.4 with
`-O3 -DNDEBUG -DLEAN_EXPORTING` and no LTO on the same shared Intel Core Ultra 7
165U x86_64 Linux host. Historical samples are marked separately above; the
paired benchmark below measured those historical source bytes. The complete committed
benchmark was rebuilt and rerun at both endpoints, all eleven lengths and three
alternating-order trials (132 rows). Every pre/post full-result gate passed.
The measured unit is nanoseconds per complete digest, including retained-output
replacement; no checksum or equality is inside the clocks.

| Digest / 1 MiB | Wrapped reference ms | Packed candidate ms | Median reference/candidate |
|---|---|---|---|
| Keccak-256 | 815.4/830.1/826.9 | 38.2/38.8/38.4 | 21.53× |
| Keccak-512 | 1836.3/2006.0/2439.5 | 96.0/96.2/97.7 | 20.86× |

Historical wrapped-reference source SHA-256 identities, separately from the historical samples:

- `STFSpec/Hash/KeccakPermutation.lean`: `8bd477bfa1cf3207f3a031db767c201d7685b89d8c5a5556fd6212b7aa36f75b`.
- `STFSpec/Hash/KeccakSponge.lean`: `651fb1a07145e1759a6eec339b7bb2e682cfe631acb784cba3ef4b1073d63509`.
- `STFSpec/Hash/PackedKeccakPermutation.lean`: `f85e956ed1efdc1d5ae0d73fe418f445b90dd96c93ef10649338b67ebe04d09e`.
- `STFSpec/Hash/PackedKeccakSponge.lean`: `63e10871dad163845dda451f62d3dfb203092c1e058728de9ba379f3ff6a455f`.
- `scripts/PackedKeccakBench.lean`: `67b0ed5d7b3b91e561c5a386b619110e0040f82218631497b2e5858d32c1111c`.

Historical wrapped-reference native binary SHA-256: `d13649d8f3decaf684e4a48be67e15f6a6ed85a2d354c45df076950dd0d9af08`.
Generated C and native assembly again confirm one digest closure call and
retained-output replacement at every timed loop back edge, without equality or
checksum. The candidate graph retains the scalar-field observations above.
These local reference comparisons are separate from native-client or target
throughput evidence. Frequency, affinity and host contention were uncontrolled;
allocation volume/peak-live-space and future-consumer composition remain open.
This diagnostic changes no default, D4 status or DEBT replacement criterion.

These retained paired measurements precede the merged provider formatting and
public-law changes. They describe the named historical source bytes.

### 2026-10-01 merged-provider candidate diagnostic

A fresh run on merged provider parent
`042b4cf4a9f9ce9d8268eaeb8e1dea088ace4571` kept the packed candidate and
benchmark source bytes above, while the retained reference sponge source SHA-256
is now `3a6a68a63d82217d2fa97c780cf51a09016bd12de8e1fd621248bb8b312ca755`.
The compiler, native flags and shared host are as described above. The current
native binary SHA-256 is
`c24a347532204d175b3ee1ac5974a8674732569b687e2c61848d4df6fdeb90a7`.
All 132 alternating-order trials and 264 complete pre/post output gates passed;
the same eleven lengths, two endpoints, repetitions and nanosecond units apply.
The following three-sample results belong only to this merged-provider run:

| Digest / 1 MiB | Current reference ms | Packed candidate ms | Median reference/candidate |
|---|---|---|---|
| Keccak-256 | 2408.6/4412.0/1722.6 | 96.9/89.9/71.5 | 26.78× |
| Keccak-512 | 4404.0/4116.6/4915.0 | 161.5/164.7/162.8 | 27.05× |

These samples are separate from both historical tables and are not pooled with
them. Fresh current C and linked assembly retain the scalar-state and timed-loop
observations above. Shared-host contention, affinity and frequency remain
uncontrolled; no native-client target, allocation-volume, peak-live-space or
future-consumer C1–C4 conclusion follows. D4, the reference default and this
entry's replacement criteria remain unchanged.

This exception keeps the legible reference and ordinary model proofs required
by D4. Trie/code/header, opcode, address and constant-acquisition consumers
inherit this provider cost; their semantics and query obligations remain unchanged.
Review before trie/block integration, release or a toolchain/pin update. Replace
only with an ordinary all-input equality or model refinement preserving the
reference contract and public caller proofs. Measure complete digests, including
conversions, padding and allocations, representative short and large consumers,
C1 retention/cleanup costs and the CONTRIBUTING §3 native-client baseline before
closing this entry. No narrower domain or semantic shortcut is permitted.
Query/security/accelerator and composed C1–C4 obligations remain open.

## DEBT-RIPEMD-DIGEST — boxed compression and byte conversion

**Status:** open, 2026-09-30. **Owner:** EthHash maintainers. **Authority:** D4/D18.

The production `ripemd160 : ByteArray → FixedBytes 20` retains its all-input
MD4 padding, ordered compression and twenty-byte model correspondence through
`Ripemd160.ripemd160_digest`. Expected workloads are precompile messages,
including empty/short, 55/56/63/64-byte boundaries and large multi-block inputs.
Padding creates at most 72 suffix bytes and appends once to a packed message;
block processing is O(message bytes), with constant-width sixteen-word decoding
and the accepted eighty-round dual-branch compression per block. No intermediate
whole-message list is built in the executable digest path. The separate proof
model deliberately uses lists and BitVec words; it is not the native path.

Reproduce static evidence with `lake build EthHash:static EthBase:static --wfail`
and inspect `Ripemd160Digest.c`, `Ripemd160Compression.c`, `Base/Bytes.c` and
`Base/FixedBytes.c` under `.lake/build/ir/STFSpec/Hash/` and
`.lake/build/ir/STFSpec/`. The packed suffix/serializer specializations use
`lean_byte_array_push`; `blocks` decreases its count and advances by 64 using
`goto _start`. Byte reads compare natural offsets with the packed size before
`lean_byte_array_fget`; even a conceptual enormous offset does not reach a
narrowed byte index. `parseBlock` constructs sixteen boxed UInt32 words through
an `Array.ofFn` callback. The accepted compression continues using fixed-size
boxed vector states, native UInt32 arithmetic and eighty dual rounds per block.
This preserves legibility and its ordinary model proof; it is an explicit local
reference allocation exception rather than a speed claim.

Byte decoding uses Nat radix-256 sums bounded below 2^32; word serialization
uses Nat division and bounded exponents 0..3. The suffix length field performs
low-64 Nat arithmetic and bounded exponents 0..7. These are conversion/index
costs distinct from native compression lane arithmetic. The checked public Base
`FixedBytes.ofBytes?` constructor converts twenty bytes into its private numeric
representation; subsequent `toBytes` materializes the fixed-width output again.
That bounded conversion can involve multi-limb Nat arithmetic. No claim that
all digest arithmetic is native UInt32, that all storage is unboxed or that static
call-site counts equal dynamic allocated volume is made.

Current compiled whole-result checks cover all nine primary digest facts,
including a compact million-a message, and finite actual pinned precompile
digests after checking/stripping the twelve-byte zero prefix. These correctness
checks include the full public fixed-byte output path. They are finite native
validation, not throughput, dynamic allocation, host resource or C1–C4 acceptance.
No native-client target is discharged. Review at consumer integration, release,
and toolchain/pin updates. Replace the boxed compression representation or prove
more direct byte conversions under D25 when representative complete precompile
measurements make these costs material; preserve the arbitrary-word compression,
all-input byte model, minimal padding and complete fixed output laws. Measure
allocation, conversions and complete lifetime cost with correctness outside any
timed loop before closing this exception. The consumer still owns gas-before-
computation and DISC-005/O12 policy.

## DEBT-COMPACT-DECODE — temporary digit lists

**Status:** open, 2026-10-01. **Owner:** EthCommit maintainers. **Authority:** D18.

`compactToNibbles : ByteArray → Except TrieError (Nibbles × Bool)` preserves its
all-input List model, exact empty diagnostic, ordered digit/flag/length laws,
canonical inverse and normalization contract in `STFSpec/Commit/Compact.lean`.
The future witness node decoder is the expected caller. Typical node paths are
short; the API also accepts every nonempty leading byte and arbitrarily long
finite suffixes. The indexed builder creates a bounded-digit
List; public `Nibbles.ofList` maps it to a UInt8 List and converts that into the
packed output. Work and temporary storage are O(decoded length), with no slicing
or mutation API and no claim of list fusion or one packed allocation.

This exception keeps the representation private and uses the existing proven
public construction boundary. A direct packed generator and its observer laws
are currently absent from that boundary; adding them is a separate provider work
item. Reproduce the code shape on pinned Lean 4.34.0 with
`lake build EthCommit:static --wfail`, then inspect `compactToNibbles` and its
specialized `List.ofFn`/`Nibbles.ofList` path in
`.lake/build/ir/STFSpec/Commit/Compact.c` and `Nibbles.c`: list construction and
mapping precede the byte-array conversion. This is static code-shape evidence,
not measured allocation volume, peak live space, throughput or completed C1–C4.
Finite compiled checks compare complete decoded and reencoded results. Repeated
calls release earlier results between cases. These checks provide correctness
evidence for those cases; they do not measure allocation, peak live space or
throughput.

Review before integrating the node decoder, at release and toolchain/pin updates.
Replace through the public model boundary when a reviewed packed provider builder
is available or representative witness profiles make the temporary lists material.
The replacement must preserve `compactToNibbles_eq_model` and all exact
success/failure/observer, canonical inverse and normalization laws, keep public
caller proofs unchanged, and pass authenticated source and native full-result
checks. Measure complete construction/conversion/allocation and lifetime cost
before closing the entry. No input restriction or host-error policy is authorized.
