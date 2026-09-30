# Technical-debt register (D18)

**Status (2026-09-30):** current register under D18. The outstanding entries below record local performance exceptions. Known candidate: per-query storage-trie decoding in the witness backend, pending the memo design (DECISIONS F6).

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
compression 64; future digest work multiplies this cost by the message block count.
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
