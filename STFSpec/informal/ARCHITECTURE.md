# Spec architecture

*Status: current (v2.5, 2026-10-06). Decision statuses and question dispositions are owned by [DECISIONS](DECISIONS.md); the acceptance criteria are in [REVIEW §7](REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks). Project status is in the README.*

This document is the intended breakdown of the spec: the libraries, what each may depend on, the data structures each starts with, the *boundary* each must preserve when its implementation changes, and the properties to be proved. It follows [`CONTRIBUTING.md`](../../CONTRIBUTING.md): EEST zkevm conformance is mandatory and decisive, legibility is first-class, and performance comes from asymptotically good data structures. Everything here is a design contract, not a proved result; for example, the source-checked gas accounting in §5.5 is evidence for a proof obligation, not a termination theorem.

**Normative source.** The pin is `tests-zkevm@v21.0.0` @e1a316a0 ([`reference.toml`](../../reference.toml)), and the guest contract is [`STFSpec/informal/CONTRACT.md`](CONTRACT.md). The module list mirrors `src/ethereum/forks/amsterdam/` (about 17k lines of Python across 60 files), the shared `src/ethereum/{state,state_mpt,merkle_patricia_trie,exceptions}.py`, `crypto/` and `utils/`, and the pinned Python dependencies, whose behaviour is part of the semantics.

**Document ownership.** `reference.toml` owns source, fixture and toolchain pins; `CONTRACT.md` owns the guest contract and discrepancy policy; `scripts/boundaries.toml` owns the enforced import permissions (§3 must agree with it); this document owns the component contracts. [COMPOSITION](COMPOSITION.md) records the conditional end-to-end argument and the shared adapters that refine these contracts. Update the owning document and its consumers together when a contract changes.

Two distinctions matter throughout. Local gas accounting does not by itself give progress of a whole call; that is the fuel obligation G2 (§5.5). And `Models` states agreement of whatever a backend returns, not that the backend returns (backend progress, §5.3).

## 1. What the architecture must make easy

Formal specs accumulate coupling through *proofs*, not only through signatures. A caller that unfolds a container's internals is coupled to that representation even when the function's type is clean. So the architecture is judged by how well it contains change:

- **Behaviour-preserving changes** (representation, caching, algorithm, execution strategy) must stay local to one component. They are justified by re-establishing that component's contract, and callers' proof scripts should survive.
- **Semantic changes** (fork updates, corrections to accepted or rejected behaviour) must be concentrated in named places: parameters, the affected fork modules, and their proofs. They are made by explicitly changing the contract, the tests and the affected proofs.

**Acceptance tests for the architecture.** The architecture is frozen only after these four replacement exercises pass on an integration slice ([REVIEW §7](REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks) "Replacement gates"):

1. **Replace the memory implementation** while preserving the proofs of the memory opcodes.
2. **Replace the witness-trie implementation** while preserving the proofs of the arithmetic and storage opcodes.
3. **Apply a representative gas-rule patch** such that the changes fall only in gas policy, the affected instruction semantics and their proofs.
4. **Change the stored representation of `U256`** (for example from `BitVec 256` to four `UInt64` limbs) while preserving the opcode proof scripts unchanged. A named API alone doesn't guarantee this: callers could still rely on `BitVec` instances or unfold arithmetic definitions. So `U256` is a `structure` from the start, never an `abbrev`, with *stable observers* (`toBitVec`, `toNat`) and representation-independent operation laws stated through them (§5.1). The exercise tests that promise.

---

## 2. Layering and the seams consumers need

```
L7  Guest               bytes → bytes (run_stateless_guest); header chain; witness decoding
L6  Fork composition    selects Amsterdam parameters, fork modules and the precompile table
L5  Block execution     execute_block, apply_body, process_transaction, BAL, receipts, requests, withdrawals
L4  Call execution      the recursive runner: message call / create, child resume, termination
L3  Opcode stepping     Evm frame, stack, memory, gas meter, one handler per opcode; precompiles alongside
L2  State semantics     accounts, PreState record + ModelsLookups, tx/block overlays, lifetimes, BlockDiff
    State backends      full-state backend · witness-state backend   (implement L2 using L1)
L1  Commitments         MPT (mathematical root, partial trie, incremental root), commitment codecs
L0  Base, codecs, crypto  primitive types; RLP/SSZ; keccak/SHA-256/RIPEMD-160/BLAKE2; fields, curves, pairings, KZG
```

**The seams consumers need.**
- **Guest:** `runStatelessGuest : ByteArray → ByteArray`, split into decode, verify and encode. This is evm-asm's `Faithful` shape and pancaketh's refinement target.
- **Block execution:** `executeBlock`, parametric in a `PreState` record. Two backends implement that record. This is EELS's own seam and evm-asm's `ExecutionSeam`.
- **Opcode step:** `step`, with one function per opcode, for dispatch-loop simulation proofs.

---

## 3. Libraries and allowed dependencies

All core libraries live in one Mathlib-free **core Lake package** (the repository root; module prefix `STFSpec.`, for example the library `EthVmCore` is rooted at `STFSpec.Vm.Core`) (`CONTRIBUTING.md` §4: the boundary is package-level). Import rules *inside* the package are not enforced by Lake, as verified by experiment. So they are checked in CI by `scripts/check_boundaries.py` against **`scripts/boundaries.toml`**, which is the machine-readable form of this table and the source of the README diagram.

| Library | Contents | May depend on | Must **not** depend on |
|---|---|---|---|
| `EthBase` | primitive types and conversions: `U256` API, `U64`, `Bytes`, `Address`, `Hash32`, `Bytes32`, big-endian conversions, key orderings, the `Envelope` record (no fields yet, B6), and small policy-free records needed below both VM and block (`Authorization`, `StateGasPerByte`, the `HashConsts` record of keccak-derived constants) | Lean core | everything else. It contains **no fork policy**. |
| `EthHash` | keccak-f/keccak256, SHA-256, RIPEMD-160, BLAKE2 F; the `KeccakQuery` class, its `Id` instance and transformer lifts, and `HashConsts.query` (D5) | `EthBase` | — |
| `EthField` | prime fields and towers (carry-preserving Montgomery; source per D6) | `EthBase` | VM, state |
| `EthCurve` | curve groups, ECDSA recover/verify, MSM | `EthField` | VM, state |
| `EthPairing` | pairings, KZG (cryptography-specs as a reference only, D15/D26) | `EthCurve` | VM, state |
| `EthCodec` | RLP, SSZ, `hash_tree_root` | `EthHash` | state, VM |
| `EthState` | **semantic** state: `Account`, the `PreState m` record and its *lookup* contract (`ModelsLookups`), `MathState`, overlays (`TxState`/`BlockState`), lifetimes, `BlockDiff`, and the lookup, overlay and rollback laws | `EthBase` | **`EthCommit`, `EthCodec`**: no hashed nodes, RLP, dirty paths, witness decoding or roots |
| `EthCommit` | MPT **generic over encoded keys and values** (`ByteArray → ByteArray` maps): nibbles, hex-prefix, node types, the mathematical root, witness decoding, the partial trie, lookup/update/delete, incremental root | `EthCodec` | `EthState`, VM: it knows nothing about accounts |
| `EthStateCommit` | **integration:** account and storage leaf encodings, `mathStateRoot` (account trie of storage roots), and the binary full contract `Models ps σ := MathState.WF σ ∧ CodeAuthentic σ ∧ ModelsLookups constsId ps σ ∧ ModelsCode ps ∧ ModelsRoot ps σ`, where `constsId` names `Id.run (HashConsts.query (m := Id))` (Q57; EthStateCommit SC7/§7.3). `ModelsCode` checks successful code results against their concrete hash; `ModelsRoot` states `ps.stateRoot d = .ok r → r = Id.run (mathStateRoot (m := Id) constsId (σ.apply d))` for every well-formed diff | `EthState`, `EthCommit` | VM |
| `EthStateFull` | full-state backend: `PreState` from a mathematical state; `stateRoot` via `mathStateRoot` | `EthStateCommit` | VM |
| `EthStateWitness` | witness-state backend: node and code DBs, `PreState` over the partial trie | `EthStateCommit` | VM |
| `EthVmCore` | `Evm` frame, `Message`, environments; **Stack**, **Memory**, **GasMeter** and gas *policy* (the parameter record lives here); jumpdest analysis | `EthState` | `EthCommit`, backends |
| `EthVmInstructions` | one handler per opcode, producing a `StepResult` (successor frame, halt/revert/exceptional outcome, or a **child call/create request**) | `EthVmCore`, `EthHash`, `EthCodec` (CREATE addresses) | **`EthVmRunner`, `EthPrecompiles`**, crypto internals |
| `EthPrecompiles` | one module per precompile: input parsing, gas, output encoding over named crypto primitives | `EthVmCore`, `EthHash`, `EthPairing` | `EthVmInstructions`, `EthVmRunner` |
| `EthVmRunner` | the recursive executor: runs the frame loop, executes child requests, **named resume operations** on the parent, termination; parameterised by a precompile table; EIP-7702 authority recovery | `EthVmInstructions`, `EthCurve` (secp256k1 recovery, D26) | precompile *implementations* (it receives a table) |
| `EthBlock` | header, transaction and receipt types, validation, `processTransaction`, `applyBody`, `executeBlock`, BAL, bloom, requests, withdrawals | `EthVmRunner`, `EthCodec`, `EthCommit` (tx/receipt/withdrawal roots) | backends |
| `EthFork` | `Amsterdam` composition: parameter records, the fork modules whose behaviour changed, the precompile table, and the selection | `EthBlock`, `EthPrecompiles` | — |
| `EthStateless` | the `ExecutionWitness`/`StatelessInput` codecs, header-chain validation, `verifyStatelessNewPayload`, `runStatelessGuest` | `EthFork`, `EthStateWitness` | — |
| `EthConformance` | EEST runners, `core` `#guard` suites | `EthStateless`, `EthStateFull` | — |

**Outside the core package:**
- **`STFSpecMathlib/`**, the Mathlib bridge package: `EthFieldMathlib`, `EthCurveMathlib`, `EthPairingMathlib`.
- **`STFSpecSecurity/`**, the security package: `EthSecurity` (requires the core and the bridge package) and the separate `ToVCVio` local RLP/reference support library (existing core/standard dependencies; see its owning guidance). VCV-io may enter here only, subject to Q14/D26; it is not installed.

**Reduced dependency overview** (the README diagram is generated from `boundaries.toml`; edges implied by longer paths are omitted). The table above includes additional permitted imports, such as hashes used directly by instructions and precompiles:

```
EthStateless    → EthFork, EthStateWitness
EthFork         → EthBlock, EthPrecompiles
EthBlock        → EthVmRunner, EthCommit
EthVmRunner    → EthVmInstructions, EthCurve   (D26)
EthVmInstructions → EthVmCore, EthCodec
EthPrecompiles  → EthVmCore, EthPairing
EthPrecompiles  → EthHash
EthVmCore      → EthState
EthStateFull    → EthStateCommit
EthStateWitness → EthStateCommit
EthStateCommit  → EthState, EthCommit
EthState        → EthBase
EthCommit       → EthCodec → EthHash → EthBase
EthPairing      → EthCurve → EthField → EthBase
EthField        ⇢ CompPoly-derived Montgomery code, vendored or upstream (D6);  EthPairing/EthCurve ⇢ cryptography-specs as reference (D15)
EthSecurity     → EthStateless, EthStateFull, EthPairingMathlib (STFSpec/informal/contracts.toml), VCV-io, Mathlib
ToVCVio        → EthBase, EthCodec, EthCommit (STFSpec/informal/contracts.toml); no VCV-io import
Eth*Mathlib     → Eth*, Mathlib
```

**Why state semantics are split from the trie.** An SSTORE proof should talk about storage reads, writes, gas and rollback, never about hashed nodes, RLP, dirty paths or witness decoding. The ownership rule is:
- lookup, overlay and rollback laws live in `EthState`;
- a trie generic over bytes lives in `EthCommit`;
- everything that needs *both*, namely how accounts and storage are encoded as trie leaves, what the state root of a mathematical state is, and code-hash agreement, lives in the small `EthStateCommit` component.

No semantics are duplicated, and neither side imports the other. With `EthState` independent of `EthCommit`:
- the trie implementation can be replaced while VM and block proofs are preserved (replacement exercise 2);
- a future change of the protocol's commitment scheme has one bounded integration point, the backends.

**Why stepping is split from call execution.** `EthVmInstructions` describes CALL/CREATE as a *request*, without importing the recursive interpreter. Recursion and termination live only in `EthVmRunner`. So arithmetic, memory and storage proofs survive if the runner is replaced by an explicit continuation stack (D13). Likewise, opcode proofs don't depend on BLS pairing internals, because precompiles are reached only through the table the runner receives.

---

## 4. The component contract (template)

Every replaceable component publishes:

1. **Operations and observations**: the executable API.
2. **A model or representation relation**, where the representation is not itself the semantics (for example `PreState.Models`, and the partial trie's `represents` relation to a mathematical map).
3. **Well-formedness** and its preservation by every operation.
4. **Behavioural laws** that callers use (read-after-write, frame/disjointness, snapshot/revert, and so on).
5. **Stable equations** for its public execution functions: named `@[simp]`-free equation lemmas that callers rewrite with.

**Model-based specification (after Nipkow et al., *Functional Data Structures and Algorithms*, Ch. 6).** Items 2–4 take a specific form:
- Each component has a public **mathematical model** (for example a finite map, a byte sequence, or a list), an **abstraction** α from the representation to the model, and an **invariant**.
- Each operation `f` has exactly two obligations: it **preserves the invariant**, and it **commutes with the abstraction**: `α (f x) = f_model (α x)`, under the invariant.
- The behavioural laws callers use (read-after-write, clear suppression, snapshot/revert, sortedness of the BAL output) are **derived once on the model**, not re-proved per representation.
- **A replacement representation re-proves only the per-operation commuting equations and invariant preservation.** Every law stated on the model, and every caller proof using it, survives unchanged. Replacement exercises 1, 2 and 4 test exactly this.
- **Where the representation holds strictly less information than the model** (the partial trie, whose `hashed` stubs hide subtrees), α is replaced by an **abstraction relation** `represents t M`, which may relate one trie to many maps. The commuting obligation becomes a simulation: if `represents t M` and the operation succeeds on `t`, then `represents (f t) (f_model M)`. The book has no such case; it is our addition (§5.4).
- Lean's `Std` trees already follow this method: `toListModel` plays the role of the book's `inorder`, with `Ordered` as its invariant and `toListModel_insert` as a commuting equation (`Std/Data/DTreeMap/Internal/Def.lean:73`, `WF/Lemmas.lean:912`). So our wrappers inherit most per-operation equations from `Std`.

**Resource evidence accompanies the contract.** Each component's decision record states operation and size parameters, key/payload costs, retained-version and ownership assumptions, and whether bounds are worst-case, expected or amortised. Record allocation, peak live space and reclamation as well as operation counts. Distinguish Lean proofs from source checks, paper-derived bounds and measurements. Cost upper bounds are separate from semantic equations: a replacement may improve cost without preserving exact cost. This applies the modularity lesson of [Grodin, Li & Harper, POPL 2026](https://www.cs.cmu.edu/~runmingl/paper/afat.pdf) without adopting a new proof framework. Semantic gas and interpreter fuel do not by themselves bound host time, space or zkVM cycles.

**Proof-coupling rules.**
- Callers use only the public laws and equations. They never unfold container internals (`ByteArray.data`, array updates, buffer builders, map trees) or compiler-generated recursion equations.
- Intentionally public semantic model definitions may be unfolded. Concrete `U256` operation definitions remain behind the observer laws, even when their initial implementation uses BitVec.
- Simp sets are small and predictable, one per component, opt-in (`simp [Memory.laws]`). There is no global simp set that expands whole state structures.
- **Replacement procedure:** implement the new representation, establish its relation to the same contract, re-prove the component's public laws, then rebuild callers. Downstream files need rebuilding; their proof scripts should not need edits. The acceptance exercises in §1 test exactly this.

A *universal* interchangeable-container framework is explicitly **not** built. There are only small wrappers at the domain boundaries below.

Each implemented boundary also records its EELS function and full source commit, owning Lean module, public laws, and regression inputs. This source map belongs next to the component contract; moving an implementation preserves the map and stable law names. Declaration and import checks do not enforce proof independence or semantic adequacy: the replacement exercises and proofs do.

---

## 5. Components: initial representation, preserved boundary, proofs

Proof-obligation tags:
- **[T]** totality or termination.
- **[R]** needed by consumers' refinement proofs.
- **[C]** a component's own laws or correctness.
- **[F]** fast path ≡ reference (only if attached).
- **[S]** security (`EthSecurity`).

### 5.0 Persistence rule: what a snapshot may reach

Our state is used **persistently**: a call-frame snapshot keeps the old version, and revert returns to it (LIFO, nested up to depth 1024).

- **Ordinary ephemeral amortisation can fail under this pattern.** Okasaki's persistence counterexample (thesis §3.2, p. 19) repeats an expensive operation on a kept version. Nipkow et al. make the same point (p. 227). A bound proved for a single sequence of latest-version updates does not cover replay from retained parents. Memoised laziness can support persistent amortisation; Okasaki reports strict worst-case alternatives for his structures and overheads when lazy versions are used mostly single-threaded (p. 128). Lean's default evaluation is strict.
- **Linear-only structures lose in-place update when shared.** Lean's `Array`, `ByteArray` and `Std.HashMap` (array-backed, `DHashMap/RawDef.lean:54`) update in place only when unshared (Ullrich & de Moura, *Counting Immutable Beans*, IFL 2019). A snapshot shares them, and the next write copies the whole structure, so each write after a snapshot costs time linear in the structure's size.

**Rule.**
- Data **updated while an old version is retained** initially uses a **worst-case persistent structure**: balanced trees (`Std.TreeMap`/`ExtTreeMap`), lists, or ropes. Read-only payloads may be shared freely. Lean's trees use the Adams-style size variant with `delta = 3`, `ratio = 2`; balance preservation comes from Lean's own proofs. Hirai–Yamamoto's original-WBT theorem uses a different weight definition and cannot be transferred by matching constants alone.
- **Ephemeral or ordinarily amortised structures** (`Array`, `ByteArray`, `HashMap`) are updated only under linear ownership: memory, stack and observation sets threaded outside the snapshot. A DB built linearly and then frozen may be shared read-only.
- A HashMap with an undo journal (what geth, revm and evmone do) is a valid *later* representation for revertible state. Only the newest version and its ancestors are ever reused, which is exactly the *semi-persistent* setting of Conchon & Filliâtre (ESOP 2008). Adopting it would be a representation replacement proved against the same model-based contract (§4), with the semi-persistence discipline as an explicit obligation. It is a representation replacement under D25 (D22); `@[csimp]` is banned outright (D21).
- Selecting a saved root is O(1); reclaiming discarded branches and payloads can take time proportional to the released structure in Lean's reference-counting runtime. Benchmark complete frame lifetimes, including cleanup and retained space. A journal's resizing bound must also cover undo and capacity management; linear ownership alone does not prove that bound.
- `Std.HashMap` has expected fast operations under a suitable hash distribution, not a worst-case O(1) guarantee. Equality/hash laws establish functional correctness only. Keccak collision resistance does not prevent ordinary bucket collisions. Measure the eventual key instance and adversarial distributions, including DB construction; compare ordered trees or sorted read-only arrays where deterministic bounds matter.
  Hash32 table support is owned by EthBase (Q51; model/laws in EthBase §3); it supplies functional compatibility with actual equality, not suitable-distribution or authentication evidence. Concrete NodeDB construction and adversarial-distribution cost measurements remain open.

**Known `Std` costs** (verified in source, v4.34.0):
- `union` inserts the smaller map into the larger (`Operations.lean:555–560`), costing O(m log(n+m)) rather than the join-based O(m log(n/m+1)), with the second argument winning conflicts. `mergeWith` folds **the second map** using `alter`, regardless of relative size (`:939–945`); its cost also includes the supplied merge function.
- `ofList` is repeated insertion, O(n log n), and there is no linear-time build from sorted input.
- The checked tree modules contain no height or operation-cost theorem. O(log n) is an analytical expectation from their balance invariant; a formal bound must cover that actual invariant, key comparisons and runtime assumptions.

These matter for folding transactions into `BlockState` and for the BAL builder. If profiles show them, investigate join-based `union` built on `Std`'s existing `link`, contributed upstream. Set-union algorithms are only a starting point: preserve map conflict bias, tombstones and storage-clear chronology.

**Not used:**
- `Lean.PersistentHashMap`/`PersistentArray`: each is built on 17 `partial def`s, with 2 and 0 theorems respectively. Their opaque recursive bodies and missing functional laws are unsuitable for the core contract and audit.
- HAMT/CHAMP initially: total definitions, collision handling, laws and measured benefit would need to justify the additional maintenance. A proved final sort can supply sorted BAL output independently of container iteration order.
- Bespoke Patricia maps.

### 5.1 Base and codecs

| Component | Initial representation | Boundary to preserve | Proofs |
|---|---|---|---|
| EVM word `U256` | `structure U256` wrapping a `BitVec 256` field (D1(a) first). The field is internal by convention, and exercise 4 checks it: callers go through the observers. It is a `structure`, not an `abbrev`, so callers cannot silently use `BitVec` instances. It carries explicit EVM arithmetic (`evmDiv x 0 = 0`, `evmMod x 0 = 0`, signed ops, `addmod`/`mulmod`, `exp`, `signextend`, `byte`, shifts). | **stable observers** `toBitVec : U256 → BitVec 256` and `toNat`, which are injective with an extensionality lemma, plus **representation-independent operation laws** stated through them (for example `(a + b).toBitVec = a.toBitVec + b.toBitVec`, `(evmDiv a b).toNat = if b.toNat = 0 then 0 else a.toNat / b.toNat`). Callers use only these; the operation definitions are not unfolded downstream | [R] the operation laws. [F] if the representation changes (D1(b)), only this component's definitions and law proofs change. Replacement exercise 4 tests this |
| `Address`, `Hash32`, `Bytes32` | distinct fixed-width domain types (D2) | equality, a total order (a hand-written `compare` for map keys), and byte conversions | [C] conversion bijections; `compare` is a lawful order |
| `Bytes` | `ByteArray` | the byte-sequence API with extract/append laws | [C] local library of laws |
| `Envelope` | record of implementation limits | explicit hypotheses in consumer theorems | these limits do not narrow the reference guest's accepted input domain. A bounded optimization must refine a total reference, or a deviation must follow the protocol discrepancy policy |
| RLP | `RlpItem` tree; builder encode; cursor decode | encode/decode and canonical-form rules | [T] decode is total on any bytes (recursion on remaining length); [C] round-trip; [C] **injectivity/prefix-freeness** (feeds [S]) |
| SSZ | structures plus codecs; `hash_tree_root` with a zero-hash cache | codec and `hash_tree_root` API | [T] offset decoding bounded by input length; [C] round-trip, padding/limit lemmas |
| Hashes | readable references; proved fast paths only later (D4) | `keccak256 : ByteArray → Hash32`, etc. | [C] size and KATs; [F] fast ≡ reference; [R] keccak-f ≡ the ZisK accelerator's `keccakF` (`ZiskAccel`, in a bridge module) |

### 5.2 Crypto (precompile mathematics)

These are as in v1.1, with the reference sources:
- **BLS12-381/KZG:** ethereum/cryptography-specs (D15).
- **Fast fields:** our own carry-preserving CIOS Montgomery backend, which needs only `p < R`: `Wide8` (8×32-bit limbs) for every pinned modulus below 2^256, and `W12` for BLS12-381 q. It is derived from CompPoly's zero-import `…Defs` (D6). Measured: the `Nat` reference is 3–6.5× slower than `Wide8` (several times, not orders of magnitude), and `Wide8` is 20–35× slower than native ecrecover. The remaining gap to native is curve-level (`EthCurve`: Shamir/Straus, wNAF, GLV).
- **Curves:** projective internally (D7).

Mathematical correctness and cryptographic security are separate deliverables (D12). **Isolation rule:** a change to pairing internals affects only `EthPairing`/`EthPrecompiles` and their proofs. No opcode proof depends on them.

### 5.3 `EthState`: state semantics

| Component | Initial representation | Boundary to preserve | Proofs |
|---|---|---|---|
| `Account` | `{nonce : Nat, balance : U256, codeHash : Hash32}` | — | — |
| `PreState` | an explicit **record of operations**, parametric in the hash monad (D5): `PreState m` with `getAccount? : Address → m (Except WitnessError (Option Account))`, `getStorage : Address → Bytes32 → m (Except WitnessError U256)`, `getCode : Hash32 → m (Except WitnessError ByteArray)` (B2), and `stateRoot : BlockDiff → m (Except WitnessError Hash32)`. Execution uses `m := Id`; lookup/full models are stated at `PreState Id`. The provider appears visibly in execution and theorem statements. | the supplied record type and supplied **`ModelsLookups consts ps σ`** (EthState R8/§5; Q57): successful answers agree with mathematical observers, *including account absence*, and code uses `σ.code? consts h` at the supplied reserved hash. Tracker premises use `BlockState.consts`; no provider field or local acquisition is added. Full `Models` stays binary at the coherent concrete Id record (§3). Generic coupling remains D5/X7 | each backend proves full `Models` (§5.4) and the caller establishes context coherence |
| Revertible tx state | persistent `Std.ExtTreeMap` overlays. Storage is **nested by address** (`Address → Bytes32 → U256`), because clearing and committing storage are account-level operations. | `getStorage`, `getStorageOriginal`, `setStorage`, `clearStorage`, `getAccount`, `setAccount`, `getCode`, `setCode`, `snapshot`, `revert`, with laws | [C] read-after-write, read-through order. The **`clearStorage` law:** a clear suppresses lower overlays and the pre-state for slots not subsequently rewritten in that overlay. Later local writes remain visible. The clear converts pending writes to reads (`state_tracker.py:547–568`). [C] revert restores exactly the revertible component |
| Persistent observations | **kept outside the snapshotted component** and threaded linearly alongside it: `account_reads`, `storage_reads`, `code_reads` and `created_accounts`. They are never reverted within a transaction, so no snapshot needs to hold them, and they can be ephemeral sets (`Std.HashSet`, or `TreeSet` where sorted output is needed). Keeping them inside the snapshot would make every write copy them | add and observe, with monotonicity | [C] monotone across reverts; [C] the split is invisible to callers: reading through the combined state gives the EELS results |
| Frame accumulators | **warm access sets:** persistent trees, since a child extends the parent's set and a failed child's additions are discarded. **Logs:** a strict rope (`leaf · concat`) with O(1) append, so merging a child's logs into the parent never copies them once per call-depth level. Refund counter: a signed `Int` | as §6 | [C] merge-on-success/discard-on-failure laws on the model (a set or a list of logs) |
| `BlockDiff` | extensional maps plus the account, storage-address and slot first-write orders (B1); the iteration order of storage clears is open (F7) | the ordered diff API consumed by the backends' `stateRoot` | [C] order metadata enumerates each live write once |

Extensional maps (`ExtTreeMap`) give `=`-reasoning. They do *not* by themselves make snapshots cheap or establish storage semantics. Snapshot cost comes from persistence, and correctness from the laws above; key ordering still matters for speed (D2).

Q58's supplied `BlockDiff.StructuralPremises` and ordinary laws
are owned by EthState §5/§7.4: deletion tombstones clear storage, and every raw
storage-change address has a present post-account, including empty patches and zero
writes. With initial MathState.WF this suffices for structural output WF on all finite
raw inputs, with arbitrary metadata/code/account fields. It does not supply full
BlockDiff.WF, optional slot-order-map missing/extra-entry policy, replay history,
reachability, AccountWritesLookedUp or F7, and does not replace root/availability premises.

**Log traversal.** Flatten once at receipt construction using an explicit traversal stack and one linear output builder, preserving order and duplicate occurrences. The list-append equation is a model law, not an instruction to append recursively flattened lists. That implementation can be quadratic on skewed ropes. Rope height can grow with sibling calls beyond the call-depth limit; prove traversal totality and avoid dependence on host recursive stack depth. Include empty-child merges, skewed shapes and cleanup in the C3 measurements.

**Storage precedence** (`state_tracker.py:295–340`): transaction slot write → transaction clear → block slot write → block clear → pre-state. `getStorageOriginal` skips transaction writes and clears; it returns zero for an address in `created_accounts`, otherwise it reads block writes, block clears, then pre-state. These are separate public laws because SSTORE gas depends on both current and original values.

**Code-hash ownership.** EELS `set_code` computes keccak (`state_tracker.py:734–760`). To keep `EthState` independent of `EthHash`, the state operation accepts code bytes and an already computed hash; hash-aware callers compute the hash and establish agreement. `EthStateCommit` owns the agreement law, including empty-code handling. This rearranges ownership without changing the EELS order of state changes or observations.

**Backend progress is separate from agreement.** `Models` constrains successful responses; a provider returning only errors would satisfy those implications vacuously. The full backend must additionally prove successful lookup and root computation for every well-formed finite state/diff. The witness backend must prove success when the required authenticated data is available and valid, respecting eager decoding and its trigger points. Authenticated absence is a successful result, not missing witness data. Security soundness and execution completeness use these different obligations explicitly.

### 5.4 State backends and commitments

| Component | Initial representation | Boundary to preserve | Proofs |
|---|---|---|---|
| Witness/code DBs | read-only `Std.HashMap Hash32 ByteArray` after construction, built through the hash oracle | `lookup`, and the separate predicates `NodeDB.Authentic`/`CodeDB.Authentic` ("a stored value hashes to its key", F4) | [C] authenticated-content invariant |
| Witness decoding | **eager**, matching the reference: decoding a root decodes everything reachable from it through the node DB (`incremental_mpt.py` `decode_witness_to_mpt`/`_decode_witness_node`/`_resolve_child_ref` at e1a316a0). It is triggered where the reference triggers it: the account trie at first account access; each storage trie at first access to that account's storage; and, in state-root computation, the storage trie of every account with storage changes and the account trie (`witness_state.py` `_get_decoded_secure_root`, `compute_state_root_and_trie_changes`). The source caches read decodings by root hash; Q55 leaves generic successful-result ownership/lifetime and F6 open, and root computation decodes afresh. A malformed node *anywhere* reachable makes validation fail (O4), even if no lookup would reach it; a lazy path walk would accept witnesses the reference rejects. | `decodeRoot {m} [Monad m] [KeccakQuery m] (emptyRoot : Hash32) (db : NodeDB) (r : Hash32) : m (Except TrieError Ref)` (Q55 local operation/laws owned by EthCommit §3; witness adapter separate; empty root short-circuits without a local query, `incremental_mpt.py:1024–1030`) | [T] see "Termination of witness decoding" below; [C] actual raw-preimage answer/cache provenance; equality to a DB reference only under `Authentic keccak256` and raw length ≥32 at concrete Id |
| Partial trie | explicit `Node.leaf/ext/branch/hashed` carriers and `Ref := Option Node` (EthCommit §3/§5): `none` is absence, and inline/cached references retain encoding context rather than separate Ref variants. B3 requires representation hiding and demonstrated DISC-003 provenance sufficiency before semantic adoption (EthCommit §10). Branch children are an `Array (Option Node)` with a separately stated size-16 invariant, because the kernel rejects `Vector` in this nested inductive (F5, [DECISIONS §3](DECISIONS.md)). Each resolved node carries completed immutable `Enc` fields; acquisition/cache interpretation and operational refinement are owned by EthCommit §5/§6/§7.6. geth, remerkleable and milhouse do the same, and snapshots never invalidate it. | `lookup`/`update`/`delete`/`root`, with **agreement with the mathematical root** | [T] bare lookup descends by proper-child Node size (Q59); admitted update/delete use their separate nonempty-path remaining-key descent; [C] **agreement theorem** (shape below); [S] ROM lift |

**MPT proof pattern.**
- **Canonical form, after Nipkow et al. Ch. 12 (Patricia tries).**
  - An invariant `Canonical` states the node-shape rules: no empty extension, a branch with at least 2 occupied entries, an extension child that is a branch, and a leaf with any remaining path.
  - A **single normalising smart constructor** (the book's `nodeP`) is the only way updates and deletes build nodes, including branch collapse and extension merge. So canonicity is preserved by construction.
  - "Canonical tries are equal iff they represent the same map" (book Exercise 12.1) gives order-independence of the mathematical root.
- **Abstraction relation, not a function** (§4): `represents t M`.
- **Theorem statement shape, after Kestrel's ACL2 `books/kestrel/ethereum/mmp-trees.lisp` (Coglio).**
  - The hash-preimage database is explicit.
  - Decoding means "some map encodes to this root".
  - Operations report a **`collision`** outcome instead of assuming collisions away. The file says so: "Since we cannot ignore the mathematical possibility of hash collisions, [these functions] all return an error flag that, when equal to `:collision`, indicates that a collision in the constructed database took place".
  - Our deterministic agreement theorem takes the same form: either the result agrees with every map the witness can represent, or a keccak collision is computable from the database and the queried preimages.
- **Incremental root:** Cassez (FM 2021) is the precedent for proving an incremental root equal to the from-scratch root.
- **The security framing** is Miller, Hicks, Katz & Shi (*Authenticated Data Structures, Generically*, POPL 2014): the guest is the verifier, the witness is the proof stream, and accepting a wrong state implies a collision.
- A PAM-style augmented map does *not* fit: the MPT root depends on trie shape, not only on key order.

**Termination of witness decoding and traversal.** Valid empty-path leaves must be accepted. Node decoding, reference resolution and key traversal are separate:

- **Decoded node shapes, following the reference's checks.**
  - A **leaf may have an empty remaining path.** This is valid, for example after a branch consumes the final differing nibble, and the reference accepts it.
  - An **extension must have a non-empty path**, and its child must be a branch or a hashed reference (asserted by the reference).
  - A **branch must have at least 2 occupied entries**, counting its value.
  - Any other list length is malformed.
- **Bare lookup traversal** (Q59) descends by proper-child Node size, independently
  of key consumption. A matched empty extension still moves to a proper child;
  branch terminal values precede bounds, and only an in-bounds selected child is
  traversed. EthCommit §7.0.5 owns the supplied equations.
- **Admitted mutation traversal** (update/delete) has a separate remaining-key
  measure under the nonempty-extension path invariant. A branch consumes one nibble
  and an admitted extension at least one; a leaf is terminal and consumes nothing.
  This measure does not establish termination for arbitrary bare lookup inputs.
- **Reference resolution** (hash → node through the DB, or an inline RLP list → node) doesn't consume nibbles, so it is bounded separately:
  - Inline references recurse on strictly smaller RLP subterms.
  - Hashed references recurse through the DB. Eager decoding is a depth-first traversal that tracks the hashes on the current path; meeting one again is `WitnessError.malformed`. The proposed measure is (number of DB entries not on the current path, size of the inline subterm), to be checked under [REVIEW §7](REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks) W1.
  - This is total on *arbitrary* DBs **without** assuming collision resistance. At concrete Id, on a cycle the reference would recurse until `RecursionError`, which is caught and gives `False`; the mathematical cycle totalization gives that output deterministically, without claiming the finite host-limit query trace (`STFSpec/informal/CONTRACT.md` O12).
  - Diamond-shaped sharing, where the same hash is reached by two paths, is not a cycle. Memoizing **completed, validated** decodings may avoid repeated expansion; a global visited set must not mistake sharing for a cycle or skip a malformed descendant. Prove unchanged accept/reject behaviour, including off-path malformed nodes, plus Q55's cache/path/effect/first-error conditions before selecting sharing. Missing child preimages can remain unresolved hashed references until needed, as in the reference; a missing root being decoded fails immediately.

| Component | Initial representation | Boundary to preserve | Proofs |
|---|---|---|---|
| Mathematical root | `patricialize`-style definition over a finite map | proof-carrying reachable helper domain (Q50), all maps start at zero | [C] domain/strict descent and recursive C7 construction with every-node representative independence in EthCommit §3; C8 total local root/reference equality in EthCommit §3; canonicality and whole-source refinement open |
| Full-state backend | a mathematical state plus `mathStateRoot` | `PreState` + `Models`, plus progress | [C] agreement and successful operations on well-formed finite state/diffs |
| Witness-state backend | DBs plus partial trie | `PreState` + `Models`, plus data-availability conditions | [C] agreement for every σ consistent with the witness and rooted at `parent.state_root`, modulo collisions; success under the explicit availability conditions |

### 5.5 `EthVm`: opcode stepping, precompiles, call execution

| Component | Initial representation | Boundary to preserve | Proofs |
|---|---|---|---|
| Operand stack | `Array U256`, depth ≤ 1024 | `push`, `pop`, `peek`, `depth`, and **failure behaviour** (underflow/overflow as exceptional halts) | [C] stack laws; [R] used by per-opcode lemmas |
| Memory | `ByteArray` (D11) | logical size (32-byte words), zero extension, word/byte reads and writes, copying with zero padding | [C] **read-after-write and disjoint-window laws**, expansion laws. Memory-opcode proofs use only these (exercise 1) |
| Gas meter | a dedicated `GasMeter` record (2-D: execution plus state gas with reservoir/spill), following `gas.py` names | **charge, reserve, return (child gas), and exceptional-halt behaviour** as named operations with laws; gas *policy* (costs) is a separate parameter record | [C] meter laws; [T] the measure (below); exercise 3 |
| Jumpdest analysis | a bitmap per code; optionally a cache keyed by code hash (§7) | `isValidJumpdest code pc` | [C] equals EELS `get_valid_jump_destinations` |
| Instructions | one handler per opcode → `StepResult = next frame · halt/revert/exceptional · childRequest` | the per-opcode semantics | [R] per-opcode lemmas stated with stack, memory, gas and state laws only |
| Precompiles | one module each; dispatch through a table of `PrecompileFn m := Bytes → GasMeter → m PrecompileResult` (monadic because ECRECOVER hashes through `KeccakQuery`, D5); the meter law holds for every `m` | EVM-level behaviour per EELS | conformance; D12 |
| Runner | recursive, EELS-shaped (D13): runs the frame loop, executes a `childRequest` and applies a **named resume operation** (`resumeAfterCall`, `resumeAfterCreate`) | `processMessageCall`/`processCreate` | [T] the termination design (below); resume laws |

**Termination design** (revised 2026-09-28 from prior art: EVMLean, powdr and EVMYulLean, cited below; still a hypothesis until the fuel-adequacy investigation ([REVIEW §7](REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks) G2–G7) passes). It keeps three things separate: **semantic gas** (Ethereum's), **interpreter fuel** (a Lean artifact), and the **contracts** proofs use.

- **The v2 measure is wrong under Amsterdam gas** [verified at e1a316a0]. `gas_left` is *not* monotone within a frame. `credit_state_gas_refund` does `gas_left += min(amount, state_gas_spilled)` (`vm/gas.py:606–628`), and SSTORE calls it when a slot is set and then cleared (`vm/instructions/storage.py:151`); `repay_state_gas_spill` and `restore_state_gas*` also move gas between pools. So neither `gas_left` nor `gas_left + state_gas_left` strictly decreases.
- **Proof potential instead of `gas_left`:** `Φ = gas_left + state_gas_spilled + state_gas_committed_spill`. Every mutation of these fields in the pinned `vm/gas.py` was checked by reading (2026-09-28):

  | Operation (line) | Effect on Φ |
  |---|---|
  | `charge_gas` (`:405`) | decreases by the charge; strict only for a positive charge |
  | `charge_state_gas`: from the reservoir (`:441`) / spill path (`:445–446`) | unchanged / unchanged (moves `gas_left` into spill) |
  | `commit_state_gas` (`:500–502`) | unchanged (spill into committed) |
  | `restore_state_gas` (`:524–527`) | unchanged (spill back into `gas_left`) |
  | `restore_state_gas_to_entry` (`:559–565`) | unchanged (both spills back into `gas_left`) |
  | `credit_state_gas_refund` (`:625–627`) | unchanged (spill into `gas_left`; the rest goes to the reservoir, which is not in Φ) |
  | `repay_state_gas_spill` (`:653–655`) | unchanged |
  | `forfeit_remaining_gas` (`:675`) | non-increasing (`gas_left` := 0); strict when it was positive |
  | `drain_state_gas_reservoir` (`:717–719`) | unchanged (reservoir is outside Φ) |
  | CREATE grant (`:697`), CALL charge/grant, `restore_child_gas` (`:745`) and `incorporate_child` (`vm/__init__.py`) | withholding decreases the parent potential; returning child gas can increase it: a **cross-frame obligation**, not a local monotonicity law |

  Within a frame, excluding child returns, Φ never increases and positive execution charges strictly decrease it. `restore_child_gas` is used when a child is never entered and adds the supplied grant; for CALL that grant can include the stipend. It does not itself restore either spill field. **Still to prove:** progress across complete CALL/CREATE iterations, covering forwarding, the 63/64 rule, paid stipends, depth/balance failures, child returns (success, revert, exceptional halt) and `incorporate_child`. Every continuing Amsterdam opcode iteration must decrease Φ by at least 1; zero-cost terminal instructions need only the final fuel unit. None of these source observations is yet a Lean theorem.
- **Shape, adopted from EVMLean (`step_semantics` @cdbd150).**
  - A lexicographic measure `(STACK_DEPTH_LIMIT − depth, stage rank, frame fuel)` via `termination_by` (EVMLean `Semantics.lean:228, 701, 795`).
  - Establish the depth bound and handle failed depth checks before recursive child descent. Saturating `Nat` subtraction would otherwise hide a failure of strict decrease at the limit. Preserve the reference's preflight/charging order while doing so.
  - **Fuel only in each frame loop,** seeded by a computable bound from that frame's entry potential (candidate: Φ + 1, not yet proved). The runner has no global fuel parameter; each child receives its own derived frame budget. One fuel unit accounts for a completed parent opcode iteration, including executing a child request and resuming the parent. Codecs, trie traversal and other helpers have separate termination measures.
  - Fuel sufficiency follows EVMLean's lemmas: `X_no_OufOfFuel_of_gas_lt_fuel` (`NoOutOfFuel.lean:318`), resting on "a continuing step decreases gas" and "a child returns no more gas than it received" (`Theta_gas_le`, `GasLemmas.lean:1327`). Together that is about 2,150 lines for 1-D gas, so budget for more with 2-D gas.
  - The 1-D theorem is a proof pattern, not a theorem about Amsterdam. Bound returned child **potential**, rather than only `gas_left`, and include stipend accounting in the parent's whole-iteration progress law.
  - **Improvement over EVMLean:** pass depth in a context argument which `step` cannot return or mutate; only the runner constructs a child's context. This avoids EVMLean's depth reset after each step ("ugly", `Semantics.lean:774`).
- **Four guarantees the fuel-adequacy investigation (REVIEW §7 G2–G7) must establish** (the pattern of powdr `yul-semantics` `Adequacy.lean`, where `EVM.run_adequacy` was checked: its axioms are `propext` and `Quot.sound`):
  1. **Soundness:** a completed checked execution corresponds to the semantic execution relation.
  2. **Completeness:** every semantic execution is reproduced at *all sufficiently large fuel* (`∃ N, ∀ n ≥ N`).
  3. **Fuel monotonicity at fixed semantic gas:** increasing *fuel* preserves the result.
  4. **Fuel sufficiency:** a computable frame-budget policy rules out internal fuel exhaustion (O11), including for executions ending in revert or EVM out-of-gas.

  It must define the fuel-indexed family precisely: a frame loop with explicit test fuel and derived child budgets, or an equivalent policy assigning budgets to all frames. Guarantees 2–3 quantify over that fuel/policy at fixed input and semantic gas; they do not silently introduce a global guest fuel argument. Guarantee 4 also requires `∀ input, ∃ out, runStatelessGuestChecked input = .ok out`, so **every** internal-error fallback is unreachable, even if `InternalError` later gains constructors.
- **Fuel is not gas.** Increasing *gas* can change the output: the GAS opcode, gas-dependent control flow, and the gas forwarded to calls all see it. So statements of the form "enough gas preserves behaviour" (for example eip8200's `∀ g ≥ g₀, …`) hold only for restricted computations, or under an explicit hypothesis. They are never a general property of the spec.
- **Avoid:**
  - `partial` runners with heuristic fuel (powdr `evm-semantics` `Tx.lean:239`, fuel `2·gasLimit + 100000`, no theorem);
  - `OutOfFuel` inside the EVM exception type (EVMYulLean), which O11 forbids;
  - a continuation-stack runner, unless we budget for a measure over the whole stack (D13).
- **Gas representation:** execution/state gas amounts, reservoirs and spills use `Nat` with checked charging, never a wrapping `UInt256` as in EVMYulLean. The **refund counter is `Int`**, matching EELS `GasMeter.refund_counter` (`gas.py:307`) and SSTORE's subtraction (`storage.py:134`); do not silently saturate a negative per-frame refund. Conversion/capping at transaction settlement has its own preconditions and laws.
- **Where it lives:** only in `EthVmRunner`. Generic proofs state the conditions they need of the gas parameters, and the Amsterdam instantiation discharges them (§8).

**Patterns for consumers' refinement proofs (evm-asm, pancaketh)**, from powdr:
- `yul-compiler`'s forward simulation with existential gas (`∃ b, ∀ s0, b ≤ gas → ∃ s', Steps …`), with additive gas for straight-line code and `GasTx` for calls;
- `eip8200-challenges`' `∃ g₀, ∀ g ≥ g₀, Eval … (.returned (spec cd))` with `GasSteps`/`execN` symbolic stepping.

Both are stated over a `Step` relation. Our `step` function should therefore come with a derived relation connected in both directions, plus determinism lemmas including exception precedence (powdr `evm-semantics` `StepDeterminism.lean`: `step_iff_stepF`, `step_deterministic`). Two further patterns:
- `yul-compiler`'s **`GasTx`** gas transformers compose remaining-gas bounds, covering ordinary subtraction and EIP-150's proportional loss when a child consumes its allowance.
- eip8200's **`GasSteps`** makes functional execution proofs carry their gas cost, so a concrete resource schedule reuses the same trace.

Neither uses `native_decide` or `bv_decide` in the inspected proof paths. Our declaration check judges the resulting axiom footprint, not tactic names alone; any future tactic used for arithmetic must produce a proof accepted by the declaration check.

**Execution contracts over selected observations** (powdr `evm-semantics` `EVM/Contract.lean`). Proofs about a code fragment state what it does to memory windows, storage slots, return data and gas, with **frame conditions** for semantic observations it leaves unchanged. This keeps unrelated representations out of caller proofs. Exact equality remains appropriate for a component's snapshot/rollback laws. Gas, warm sets, persistent access records and logical memory size remain semantic even when a particular functional theorem projects them away. There is still **one authoritative implementation** per opcode, and the child-request/runner split is kept.

### 5.6 Block, fork, guest, security

| Component | Initial representation | Boundary to preserve | Proofs |
|---|---|---|---|
| Transactions, headers, receipts, withdrawals, requests | structures plus codecs | codecs, validation predicates | [C] codec round-trips |
| Validation errors | explicit `BlockError`/`TxError` inductives: one constructor per distinct reference behaviour, classified by the first consuming handler (D14), including the enumerated O13 faults | — | fidelity via conformance |
| `processTransaction`, `applyBody`, `executeBlock` | EELS order | `executeBlock : … → PreState m → … → m (CheckedResult BlockError BlockDiff)`, used at `m := Id` | [R] the seam |
| BAL builder | `ExtTreeMap` builder; sorted output | builder API | [C] sorted and deduplicated: `Std`'s `ordered_keys_toList` (`TreeMap/Lemmas.lean:961`) plus uniqueness of sorting (Nipkow et al. Thm 2.9) pin down the output independently of the builder. Cost caveat: `ofList`/`union` (§5.0) |
| Guest | EELS control flow; outcome mapping O1–O13 (`STFSpec/informal/CONTRACT.md` §4) | `runStatelessGuest` | [R] top-level refinement target |
| Security | VCV-io bridge; scoped relative to the authenticated context (`STFSpec/informal/CONTRACT.md` §7) | — | [S] deterministic trie agreement, block-level agreement and the Keccak ROM bound (D5); separate SSZ/SHA-256 request-binding theorem; external anchors and precompile security assumptions stated explicitly |

---

## 6. State lifetimes (structural, per component)

A call snapshot captures **exactly** the revertible transaction component. Every other component has an explicit rule for each lifecycle event. The table follows EELS at e1a316a0: `state_tracker.py` (`copy_tx_state` :763–796, `destroy_storage` :547–568, `get_storage` :295–314), `vm/__init__.py` (`incorporate_child` :194–234) and `vm/instructions/system.py`. Each cell is to be re-confirmed line by line when the module is written.

| Component | Child returns successfully | Child reverts | Child halts exceptionally | Transaction completes | Block completes |
|---|---|---|---|---|---|
| **Revertible tx writes**: account, storage and code writes, storage clears, transient storage | kept (the child mutated the shared tx state) | restored to the call snapshot | restored to the call snapshot | account, storage and code writes and clears fold into `BlockState`; **transient storage is discarded** (a fresh `TransactionState` per tx) | `BlockState` → `BlockDiff` → `stateRoot` |
| **Persistent observations**: account, storage and code reads | kept | **kept** (shared by the snapshot) | **kept** | fold into the block's reads | account/storage reads feed BAL; code reads record code accesses for witness construction |
| `created_accounts` | kept | **kept** (shared) | **kept** | discarded (fresh per tx) | — |
| **Frame accumulators**: logs, `accounts_to_delete`, refund counter, warm access sets | merged into the parent (`incorporate_child`) | discarded | discarded | logs → receipt; deletions applied; refunds settled; warm sets discarded | logs → bloom/receipts root |
| **Gas meter** | remaining gas returns to the parent | remaining gas returns; state gas rolled back to the baseline, spill refilled, refunds discarded | child's remaining execution gas **forfeited**; state gas settled as for a revert | `settle_transaction_gas` | block gas checks |
| Return data | CALL-family: child output; CREATE-family: **empty**, with child output installed as code instead | child output (revert data) | empty | — | — |
| BAL builder | — | — | — | `update_builder_from_tx` | build, hash, validate |

Preflight failures and CREATE collisions do not spawn a child; their nonce, gas, access and return-data effects belong to the instruction's preflight/resume contract, not a generic child-rollback rule (`system.py` `generic_create` and `generic_call`). In particular, successful creation leaves parent return data empty (`:191`); it does not expose deployed code as CALL return data.

---

## 7. Caches and diagnostics are not semantic state

- **Caches** (jumpdest bitmaps keyed by code hash, decoded-node caches, zero-hash tables) live outside semantic state. Each has an invariant that its answers equal those computed from the underlying data, in the form of Nipkow et al. Ch. 18's memoisation-consistency invariant. Removing or replacing a cache requires an observer/refinement proof. For Q55 decoder actions, stable interpreted value equality alone does not prove unchanged generic query effects or first failures; a thunk of an action does not cache its executed result. In particular, the reference witness storage-root cache affects arbitrary helper calls: the pure replacement is justified only on reachable read-before-write traces (COMPOSITION §3). Raw node encodings must also be preserved. (A hash cached *inside* an immutable trie node, §5.4, is part of that node, not a separate cache.)
- **Diagnostics** (tracing, EIP-3155-style step traces) go through an **event interface**: the runner emits events, and a consumer folds them. Diagnostics must never retain whole previous frames, since that would break the linear use of the memory buffer and silently make memory writes quadratic. The event type carries copies of small values only. A linearity check, to be added with the runner, must run with tracing both on and off and **on a compiled `lake build` executable**: `#eval` in the interpreter shows far more sharing, so linearity observed there is not representative.

---

## 8. Fork parameters versus fork behaviour

- **Parameter records** hold constants: the gas cost schedule (including every precompile pricing table), limits, blob schedule and system addresses. The record *types* live next to their semantics (gas records in `EthVmCore`, blob parameters near block validation), **not** in `EthBase`; the Amsterdam *values* live in `EthFork` (B8). Only `STACK_DEPTH_LIMIT` is a literal in `EthVmCore`, because the depth proofs need a kernel-reducible bound (F8).
- **Named fork modules** hold behaviour that changed: instruction semantics, transaction rules, block processing, codecs. Unchanged code is shared, and names and source mappings to EELS are preserved.
- **An explicit composition module** (`EthFork.Amsterdam`) selects the parameters, the fork modules and the precompile table.
- **Conditions for generic proofs** are stated explicitly (for example gas monotonicity for termination, and accounting conservation). Arbitrary configurations need not satisfy them; the supported instantiation discharges them.
- Only Amsterdam is instantiated (D3).

---

## 9. Change management and technical debt

**Implementation policy (D18, accepted 2026-09-28; see `CONTRIBUTING.md` §4).** Implementations are final with respect to all required properties, and data structures are performance-appropriate. A justified exception (legibility, or drastic proof-friendliness) is recorded in [`STFSpec/informal/DEBT.md`](DEBT.md), with:
- the affected component and the contract it preserves;
- the current limitation and a regression example (a benchmark or input);
- the evidence needed to replace it.

Compatibility shims are temporary and carry a removal milestone. Missing semantics, unproved fuel sufficiency and unauthorized protocol deviations cannot be reclassified as performance debt.

**Two kinds of patch.**
- **Behaviour-preserving:** representation, caching, algorithm, execution strategy. It must establish equivalence or refinement against the unchanged contract.
- **Semantic:** fork updates, or corrections to accepted/rejected behaviour. It needs explicit changes to the contract, the tests (fixtures and `core` checks) and the affected proofs, plus a `reference.toml` update if the pin moves.

Consumers (evm-asm, pancaketh) stay pinned to released commits while semantic changes are reviewed. No permanent competing copies of the spec are kept.

---

## 10. Summary: what needs proofs

| Item | Proof | Kind |
|---|---|---|
| Std containers | reuse Std implementation lemmas; prove domain adapters, ordering and any missing public laws | [C] at the owning boundary |
| `U256` API spec lemmas | yes | [R] |
| Stack, memory, gas-meter laws | yes: the public contracts | [C], used by [R] |
| Overlay laws, including `clearStorage` suppression, snapshot/revert, persistence of observations | yes | [C] |
| `PreState.Models` and backend progress/data availability | yes, separately | [C] |
| Partial trie agreement with the mathematical root | yes: central | [C], feeds [S] |
| Totality of codecs and trie traversal on malformed input | yes | [T] |
| Runner termination, fuel sufficiency and adequacy | yes | [T] |
| RLP injectivity, SSZ and RLP round-trips | yes | [C], feeds [S] |
| Cache invariants | yes (small) | [C] |
| Fast paths ≡ references; ≡ ZisK accelerator definitions | when attached | [F], [R] |
| Field/curve/pairing mathematics; cryptographic security | per D12 | Mathlib partners, [S] |

---

## 11. Decision points

The options considered for each decision, and what evidence settles or revisits it. **The chosen option and the status are recorded only in [`STFSpec/informal/DECISIONS.md`](DECISIONS.md).**

| # | Decision | Options | Settled or revisited by |
|---|---|---|---|
| D1 | U256 stored representation | (a) a `structure` wrapping `BitVec 256` *(initial)* · (b) a limb `structure` whose operations are limb implementations, proved to satisfy the same observer laws (a representation replacement under D25; `@[csimp]` is banned by D21) | benchmark through the proof interface in an opcode loop, **and replacement exercise 4**. Callers see only observers and laws, so moving from (a) to (b) is a behaviour-preserving patch |
| D2 | Address/hash representation and key ordering | `BitVec n` · `Vector UInt8 n` · `ByteArray` + size proof | map-key `compare` cost |
| D3 | Forks | Amsterdam only, with parameter records, fork modules and a composition module (§8) | — |
| D4 | Hash implementations | reference · reference + proved fast | measurement; keccak dominates witness cost |
| D5 | Keccak abstraction scope | `KeccakQuery` on trie/witness/code/header kernels only · **every keccak, with monad-parametric interfaces including precompiles**. Constants acquisition (F20): inside the block kernel · **once by the caller at the guest, standalone and engine-driver boundaries** | the agreement prototype and the security theorem's scope establish whether a narrower oracle scope is sufficient; production evidence that F20 cannot preserve reference failure order or coherent oracle interpretation (DECISIONS §6) |
| D6 | Field arithmetic source | vendor the carry-preserving variant of CompPoly's `…Defs` · upstream the fix to CompPoly | width settled by measurement (carry-preserving CIOS, `p < R`: `Wide8`/`W12`); remaining: source, `sub`/`neg` and `W12` laws, observers, inversion |
| D7 | Curve coordinates | affine · projective internally | pairing/MSM measurement |
| D8 | Missing witness data | `Except WitnessError (Option α)` | — |
| D9 | `PreState` | record of operations + `Models` predicate | proof ergonomics in use |
| D10 | Full-state backend | include | — |
| D11 | Memory representation | `ByteArray` · zero-extending buffer | exercise 1 plus measurement |
| D12 | Precompile deliverables | (i) executable · (ii) mathematical correctness · (iii) cryptographic security | — (tracked and scheduled separately) |
| D13 | Call execution | recursive runner (EELS-shaped) · explicit continuation stack | the fuel-adequacy investigation (REVIEW §7 G2–G7). Because of the stepping/runner split, either choice keeps the opcode proofs |
| D14 | Failure semantics | the O1–O13 mapping, clarified as (O3: empty header list; O4: eager witness decoding; O11: checked runner versus public function; O12: reconciled with the discrepancy policy) | O12's resolution (DISC-001) |
| D15 | BLS12-381/KZG reference | ethereum/cryptography-specs · own | packaging and toolchain |
| D16 | State/commitment separation | `EthState` independent of `EthCommit`; two backends | replacement exercise R2 |
| D17 | Stepping/runner separation | `StepResult` with child requests; the runner alone recursive; enforced imports | replacement exercise R1 and the fuel-adequacy investigation |
| D18 | Implementation policy | final with respect to all required properties, with performance-appropriate data structures; justified exceptions recorded in the debt register; semantic incompleteness is never debt | per debt entry |
| D19 | Witness decoding strategy | **eager, as the reference does** (accepted as the semantics) · lazy (rejected: it would accept witnesses the reference rejects) | a caching layer may make it lazy *internally* only if it provably yields the same accept/reject result |
| D20 | State/commitment integration | `EthStateCommit` owns encodings, `mathStateRoot`, `ModelsRoot` and `ModelsCode`; the trie is generic over bytes | replacement exercise R2 |
| D21 | Additional trust assumptions; executable correspondence | banned: `native_decide`, `bv_decide`, `decide +native` (they add axioms); and, as design rules, `@[csimp]`, `implemented_by`, `extern`, `unsafe`, `partial`, `opaque` | enforced by `check-decls` (no exemption mechanism) |
| D22 | Revertible-state representation | persistent worst-case trees (`Std.TreeMap`) · HashMap + undo journal (semi-persistent) | a journal is only a later, measured representation replacement proved against the same contract with the semi-persistence discipline, never a `@[csimp]` |
| D23 | Observation sets and `created_accounts` | inside the snapshot · threaded linearly outside it | — (never reverted within a transaction) |
| D24 | Logs | array/list append · strict rope | cost check C3 |
| D25 | Contract style | laws listed per component · model-based (invariant + commuting equations; laws derived on the model; an abstraction relation for partial structures) | replacement exercises R1, R2, R4 |
| D26 | secp256k1 recovery for senders and EIP-7702 authorities | `RunnerEnv` parameter · direct `EthCurve` dependency of `EthVmRunner` | — (pure-Lean dependencies only) |
| D27 | `Log`/`BlockOutput` placement | `Log` in `EthVmCore`, `BlockOutput` in `EthBlock` | — (one owner per public type, `STFSpec/informal/contracts.toml`) |

**RLP total-domain options (Q47).** Retain total encoder signatures with a modular byte tag and unbounded minimal length digits; add a rejecting API; or select another total prefix completion. The owning disposition is in DECISIONS Q47. Revisit against a concrete consumer requiring behavior beyond `Encodable`, keeping mathematical completion separate from pinned-host and protocol correspondence.

**Two-item field diagnostic options (Q52).** Name the path-list and leaf-value-list failures separately; reuse unrelated existing diagnostics; or introduce a generic shape catch-all. The source checks the first field at `incremental_mpt.py:946` before compact decoding and the second at `:951` only on a successfully decoded leaf flag. DECISIONS Q52 owns the disposition. The distinct names retain that order, Q48 and existing O4 projection; whole decoding and witness/guest adapters remain open.

**Empty compact diagnostic options (Q48).** Name the raw first-byte failure `Malformed.compactEmpty`; reuse `rlp`; or reuse `pathEmpty`. The source raises `IndexError` at `incremental_mpt.py:878` before a decoded path/leaf flag exists, while the later extension check at `:959` rejects an empty decoded path. The owning disposition is DECISIONS Q48. All options preserve nonempty leniency and O4's output; the chosen name keeps the two phases inspectable.

**Nibble provider options (Q49).** Nat-indexed bounded packed generation or model construction; guarded/clipped packed copies or a later view representation; direct packed lexicographic scan or common-prefix scan followed by next digit/length comparison. Each option preserves the same List observers and ordinary equality bridge, without public storage or unchecked digit conversion. The owning disposition is DECISIONS Q49. Exact public model/index/size laws, lawful map clients and local current-source compiled correctness supply provider evidence; views and aggregate costs are revisited under D25/D18 and C1–C4.

**Reachable mathematical-root helper domain and supplied empty root options (Q50).**
An explicit proof-carrying reachable domain at arbitrary depth, a private reachable
helper with a zero wrapper, or an outside-domain completion. Empty roots use
caller-supplied F20 constants; local root execution and prior acquisition are
distinct. The owning disposition is DECISIONS Q50. Finite-map domain/descent laws
supply support, and recursive C7 uses the existing C6 operation with ordinary
public dispatch/extensionality laws and private every-node representative independence
(EthCommit §3). C8 supplies the total local root and ordinary reference/fused
equality with explicit lawful sequencing. Concrete pinned-root correspondence
retains prepared-map/value interpretation, complete assembled `Encodable`, coherent
F20 constants and host premises. Canonicality and whole-source refinement remain
separate obligations.


**Hash32 table-support options (Q51).** Truncated Nat hashing; the explicit complete 32-digit support model with ordinary streaming/reference equality; or another support representation behind the same model laws. The owning disposition is in DECISIONS Q51 and the provider contract in EthBase §3. EthBase's boundary excludes protocol/cryptographic hashing and permits the named nonprotocol support instance; every Keccak remains routed through KeccakQuery (D5). Revisit executable support costs against actual construction/allocation/adversarial-distribution evidence; functional lawful-hash proofs do not close §5.0 or C1–C4.

**Typed-trie default/validity and key options (Q53).** Arbitrary defaults with lawful
equality and a separate preparation proof preserve the source setter's all-value domain.
A fixed class default with a linking law narrows that domain; an explicit preparation-error
API broadens modeled failures and changes the interface scope. Generic `KeyBytes` requires
injective byte interpretation and comparison agreement with byte lexicographic order;
initial ByteArray specialization would avoid a generic adapter. The owning disposition
is DECISIONS Q53: keep the generic contract and begin with proof-carrying unsecured safe
preparation/root. Typed root passes the caller's F20 empty root directly to `mathRoot`
on the pure prepared map; equality to a separate monadic sequential reference requires
`LawfulMonad`, while local composition/empty equations need `Monad` alone. Secure traversal,
collision folding, source history and generic coupling remain separate open obligations.
EthCommit §3 supplies generic storage/safety, pure unsecured preparation and typed root composition; concrete consumer bridges remain open. This interface clarification changes no dependency boundary or implementation readiness.

**Existing Bytes ordering options (Q54).** A bounded packed scanner can stop at
the first differing byte; executable List conversion also satisfies byte semantics
but materializes both whole lists. An additional container or raw ByteArray order
widens the interface. Numeric and length-first orders disagree with unsigned byte
lexicographic order for varying lengths and significant leading zeros; actual RLP
ordinal keys also differ from numeric order. DECISIONS Q54 owns the disposition;
EthBase §3/§5/§7 owns the exact full-finite Bytes model and provider signatures.
Scanner details are private and replaceable behind ordinary public equations (D25).
The conditional EthCommit adapter and consumer integration are separate; correctness
proofs/local comparator measurements do not close actual map/preparation/root,
allocation/retention, replacement or C1–C4 obligations.

**Decoder cached-hash options (Q55).** The owning disposition is DECISIONS Q55;
EthCommit C13–C14/§5/§7.6 owns the exact unimplemented acquisition contract.
The selected target keeps `Enc` and queries each eligible complete raw occurrence
before parsing. A pure frontend with a complete-preimage answer context would
need coverage/coherence for every entered DB/inline occurrence; an upfront prepass
changes triggers, repeated effects, unused-entry acquisition and first failure.
An effectful demand interpreter has substantially the selected boundary; a total
concrete hash callback would bypass D5. A deferred digest representation would
change the length/cache invariant and child/root/update observers, and require
materialization plus source-order failure proofs; it is not selected.

The current-path/inline structural measure above is unchanged. The mathematical
baseline has no completed-node memo, so diamond siblings enter distinct raw
occurrences. B15 sharing needs path, cache, effects and first-error refinement;
a hash-only cycle-error table is not justified. Generic backend result ownership,
lifetime and F6 remain open. Coherent F20 constants are caller supplied; Q55 adds
no local constant acquisition, host policy, production cost exception or readiness.

**Logical Patricia RLP-domain options (Q56).** Total noncomputable logical folds
state exact widths and descendant/complete domains without executable extraction.
Executable width or certificate construction would require a separate implementation,
model equality and consumer/resource evidence. A domain-restricted or rejecting
interface would change the all-finite logical domain and API. DECISIONS Q56 owns
the disposition and precise interface. Revisit when a consumer requires executable
extraction/construction or public provider/domain laws change, retaining Q47's
separation of total completion from standard encodable scope.

**Lookup-record options (Q57).** An explicit record only on ModelsLookups matches
the existing public code observer and BlockState context while keeping full Models
binary at its concrete Id interpretation. Parameterizing all full predicates would
require a wider migration and an explicit concrete-coherence restriction; arbitrary
reserved hashes cannot silently imply concrete code authenticity. A fixed literal
binding bypasses generic caller interpretation; acquisition in EthState violates D16.
Universal record quantification overconstrains one provider's reserved-hash answers;
existential hiding does not supply the tracker equation at its actual record. A new
PreState field changes D9, while omitting code agreement loses R8's observer contract.
DECISIONS Q57 owns the disposition. Full record/root/decoder coherence and generic
D5/X7 coupling cannot follow from equality of the emptyCodeHash field alone.

**Structural diff options (Q58).** Separate two-clause structural premises admit
every finite raw diff with arbitrary metadata/code/account fields and support a
conditional output-WF law; raw deletion/storage helpers alone supply no such premises.
Weaker output-only conditions would not preserve the selected deletion-to-clear and
raw-address clauses. Full static WF additionally needs enumeration of raw writes,
with tombstones/empty patches/zeros included. Its optional slot-order map could require
explicit lists at changed addresses, exact matched outer domains, defaulted changed
lists or global defaulted membership: those differ on missing empty-patch lists and
extra entries. None of those completions follows from the structural contract. First-live
write order, reachable extraction, AccountWritesLookedUp and F7 need separate history
and operational contracts. DECISIONS Q58 owns the bounded disposition; EthState §7.4
owns its law targets, without an additional account-reformulation law.

**Pure lookup selected-access options (Q59).** DECISIONS Q59 owns the disposition;
EthCommit C20/§§5/7 owns its supplied diagnostic and §7.0.5 constructor equations.
Candidate A retains the total bare `Ref → Nibbles → Except TrieError (Option ByteArray)`
API and names only a reached nonterminal out-of-range selected slot with
`Malformed.branchIndex (index : Nat) (arity : Nat)`. Candidate B changes that API
to take a key-dependent selected-access domain proof or certified input: extensions
require child coverage only on a prefix match, terminal branches require no bound,
and nonterminal branches require the actual selected bound and child's coverage.
Merely adding a theorem premise to an unchanged total bare API leaves its outside-domain
behavior unselected. Eager size 16/WF admission, out-of-range-slot absence and off-path scans
change bare behavior and are not variants of the same contract.

Python's `witness_state.py:53–100` list access has a defined IndexError; the choice
is the typed diagnostic/domain adaptation. Source value/stub correspondence is limited
to valid selected accesses and actual Hash32-to-64-nibble/source-class/host premises.
Proper-child Node-size descent handles matched empty extensions independently of key
consumption. Private cursor/reference/child-size support and ordinary all-bare-input
fast/reference equality are supplied under D18/D25 (EthCommit §3). No compiled feasibility,
speed, guest reachability/output, host resource or readiness result follows; decoder,
mutation, cache, root and security obligations retain their owners.

## 12. Not yet decided

- **O12** host-resource interpretation (DISC-001, DISC-006).
- Open obligations from the interface prototype (DECISIONS §3): **F6** storage-trie memo ownership, lifetime and triggers; **F7** clear iteration order in the witness root; **F11** how `ChildSettled` is produced; **O2** request-root unreachability proof.
- The fuel budget policy Φ + 1 (B11; the fuel-adequacy investigation, [REVIEW §7](REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks) G2–G7).
- **Compilation (future work).** A compiler from the spec to a verified assembly shape comes only after the guest assembly (evm-asm, or Pancake with autoresearch-style optimisation) has been fine-tuned and verified; veir or Lean's IR become relevant then. Nothing in the current phase depends on it. Keep abstract types behind interfaces so that implementations can refine representations locally.

- Exact module file names (they follow EELS).
- The fuzzing harness design (bug-finding only).
- Build flags (`precompileModules`, LTO).
- The diagnostic event schema (§7).
