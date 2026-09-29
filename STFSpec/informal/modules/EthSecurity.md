# `EthSecurity`: witness soundness, header-chain and request binding, and the Keccak ROM bound

*Status: informal specification, draft. Date: 2026-09-29. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F2, F3, F4, F15, F18 and §9 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: P4, D5, D8, D9, D12, D14, D16, D19, D20 · questions: B9 (Q11), B10 (Q12), Q13, Q14, Q44.*

`EthSecurity` is the library of the **security package** (`STFSpecSecurity/lakefile.toml`, root `STFSpecSecurity`; it requires the core and the Mathlib bridge package; Mathlib v4.34.0; VCV-io to be added). It defines no executable behaviour. **[V]** marks a claim checked against source (pinned EELS, or VCV-io at `f5119c6`, 2026-09-26); **[I]** marks an inference or proposal.

## 1. Purpose

`EthSecurity` states and proves what a successful guest run establishes, relative to the authenticated context of `STFSpec/informal/CONTRACT.md` §7. It has four results: (1) a **deterministic trie agreement** theorem in the collision-reporting form of Kestrel's ACL2 MPT book, (2) a **block-level agreement** theorem: a successful stateless run implies the same result from stateful execution over every state consistent with the parent state root, unless a keccak collision is computable, (3) **header-chain binding** and, separately, **request-commitment binding** through SSZ/SHA-256, and (4) a **random-oracle bound** obtained from the deterministic theorems through VCV-io's simulation bridge lemma and `romCRAdvantage_le_birthday`. It sits outside the core layer diagram (ARCHITECTURE §3, "Outside the core package") and consumes the [S]-tagged obligations of `EthCommit`, `EthStateCommit`, `EthStateWitness`, `EthBlock` and `EthStateless`.

## 2. Requirements

**R1. Scope (CONTRACT §7).** Every theorem must say which of the three obligations it covers:
- *witness/state agreement*: relative to the supplied parent header;
- *request-commitment binding*: identifying the request from the output root; SHA-256 and SSZ laws only;
- *accepted-chain validity*: **not** proved here. The verifier supplies the external anchors: that the `NewPayloadRequest` with the output root is the one it intends to validate and that its parent is on the accepted chain; that `chain_id` and schema are the expected ones; and that the fork is active at the payload timestamp (the reference omits this check, `stateless.py:275–277`).

No theorem may assume collision resistance for **totality**: `runStatelessGuest` must be proved total on all bytes and all finite witness DBs unconditionally (`EthStateless` L-total, L-internal). Collision hypotheses appear only in agreement and binding statements, and only as an explicit disjunct or a probability bound.

**R2. Deterministic form first.** Each agreement or binding theorem must be stated for an **arbitrary** hash function `h : ByteArray → Digest` (the core kernels are generic over `KeccakQuery`, D5) and must conclude "agreement **or** a collision of `h`, returned by a *computable* extractor over an explicit, finite preimage set". This is the ACL2 `:collision` convention ("Since we cannot ignore the mathematical possibility of hash collisions, [these functions] all return an error flag that, when equal to `:collision`, indicates that a collision in the constructed database took place", `books/kestrel/ethereum/mmp-trees.lisp`, via ARCHITECTURE §5.4). The deterministic theorem is the primary guarantee: for a fixed, unkeyed hash such as keccak-256 it is the meaningful standard-model statement ("any disagreement exhibits an explicit collision"). The ROM bound (R6) is an idealized quantitative complement, never a substitute.

**R3. The preimage set.** The extractor must include σ’s code preimages as well as witness code preimages, node encodings and secure-key preimages. It may search only a named finite set of byte strings, and the proof report must list it (CONTRACT §7, last paragraph). For a stateless input `x` and a state `σ` it is:
- the witness node DB entries `x.witness.state` (hashed by `build_node_db`, `witness_state.py:37–42`) and code DB entries `x.witness.codes` (`:45–50`);
- the raw witness headers `x.witness.headers` (hashed by `validate_headers`, `stateless.py:254–256`) and `rlp(parent_header)` (hashed by `validate_header`, `fork.py:501`);
- the payload header RLP hashed by the block-hash check (`is_valid_block_hash`), the key/value encodings of the transactions and withdrawals tries (payload side) and of the transactions, receipts and withdrawals tries (block side), the raw BAL bytes and the built BAL's RLP;
- transaction encodings and signing-hash preimages, the recovered public keys hashed into sender and authority addresses, and ECRECOVER's recovered keys;
- the KECCAK256 opcode inputs, CREATE/CREATE2 address preimages, newly deposited code and installed delegation code (their code hashes), and bloom entries (log addresses and topics);
- the `HashConsts` preimages (`b""`, `rlp(b"")`, `rlp([])` and the EIP-7708 transfer-event signature), queried once per block;
- σ’s stored code byte strings and authentic code changes in σ.apply d;
- the canonical node encodings of every trie of `σ` (account trie and each storage trie) and of `σ.apply d`, as queried by `mathStateRoot`;
- secure-trie keys `address` and `slot` whose `keccak` paths are walked (`merkle_patricia_trie.py`, secured tries);
- node encodings created by the witness backend's incremental root update;
- for header binding, the RLP encodings of the accepted chain's last 256 headers.

**R4. Shared-oracle scope (D5).** **Broad scope, monad-parametric** (D5/B10, 2026-09-28; interfaces settled by review of a compiled prototype of the interfaces, 2026-09-29, DECISIONS §3): **every** keccak call goes through `KeccakQuery`, so all uses share one `h`; there are no concretely computed exceptions. Every core function that hashes, or reads a pre-state, is generic in `{m} [Monad m] [KeccakQuery m]`, and the executable spec is its `m := Id` instance (concrete keccak256). The uses are:
- trie node hashing and secure-key hashing (`EthCommit`); node-DB and code-DB keying and account code-hash agreement (`EthStateWitness`, `EthStateCommit`);
- header-chain hashing (`EthStateless.validateHeaders`), the parent-hash check in `validate_header` (`EthBlock`), the payload block-hash check `is_valid_block_hash` and the payload transactions/withdrawals roots (`EthStateless`);
- transaction and signing hashes, sender and authority address derivation, transactions/receipts/withdrawals roots, the bloom and the BAL hash (`EthBlock`);
- the KECCAK256 opcode, CREATE/CREATE2 addresses, newly installed code hashes on code-deposit and delegation paths (`EthVmInstructions`, `EthVmRunner`), and ECRECOVER (`EthPrecompiles`, as `PrecompileFn m`);
- the keccak-derived constants, a `HashConsts` record (`emptyCodeHash`, `emptyTrieRoot`, `emptyOmmerHash`, `transferTopic`; `EthBase`) queried once per block by `HashConsts.query` (`EthHash`).

A narrower scope must be justified by the agreement prototype. Closure of the agreement argument over this scope is not yet established, and the oracle coupling for `Models` at generic `m` is open (`Models` is stated at `PreState Id`).

**R5. Block-level agreement is backend-relative.** The stateful side is any `PreState` that models `σ` and makes progress (every operation succeeds on well-formed diffs), instantiated by `EthStateFull`. The theorem must not assume the witness is *minimal*; it must allow *any* witness the guest accepts.

**R6. ROM bound.** The ROM statement must: model keccak as `OracleSpec` `ByteArray →ₒ Digest` with `Digest := Vector UInt8 32` (VCV-io requires `SampleableType` on the range and `DecidableEq` on the domain; [V] at `f5119c6`); count the adversary's queries plus the guest's and the stateful run's queries on its output (both bounded by explicit functions of input size and `|σ|`); and derive the bound only through `romCRAdvantage_le_birthday` (`VCVio/CryptoFoundations/HardnessAssumptions/CollisionResistance.lean:269` [V]):

```
romCRAdvantage A ≤ ((t + 2) * (t + 1) : ℕ) / (2 * Fintype.card Y)     -- for a t-query ROM-CR adversary
```

and the bridge `probEvent_eq_one_simulateQ_randomOracle_run_iff` (`VCVio/OracleComp/QueryTracking/RandomOracle/Simulation.lean:475` [V]; `BoundedROMCRAdversary` at `CollisionResistance.lean:184`), which turns a deterministic "for every answer function" statement into a probability-one statement under the lazily sampled oracle.

**R7. Request binding is separate.** `new_payload_request_root` is SSZ `hash_tree_root` over SHA-256 (`stateless.py:220–226`), with progressive containers and lists (`utils/ssz.py:250–251`). Binding is proved from SSZ merkleization laws (`EthCodec`) and a SHA-256 collision extractor, independent of keccak. No keccak ROM statement may be used to justify it.

**R8. Precompiles.** Cryptographic security of precompiles (ECDSA recovery, P-256, BN254/BLS12-381 pairings, KZG) is D12(iii) and out of this library's first scope. The agreement theorems need none of it, since both sides compute the same precompile functions (ECRECOVER's keccak goes through the shared oracle, R4). The public-key hint needs none either: the reference accepts a hint only if it equals the recovered key (`transactions.py:916–934`), a deterministic equality (`EthBlock` law).

## 3. EELS source map

`EthSecurity` specifies no EELS behaviour and claims no inventory items. It refers to, and depends on the specifications of, items claimed elsewhere: `forks/amsterdam/stateless.py` and `forks/amsterdam/stateless_guest.py` (`EthStateless`), `forks/amsterdam/witness_state.py` and `forks/amsterdam/incremental_mpt.py` (`EthStateWitness`), `merkle_patricia_trie.py` and `state_mpt.py` (`EthCommit`/`EthStateCommit`), `forks/amsterdam/fork.py` `validate_header`/`execute_block` (`EthBlock`), `utils/ssz.py` (`EthCodec`).

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| none | — | — | proof library |

**External semantics.** None executed. The theorems idealize the external `hashlib`/pycryptodome keccak and SHA-256 (`crypto/hash.py`) as arbitrary functions (deterministic form) or random oracles (ROM form); `EthHash` proves its keccak/SHA-256 equal to the FIPS 202/180-4 definitions separately. The `eth-remerkleable` merkleization is idealized through `EthCodec`'s SSZ spec.

## 4. Tests

- **EEST fixture areas:** none decide security. `eip8025_optional_proofs/witness_validation_state`, `witness_validation_codes`, `witness_validation_headers`, `witness_public_keys` and `witness_validation_chain_id` are the negative cases whose rejection the theorems explain; they are used as **sanity instances**: each theorem's hypotheses must be satisfiable on at least one corpus record (non-vacuity), checked by evaluating the executable parts.
- **EELS unit tests:** none.
- **`core` cases:** none (this library is not in the core). In `STFSpecSecurity/` add `example`s that instantiate each theorem on a two-leaf trie and a one-header chain, and a canary `example` instantiating the VCV-io bridge lemma for `keccakSpec`, as VCV-io's own `VCVioTest/Computability.lean` does for its ROM runtime [V].
- **Property checks:** the collision extractors are executable; test that on every corpus record they return `none` when fed the record's own preimage set (no accidental collision), and that on synthetic inputs built with a deliberately colliding toy hash they return the collision.
- **Declaration check:** release theorems must use only `propext`, `Quot.sound`, `Classical.choice`, with no `sorry` through dependencies (`CONTRIBUTING.md` §4); conditional theorems list each hypothesis and the bridge that discharges it.

## 5. Interface

Namespace `STFSpecSecurity`; all public. Names of core items are those of their owning specs; `h` ranges over `ByteArray → Digest`.

```lean
abbrev Digest := Vector UInt8 32
structure Collision (h : ByteArray → Digest) where
  x : ByteArray; y : ByteArray; ne : x ≠ y; eq : h x = h y
def CollisionIn (h) (S : Finset ByteArray) : Prop := ∃ c : Collision h, c.x ∈ S ∧ c.y ∈ S

-- VCV-io bridge (D5): the core class, instantiated from VCV-io's query class
def keccakSpec : OracleSpec ByteArray := ByteArray →ₒ Digest
instance [HasQuery keccakSpec m] : STFSpec.Hash.KeccakQuery m
-- a core kernel in the D5 scope: generic in the oracle monad, as every hashing signature is
abbrev KeccakKernel (α) := ∀ {m : Type → Type} [Monad m] [STFSpec.Hash.KeccakQuery m], m α
theorem keccakQuery_ofFn (f) (k : KeccakKernel α) :
  simulateQ (QueryImpl.ofFn f) (k.run (m := OracleComp keccakSpec)) = k.run (m := Id) (h := f)

-- Proposed hash-relative theorem templates, not compiled concrete APIs.
-- Notation: for a kernel k : KeccakKernel α, `k h` is k run with every query answered by h
-- (simulateQ (QueryImpl.ofFn h)); at h = keccak256 it is the executable m := Id instance.
-- `PreState` below means the core's `PreState m` at that run; Models/Progress are stated at
-- `PreState Id`, and stating them for arbitrary h is the open oracle coupling (D5).
-- CodeAuthenticQ requires D5 closure; Id specialisations must match COMPOSITION and the
-- module §5 signatures.
-- (1) deterministic trie agreement
def trieQueries (h) (db : NodeDB) (M : Std.TreeMap ByteArray ByteArray) : Finset ByteArray
def extractTrieCollision (h) (db : NodeDB) (M) : Option (Collision h)             -- computable
theorem decodeRoot_represents (h db r t) (M) (ha : NodeDB.Authentic h db) :
  decodeRoot h db r = .ok t → mathRoot h M = r →
  represents t M ∨ ∃ c, extractTrieCollision h db M = some c
theorem witness_lookup_agreement (h db r k v M) (ha : NodeDB.Authentic h db) :
  lookupWitness h db r k = .ok v → mathRoot h M = r →
  M.get? k = v ∨ ∃ c, extractTrieCollision h db M = some c
theorem witness_root_update_agreement (h db r ops r' M) (ha : NodeDB.Authentic h db) :
  rootAfter h db r ops = .ok r' → mathRoot h M = r →
  mathRoot h (M.applyOps ops) = r' ∨ ∃ c, extractTrieCollision h db M = some c

-- state level (from EthStateCommit/EthStateWitness contracts)
-- witnessPreState is built by authenticated DB builders with constants from the same h;
-- its hash-relative WitnessBackend.WF must be established, not inferred from root equality.
def stateQueries (h) (x : StatelessInput) (σ : MathState) : Finset ByteArray      -- R3
def extractStateCollision (h) (x) (σ) : Option (Collision h)
theorem witness_models (h x σ) (hwf : MathState.WF σ) (hauth : CodeAuthenticQ h σ) (hroot : mathStateRoot h σ = (parentOf x).stateRoot) :
  ModelsUpToCollision (witnessPreState h x) σ (extractStateCollision h x σ)

-- (2) block-level agreement
theorem stateless_implies_stateful (h) (x : StatelessInput) (σ : MathState)
    (ps : PreState) (hm : Models ps σ) (hp : Progress ps)
    (hv : classify h (schemaIdBytes ++ encode x) = .ok (.valid root cid))
    (hroot : mathStateRoot h σ = (parentOf x).stateRoot) :
    (∃ d blk, executeNewPayloadRequest h x.newPayloadRequest ps (ctxOf x) none = .ok (.ok (d, blk))
        ∧ executeNewPayloadRequest h x.newPayloadRequest (witnessPreState h x) (ctxOf x)
            (some x.publicKeys) = .ok (.ok (d, blk))
        ∧ mathStateRoot h (σ.apply d) = x.newPayloadRequest.executionPayload.stateRoot)
    ∨ ∃ c, extractStateCollision h x σ = some c
corollary stateless_implies_full (h x σ) (hwf) (hauth) (hcomplete) : …
  -- use the hash-relative full backend with explicit WF/authenticity/progress;
  -- the concrete specialisation is FullState.ofMath σ hwf hauth

-- (3a) header-chain binding
def headerQueries (hs : Array ByteArray) (chain : List Header) : Finset ByteArray
theorem header_chain_binding (h) (hs : Array ByteArray) (chain : List Header)
    (hok : validateHeaders h hs = .ok (ds, bh)) (hne : 0 < hs.size)
    (hpar : h (rlp ds.back) = payloadParentHash)
    (hanchor : AcceptedTip chain payloadParentHash) :                 -- external anchor
    (ds.toList = chain.lastN hs.size ∧ bh.toList = (chain.lastN hs.size).map (h ∘ rlp))
    ∨ ∃ c, extractHeaderCollision h hs chain = some c
theorem blockhash_agreement … -- BLOCKHASH reads in the witness context equal the accepted chain's, or a collision

-- (3b) request-commitment binding (SHA-256; separate)
def extractSszCollision (sha : ByteArray → Digest) (r₁ r₂ : NewPayloadRequest) : Option (Collision sha)
theorem request_root_binding (sha) (r₁ r₂ : NewPayloadRequest) :
    hashTreeRoot sha r₁ = hashTreeRoot sha r₂ → r₁ = r₂ ∨ ∃ c, extractSszCollision sha r₁ r₂ = some c

-- (4) ROM bound
structure DisagreementAdversary (t : ℕ) where
  run : OracleComp (unifSpec + keccakSpec) (StatelessInput × MathState)
  bound : IsQueryBound run (budget for keccak queries := t)          -- VCV-io QueryBound/Basic.lean:46; exact form open
def disagreementExperiment (A : DisagreementAdversary t) : ProbComp Bool   -- R6: sample, run A, run both sides, test
def queryBudget (x : StatelessInput) (σ : MathState) : ℕ                 -- guest + stateful + extractor queries
theorem rom_disagreement_bound (A : DisagreementAdversary t) (Q : ℕ)
    (hQ : ∀ x σ, (x, σ) ∈ support A.run → queryBudget x σ ≤ Q) :
    𝒟[disagreementExperiment A] {true} ≤ (((t + Q + 2) * (t + Q + 1) : ℕ) : ℝ≥0∞) / (2 * 2^256)
```

`ModelsUpToCollision ps σ c` is `EthStateWitness`'s collision-indexed form of `Models` (each *successful* operation agrees with `σ`, or `c = some _`); `Progress` is `EthStateFull`'s. `AcceptedTip` is a hypothesis-only predicate naming the external anchor.

## 6. Data structures

| Object | Representation | Model | Invariant | Persistence | Complexity |
|---|---|---|---|---|---|
| `Collision h` | structure with proofs | a pair `(x, y)` | `x ≠ y ∧ h x = h y` | value | — |
| preimage sets | `Finset ByteArray` (noncomputable use only in statements) | finite set | contains every queried input (R3) | — | extractors run in O(Σ sizes · log) with sorted buckets [I] |
| extractors | computable functions over the core's decoded data | partial function to collisions | returns only genuine collisions (soundness lemma) | value | polynomial in input + `\|σ\|` |
| oracle spec | VCV-io `OracleSpec`, range `Vector UInt8 32` | random function | `SampleableType`, `DecidableEq` instances | — | — |
| experiments | `OracleComp`/`ProbComp` values | distributions (VCV-io `evalDist` is a Mathlib `Measure`) | query bounds | — | noncomputable semantics |

Every extractor comes with a soundness lemma (`extract… = some c → c.x ∈ S ∧ c.y ∈ S`), so the deterministic theorems imply `CollisionIn h S`.

## 7. Contract and laws

All [S]; each lists the core obligations it consumes (the ids are the owning modules' laws).

1. **Trie agreement** (`decodeRoot_represents`, `witness_lookup_agreement`, `witness_root_update_agreement`). Consumes: `EthCommit` [C] canonical-form invariant and "canonical tries are equal iff they represent the same map" (Nipkow et al. Ex. 12.1), `represents` simulation laws for lookup/update/delete, NodeDB.Authentic and the decoded-node hash law, RLP prefix-freeness/injectivity (`EthCodec`), eager decoding (D19) so that the decoded trie covers everything reachable. **Strategy:** induction on the decoded trie; at each hashed reference compare the witness node with `M`'s canonical subtrie node: equal encodings → recurse; different encodings with equal hash → collision; RLP injectivity closes the "same encoding, different node" case. Incremental root agreement follows Cassez (FM 2021) for "incremental = from-scratch" plus the same case split.
2. **State models up to collision** (`witness_models`). Consumes `EthStateCommit` account/storage leaf encodings and `ModelsRoot`/`ModelsCode`, `EthStateWitness` backend construction, including WitnessBackend.WF authentication/coherence. Code: a code-DB hit `c'` for `code_hash` with `σ` holding `c ≠ c'` and `keccak c = code_hash` is a collision.
3. **Block agreement** (`stateless_implies_stateful`). Consumes: `EthStateless` L-backend-generic (the payload path touches `pre` only through `PreState` operations), `EthBlock` L-hint-equivalence (hint accepted ⇒ same result as recovery), and a **Models-parametricity** law for `executeBlock`: if `ps₁`, `ps₂` both model `σ` and every operation `ps₁` answers during the run succeeds, and `ps₂` has progress, then the runs agree. **Strategy:** a simulation between the two runs in which the only differing component is the backend, with equal answers at every query (from `Models`), then `ModelsRoot` for the post-state root. The proof size of the parametricity law is the dominant unknown (§10).
4. **Header binding** (`header_chain_binding`, `blockhash_agreement`). Consumes `EthStateless` L-headers, RLP injectivity and re-encoding identity (`rlp (decode b) = b`), `EthBlock` `validate_header` parent-hash check. **Strategy:** backward induction along the chain from the anchored parent hash.
5. **Request binding** (`request_root_binding`). Consumes `EthCodec` SSZ laws: injectivity of serialization-to-chunks for each type, merkleization with length mix-in and progressive-container active-field mix-in, and the SHA-256 pair-hash structure. **Strategy:** the standard Merkle binding argument (VCV-io `getPutativeRootWithHash_binding_collision` pattern, `MerkleTree/Inductive/Binding.lean:192` [V]) generalised to SSZ's shapes.
6. **ROM bound** (`rom_disagreement_bound`). From (3) and (4) for every `h`, the bridge lemma gives: with probability 1 over the lazily sampled oracle, a win implies the final cache contains a collision. Build a `BoundedROMCRAdversary` that runs `A`, then both sides and the extractor, with `t + Q` queries; apply `romCRAdvantage_le_birthday` with `Fintype.card Digest = 2^256`. With `t + Q = 2^64` the bound is about `2^-129` [I: arithmetic only].

**Non-vacuity obligations.** For each conditional theorem, exhibit an instance satisfying all hypotheses (a corpus record plus its reconstructed pre-state), so that no theorem is trivially true.

### Informal correctness argument

**Claim.** Subject to authentic/available full state, root agreement, the resolved oracle model and an external chain anchor, successful stateless verification implies the corresponding full-state result or an extractable hash collision; a ROM bound requires a separate complete query budget.

**Premises.** Models plus progress, CodeAuthentic/CodeComplete where used, successful witness operations, reachable read-before-write, backend trace refinement, header/schema binding and the four runner guarantees. The keccak-derived constants are `HashConsts`, answered by the same oracle (F2), and newly produced code hashes are oracle answers (D5).

**Argument.** Compare authenticated witness nodes with the mathematical trie: equal preimages permit descent, whereas unequal preimages with equal hashes supply a genuine collision. Include secure keys and both code stores in this comparison. Simulate the successful execution trace query by query; full-state progress ensures it can follow the witness's successful answers. Preserve frame observations, diffs and error order using the component contracts, then apply the root-update law. Verified sender hints give the same sender as recovery. Header binding descends from the externally accepted tip; request binding uses the separate SHA-256/schema argument. Finally, run the deterministic extractor inside the oracle experiment and count adversary, guest, full-state and extractor queries before applying a collision bound.

**Open obligations.** Define and prove the simulation, extractor and budgets; prove that `HashConsts` and newly produced code hashes are authentic relative to `h`, fold secure-key collisions, and state `Models` at generic `m` (the open oracle coupling). Always-error backends must not make the theorem vacuous. No numeric security conclusion follows until the VCV-io theorem, oracle coupling and all domains are fixed.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthStateless`, `EthStateFull`, `EthPairingMathlib`. Direct repository imports; external Mathlib and the proposed VCV-io dependency are discussed below.
- **Used by:** release reports and consumers who cite soundness (evm-asm, pancaketh, zkVM teams).
- **Seams consumed:** the `KeccakQuery` class and its `ExceptT`/`StateT` lifts (`EthHash`, D5), `HashConsts` (`EthBase`), and every [S]-tagged obligation of `EthCommit`, `EthStateCommit`, `EthStateWitness`, `EthBlock`, `EthStateless`, `EthCodec`.
- **Cross-module invariants relied on:** kernels in the D5 scope are generic over `KeccakQuery` and instantiated with `m := Id`, concrete keccak, in the executable spec; the executable result equals `simulateQ (QueryImpl.ofFn keccak256)` of the generic kernel (`keccakQuery_ofFn`, a proof obligation of the bridge instance). **Guaranteed:** nothing to the core; theorems only.

## 9. Open decisions

- **D5** (provisional: broad scope, monad-parametric; B10): every keccak goes through one oracle (R4). This library supplies the evidence D5 names: the coupling proof, including `Models` at generic `m` (open), and the agreement prototype that alone could justify a narrower scope.
- **D12** (precompile deliverables, accepted): cryptographic security (iii) is tracked separately; the agreement theorems do not depend on it.
- **D9**, **D16**, **D20** (PreState shape, state/commitment separation, integration): the block agreement theorem is stated through `Models` and `Progress` exactly because of them.
- **D19** (eager decoding): used by trie agreement (every reachable node is decoded and checked).
- **D8** (missing witness data as `Except`): agreement is stated for successful runs only.
- **P4** (package layout): VCV-io joins the security package `STFSpecSecurity/`, and only it.
- **D14**: `classify`'s `.valid` constructor is the hypothesis of block agreement.
- `PreState` as a query interface: resolved, DECISIONS B9 (Q11): keep the accepted record; add a proof-level query trace or adapter.
- Completeness (liveness) theorem: DECISIONS Q13 (later; needs a specified witness generator).
- VCV-io pin and API: DECISIONS Q14 (pin a full commit when work starts; `Measure`-based API).

## 10. Gaps

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **VCV-io has no MPT, RLP or trie support** [V: a grep over VCV-io main for patricia/trie/MPT/rlp/verkle finds nothing]. Its `HashForest` (variadic mixed nodes, `providedDigest`) covers node shapes but has no binding, uniqueness or extractability theorems yet, does not model RLP's "embed if shorter than 32 bytes, else hash" references, and does not walk keyed paths. The MPT layer (node datatype, RLP injectivity, get/absence/update against a witness DB, a binding theorem) is new work, estimated at 2–4k lines [I].
- **VCV-io is not a dependency yet**, tracks `main` with high churn (about 200 commits in a month), has deprecated `evalSPMF`/`probOutput`/`probEvent` (since 2026-09-13) in favour of `Measure` semantics, and changed advantage types to `ℝ≥0∞`. Statements here use `𝒟[·]`; lemma names may move. Compiling a VCV-io executable pulls in the whole Mathlib C closure (145 MB binary in a test build); irrelevant for proofs, but it rules out using VCV-io in the core.
- **Oracle domain.** `randomOracle` needs `DecidableEq` on the domain; the domain is `ByteArray` (unbounded length). Lean core provides `DecidableEq ByteArray` (`Init/Data/ByteArray/Basic.lean:36` at v4.34.0 [V]); whether VCV-io's `QueryCache` machinery and `BoundedROMCRAdversary` (which also needs `Inhabited X`) work smoothly with `ByteArray` keys is unchecked [I].
- **Models-parametricity of `executeBlock`** has no proof strategy cheaper than a whole-STF simulation; the proof-level query trace or adapter of DECISIONS B9 is the intended route. This is the largest unknown and blocks theorem (2).
- **`KeccakQuery` bridge obligation** (`keccakQuery_ofFn`) is unproved and depends on how `EthHash` defines the class; the executable path must be *definitionally* or provably the `Id` instance.
- **Preimage-set completeness.** R3 is argued from the pinned source, not proved: every keccak call inside the D5 kernels must be shown to add its input to the set. Incremental-root node encodings are the easiest to miss.
- **Witness DB duplicates and collisions inside the DB.** `build_node_db` silently keeps the last of two entries with the same hash (`witness_state.py:40–41`); that case must yield a collision from the extractor, not an arbitrary choice. Stated but unproved.
- **O12 interaction.** If DISC-001 leads to a depth or size limit in witness decoding, the trie agreement theorem is unaffected (it covers successful runs), but totality statements must be rechecked.
- **Security assumptions not yet stated:** SHA-256 collision resistance for request binding (standard-model form via the extractor; no ROM version proposed); the soundness of `EthHash`'s keccak-256 and SHA-256 against FIPS 202/180-4 (a [C] obligation owned by `EthHash`, needed to connect "keccak" in the theorems to the Ethereum function); ECDSA/KZG/pairing security (D12(iii)); the zkVM's own soundness and the correctness of the compiled guest (out of scope; the consumers' refinement proofs).
- **Accepted-chain validity is external and unformalized.** There is no Lean predicate for "the verifier's accepted chain" beyond the hypothesis `AcceptedTip`; fork activation and chain id are likewise hypotheses.
- **Quantitative query budgets.** `queryBudget x σ` must be computed from the executable spec (nodes decoded, roots recomputed, headers hashed); no bound function exists yet, and the stateful side's `mathStateRoot` makes it linear in `|σ|`.
- **Completeness/liveness** (DECISIONS Q13) is not stated: nothing guarantees that an honest prover's witness is accepted.
- **Consumers' composition.** How evm-asm's or pancaketh's refinement theorem composes with these statements (their toolchains are v4.33.x; a Mathlib version conflict with evm-asm) is unresolved.
