# Guest protocol contract

*Status: draft guest contract. Date: 2026-10-01.*

Pinned by [`reference.toml`](../../reference.toml): execution-specs `tests-zkevm@v21.0.0`, commit `e1a316a0`, branch `projects/zkevm-releases`. Source observations below refer to that commit; line references are under `src/ethereum/forks/amsterdam/`. **Status:** draft specification contract. D14 is accepted (structure and guidelines). The row set is complete only once the failure ledger (maintained outside this repository; X1) closes. The public signature is the target, not an implemented function. No O12 deviation has been accepted or reported upstream by this repository.

## 1. Signature

```
runStatelessGuest : ByteArray → ByteArray        -- stateless_guest.py: run_stateless_guest
```

The function is total and deterministic. It reads no environment.

## 2. Input encoding

```
input = schema_id (2 bytes, big-endian) ++ SSZ(StatelessInput)
schema_id = (ProtocolFork.Amsterdam = 0x15) << 8 | revision 0x01 = 0x1501
```

`StatelessInput` (`stateless.py`) is an SSZ container with these fields:

| field | SSZ type | limits |
|---|---|---|
| `new_payload_request` | `NewPayloadRequest` container | — |
| `witness` | `ExecutionWitness` {`state`: progressive list of `byte_list(2^10)` (trie-node preimages); `codes`: progressive list of `byte_list(2^16)`; `headers`: `ssz_list(256)` of `byte_list(2^10)` (RLP headers)} | `MAX_WITNESS_NODE = 2^10`, `MAX_CODE = 2^16`, `MAX_HEADER = 2^10`, `MAX_WITNESS_HEADERS = 256` |
| `chain_id` | `uint64` | — |
| `public_keys` | progressive list of `byte_vector(65)` (uncompressed sender public keys, in payload order) | **new in this release** (absent at `projects/zkevm` @94ec9d66) |

`public_keys` is an untrusted hint. The reference verifies each key by full recovery (`transactions.py:916–934`: it recomputes `recover_transaction_public_key` and compares) and checks the count (`fork.py:312`). An implementation may use a cheaper check that is equivalent on every input.

## 3. Output encoding

`SSZ(StatelessValidationResult)`, 43 bytes. SSZ integers are little-endian.

| field | type | bytes |
|---|---|---|
| `new_payload_request_root` | `Hash32` = SSZ `hash_tree_root(new_payload_request)` | 32 |
| `successful_validation` | `boolean` | 1 |
| `chain_id` | `uint64` | 8 |
| `schema_id` | `uint16` | 2 |

## 4. Outcome table

EELS has two nested catch-all handlers:

- The **outer** one is in `run_stateless_guest`. It surrounds decoding and the whole of `verify_stateless_new_payload`.
- The **inner** one is in `verify_stateless_new_payload`. It surrounds everything *after* `compute_new_payload_request_root`.

In the spec, each row below becomes one or more explicit constructors; there is no catch-all. Classification follows the **first reference handler that consumes the exception** (D14). A local handler can consume a failure before either catch-all sees it: for example, `is_valid_versioned_hashes` (`execution_engine/new_payload.py:60–68`) turns every payload-transaction decode failure into `False` (O6).

| # | Situation | Raised where (reference) | Output |
|---|---|---|---|
| O1 | input shorter than 2 bytes; schema id ≠ `0x1501`; SSZ decoding fails (malformed offsets, limits exceeded, trailing bytes) | `deserialize_stateless_input` (outer handler) | **zero sentinel**: root = 0³², validation = false, chain_id = 0, schema_id = 0 (`_default_failed_stateless_output`) |
| O2 | failure while computing the request root | `compute_new_payload_request_root` is *outside* the inner handler | **zero sentinel**. Conjectured unreachable on decoded values: the spec is to prove this (EthStateless L-root) and adds a constructor only if the proof fails (DECISIONS §3, O2) |
| O3 | witness headers invalid: more than 256, RLP decode fails (tries Amsterdam, then the previous-fork header), or not contiguous by `parent_hash` | `validate_headers` (inner) | `(root, false, chain_id, 0x1501)` |
| O3a | **empty witness-header list.** SSZ permits it, and `validate_headers` accepts it (its length check is `≤ 256`, and the contiguity loop is empty). The reference then fails at `decoded_headers[-1]` (`stateless.py:281`, an `IndexError`) inside the inner handler. The spec has an explicit constructor `MissingParentHeader` | inner handler | `(root, false, chain_id, 0x1501)` |
| O4 | witness incomplete or malformed. Cases:<br>(a) the preimage of a trie root being decoded is missing from the node DB (`KeyError`);<br>(b) **any node reachable from that root through the DB is malformed**: decoding is *eager*, so this applies even off the accessed paths. Malformed means an RLP decode failure, an invalid child-reference length, a non-empty-string "empty node", a list-valued first field of a two-item node before compact decoding (`incremental_mpt.py:946`, Q52), raw empty compact path bytes (EthCommit C3, Q48), a list-valued second field after successful leaf compact decoding (`:951`, Q52), an extension with an empty decoded path or a non-branch child, a branch with fewer than 2 occupied entries, or a list length other than 2 or 17;<br>(c) a lookup or root update meets an unresolved hashed node (`AssertionError` in `witness_state._trie_lookup`, `witness_state.py:73`, for lookups; the `HashedNode` assertions in `incremental_mpt.py`, lines 233, 245, 266 and 327, for root updates; which of these are reachable is part of X1);<br>(d) a code hash is missing from the code DB;<br>(e) an account/storage leaf fails decoding when inspected (`witness_state.py:103–127, 198–203`): invalid RLP or an empty account leaf; account list length other than four, a non-empty list-valued account field, balance outside U256, or a non-empty root/hash whose length is not 32; storage integer outside U256. Preserve the accepted leniencies: leading-zero integers, falsy account fields (including empty lists) taking defaults, and list-valued storage leaves reading as zero (EthStateCommit SC5/SC6). Decoding happens at the first account access (account trie), at the first storage access per account (that storage trie), and during state-root computation for the storage trie of every account with storage changes and for the account trie (`witness_state.py` `_get_decoded_secure_root`, `compute_state_root_and_trie_changes`). Decoded roots are cached by root hash | `WitnessState` (`_trie_lookup`), `incremental_mpt` (`_decode_witness_node`, `_resolve_child_ref`, `decode_witness_to_mpt`), `KeyError` (inner) | `(root, false, chain_id, 0x1501)` |
| O5 | public-key hint count mismatch or a wrong key | `fork.py:312`, `transactions.py:932` (inner) | `(root, false, chain_id, 0x1501)` |
| O6 | invalid block: header checks against the parent (including `parent_hash = keccak(rlp(last witness header))`, `validate_header`), size, gas, a root mismatch (state/tx/receipt/withdrawal), bloom, requests hash, BAL, block hash, versioned hashes. **On the guest path, every deterministic payload-transaction decode failure lands here** (RLP `DecodingError`, `TransactionTypeError`, the empty-transaction assert, and `RecursionError` from deep nesting), because `is_valid_versioned_hashes` consumes it first and reports invalid versioned hashes. A standalone `execute_block` still raises these errors itself; its decode errors are not dead code | `execute_new_payload_request` / `execute_block` (inner) | `(root, false, chain_id, 0x1501)` |
| O7 | invalid transaction (any `InvalidTransaction` subclass raised by admission, not by decoding: see O6) | `check_transaction` etc.; it invalidates the block (inner) | `(root, false, chain_id, 0x1501)` |
| O8 | a frame **reverts** or halts exceptionally (including EVM **out-of-gas**) | consumed inside the transaction (`process_call`/`process_create`); state and gas are handled as per EELS | **no direct effect**; the block may still be valid (then O10) |
| O9 | a precompile fails on its input (for example an invalid point) | an exceptional halt of that frame (O8), or empty output where EELS specifies it (ecrecover, p256verify) | as O8 |
| O10 | everything validates | — | `(root, true, chain_id, 0x1501)` |
| O11 | **spec-internal fuel exhaustion** (a Lean artifact, not an Ethereum outcome) | — | The proposed **checked runner** `runStatelessGuestChecked : ByteArray → Except InternalError ByteArray` computes per-frame budgets from a proved budget policy (`ARCHITECTURE.md` §5.5); there is no external or global guest fuel argument. It reports `.error .fuelExhausted` separately from EVM out-of-gas (O8). The **public total function** projects `.ok out` to `out` and uses `zeroSentinel` on an internal error. The required theorem is **`∀ input, ∃ out, runStatelessGuestChecked input = .ok out`**: all internal-error branches are dead, including any added in future. Fuel sufficiency is part of this theorem. Consumers use it when refining the public function. Conformance calls the checked runner and reports any internal error as a *spec bug*, never a guest output. A compiled prototype of the interfaces showed this channel split: its O11 example gives `.error (.fuelExhausted …)` from the checked runner and the sentinel from the public function. Fuel sufficiency (G2, G4–G7) remains unproved. |
| O12 | Python-runtime failures caught as `False` or the sentinel (`RecursionError`, `MemoryError`, interpreter limits) | — | **Subject to §6, not an approved deviation.** Where a deterministic failure follows from the code, preserve the same output explicitly; witness-reference cycles are classified as O4. Host resource limits can also reject finite acyclic inputs and depend on Python configuration and the machine. A proposed interpretation of such limits is tracked in [`DISCREPANCIES.md`](DISCREPANCIES.md), DISC-001. Reproducer, environment, upstream response and an accepted decision record are required before changing reference behaviour. The phrase “unconstrained host” is not by itself a defined acceptance rule. The guest-process recursion limit is **100,000** (py_ecc raises it; `import ethereum` alone gives 12,288). |
| O13 | **enumerated deterministic reference faults**: implicit Python failures (`IndexError`, `OverflowError`, `AssertionError`, …) that follow deterministically from the code, are raised during block execution, and are consumed by the inner catch-all. It is a documentation category, not a new outcome and not a catch-all. **Each fault is listed and gets its own named constructor**; anything not listed is a gap, not a default. Examples: a missing BLOCKHASH ancestor (`vm/instructions/block.py:58`, witnessed by fixture `validation_headers_missing_oldest_blockhash_ancestor`); `U64` overflow of a legacy-`v` chain id (`transactions.py:878`, witnessed by a probe input). Further sites are argued reachable: balance overflow, parent-header `U64` overflows and BLOBBASEFEE `U256`. Each owning module enumerates its members with named constructors: EthBlock §2.12, EthVmCore R-EXC-2 and EthState R29. Error types are frozen per module once its entries close (B14) | inner handler | `(root, false, chain_id, 0x1501)`: the existing output, unchanged |

**Failure precedence.** Decode before request-root computation, then validate in the pinned EELS order. The first failing phase determines which output fields survive. In particular, more than 256 headers cannot enter through valid SSZ bytes: the list limit fails during decoding (O1). O3's length check is defensive at the typed validation seam. Explicit error constructors preserve phase ownership and check order when several conditions fail together.

## 5. Checks excluded by the reference

- **Fork activation.** "EEST has one implementation per fork, so it does not need to check the execution payload timestamp against the current fork activation information. A real implementation MUST do these checks!" (`stateless.py`, `verify_stateless_new_payload`). The spec follows the reference and records this as an explicit exclusion.
- **Anything authenticated outside the guest** (§7).

## 6. Authority and discrepancy policy

1. **Fixtures decide where they speak.** Agreement with every `statelessOutputBytes` in the pinned corpus is mandatory and decisive.
2. **Outside fixture coverage, the pinned EELS source governs.** That is the Python at `release.commit`, read as a specification, together with the pinned dependency behaviour listed in `reference.toml`.
3. **When the spec, EELS and the fixtures disagree,** or EELS behaviour is accidental (O12), relies on host-dependent `hashlib`/OpenSSL behaviour, or is otherwise unclear:
   - record it in `STFSpec/informal/DISCREPANCIES.md` with a reproducer;
   - report it upstream to execution-specs;
   - follow the reference until upstream decides.

   A spec deviation is allowed only by an accepted decision record that names the discrepancy.
4. **Other implementations never decide.** evm-sail, SpecRef, clients and fuzzing oracles only find bugs.

## 7. What the guest does and does not establish (scope for security statements)

The output commits to the `NewPayloadRequest` by its SSZ root, plus `chain_id` and the schema. Inside the guest, the pre-state is anchored by a chain of checks:

- `payload.parent_hash = keccak(rlp(last witness header))` (O6, `validate_header`);
- the witness headers are contiguous by `parent_hash` (O3);
- the last header's `state_root` roots the witness trie.

**External anchors that the guest does not check** (the verifier's obligation):

- that the `NewPayloadRequest` with that root is the one the verifier intends to validate, and that its parent is on the accepted chain;
- that `chain_id` and the schema/fork are the expected ones.

Security statements separate three obligations:

- **Witness/state agreement:** relative to the supplied parent header, a successful guest agrees with execution over any well-formed state consistent with that root, under the stated Keccak collision assumptions and backend contracts.
- **Request commitment binding:** identifying the supplied request from its output SSZ root additionally uses SHA-256 binding and the SSZ schema's encoding/merkleization laws. This is separate from the Keccak witness theorem. SSZ uses SHA-256 ([Ethereum SSZ transaction specification](https://eips.ethereum.org/EIPS/eip-6493#security-considerations)).
- **Accepted-chain validity:** the verifier supplies the external anchors above. Precompile mathematical correctness and cryptographic security remain separately tracked deliverables (D12).

Totality on malformed bytes and arbitrary finite witness DBs is unconditional; it must not depend on collision resistance. Resource envelopes and host-limit discrepancies are explicit hypotheses or decisions, not hidden restrictions on accepted inputs. The security proof report must name each hash/oracle, its queried preimages and the bridge from concrete execution to the abstract theorem.
