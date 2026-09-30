## Cross-cutting gaps and coordinated owners

*Status: live cross-cutting gap register. Date: 2026-09-30.*

Maintained by hand. Each item says what is missing, the evidence, and who should own it.

### X1. Reachable Python exception sites are not all classified (highest divergence risk)
Under the reference's two catch-all handlers (`STFSpec/informal/CONTRACT.md` §4), *any* Python exception becomes an outcome. That includes implicit ones:
- `OverflowError` from plain `U256`/`U64`/`Uint` arithmetic, which raises rather than wraps; only `wrapping_*` wraps (checked against `ethereum-types` 0.4.1);
- `KeyError` from dict lookups;
- `IndexError` (for example `decoded_headers[-1]`, O3a);
- `AssertionError` from witness-decoding asserts;
- `ValueError` from codecs;
- `RecursionError` and `MemoryError`.

**Tooling exists:** the failure ledger (maintained outside this repository). It combines a static superset of candidate sites with a dynamic pass that runs the pinned EELS over the full fixture corpus. For each site it records the first consuming handler and a proposed outcome; enumerated deterministic faults go to CONTRACT O13. **Remaining:** close the unresolved sites (most of the candidate sites), module by module, and freeze each module's error types as its entries close (B14). **Owners:** `EthConformance` coordinates; each module owns its sites; `EthStateless` owns phase projection.

### X2. Adversarial inputs on which the reference effectively does not terminate
The guest must terminate on *every* input. The design requires totality, which is not yet proved. DISC-002/004 already record the Taylor/DAG cases; host depth/resource acceptance needs a deliberate policy:
- **Blob gas price Taylor loop.** `taylor_exponential` (`utils/numeric.py:177`) runs about 2.7·x iterations on growing integers, with x = excess / 11684671. Measured: 2,338 iterations at an excess of 10¹⁰. It is called for *every* block from `validate_header` → `calculate_excess_blob_gas(parent)` → `calculate_blob_gas_price` (`fork.py:473`, `vm/gas.py:936`, EIP-7918) whenever the parent's blob gas is at or above target. A crafted parent header with an excess near 2^64 needs about 4×10¹² iterations. The parent header is authenticated only externally (CONTRACT §7), so this is reachable in the guest. It is a liveness issue, not a soundness one.
- **Deep witness nesting.** Eager witness decoding (D19) recurses without a depth limit. The guest-process recursion limit is 100,000 (py_ecc raises it). The earlier estimate of about 1,000 nested nodes assumed a limit of 12,288, and the threshold has not been re-measured. Where the reference raises `RecursionError`, the output is `false`, whereas a spec with no depth limit could accept (EthStateless). Tracked in DISC-001; the spec must decide deliberately.
- **Deep RLP nesting.** In the guest process, 20,000 nesting levels decode and 40,000 raise `RecursionError`, reachable through payload transactions. On the guest path, `is_valid_versioned_hashes` consumes that error, so the output is O6 (DISC-001, DISC-006; EthCodec).
- **`MemoryError`:** host-dependent (CONTRACT O12).

### X3. Host-dependent reference behaviour
- `hashlib` RIPEMD-160 can raise on hosts whose build/provider configuration lacks RIPEMD-160, which would invalidate blocks calling precompile 0x03 (EthCodec, EthPrecompiles).
- `crypto/hash.py` prefers `hashlib` keccak when OpenSSL provides it, and falls back to pycryptodome otherwise.

D14/O12 has not selected a host-resource/capability policy. Record Python/OpenSSL capability for each reference run, and do not assume host failures are excluded from fidelity.

### X4. Reference evidence must use the locked environment
The 2026-09-28 review reran its five counterexamples in a clean checkout at the exact pin using unchanged `uv.lock`, including ethereum-rlp 0.1.6 (see REVIEW §2). Earlier evidence using 0.1.7 remains historical and must be rerun when load-bearing. A repeatable CI reference harness is still missing. **Owner:** EthConformance.

### X5. Fixture corpus observations (verified 2026-09-28)
- **Where the records are.** All 29,030 guest records are in `blockchain_tests` (`blockchain_tests_engine` has none), and 24,283 inputs are distinct.
- **138 guest records sit on blocks marked `expectException` but report success.** On the 60 checked, the input's payload is not the fixture block, and EELS reproduces the recorded output. So a runner must not equate the guest result with block validity.
- **237 valid Amsterdam blocks have no guest record,** reason unknown.
- **Only 9 zero-sentinel (malformed-input) records** exist, all in `eip8025/stateless_input_bytes`. Malformed-input coverage is thin.
- **Transition fixtures** (`for_bpo2toamsterdamattime15k`) need bpo2 execution, which D3 excludes.
- **No mapping yet** from EEST exception labels to our explicit error constructors.

### X6. Termination is designed but unproved
- CALL/CREATE progress across complete iterations;
- fuel sufficiency;
- the four fuel guarantees;
- termination of `taylor_exponential`, and of every loop in the codecs and trie.

See ARCHITECTURE §5.5 and [REVIEW §7](REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks) G2–G7.

### X7. Security proof has an unknown core step
Proving directional simulation of a successful witness trace by a progressive full backend is the largest unknown. Models alone does not establish availability and must include full-state code authenticity. Also:
- VCV-io has no MPT or RLP support, and is not yet a Lake dependency;
- keccak-derived constants go through the same oracle (`HashConsts`, D5); still open are the oracle coupling for `Models` and `Progress` at generic `m`, secure-key collision folding, and the complete code preimage sets. Generic provider coherence must use hash-relative forms of those premises: combining keccak-literal `Models` with an oracle that differs on constant preimages can make them inconsistent. Prove the concrete bridges and exhibit providers satisfying all premises before claiming nonvacuous generic agreement (EthSecurity §5).
- Direct proof imports are now registered in contracts.toml; the actual proof implementations are absent.

### X8. Consumer migration cost is unmeasured
evm-asm's per-opcode theorems use `BitVec 256`, so the `structure U256` needs a bridge through `toBitVec`. pancaketh needs a name map. Neither has been tried.

### X9. Evidence gaps in the research base
Several literature items were read at abstract level only; the full text of Allain, Clément, Moine & Scherer, *Snapshottable Stores* (ICFP 2024), was not accessible. The first-pass benchmark numbers remain provisional, and some must not be cited: the first-pass 256-bit word timings predate a limb-multiplier carry fix and fold a checksum into the timed loop, and the other first-pass figures are orders of magnitude only.

### X10. The witness post-state root depends on write order and on earlier lookups
- **Order.** EELS applies account changes in first-write order, with inserts and deletes interleaved (`witness_state.py:303–309`). A delete that collapses a branch onto a missing sibling fails before an insert under that branch, and succeeds after it (run by the EthState/EthStateWitness authors). Storage tries apply non-zero writes, then zero writes, each in first-write order. `BlockDiff` carries the account, storage-address and slot orders (B1). Their clear/rollback/merge laws are outstanding, and so is the iteration order of storage clears (DECISIONS F7, open).
- **Earlier lookups.** For changed accounts, the storage root comes from a cache filled by earlier lookups, and is the empty root if the address was never looked up. This is safe only because every account write is preceded by a lookup: an invariant to prove (COMPOSITION §3, item 2).

### X11. Reference acceptance is not canonical
The reference accepts non-canonical witness encodings (DISC-003) and lenient leaf decodings (a list-valued storage leaf reads as 0, and empty lists in an account leaf read as defaults). CONTRACT O4(e) lists the leaf failures; exact adapters and precedence remain to be proved under EthStateCommit SC5/SC6. The spec must reproduce the accepted set exactly.

### X12. Upstream crypto pieces are missing
- The 381-bit Montgomery field (`W12`) exists only as a prototype outside the core; it is not yet in the core or upstream.
- No BN254 Lean reference.
- ethereum/cryptography-specs is not reusable as-is: it targets Lean v4.29.1, and uses `partial def`, `get!` and `native_decide`, which our declaration check rejects.
- Mathlib has no pairing theory and no point counting, so bilinearity and the group orders (D12 (ii)) have no known proof route.
- The secp256k1 and P-256 behaviour is inferred from the standards and test runs, because the reference libraries are compiled.

### X13. Shared interfaces and record instances are not compiled (implementation task, not a spec defect)
The spec guidance documents' Lean-like signatures are informal by design (`CONTRIBUTING.md` §5.4), so placeholders there are not defects in themselves. A compiled prototype of the interfaces covered one complete guest path, and its dispositions are folded into the spec guidance documents (DECISIONS §3). Compiling the interfaces in the core is implementation work. The review aligned the common types and checked errors, but some signatures still contain placeholders and inferred or undefined local types; the implementer resolves those. REFERENCE-RECORDS captures exact source fields; each schema owner must expand its records and prove both adapter inverses. **Owners:** each schema/API owner; EthStateless coordinates the complete path.

### X14. Informal premises are not yet discharged
All 23 modules and COMPOSITION contain conditional arguments. No completed Lean definitions/proofs exist. REACHABLE caller invariants, code authenticity, rootability/encodability domains and backend progress must be established independently; document-structure checks cannot prove them. **Owners:** the producers/consumers in COMPOSITION §7 and REVIEW §3.

### X15. Open interface obligations from the interface prototype
Four items from the interface-composition prototype are open (`STFSpec/informal/DECISIONS.md` §3):
- **F6:** memo ownership, lifetime and decode triggers for storage tries (EthStateWitness). Cache mechanics stay outside semantic state; this is a DEBT candidate until settled.
- **F7:** the iteration order of storage clears in the witness root replay (EthState, EthStateWitness). It must agree on failures and observations, not only on roots.
- **F11:** how the runner produces `ChildSettled` (EthVmRunner).
- **O2:** the proof that request-root computation cannot fail on decoded values (EthStateless).

**Owners:** as listed.
