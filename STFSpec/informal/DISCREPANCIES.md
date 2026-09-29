# Protocol discrepancy register

Status: no accepted deviations. Date: 2026-09-29. This register implements the recording part of [`CONTRACT.md`](CONTRACT.md) §6; an entry does not authorize a change or imply that an upstream report exists. Preserve the pinned reference until an accepted decision says otherwise.

## DISC-001: Python host resource limits

- **Status:** proposed investigation; one reproducer recorded (deep RLP, below); not reported upstream; no accepted deviation.
- **Scope:** O12. Python recursion/allocation limits may turn finite inputs into failure outputs whose value depends on the host and the catching phase. Cycle detection can reproduce a deterministic invalid-witness output; finite deep or large inputs need separate analysis.
- **Reference:** execution-specs commit `e1a316a06fc3d3e0a5da36fdc78580811e9d8a36`, `stateless_guest.run_stateless_guest` and `stateless.verify_stateless_new_payload`, with dependencies in `reference.toml`.
- **Evidence required:** exact input bytes and digest; Python/dependency versions; recursion limit, memory/container limits and relevant host settings; command; exception and catching phase; encoded output; comparison across environments. Distinguish fixture-covered cases from uncovered inputs.
- **Tracked cases:** deep RLP nesting in payload transactions (DECISIONS Q20); deep acyclic witness chains (Q6); DAG-shaped witnesses (DISC-004).
- **Recorded evidence (2026-09-29, from running the pinned EELS with the failure ledger, maintained outside this repository):**
  - Environment: CPython 3.13.7, OpenSSL 3.0.16, locked dependencies. The guest-process recursion limit is **100,000**, because `py_ecc` raises it; `import ethereum` alone sets 12,288.
  - Deep RLP (deterministic probe inputs mutating a corpus transaction): 20,000 nesting levels decode, while 40,000 and 120,000 raise `RecursionError`. On the guest path, the `is_valid_versioned_hashes` catch-all consumes it, so the output is O6 (see DISC-006).
  - Deep witness chains have not been re-measured under the 100,000 limit.
- **Open question:** which resource-independent interpretation, if any, upstream intends for valid finite inputs rejected only by host limits. “Unconstrained host” is not a computable or approved acceptance rule.
- **Resolution:** pending reproducer, upstream issue/response and accepted decision record. D14 confirmation alone must not silently authorize an unspecified O12 deviation.

## DISC-002: Blob gas price Taylor loop is infeasible on adversarial parent headers

- **Status:** measured locally; reproducer (a crafted guest input) pending; not reported upstream; no accepted deviation.
- **Scope:** liveness only. The reference *is* total, but at impractical cost; the output is not wrong.
- **Reference:** `utils/numeric.py:177` `taylor_exponential`, called from `vm/gas.py:936` (`calculate_excess_blob_gas`, EIP-7918), which is called from `fork.py:473` (`validate_header`) for **every** block whose parent's `excess_blob_gas + blob_gas_used ≥ BLOB_TARGET_GAS_PER_BLOCK`; also `vm/gas.py:1011, 1046` and `vm/instructions/environment.py:606`. `BLOB_BASE_FEE_UPDATE_FRACTION = 11684671` (`vm/gas.py:146`).
- **Evidence:** measured 2026-09-28 by running the loop's recurrence in Python. The iteration count is about 2.7·x, with x = excess / 11684671: 35, 245 and 2,338 iterations at excesses of 10⁸, 10⁹ and 10¹⁰. Extrapolated, an excess near 2^64 needs about 4×10¹² iterations on growing integers. The parent header is authenticated only externally (CONTRACT §7), so the guest can receive it.
- **Proposed Lean behaviour:** the same function, with a termination proof (the accumulator reaches 0 once `i` exceeds the numerator/denominator ratio by enough). A faithful implementation is equally slow; any faster algorithm must be proved equal (D21).
- **Open question for upstream:** should the spec bound `excess_blob_gas` (for example by validating the parent against its own parent), or accept that guests can be made to hang on unanchored inputs?

## DISC-003: Non-canonical witness node encodings are accepted

- **Status:** observed by running the pinned EELS (EthCommit/EthStateWitness specs, DECISIONS B3); reproducers for two of the behaviours are committed as checks 3 and 4 of `scripts/spec_review.py` (STFSpec/informal/REVIEW.md §2); not reported upstream.
- **Scope:** acceptance. The reference accepts:
  - hex-prefix flag bits 2–3 and padding nibbles;
  - inline children of 32 bytes or more;
  - hash references to nodes shorter than 32 bytes;
  - list-valued branch values.

  With such nodes, a no-op delete can change the root, and an extra unused `0x80` DB entry can flip an accepted witness to rejected.
- **Proposed Lean behaviour:** reproduce the reference exactly (P2): the decoder accepts the same set. The canonical-form invariant (ARCHITECTURE §5.4) applies to tries *built* by the spec, not to decoded witnesses. This needs an accepted decision record.

## DISC-004: Exponential decoding of DAG-shaped witnesses

- **Status:** observed in the pinned source (`incremental_mpt.py` `_resolve_child_ref` decodes a shared hash once per occurrence); not reported upstream.
- **Scope:** liveness and performance. Outputs are unaffected in principle, but the reference may not finish on crafted DAGs, which also interacts with DISC-001 (recursion depth).
- **Proposed Lean behaviour:** memoised eager decoding by hash (DECISIONS B15), with a proof that it gives the same accept/reject result as occurrence-wise decoding.

## DISC-005: RIPEMD-160 depends on the host OpenSSL

- **Status:** from reading the pinned source and the Python/OpenSSL documentation; not reproduced here.
- **Scope:** acceptance, host-dependent. `precompiled_contracts/ripemd160.py:52` uses `hashlib.new("ripemd160")`, which can raise `ValueError` when the host build/provider configuration lacks RIPEMD-160. Absence of the legacy provider alone is insufficient: [OpenSSL documents](https://docs.openssl.org/3.0/man7/EVP_MD-RIPEMD160/) RIPEMD-160 in the default provider since 3.0.7. The error invalidates the block instead of executing the precompile.
- **Proposed Lean behaviour:** a real RIPEMD-160, as the Frontier precompile 0x03 is defined in the Yellow Paper, which is the unconstrained-host behaviour (DISC-001 applies); record the host OpenSSL in every EELS evidence run (X4). The host of the recorded EELS runs (OpenSSL 3.0.16) provides RIPEMD-160.

## DISC-006: Local catch-alls make host failures look like invalid versioned hashes

- **Status:** observed by running the pinned EELS over the full fixture corpus and targeted probe inputs (2026-09-29); not reported upstream; no accepted deviation.
- **Scope:** observability of host-resource failures (O12).
  - `is_valid_versioned_hashes` (`execution_engine/new_payload.py:60–68`) decodes every payload transaction under `except Exception: return False`. So any failure while decoding, including host failures such as `RecursionError` or `MemoryError`, is reported as O6 "invalid versioned hashes" before `execute_block` runs.
  - Deterministic decode failures are correctly O6 on the guest path.
  - Host failures are indistinguishable from them in the output.
- **Proposed Lean behaviour:** follow the reference for deterministic decode failures (O6). Host-resource cases stay under DISC-001; they are not decided here.
- **Open question for upstream:** whether that catch-all is intended to absorb non-decoding exceptions.

Future entries use the same fields and include fixture identities, proposed Lean behaviour, affected public laws, regression tests and links to upstream/decision evidence. Keep resolved entries and their reproducers when the pin changes.
