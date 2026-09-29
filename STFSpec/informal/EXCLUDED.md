# EELS items deliberately not specified

*Status: exclusions at tests-zkevm@v21.0.0 @e1a316a0. Date: 2026-09-29.*

Each entry: a backquoted `` `file::name` `` or `` `file::*` `` token and the reason. `scripts/check_spec.py`
counts these as covered. An exclusion is a claim that the item has no effect on
`run_stateless_guest` at the pinned release (or is host-side tooling); it must say why.

| EELS item | Reason |
|---|---|
| `forks/amsterdam/stateless.py::ExecutionPayloadHeader` | Empty scaffolding dataclass ("TODO: Replace with the fork-specific execution payload header container", `stateless.py:78–83`); referenced only by `NewPayloadRequestHeader`, never by the guest path. (G6) |
| `forks/amsterdam/stateless.py::NewPayloadRequestHeader` | Header-only request form "for stateless flows" (`stateless.py:89–100`), not an SSZ container and not used by `run_stateless_guest`, `verify_stateless_new_payload` or any host tool at e1a316a0 (grep over `src/` and `packages/`). Revisit if a future release switches the input to the header form. (G6) |
| `forks/amsterdam/execution_engine/forkchoice_update.py::notify_forkchoice_updated` | Body is `raise NotImplementedError` (`forkchoice_update.py:16–26`); fork choice is a consensus-client concern and has no role in stateless validation. No fixture exercises it (engine fixtures record only `forkchoiceUpdatedVersion`). (G6) |
| `forks/amsterdam/execution_engine/get_payload.py::get_payload` | Body is `raise NotImplementedError` (`get_payload.py:11–17`); payload building is block production, not validation. (G6) |
| `forks/amsterdam/execution_engine/types.py::PayloadAttributes` | Parameter type of `notify_forkchoice_updated` only (block building); not SSZ, not in `StatelessInput`. (G6) |
| `forks/amsterdam/execution_engine/types.py::BlobsBundle` | Field type of `GetPayloadResponse` only (block building). (G6) |
| `forks/amsterdam/execution_engine/types.py::GetPayloadResponse` | Return type of the unimplemented `get_payload` only. (G6) |
| `forks/amsterdam/execution_engine/types.py::_ZERO_HASH32` | Defined (`types.py:32`) but referenced nowhere in `src/` or `packages/` at e1a316a0; dead constant. (G6) |
| `forks/amsterdam/stateless_host_exec_witness.py::*` | Host-side witness *construction* (`build_execution_witness`, `get_witness_codes`, `get_witness_ancestors` and helpers). No effect on `run_stateless_guest`: the guest accepts any witness sufficient for execution, and fixtures carry the witness inside `statelessInputBytes`. Its node selection is a host policy (minimality/sorting), not a validity criterion. Fuzzing of new blocks uses the pinned EELS host out of process instead (`EthConformance` R8); a Lean-native generator is deferred (`STFSpec/informal/DECISIONS.md` Q7). Also depends on access recording in `incremental_mpt.py`/`state_tracker.py` owned by G3. (G6) |
