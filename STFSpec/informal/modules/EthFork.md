# `EthFork`: the Amsterdam composition

*Status: informal specification, draft. Date: 2026-09-30. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F2, F8, F9, F20 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D3, D5, D13, D17, D21 · questions: B8 (Q1/Q26/Q43), B11, Q5, Q8.*

Line references are to `src/ethereum/forks/amsterdam/`. **[V]** means read (or evaluated) at the pin; **[I]** means an inference.

## 1. Purpose

`EthFork` is layer L6 (ARCHITECTURE §2, §8; D3). It is the one place where Amsterdam is chosen. It holds:
- the **values** of the parameter records whose types live next to their semantics (`BlockConfig` in `EthBlock`, `GasCosts`/`StateGasCosts`/`VmLimits` in `EthVmCore`). Every Amsterdam value lives here, including the precompile pricing constants (DECISIONS B8, F8, F9); the owning modules define only the record types;
- the **precompile table** built from `EthPrecompiles`;
- the selection of the named fork modules.

It exports one configured entry point, `Amsterdam.executeBlock`, for `EthStateless`. Like `EthBlock.executeBlock`, it is generic in `{m} [Monad m] [KeccakQuery m]` (D5); `EthStateless`'s public entry point uses it at `m := Id`, where `KeccakQuery Id` is concrete keccak256. The keccak-derived constants (`HashConsts`, `EthBase`) arrive from the caller under F20: this module forwards the same `consts` to `EthBlock.executeBlock` without acquisition or literal substitution. It also states the hypotheses that generic proofs (termination, arithmetic safety, conservation) need of a configuration, and discharges them for the Amsterdam instance. It contains no execution logic.

## 2. Requirements

- **R-F1 (block parameters)** (`fork.py:114–146`):
  - `baseFeeMaxChangeDenominator = 8`, `elasticityMultiplier = 2`;
  - `maxBlockSize = 10 485 760`, `safetyMargin = 2 097 152`, `maxRlpBlockSize = maxBlockSize − safetyMargin = 8 388 608` (EIP-7934). The derived value must be defined by the same subtraction, not as a literal.
- **R-F2 (system addresses and system-call budget)** (`fork.py:117–141`; `requests.py:49`). The addresses must be byte-exact:
  - `systemAddress = 0xfffffffffffffffffffffffffffffffffffffffe`;
  - `beaconRoots = 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02` (EIP-4788);
  - `historyStorage = 0x0000F90827F1C53a10cb7A02335B175320002935` (EIP-2935);
  - `withdrawalRequests = 0x00000961Ef480Eb55e80D19ad83579A64c007002` (EIP-7002);
  - `consolidationRequests = 0x0000BBdDc7CE488642fb579F8B00f3a590007251` (EIP-7251);
  - `builderDeposits = 0x0000BFF46984E3725691FA540A8C7589300D8282` and `builderExits = 0x000064D678505AD48F8CCB093BC65613800E8282` (EIP-8282);
  - `depositContract = 0x00000000219ab540356cbb839cbe05303d7705fa` (EIP-6110, the mainnet address, used for every chain id; see Gaps).
  
  The system-call budget is `txGas = 30 000 000` and `maxSstoresPerCall = 16`.
- **R-F3 (transaction parameters)** (`transactions.py:64–88`): `blobCountLimit = 6` (per transaction, EIP-7594); `accessListAddressFloorTokens = 80` and `accessListStorageKeyFloorTokens = 128` (EIP-7981).
- **R-F4 (gas, state-gas, VM-limit and blob schedule: the values).** `EthFork` defines the Amsterdam values of `EthVmCore`'s `GasCosts`, `StateGasCosts` and `VmLimits` record types (DECISIONS B8, F8). The record types, and the source-map claims on `vm/gas.py:48–266`, stay with `EthVmCore`. `vmLimits.stackDepthLimit` must be definitionally `EthVmCore`'s `abbrev STACK_DEPTH_LIMIT : Nat := 1024`, stated as `vmLimits_depth : vmConfig.limits.stackDepthLimit = STACK_DEPTH_LIMIT := rfl` (the depth proofs need a kernel-reducible literal). `GasCosts` includes **every** precompile pricing dependency as fields (B8, F9): the EIP-2537 pairing base 37 700 and per-pair cost 32 600 (literals in `vm/precompiled_contracts/bls12_381/bls12_381_pairing.py:46`), the G1/G2 MSM discount tables `G1_K_DISCOUNT`/`G2_K_DISCOUNT`, the maximum discounts `G1_MAX_DISCOUNT`/`G2_MAX_DISCOUNT` and `MULTIPLIER` (`vm/precompiled_contracts/bls12_381/__init__.py:37–301`); `EthPrecompiles` reads them from the config and holds no pricing literals. The values `EthBlock` depends on must hold for these records. They are checked by `#guard` against [V] values evaluated at the pin:
  - transaction costs: `TX_BASE 12000`, `TX_VALUE_COST 6000`, `CREATE_ACCESS 12000`, `COLD_ACCOUNT_ACCESS 3000`, `TX_DATA_TOKEN_STANDARD 4`, `TX_DATA_TOKEN_FLOOR 16`, `TX_ACCESS_LIST_ADDRESS 2900`, `TX_ACCESS_LIST_STORAGE_KEY 2000`, `EXECUTION_PER_AUTH_BASE_COST 7816`;
  - limits: `TX_MAX_GAS_LIMIT 2²⁴`, `TX_MAX_TOTAL_GAS_LIMIT 2³² − 1`, `LIMIT_ADJUSTMENT_FACTOR 1024`, `LIMIT_MINIMUM 5000`, `BLOCK_ACCESS_LIST_ITEM 2000`;
  - blob schedule: `PER_BLOB 2¹⁷`, `BLOB_SCHEDULE_TARGET 14`, `BLOB_SCHEDULE_MAX 21`, `BLOB_BASE_COST 2¹³`, `BLOB_MIN_GASPRICE 1`, `BLOB_BASE_FEE_UPDATE_FRACTION 11 684 671`, so `MAX_BLOB_GAS_PER_BLOCK = 2 752 512` and the target is 1 835 008;
  - state gas: `COST_PER_STATE_BYTE 1530`, `STORAGE_SET 97 920`, `NEW_ACCOUNT 183 600`, `AUTH_BASE 35 190`.
  
  EELS notes that these classes "may be patched at runtime by a future gas repricing utility" (`gas.py:45, 70`). The spec fixes them as constants; no runtime patching exists.
- **R-F5 (precompile table)** (`vm/precompiled_contracts/mapping.py:59`, owned by G2). `amsterdam.precompiles` must map exactly 18 addresses:
  - `0x01` ecrecover, `0x02` sha256, `0x03` ripemd160, `0x04` identity, `0x05` modexp;
  - `0x06`/`0x07`/`0x08` BN254 add/mul/pairing, `0x09` blake2f, `0x0a` point evaluation;
  - `0x0b`–`0x11` BLS12-381: G1 add, G1 MSM, G2 add, G2 MSM, pairing, map Fp→G1, map Fp²→G2;
  - `0x100` p256verify.
  
  Each maps to the `EthPrecompiles` function. The **key set** is itself semantic: it is added to every transaction's warm address set (`vm/interpreter.py:172`) and decides precompile dispatch (`:438`). So `precompiles.addresses` must be exactly this set (the `lookup_iff` field of `EthVmCore`'s `PrecompileTable` ties it to dispatch).
- **R-F6 (behaviour selection).** The Amsterdam changes listed in `__init__.py:7–20` are located as follows. They are implemented in the named modules, not here.
  - EIP-2780: `EthBlock` intrinsic gas and the `EthVmRunner` top frame.
  - EIP-7708: transfer logs, `EthVmInstructions`/`EthVmRunner`.
  - EIP-7778: `EthBlock` settlement use.
  - EIP-7843: the header field in `EthBlock`, the SLOTNUM opcode in `EthVmInstructions`.
  - EIP-7928: `EthBlock` BAL, with `EthState` reads.
  - EIP-7954: code size, `EthVmCore`/`EthVmRunner`.
  - EIP-7976/7981: `EthBlock` intrinsic gas.
  - EIP-7997: **no code at the pin** [V, by grep]; see Gaps.
  - EIP-8024: `EthVmInstructions`.
  - EIP-8037/8038: `EthVmCore` gas, with `EthBlock` capacity and settlement use.
  - EIP-8246: `EthVmInstructions` SELFDESTRUCT and `EthBlock` `clearAccountPreservingBalance`.
  - EIP-8282: `EthBlock` requests.
  
  Only Amsterdam modules exist (D3). The bpo5 `PrevHeader` type in `EthBlock` is the only previous-fork artefact.
- **R-F7 (composition).** `Amsterdam.executeBlock consts := EthBlock.executeBlock Amsterdam.config consts`. `EthStateless` must call only this, never `EthBlock.executeBlock` with another config.
- **R-F8 (fork metadata).**
  - `forkCriteria = Unscheduled(order_index = 3)` (`__init__.py:43`) is recorded as data only. The guest never consults it: the reference excludes fork-activation checks (CONTRACT §5, `stateless.py` comment), and so does the spec.
  - `applyFork` (`fork.py:179`) is the identity on `BlockChain σ`. It is used by `EthConformance` only if a transition fixture is ever driven through the full-state path.

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `forks/amsterdam/fork.py::BASE_FEE_MAX_CHANGE_DENOMINATOR` | 114 | `amsterdam.block.baseFeeMaxChangeDenominator` | 8 |
| `forks/amsterdam/fork.py::ELASTICITY_MULTIPLIER` | 115 | `amsterdam.block.elasticityMultiplier` | 2 |
| `forks/amsterdam/fork.py::SYSTEM_ADDRESS` | 117 | `amsterdam.system.systemAddress` | `0xff…fe` |
| `forks/amsterdam/fork.py::BEACON_ROOTS_ADDRESS` | 118 | `amsterdam.system.beaconRoots` | EIP-4788 |
| `forks/amsterdam/fork.py::SYSTEM_TRANSACTION_GAS` | 121 | `amsterdam.system.txGas` | 30 000 000 execution gas |
| `forks/amsterdam/fork.py::SYSTEM_MAX_SSTORES_PER_CALL` | 122 | `amsterdam.system.maxSstoresPerCall` | 16; reservoir = 16 · STORAGE_SET |
| `forks/amsterdam/fork.py::WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS` | 129 | `amsterdam.system.withdrawalRequests` | EIP-7002 |
| `forks/amsterdam/fork.py::CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS` | 132 | `amsterdam.system.consolidationRequests` | EIP-7251 |
| `forks/amsterdam/fork.py::BUILDER_DEPOSIT_CONTRACT_ADDRESS` | 135 | `amsterdam.system.builderDeposits` | EIP-8282 |
| `forks/amsterdam/fork.py::BUILDER_EXIT_CONTRACT_ADDRESS` | 138 | `amsterdam.system.builderExits` | EIP-8282 |
| `forks/amsterdam/fork.py::HISTORY_STORAGE_ADDRESS` | 141 | `amsterdam.system.historyStorage` | EIP-2935 |
| `forks/amsterdam/fork.py::MAX_BLOCK_SIZE` | 144 | `amsterdam.block.maxBlockSize` | 10 485 760 |
| `forks/amsterdam/fork.py::SAFETY_MARGIN` | 145 | `amsterdam.block.safetyMargin` | 2 097 152 |
| `forks/amsterdam/fork.py::MAX_RLP_BLOCK_SIZE` | 146 | `amsterdam.block.maxRlpBlockSize` | 8 388 608 (derived) |
| `forks/amsterdam/fork.py::apply_fork` | 179 | `applyFork` | identity; not on the guest path |
| `forks/amsterdam/transactions.py::BLOB_COUNT_LIMIT` | 64 | `amsterdam.tx.blobCountLimit` | 6 |
| `forks/amsterdam/transactions.py::ACCESS_LIST_ADDRESS_FLOOR_TOKENS` | 74 | `amsterdam.tx.accessListAddressFloorTokens` | 80 (EIP-7981) |
| `forks/amsterdam/transactions.py::ACCESS_LIST_STORAGE_KEY_FLOOR_TOKENS` | 82 | `amsterdam.tx.accessListStorageKeyFloorTokens` | 128 (EIP-7981) |
| `forks/amsterdam/requests.py::DEPOSIT_CONTRACT_ADDRESS` | 49 | `amsterdam.system.depositContract` | mainnet `0x00000000219a…05fa` |
| `forks/amsterdam/__init__.py::FORK_CRITERIA` | 43 | `forkCriteria` | `Unscheduled(order_index=3)`; unused by the guest (O-exclusion) |

**External semantics.** `hex_to_address` (`utils/hexadecimal.py`, G1) must be case-insensitive and left-pad to 20 bytes. The addresses above are given checksummed, and `0x01`/`0x100` are short forms. `ForkCriteria`/`Unscheduled` (`ethereum/fork_criteria.py`) are outside the inventory. They are recorded as a comment and have no semantics here.

## 4. Tests

- **EEST.** Every fixture exercises the composition. The parameter-sensitive areas are:
  - `osaka/eip7934_block_rlp_limit`, `osaka/eip7825_transaction_gas_limit_cap`, `osaka/eip7918_blob_reserve_price`, `osaka/eip7594_peerdas` (blob count);
  - `cancun/eip4844_blobs`, `cancun/eip4788_beacon_root`, `prague/eip2935_…`, `prague/eip7002_…`, `prague/eip7251_…`, `prague/eip6110_deposits`, `amsterdam/eip8282_builder_execution_requests`;
  - `amsterdam/eip7981_…`, `eip2780_…`, `eip7997_deterministic_factory_contract`;
  - all precompile areas (table keys);
  - the transition set `for_bpo2toamsterdamattime15k/*` (15 areas), with a pre-fork parent header.
- **EELS unit tests** (`tests/json_loader/`): `test_forks.py`, `test_fork_blob_schedule.py`, `test_fork_transition_schedule.py` and `test_fork_transition_networks.py`. These test EELS's fork machinery; they are relevant only as documentation of the blob schedule and transition rules.
- **`core` `#guard` cases.**
  - Every value in R-F1–R-F4 equals the constant evaluated from the pinned Python. A prototype generator (not yet in this repository) emits the `GasCosts` record (in REFERENCE-RECORDS order) and the Amsterdam values, including the BLS pricing fields, from the pinned EELS. It prints Lean fragments that are pasted by hand. It is a candidate to promote to `scripts/` with a `--check` mode, alongside `scripts/gen_eels_inventory.py`.
  - The byte strings in R-F2 (checksummed and lowercase decode alike).
  - `precompiles.addresses` equals the 18-element set.
  - `maxRlpBlockSize = 8 388 608`.
  - Each discharge lemma of §7 as a `decide`-free `#guard` on the concrete numbers.
- **Adversarial.** A call to `0x12` or `0xff` (not a precompile, so it is not warm); a call to `0x100` (warm); a block whose deposit log comes from a non-mainnet deposit address (ignored).

## 5. Interface

```lean
namespace STFSpec.Fork.Amsterdam                       -- public
def blockParams  : Block.BlockParams              -- R-F1
def systemAddrs  : Block.SystemAddrs              -- R-F2
def txParams     : Block.TxParams                 -- R-F3
def gasCosts     : Vm.GasCosts      where …     -- R-F4, the Amsterdam values (incl. BLS pricing fields)
def stateGasCosts: Vm.StateGasCosts where …
def vmLimits     : Vm.VmLimits := ⟨Vm.STACK_DEPTH_LIMIT, 0x10000, 0x20000⟩
def vmConfig : Vm.VmConfig := ⟨gasCosts, stateGasCosts, vmLimits⟩
theorem vmLimits_depth : vmConfig.limits.stackDepthLimit = Vm.STACK_DEPTH_LIMIT := rfl
def precompiles {m} [Monad m] [KeccakQuery m] : Vm.PrecompileTable m := STFSpec.Precompiles.table vmConfig  -- R-F5; EthVmCore's record (lookup, addresses, lookup_iff, meter_law)
def config       : Block.BlockConfig :=
  { gas := gasCosts, stateGas := stateGasCosts, block := blockParams,
    tx := txParams, system := systemAddrs, precompiles := precompiles, limits := vmConfig.limits }
def executeBlock {m} [Monad m] [KeccakQuery m] (consts : HashConsts) :=
  Block.executeBlock (m := m) config consts  -- R-F7, the only entry for EthStateless
def stateTransition := Block.stateTransition config   -- full-state path, at m := Id
def applyFork {σ} : Block.BlockChain σ → Block.BlockChain σ := id      -- R-F8
def forkCriteria : String := "Unscheduled(order_index=3)"            -- data only

-- generic-proof hypotheses (§7), stated in EthBlock/EthVmRunner as a Prop on a config
theorem config_wf : Block.BlockConfig.WellFormed config               -- public
theorem termination_ready : Vm.Runner.TerminationReady config             -- public
```

## 6. Data structures

| Item | Representation | Model | Invariant | Persistence | Cost |
|---|---|---|---|---|---|
| Parameter records | plain structures of `Nat`/`Address`/`U64` | themselves | `WellFormed` (§7) | read-only constants, shared | O(1) access |
| Precompile table | `EthVmCore`'s `PrecompileTable`: `lookup : Address → Option (PrecompileFn m)` (a total function by `match` on the address), `addresses : AddrSet`, with the fields `lookup_iff` and `meter_law` | finite partial map `A ⇀ PrecompileFn m` | `lookup_iff : ∀ a, (lookup a).isSome ↔ a ∈ addresses`; `meter_law` as stated in `EthVmCore` | read-only | dispatch O(1) (a match on a small integer; [I] compiles to a decision tree); warming O(18 log n) per transaction |

No mutable or snapshot-reachable state lives here.

## 7. Contract and laws

`Block.BlockConfig.WellFormed cfg` collects the hypotheses generic block proofs take. `Amsterdam.config_wf` discharges each by computation on the constants. [C]

1. Division safety: `elasticityMultiplier > 0`, `baseFeeMaxChangeDenominator > 0`, `LIMIT_ADJUSTMENT_FACTOR ≥ elasticityMultiplier`. With the `checkGasLimit` lemma of `EthBlock` §7, the latter gives `parentGasTarget > 0` whenever the base fee is computed. `BLOCK_ACCESS_LIST_ITEM > 0` and `BLOB_BASE_FEE_UPDATE_FRACTION > 0` (the Taylor denominator). [T]
2. U64 range: `BLOB_SCHEDULE_MAX · PER_BLOB < 2⁶⁴`, and `blobCountLimit · PER_BLOB ≤ MAX_BLOB_GAS_PER_BLOCK`, so a single valid blob transaction always fits an empty block's blob budget. [T]
3. Index range: `maxRlpBlockSize` is less than the minimum encoded transaction size times `2³² − 2`. So `BlockAccessIndex (n + 1) : U32` never overflows. [T] [I] The minimum encoded size is still to be fixed by `EthCodec`.
4. Gas-limit caps: `TX_MAX_GAS_LIMIT ≤ TX_MAX_TOTAL_GAS_LIMIT`. The intrinsic floor constants satisfy `TX_DATA_TOKEN_FLOOR ≥ TX_DATA_TOKEN_STANDARD`. [C]
5. Termination readiness (`TerminationReady`, the ARCHITECTURE §5.5 hypothesis): every continuing opcode's static charge is ≥ 1 (the minimum is `JUMPDEST = 1` [I]: to be confirmed against the full opcode table); `CALL_STIPEND ≤ CALL_VALUE`; the child grant never exceeds the parent's available gas. The behavioural predicate is stated in `EthVmRunner`; specialising its whole-iteration proof here is outstanding. Numeric positivity is only one premise. [T]
6. System-call budget: `txGas + maxSstoresPerCall · STORAGE_SET` fits the runner's `Nat` budget. There is no bound to check, since gas is `Nat`. System calls add nothing to block gas counters. [C]
7. Table law: `precompiles.addresses` is exactly R-F5, and every key maps to the `EthPrecompiles` function of the same EELS name. [R] Consumers use this to identify dispatch.
8. Conservation (a `WellFormed` field once `EthBlock` §7 states it): `baseFee ≤ effectivePrice` is built into admission, so the fee split never goes negative. [C]

**Derived law.** Every generic theorem `∀ cfg, WellFormed cfg → P cfg` specialises to `P Amsterdam.config` with no further obligation. Adding a fork also requires its behavioural refinement and runner progress proof if opcode or call rules change; `config_wf` alone is insufficient.

### Informal correctness argument

**Claim.** Amsterdam configuration selects the pinned constants, implementations and schemas consistently, allowing generic results to specialise when all their actual premises have been established.

**Premises.** Correct parameter values and table entries; numeric WellFormed checks; semantic correctness of the selected step/runner/precompile implementations; the runner's separate whole-iteration progress theorem.

**Argument.** Compare each literal to the pinned constant inventory. Arithmetic evaluation establishes positive denominators, range bounds and cost inequalities. Construct one VmConfig and use it both for FrameCtx/RunnerEnv and for pricing closures in PrecompileTable; the lookup/address law supplies warm-address and dispatch agreement. Construct BlockConfig from those same values. Generic block theorems then specialise by substituting this config and supplying their proofs. The termination premise concerns complete execution paths, including child forwarding and returns: evaluating JUMPDEST or stipend constants only supplies some inputs to that proof. Activation remains external because the pinned guest does not check it. A future fork whose opcode behaviour changes requires a behaviour refinement as well as new values.

**Open obligations.** Pin full parameter records, prove config coherence, and obtain TerminationReady from the runner proof instead of treating it as a computable property of GasCosts. The minimum-transaction-size/index argument and transition-header compatibility also remain to be checked.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthBlock`, `EthPrecompiles`
- **Used by:** `EthStateless`, which calls only `Amsterdam.executeBlock`, and `EthConformance`, through `EthStateless` and for `stateTransition` with the full-state backend.
- **Seams:** `EthFork` consumes `Block.BlockConfig`, `Vm.GasCosts`, `Vm.StateGasCosts`, `Vm.VmLimits`, `Vm.STACK_DEPTH_LIMIT`, `Vm.PrecompileTable m` and each `EthPrecompiles` entry. It guarantees `config_wf` and the table law. Cross-module invariant: `EthVmRunner` receives the table **only** through `config.precompiles` (D17), so no instruction proof depends on precompile internals (ARCHITECTURE §5.2 isolation rule).

## 9. Open decisions

- **D3** (accepted): Amsterdam only. The previous fork contributes only the `PrevHeader` type in `EthBlock`.
- **D12**: the precompile deliverables are tracked in `EthPrecompiles`; this module only installs the table.
- **D13/D17**: `TerminationReady` is the gas-schedule hypothesis of the recursive runner.
- **D5** (provisional, broad): `executeBlock` is monad-parametric; the keccak-derived constants are `HashConsts`, forwarded from the caller under F20, not literals here.
- **D21** (accepted): no `@[csimp]` here; constants are plain definitions.
- Values in `EthFork`, types next to their semantics: resolved by DECISIONS B8 (Q1/Q26/Q43) and F8.

## 10. Gaps

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Fork activation is excluded** (CONTRACT §5). `forkCriteria` is unscheduled at the pin, and the guest never checks the payload timestamp against any activation. This is a deliberate exclusion that follows the reference, and the L1 consumer must supply activation/chain anchoring outside this guest.
- **EIP-7997 (deterministic factory)** is listed in `__init__.py:15` but has no code in the Amsterdam package [V, by grep]. There is no `apply_fork` irregularity and no predeploy insertion. The fixture area `eip7997_deterministic_factory_contract` (21) presumably relies on pre-state allocation [I, not checked].
- **The deposit contract address is mainnet-only.** Test chains use the same constant. This is not a parameter by chain id.
- **Transition fixtures** `for_bpo2toamsterdamattime15k`: pre-fork blocks are bpo2, which is not instantiated (D3). Their `blockchain_tests` form cannot be run in full by `EthConformance`, and the runnable subset is unlisted. The parent-header fallback decodes a bpo2 header as a bpo5 `PrevHeader`; the shapes are assumed identical [I, not checked for bpo2].
- **Runtime-patchable gas constants** in EELS (`gas.py:45, 70`): if a future release patches them, this module's values and `#guard`s must be regenerated. A prototype generator exists outside this repository but runs by hand and has no `--check` mode; promoting it to `scripts/` with a CI check is outstanding.
- The **minimum transaction encoding size** needed for law 3 is not established.
- **`TerminationReady`** is a placeholder: its exact statement depends on the unfinished fuel-adequacy investigation (ARCHITECTURE §5.5; [REVIEW §7](../REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks) G2–G7).
