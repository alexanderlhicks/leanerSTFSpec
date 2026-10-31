# `EthBlock`: block, transaction and receipt semantics; block execution

*Status: informal specification, draft. Date: 2026-10-31. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F2, F8, F14, F20 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D3, D5, D8, D14, D18, D22, D23, D24, D25, D26, D27 · questions: B1, B8 (Q1), B14 (Q2), Q3, Q8, Q9, Q53, Q54.*

Conventions. Line references are to `src/ethereum/forks/amsterdam/` unless another path is given. **[V]** means read in the pinned source; **[I]** means an inference that has not been checked by running code. EELS `Uint` is `Nat`; `U64`, `U256`, `U32` are the `EthBase` fixed-width types. In `ethereum-types` 0.4.1, fixed-width constructors, `+` and `*` **raise `OverflowError`** when out of range, and every unsigned `-` raises when the result would be negative (`ethereum_types/numeric.py:44–47, 103–128`) [V]. Nothing wraps unless it calls `wrapping_*`. Where such a raise is reachable, this spec names it as an explicit constructor (§2.12).

## 1. Purpose

`EthBlock` is layer L5 (ARCHITECTURE §2). It specifies the block-level types (headers, blocks, the five transaction types, receipts, logs, withdrawals, execution requests, block access lists), their signing and hashing, static and state-dependent transaction validity, header validation against the parent, and the block pipeline `executeBlock → applyBody → processTransaction`, including system calls, withdrawals, EIP-7685 requests, gas settlement and fee payment, receipts, the logs bloom, the transaction/receipt/withdrawal tries and the EIP-7928 block access list (BAL). It provides the seam `executeBlock {m} [Monad m] [KeccakQuery m] : … → PreState m → … → m (CheckedResult BlockError BlockDiff)` (§5), run in `BlockM m := CheckedT BlockError m` (F14; `CheckedT` is owned by `EthVmRunner`). Under the broad D5 scope every keccak here (signing and transaction hashes, sender addresses, the parent-header hash, the bloom, the BAL hash, the transaction/receipt/withdrawal trie roots and `emptyOmmerHash`) goes through `KeccakQuery`; the public entry point (`EthStateless`, via `EthFork`) uses `m := Id`. It is **fork-parametric**: every Amsterdam constant it needs arrives in a `BlockConfig` record (§5). `EthFork` supplies the Amsterdam value and the precompile table. It also defines the generic `stateTransition` over a state carrier, which `EthConformance` instantiates with the full-state backend for `blockchain_tests`.

## 2. Requirements

Each requirement has an identifier (R-…) so that tests and proofs can cite it. "Raises X" means the spec returns `.error` with the constructor listed in §5 for X. The first failing check decides the error (CONTRACT §4, failure precedence), so **check order is normative**.

### 2.1 Types and codecs

- **R-HDR.** `Header` must have the 23 Amsterdam fields, in RLP order (`blocks.py:72–270`): `parentHash`, `ommersHash`, `coinbase`, `stateRoot`, `transactionsRoot`, `receiptRoot`, `bloom : Bloom`, `difficulty : Nat`, `number : Nat`, `gasLimit : Nat`, `gasUsed : Nat`, `timestamp : U256`, `extraData : Bytes`, `prevRandao : Bytes32`, `nonce : Bytes8`, `baseFeePerGas : Nat`, `withdrawalsRoot`, `blobGasUsed : U64`, `excessBlobGas : U64`, `parentBeaconBlockRoot`, `requestsHash : Hash32`, `blockAccessListHash : Hash32` (EIP-7928), `slotNumber : U64` (EIP-7843). `PrevHeader` (bpo5, `forks/bpo5/blocks.py:71`) is the first 21 of these fields [V, by `diff`]. `ParentHeader := amsterdam Header | bpo5 PrevHeader` carries the parent everywhere EELS types `Header | PreviousForkHeader` (`fork.py:163, 450`). Its `rlp` must re-encode the variant it came from, because `validateHeader` hashes it (`fork.py:501`).
- **R-BLK.** `Block = {header, transactions : Array BlockTx, ommers : Array Header, withdrawals : Array Withdrawal}` (`blocks.py:276`). `BlockTx := legacy LegacyTransaction | typed Bytes` mirrors `Tuple[Bytes | LegacyTransaction, …]`. `Withdrawal = {index : U64, validatorIndex : U64, address, amount : U64}` (Gwei) (`blocks.py:38`).
- **R-TX.** The five transaction structures must have exactly the EELS fields in RLP order (`transactions.py:94–495`). Type-specific points: `LegacyTransaction.v : U256`, and the typed variants have `yParity : U256`. `BlobTransaction.to` and `SetCodeTransaction.to` are `Address`, not optional, while the other variants have `to : Option Address` for `Bytes0 | Address`. `SetCodeTransaction.nonce : U64` whereas the other four are `U256`. `SetCodeTransaction.authorizations : Array Authorization`, with `Authorization = {chainId : U256, address, nonce : U64, yParity : U8, r s : U256}` taken from `EthBase` (`fork_types.py:87`, owned by G1).
- **R-TX-ENC.** `encodeTransaction` (`transactions.py:540`): legacy is returned as the structure (RLP-encoded where bytes are needed); type *k* ∈ {1,2,3,4} is `[k] ++ rlp tx`.
- **R-TX-DEC.** `decodeTransaction` (`:562`) on `typed b`: `b[0] ∈ {1,2,3,4}` decodes `b[1:]` as that type; `0xC0 ≤ b[0] ≤ 0xFE` decodes the whole of `b` as legacy; any other first byte in `0x00…0xBF` raises `TransactionTypeError b[0]`. Two branches are not EthereumExceptions: `b[0] = 0xFF` fails an `assert` (`:584`), and `b = []` fails with `IndexError` (`tx[0]`). The spec gives both explicit constructors (`BlockError.txDecode`) [V]. An RLP failure inside a typed payload (`rlp.DecodingError`, not an EthereumException) is also `txDecode`. **Scope of these errors.** On the complete guest path, an empty transaction is rejected first at `execution_engine/new_payload.py:112` (O6), and every other deterministic payload-transaction decode failure is consumed by `is_valid_versioned_hashes` (`new_payload.py:60–68`), which returns `False` and so gives O6 before `execute_block` runs; legacy payload bytes are also pre-decoded when the block is built (`validation_helpers.py:88–97`, G6). A **standalone** `executeBlock` (for example `blockchain_tests` through `stateTransition`) still raises its own decode errors (`TransactionTypeError` was reproduced), so the `txDecode` constructors are live and must not be removed. A host-resource failure (`RecursionError`, `MemoryError`) during `execute_block`'s repeated decode (`fork.py:873`) is not excluded by the first decode's success; it belongs to O12/DISC-001, not here.
- **R-RCPT.** `Receipt = {succeeded : Bool, cumulativeGasUsed : Nat, bloom, logs : Array Log}` and `Log = {address, topics : Array Hash32, data}` (`blocks.py:330, 363`). `encodeReceipt tx r` (`:394`) is `[k] ++ rlp r` for a typed transaction of type *k*, and the bare structure for legacy. `decodeReceipt` (`:417`) is needed only by `parseDepositRequests`, on receipts this module produced.
- **R-HASH.** `getTransactionHash` is `keccak (rlp tx)` for legacy and `keccak bytes` for typed (`:1175`). The six signing hashes (`:1015–1172`) must hash exactly these tuples:
  - pre-155: `(nonce, gasPrice, gas, to, value, data)`;
  - EIP-155: that tuple plus `(chainId, 0, 0)`;
  - EIP-2930: `0x01 ++ rlp (chainId, nonce, gasPrice, gas, to, value, data, accessList)`;
  - EIP-1559: `0x02 ++ …` with `maxPriorityFeePerGas, maxFeePerGas` in place of `gasPrice`;
  - EIP-4844: the 1559 tuple plus `(maxFeePerBlobGas, blobVersionedHashes)` under `0x03`;
  - EIP-7702: the 1559 tuple plus `authorizations` under `0x04`.

### 2.2 Signatures and senders

- **R-SIG.** `signatureRecoveryParameters chainId tx` (`:944`). It raises `invalidSignature` unless `0 < r < SECP256K1N` and `0 < s ≤ SECP256K1N / 2`. For legacy, `v ∈ {27, 28}` gives recovery id `v − 27` over `signingHashPre155`; otherwise `v` must equal `35 + 2c` or `36 + 2c`, where *c* is the **`chainId` argument**, giving id `v − 35 − 2c` over `signingHash155 tx c`. For typed transactions, `yParity ∈ {0, 1}` is required, over the type's signing hash. `recoverTransactionPublicKey` returns `0x04 ++ secp256k1Recover r s id h` (65 bytes). A failed recovery raises `invalidSignature` (`crypto/elliptic_curve.py:54, 74`; G2).
- **R-SENDER.** `recoverSender tx` (`:883`) uses `chainId tx` (0 when that is `none`), then `senderAddress pk = keccak(pk[1:])[12:32]` (`:937`).
- **R-HINT (O5).** When `publicKeys = some ks`, `checkTransaction` uses `recoverSenderFromPublicKey blockEnv.chainId tx ks[i]` (`fork.py:563–574`). It raises `invalidSignature` unless `ks[i]` **equals** the recovered key (`transactions.py:932`); any cheaper check must be equivalent on every input (CONTRACT §2). The count check comes earlier, in `executeBlock` (R-EB step 2).
- **R-CHAINID.** `chainId tx` (`:865`). For legacy: `v ∈ {27, 28}` gives `none`; `v < 35` raises `invalidSignature "bad v"`; otherwise it is `U64((v − 35) >> 1)`, which **raises `OverflowError` when the value is ≥ 2⁶⁴** [V, from the `U64` constructor]. The spec names this `BlockError.arith .chainIdOverflow`. Typed transactions return `tx.chainId`.

### 2.3 Intrinsic gas (R-IG, `calculate_intrinsic_cost`, `transactions.py:692–801`)

With `tokens(d) = zeros(d) + 4·nonzeros(d)` (`:804`) and the gas constants from `cfg.gas` (G4's `GasCosts`; Amsterdam values in brackets):

- `recipient` is `CREATE_ACCESS` [12000] for a creation (`to = none`); `COLD_ACCOUNT_ACCESS` [3000] plus `TX_VALUE_COST` [6000] if `value > 0` for a call with `to ≠ sender`; and **0 for a self-transfer** (`to = some sender`) (EIP-2780).
- `initCode = init_code_cost(len data)` for a creation, else 0.
- `dataCost = tokens(data) · TX_DATA_TOKEN_STANDARD` [4].
- `alCost = Σ_access (TX_ACCESS_LIST_ADDRESS [2900] + |slots| · TX_ACCESS_LIST_STORAGE_KEY [2000])`, and `alTokens = Σ (80 + 128·|slots|)` (EIP-7981, `cfg.tx`). Then `alData = alTokens · TX_DATA_TOKEN_FLOOR` [16]. Only transaction types 1–4 have access lists (`has_access_list`, `:1191`).
- `authCost = EXECUTION_PER_AUTH_BASE_COST [7816] · |authorizations|` (type 4 only).
- `base = TX_BASE [12000] + recipient`.
- **`execution = base + initCode + dataCost + alCost + alData + authCost`**.
- **`calldataFloor = base + len(data) · 4 · 16 + alData`** (EIP-7623 floor; EIP-7976 counts every byte as 4 tokens). The floor excludes `initCode` and `authCost`.

The state-dependent parts (new-account state gas, delegation writes) are charged in the top frame (G4), not here.

### 2.4 Static validity (R-VT, `validate_transaction`, `:592–689`), in order

1. `U256(nonce) ≥ 2⁶⁴ − 1` raises `nonceOverflow`.
2. A creation with `len data > MAX_INIT_CODE_SIZE` [131072] (`vm/interpreter.py`) raises `initCodeTooLarge`.
3. `gas > TX_MAX_TOTAL_GAS_LIMIT` [2³² − 1] raises `transactionGasLimitExceeded`.
4. For types 2–4, `maxFeePerGas < maxPriorityFeePerGas` raises `priorityFeeGreaterThanMaxFee`.
5. For type 3: `|hashes| = 0` raises `noBlobData`; `|hashes| > cfg.tx.blobCountLimit` [6] raises `blobCountExceeded`; any hash with first byte `≠ 0x01` raises `invalidBlobVersionedHash` (first failure in list order).
6. For types 3 and 4, a missing `to` raises `transactionTypeContractCreation`. [I] This is unreachable from decoding, because `to : Address` cannot decode from `0x80`, but it is kept for fidelity.
7. For type 4, an empty authorization list raises `emptyAuthorizationList`. EELS uses `not any(auths)`; an `Authorization` is always truthy [V, run at pin], so this means `auths = []`.
8. Four checks raise `insufficientTransactionGas` (in order, one constructor argument per reason): `execution > gas`; `calldataFloor > gas`; `execution > TX_MAX_GAS_LIMIT` [2²⁴]; `calldataFloor > TX_MAX_GAS_LIMIT`.

It returns `IntrinsicGasCost`.

### 2.5 Inclusion checks (R-CT, `check_transaction`, `fork.py:506–666`), in order

1. The sender, from R-HINT or R-SENDER.
2. `validateTransaction tx sender`.
3. A fresh `TxState` over the block state (`EthState`).
4. `check_block_gas_capacity` (`vm/gas.py:1053`, G4, consumed). With `L = header.gasLimit`: `min(TX_MAX_GAS_LIMIT, gas) > L − blockGasUsed` raises `gasUsedExceedsLimit .execution`; `gas > L − blockStateGasUsed` raises `gasUsedExceedsLimit .state`; `blobGas > MAX_BLOB_GAS_PER_BLOCK [2 752 512] − blobGasUsed` raises `blobGasLimitExceeded`.
5. `getAccount sender`. This is an observed read, and it can fail with `WitnessError` (O4).
6. `calculateEffectiveGasPrice` (`transactions.py:816`). For types 2–4, `maxFeePerGas < baseFee` raises `insufficientMaxFeePerGas maxFee baseFee`, and otherwise the price is `baseFee + min(maxPriority, maxFee − baseFee)`. For types 0 and 1, `gasPrice < baseFee` raises **plain `InvalidBlock`** (`:841`); this is `BlockError.gasPriceBelowBaseFee`, not a `TxError`, although EEST may label it as a transaction exception (Gaps).
7. `maxGasFee = gas · (maxFeePerGas | gasPrice)`. For type 3, `check_max_fee_per_blob_gas` (`gas.py:1016`) raises `insufficientMaxFeePerBlobGas` if `maxFeePerBlobGas < blobGasPrice(header.excessBlobGas)`; then `maxGasFee += blobGas · maxFeePerBlobGas`.
8. `checkNonce` (`:855`): an account nonce greater than the transaction's raises `nonceMismatch .tooLow`, and a smaller one raises `.tooHigh`.
9. `balance < maxGasFee + value` raises `insufficientBalance`.
10. `getCode` of the sender (observed code read; may fail with O4). If `codeHash ≠ EMPTY_CODE_HASH` and the code is not a valid EIP-7702 delegation (`vm/eoa_delegation.py:42`), it raises `invalidSender` (EIP-3607).
11. `allocate_evm_gas` (`gas.py:1120`); the access-list address and slot sets; `authorizations`. For a creation, `recipient = compute_contract_address sender account.nonce`. `accountsWithPaidWrites = {sender} ∪ ({recipient} if creation or value > 0)`. `txHash = keccak(encode tx)`. The result is `TransactionEnvironment` (G4 type).

### 2.6 Header validation (R-VH, `validate_header`, `fork.py:449–503`), in order

1. `number < 1` raises `header .numberZero`.
2. `excessBlobGas ≠ calculate_excess_blob_gas parent` (`gas.py:901`) raises `header .excessBlobGas`. The helper reads `excessBlobGas`, `blobGasUsed` and `baseFeePerGas` from **either** parent variant. Its U64 arithmetic (`excess + used`, `used · (MAX − TARGET)`) can raise `OverflowError` on an adversarial parent, which is `BlockError.arith .excessBlobGasOverflow`. Its `calculate_blob_gas_price` is a Taylor series whose cost grows with `excess` (see Gaps).
3. `gasUsed > gasLimit` raises `header .gasUsedExceedsGasLimit`.
4. `calculateBaseFeePerGas gasLimit parent.gasLimit parent.gasUsed parent.baseFee` (`:386`). It **first** calls `checkGasLimit` (`:1164`), which raises `header .gasLimit` unless `parent − parent/1024 < gasLimit < parent + parent/1024` and `gasLimit ≥ 5000`. Then, with `target = parent.gasLimit / 2`: equal usage leaves the fee unchanged; above target, the fee rises by `max(1, baseFee·Δ/target/8)`; below target, it falls by `baseFee·Δ/target/8`. A mismatch raises `header .baseFee`.
5. `timestamp ≤ parent.timestamp` raises `header .timestamp`.
6. `number ≠ parent.number + 1` raises `header .number`.
7. `len extraData > 32` raises `header .extraData`.
8. `difficulty ≠ 0` raises `header .difficulty`; `nonce ≠ 0⁸` raises `header .nonce`; `ommersHash ≠ EMPTY_OMMER_HASH` (`= keccak(rlp [])`, a `HashConsts` field) raises `header .ommersHash`.
9. `parentHash ≠ keccak(rlp parent)` raises `header .parentHash`, with the hash queried through `KeccakQuery` (D5). This is the CONTRACT §7 anchor.

`validateHeader` checks nothing else (Gaps: slot number, fork activation, timestamp upper bound).

### 2.7 Block execution (R-EB, `execute_block`, `fork.py:281–383`), in order

`executeBlock cfg consts` is the kernel: its caller supplies the constants record (F20), and the kernel neither calls `HashConsts.query` nor uses literals. `executeBlockStandalone` calls `HashConsts.query` once on entry, builds the pre-state with `mkPre consts`, then runs steps 1–10 below. The provider factory must use that same record and oracle interpretation. Each wrapper run acquires independently, without caching the record. A run that fails in steps 1–4 has still made the constant queries and called its factory.

`stateTransition cfg toPre apply chain block` first derives the parent header and block hashes, then calls `executeBlockStandalone` with the provider factory `fun consts ↦ pure (toPre chain.state consts)` and `none` for the public-key hint.

1. `len (rlp block) > cfg.block.maxRlpBlockSize` [8 388 608] raises `rlpSizeExceeded` (EIP-7934).
2. `publicKeys = some ks ∧ |ks| ≠ |txs|` raises `publicKeyCountMismatch` (O5).
3. `validateHeader cfg consts ctx.parentHeader header`.
4. `ommers ≠ []` raises `ommersNotEmpty`.
5. Build the `BlockState` over `preState` and `consts` (`BlockState` carries them), and the `BlockEnvironment` from the header fields, a fresh `BalBuilder` and `publicKeys`.
6. `applyBody`.
7. `diff := extractBlockDiff`; `stateRoot := preState.stateRoot diff` (O4 errors propagate here, **before any root comparison**).
8. Compute the transaction root, receipt root, bloom, withdrawals root, requests hash and BAL hash.
9. Compare, in this order: `max(blockGasUsed, blockStateGasUsed) ≠ gasUsed` (EIP-7778/8037); `transactionsRoot`; `stateRoot`; `receiptRoot`; `bloom`; `withdrawalsRoot`; `blobGasUsed`; `requestsHash`; `blockAccessListHash`. Each has its own `…Mismatch` constructor.
10. Return `diff`.

### 2.8 Body (R-AB, `apply_body`, `:825–898`), in order

1. `processUncheckedSystemTransaction beaconRoots parentBeaconBlockRoot` (EIP-4788), at BAL index 0.
2. `processUncheckedSystemTransaction historyStorage blockHashes.last` (EIP-2935). An empty `blockHashes` is `IndexError` in EELS; the spec names it `missingParentHash`. It is unreachable on the guest path, where O3a precedes it.
3. `trackAncestorAccess state 1` (`state_tracker.py:925`).
4. For each `i`, **decode transaction `i` lazily and then process it**. EELS uses `map`, so a decode failure of transaction `i` occurs after transactions `< i` have executed.
5. Set the BAL index to `n + 1`.
6. `processWithdrawals`.
7. `processGeneralPurposeRequests`.
8. `bal := buildBlockAccessList builder blockState`.
9. `validateBlockAccessListGasLimit bal header.gasLimit`.

**System calls** (`:706–822`). An unchecked call runs `process_top_level` with `origin = cfg.system.systemAddress` (source `SYSTEM_ADDRESS`, F8), value 0, `gasLimit = executionGrant = cfg.system.txGas` [30 M], state reservoir `STORAGE_SET · 16` [97 920 · 16], zero floor, no access lists, no paid writes, `effectiveGasPrice = baseFee`, `indexInBlock = txHash = none`. It invokes `processTopLevelChecked cfg.runnerEnv`, supplying the same configured address to the emitter context for system and user calls (F8). It then incorporates its state into the block (BAL update, then merge). No gas is added to block counters; no nonce is changed and no fee is charged. A checked call first reads the target's code through a throwaway, never-incorporated `TxState`, so that code deployed earlier in the same block is visible (`:730–743`). Empty code raises `systemContractNoCode addr`. It then makes the unchecked call, and any frame error raises `systemContractFailed addr`.

### 2.9 Transaction processing (R-PT, `process_transaction`, `:1050–1139`), in order

1. The BAL index is set to `i + 1`.
2. `trieSet txTrie (rlp i) (encode tx)`.
3. `chainId tx`; a mismatch raises `wrongChainId expected actual`.
4. `checkTransaction`.
5. `updateSenderState` (`:970`): the nonce is incremented and `balance := balance − gas·effectivePrice − blobFee`, where `blobFee = blobGas · blobGasPrice(excess)`. The **actual** blob price is charged, not the cap.
6. `processTopLevelChecked cfg.runnerEnv` (G4 runner, with the precompile table, three-field VmConfig and `cfg.system.systemAddress`, F8).
7. `settle_transaction_gas` (`gas.py:1178`, G4): `before = gas − gasLeft − stateGasLeft`; `refund = min(before / 5, refundCounter)`; `gasUsed = max(before − refund, floor)`; `stateUsed = max(0, stateGasUsed)`; `execUsed = max(before − stateUsed, floor)`; `gasLeft' = gas − gasUsed`.
8. `disburseGasFees` (`:1011`): `createEther origin (gasLeft' · price)` and then `createEther coinbase (gasUsed · (price − baseFee))`. Both are applied even when the amount is 0. [I] This is a touch whose BAL/state effect is `EthState`'s `create_ether` contract.
9. `blockGasUsed += execUsed` (pre-refund, EIP-7778); `blockStateGasUsed += stateUsed`; `blobGasUsed += blobGas`; `cumulativeGasUsed += gasUsed` (post-refund).
10. `receipt := encodeReceipt tx {succeeded := error = none, cumulativeGasUsed, logsBloom logs, logs}`; `trieSet receiptTrie (rlp i) receipt`; append the receipt key.
11. `blockLogs ++= logs`.
12. Each address in `accountsToDelete` gets `clearAccountPreservingBalance` (EIP-6780/8246).
13. `updateBuilderFromTx`, then `incorporateTxIntoBlock` (§8 seam; this order is required).

### 2.10 Withdrawals, requests, bloom, tries

- **R-WD** (`:1142–1161`). One `TxState` covers all withdrawals. For each `i`, `trieSet wdTrie (rlp i) (rlp wd)` and `createEther wd.address (amount · 10⁹)`. Then incorporate once, at BAL index `n + 1`.
- **R-RQ** (EIP-7685, `:901–967`; `requests.py`). The requests are built in ascending type order:
  1. deposits: scan the receipts **in the recorded receipt_keys order (transaction order, not sorted RLP keys)**, decoding each, for logs whose `address = cfg.system.depositContract` and whose `topics[0] = DEPOSIT_EVENT_SIGNATURE_HASH`. Each such log gives `extractDepositData data`, and the results are concatenated. They are appended as `0x00 ++ concat` only if non-empty;
  2. four checked system calls with empty calldata: withdrawal requests `0x01` (EIP-7002), consolidations `0x02` (EIP-7251), builder deposits `0x03` and builder exits `0x04` (**EIP-8282, present at the pin**). Each appends `type ++ returnData` if the return data is non-empty.

  `extractDepositData` (`requests.py:170`) raises `deposit .length` unless `len = 576`. Then it checks the five head offsets against `160, 256, 320, 384, 512` and the five length words against `48, 32, 8, 96, 8`, in that order, each with its own `deposit` constructor. It returns `pubkey ++ wc ++ amount ++ sig ++ index` (192 bytes). `computeRequestsHash rs = sha256 (concat (map sha256 rs))` (`:307–328`), using every complete 32-byte inner digest in supplied list order. The standalone hash does not filter, sort, deduplicate or validate request prefixes; those production rules belong to the caller. Empty requests are retained. The existing pure `EthHash.sha256` provider applies; D5 adds no SHA query effect. All finite inputs use Q46's total extension; source/FIPS agreement separately requires every inner `8 * request.size < 2^64` and outer `8 * (32 * rs.length) < 2^64`, plus host/API premises, with no new runtime guard.
- **R-BLOOM** (`bloom.py:29–87`). For each log, add its address and then each topic. For each entry `h = keccak e` and each `j ∈ {0, 2, 4}`: `b = be16(h[j..j+2]) & 0x7FF`, then set bit `7 − (i mod 8)` of byte `i / 8`, where `i = 0x7FF − b`.
- **R-TRIE.** Transaction, receipt and withdrawal roots are the **unsecured** MPT roots (`EthCommit`) of `rlp i ↦ value`. All three source tries have default `None` (`vm/__init__.py:107–117`), distinct from empty Bytes. EthBlock owns the Q53 value interpretations: `encodeTransaction` leaves legacy records for one RLP encoding and returns typed envelopes as Bytes (`transactions.py:540–559`); receipts likewise use legacy records or typed Bytes (`blocks.py:394–414`, `fork.py:669–703,1119–1130`); withdrawals actually enter the trie as already-RLP Bytes (`fork.py:1152–1157`). C10 returns every actual Bytes value unchanged, including typed envelopes and withdrawal encodings, so no extra RLP layer is added. Dense arrays (§5–§6) store these final encodings once. Their root composition uses EthCommit's existing `root`/`mathRoot` with the stored context's F20 empty root; typed calls supply lawful byte keys, `secured = false` and stored-value `PrepareSafe` (Q53), not just default inequality.

### 2.11 Block access list (R-BAL, EIP-7928, `block_access_lists.py`)

- **Builder updates** (`update_builder_from_tx`, `:765`). They run once per incorporation, at the current index `idx`: index 0 for the system calls, `i + 1` for transaction `i`, and `n + 1` for withdrawals and request calls. Several incorporations can share an index. The pre-value for an `(idx, address)` or `(idx, address, slot)` is memoised at its **first** use in that index (`:727–762`). It comes from the block state *before* merging: account writes, then pre-state; storage writes, then storage clears (giving 0), then pre-state (`:690–724`). For every account written in the transaction:
  - balance, nonce and code hash are compared with that pre-value (an absent account has balance 0, nonce 0 and the empty code hash);
  - if one differs, `add…Change` is called with the post-value. **Balance and code keep the last value in the index; nonce keeps the maximum** (`:463`). Code is fetched through `getCode` (observed read);
  - if one is equal, `remove…Change` is called for that index.
  
  For every storage write, the slot is converted to `U256` from big-endian. If the value differs from the pre-value, `addStorageWrite` is called; otherwise `removeStorageWrite`, which deletes the slot's entry when it becomes empty (`:539`).
- **Build** (`:831`). Add every block-level storage read (`addStorageRead`), then every account read as touched. Then `build` (`:625`). Each account has storage changes sorted by slot, each slot's changes sorted by index, **storage reads minus written slots** sorted ascending, and balance, nonce and code changes each sorted by index. Accounts are sorted by address, compared as bytes, lexicographically.
- **Hash**: `keccak (rlp bal)` (`:854`). **Gas limit** (`:863`): `Σ_accounts (1 + |writtenSlots ∪ readSlots|) > gasLimit / BLOCK_ACCESS_LIST_ITEM [2000]` raises `balGasLimitExceeded`.
- The BAL is **checked only through its hash** against `header.blockAccessListHash`. On the stateless path, that hash is `keccak(payload.block_access_list)` (`execution_engine/validation_helpers.py:79`, G6). EELS never decodes the supplied BAL.

### 2.12 Failure mapping

Classification follows the first reference handler that consumes the failure (D14; CONTRACT §4):
- **Admission.** Every `InvalidTransaction` raised by admission (R-VT, R-CT, R-PT 3) is fatal to the block (`BlockError.invalidTransaction i e`): O7.
- **Invalid block.** Every `InvalidBlock` raise site is its own `BlockError` constructor: O6.
- **Transaction decoding** (`BlockError.txDecode`, R-TX-DEC): on the guest path every deterministic decode failure is consumed earlier and is O6; on a standalone `executeBlock` the constructors are live (scope in R-TX-DEC).
- **Frames.** Reverts and halts are data (O8/O9), never errors.
- **Witness.** `WitnessError` from `PreState` lookups or the root is `BlockError.witness` (O4, D8).
- **Deterministic Python runtime faults** raised during block execution and consumed by the inner catch-all (`OverflowError`, `IndexError`, `AssertionError`) are **CONTRACT O13** members: the output is the existing `(root, false, chain_id, 0x1501)`, and each reachable site has its own named constructor: `arith .chainIdOverflow` (`transactions.py:878`, probe-witnessed), `arith .excessBlobGasOverflow` (`vm/gas.py:931, 945`, argued reachable), `state .balanceOverflow` (`state_tracker.py:663, 687`, argued reachable), and, through `vmFault`, `ancestorHashUnavailable` (`vm/instructions/block.py:58`, fixture-witnessed) and `u256Overflow .blobBaseFee` (`vm/instructions/environment.py:607`, argued reachable). `missingParentHash` is unreachable on the guest path (O3a precedes it) but live for a standalone `executeBlock`. There is no catch-all constructor; an unlisted site is a gap (B14).
- **Host resources** (`RecursionError`, `MemoryError`) are O12, not O13, and remain unresolved (DISC-001).

**Pinned blob final-addition bound.** In EELS `vm/gas.py:931–945`, let `x` and `y` be the U64 parent excess and used gas. A successful initial sum gives `x + y < 2^64`. At the pinned schedule, `21 − 14 = 7`; after the checked product succeeds, `floor(7*y/21) ≤ y`, so `x + floor(7*y/21) ≤ x + y < 2^64`. The final addition at `:944` therefore cannot itself overflow after that successful prefix. The initial sum at `:931` and the intermediate product at `:945` can still overflow, and the product is checked before division.

## 3. EELS source map

Parameter constants of `fork.py`, `transactions.py` and `requests.py`, together with `apply_fork` and `FORK_CRITERIA`, are claimed by `EthFork` (their Amsterdam values); `EthBlock` consumes them through `BlockConfig`. The exception classes of `forks/amsterdam/exceptions.py` and the shared `exceptions.py` become `TxError`/`BlockError` constructors (§5).

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `forks/amsterdam/fork.py::EMPTY_OMMER_HASH` | 116 | `HashConsts.emptyOmmerHash` (`EthBase`) | `keccak256 (rlp [])`, supplied by the caller under F20 (D5, F2); the literal `1dcc4de8…9347` (computed at pin) is its `Id` value, checked by `#guard` |
| `forks/amsterdam/fork.py::GWEI_TO_WEI` | 127 | `gweiToWei` | 10^9; withdrawal amounts |
| `forks/amsterdam/fork.py::ChainContext` | 152 | `ChainContext` | `parentHeader : ParentHeader` |
| `forks/amsterdam/fork.py::BlockChain` | 169 | `BlockChain σ` | generic over the state carrier (§6) |
| `forks/amsterdam/fork.py::get_last_256_block_hashes` | 202 | `getLast256BlockHashes` | ≤256 hashes, oldest first; `[]` for an empty chain |
| `forks/amsterdam/fork.py::state_transition` | 242 | `stateTransition` | full-state path only (blockchain_tests) |
| `forks/amsterdam/fork.py::execute_block` | 281 | `executeBlock` | the seam; check order R-EB |
| `forks/amsterdam/fork.py::calculate_base_fee_per_gas` | 386 | `calculateBaseFeePerGas` | raises `gasLimit` via `check_gas_limit` first |
| `forks/amsterdam/fork.py::validate_header` | 449 | `validateHeader` | 12 checks, order R-VH |
| `forks/amsterdam/fork.py::check_transaction` | 506 | `checkTransaction` | order R-CT |
| `forks/amsterdam/fork.py::make_receipt` | 669 | `makeReceipt` |  |
| `forks/amsterdam/fork.py::process_checked_system_transaction` | 706 | `processCheckedSystemTransaction` | no-code / failure ⇒ `BlockError` |
| `forks/amsterdam/fork.py::process_unchecked_system_transaction` | 766 | `processUncheckedSystemTransaction` | errors ignored |
| `forks/amsterdam/fork.py::apply_body` | 825 | `applyBody` | order R-AB |
| `forks/amsterdam/fork.py::process_general_purpose_requests` | 901 | `processGeneralPurposeRequests` | EIP-7685 + EIP-8282 |
| `forks/amsterdam/fork.py::update_sender_state` | 970 | `updateSenderState` |  |
| `forks/amsterdam/fork.py::disburse_gas_fees` | 1011 | `disburseGasFees` |  |
| `forks/amsterdam/fork.py::process_transaction` | 1050 | `processTransaction` | order R-PT |
| `forks/amsterdam/fork.py::process_withdrawals` | 1142 | `processWithdrawals` |  |
| `forks/amsterdam/fork.py::check_gas_limit` | 1164 | `checkGasLimit` | Bool |
| `forks/amsterdam/blocks.py::Withdrawal` | 38 | `Withdrawal` | SSZ container in Amsterdam, plain in bpo5; field order is the RLP order |
| `forks/amsterdam/blocks.py::Header` | 72 | `Header` / `PrevHeader` | 23 fields (Amsterdam) / 21 (bpo5) |
| `forks/amsterdam/blocks.py::Block` | 276 | `Block` | `transactions : Array BlockTx` |
| `forks/amsterdam/blocks.py::Log` | 330 | `Log` |  |
| `forks/amsterdam/blocks.py::Receipt` | 363 | `Receipt` |  |
| `forks/amsterdam/blocks.py::encode_receipt` | 394 | `encodeReceipt` | type-prefixed except legacy |
| `forks/amsterdam/blocks.py::decode_receipt` | 417 | `decodeReceipt` | only on self-encoded receipts |
| `forks/bpo5/blocks.py::Withdrawal` | 37 | — | unused: only the bpo5 `Header` is decoded (`stateless.py:237`) |
| `forks/bpo5/blocks.py::Header` | 71 | `PrevHeader` | bpo5 header: Amsterdam minus `blockAccessListHash`, `slotNumber`; parent only |
| `forks/bpo5/blocks.py::Block` | 253 | — | unused: only the bpo5 `Header` is decoded (`stateless.py:237`) |
| `forks/bpo5/blocks.py::Log` | 307 | — | unused: only the bpo5 `Header` is decoded (`stateless.py:237`) |
| `forks/bpo5/blocks.py::Receipt` | 340 | — | unused: only the bpo5 `Header` is decoded (`stateless.py:237`) |
| `forks/bpo5/blocks.py::encode_receipt` | 370 | — | unused: only the bpo5 `Header` is decoded (`stateless.py:237`) |
| `forks/bpo5/blocks.py::decode_receipt` | 393 | — | unused: only the bpo5 `Header` is decoded (`stateless.py:237`) |
| `forks/amsterdam/transactions.py::IntrinsicGasCost` | 46 | `IntrinsicGasCost` | `execution`, `calldataFloor` |
| `forks/amsterdam/transactions.py::SECP256K1_UNCOMPRESSED_PUBLIC_KEY_PREFIX` | 62 | `secp256k1UncompressedPrefix` | `0x04` |
| `forks/amsterdam/transactions.py::VERSIONED_HASH_VERSION_KZG` | 69 | `versionedHashVersionKzg` | `0x01` |
| `forks/amsterdam/transactions.py::LegacyTransaction` | 94 | `LegacyTransaction` | type 0 |
| `forks/amsterdam/transactions.py::Access` | 157 | `Access` |  |
| `forks/amsterdam/transactions.py::AccessListTransaction` | 177 | `AccessListTransaction` | type 1 |
| `forks/amsterdam/transactions.py::FeeMarketTransaction` | 250 | `FeeMarketTransaction` | type 2 |
| `forks/amsterdam/transactions.py::BlobTransaction` | 328 | `BlobTransaction` | type 3; `to : Address` |
| `forks/amsterdam/transactions.py::SetCodeTransaction` | 417 | `SetCodeTransaction` | type 4; `nonce : U64` |
| `forks/amsterdam/transactions.py::encode_transaction` | 540 | `encodeTransaction` |  |
| `forks/amsterdam/transactions.py::decode_transaction` | 562 | `decodeTransaction` | R-TX-DEC |
| `forks/amsterdam/transactions.py::validate_transaction` | 592 | `validateTransaction` | order R-VT |
| `forks/amsterdam/transactions.py::calculate_intrinsic_cost` | 692 | `calculateIntrinsicCost` | R-IG |
| `forks/amsterdam/transactions.py::count_tokens_in_data` | 804–814 | `countTokensInData : ByteArray → Nat` | Supplied on every finite input; whole result law and validation below |
| `forks/amsterdam/transactions.py::calculate_effective_gas_price` | 816 | `calculateEffectiveGasPrice` | legacy/2930 below base fee ⇒ `BlockError`, not `TxError` |
| `forks/amsterdam/transactions.py::calculate_max_gas_fee` | 845 | `calculateMaxGasFee` |  |
| `forks/amsterdam/transactions.py::check_nonce` | 855 | `checkNonce` |  |
| `forks/amsterdam/transactions.py::chain_id` | 865 | `chainId` | may overflow U64 (Gaps) |
| `forks/amsterdam/transactions.py::recover_sender` | 883 | `recoverSender` |  |
| `forks/amsterdam/transactions.py::recover_transaction_public_key` | 903 | `recoverTransactionPublicKey` | 65 bytes |
| `forks/amsterdam/transactions.py::recover_sender_from_public_key` | 916 | `recoverSenderFromPublicKey` | hint check, O5 |
| `forks/amsterdam/transactions.py::_sender_address_from_public_key` | 937 | `senderAddressFromPublicKey` | internal |
| `forks/amsterdam/transactions.py::_signature_recovery_parameters` | 944 | `signatureRecoveryParameters` | internal |
| `forks/amsterdam/transactions.py::signing_hash_pre155` | 1015 | `signingHashPre155` |  |
| `forks/amsterdam/transactions.py::signing_hash_155` | 1039 | `signingHash155` |  |
| `forks/amsterdam/transactions.py::signing_hash_2930` | 1065 | `signingHash2930` |  |
| `forks/amsterdam/transactions.py::signing_hash_1559` | 1091 | `signingHash1559` |  |
| `forks/amsterdam/transactions.py::signing_hash_4844` | 1118 | `signingHash4844` |  |
| `forks/amsterdam/transactions.py::signing_hash_7702` | 1147 | `signingHash7702` |  |
| `forks/amsterdam/transactions.py::get_transaction_hash` | 1175 | `getTransactionHash` |  |
| `forks/amsterdam/transactions.py::has_access_list` | 1191 | `hasAccessList` |  |
| `forks/amsterdam/bloom.py::add_to_bloom` | 29 | private `addToBloom` in `LogsBloom.lean` | packed 256-byte builder; full ordinary refinement below |
| `forks/amsterdam/bloom.py::logs_bloom` | 62 | `logsBloom` | complete generic action, empty and sequential-append laws supplied below |
| `forks/amsterdam/requests.py::DEPOSIT_EVENT_SIGNATURE_HASH` | 60 | `depositEventSignatureHash` |  |
| `forks/amsterdam/requests.py::DEPOSIT_REQUEST_TYPE` | 71 | `RequestType.deposit` | 0x00 |
| `forks/amsterdam/requests.py::WITHDRAWAL_REQUEST_TYPE` | 78 | `RequestType.withdrawal` | 0x01 |
| `forks/amsterdam/requests.py::CONSOLIDATION_REQUEST_TYPE` | 86 | `RequestType.consolidation` | 0x02 |
| `forks/amsterdam/requests.py::BUILDER_DEPOSIT_REQUEST_TYPE` | 93 | `RequestType.builderDeposit` | 0x03, EIP-8282 |
| `forks/amsterdam/requests.py::BUILDER_EXIT_REQUEST_TYPE` | 100 | `RequestType.builderExit` | 0x04, EIP-8282 |
| `forks/amsterdam/requests.py::DEPOSIT_EVENT_LENGTH` | 108 | `DepositLayout.eventLength` | 576 |
| `forks/amsterdam/requests.py::PUBKEY_OFFSET` | 114 | `DepositLayout.pubkeyOffset` | 160 |
| `forks/amsterdam/requests.py::WITHDRAWAL_CREDENTIALS_OFFSET` | 120 | `DepositLayout.wcOffset` | 256 |
| `forks/amsterdam/requests.py::AMOUNT_OFFSET` | 126 | `DepositLayout.amountOffset` | 320 |
| `forks/amsterdam/requests.py::SIGNATURE_OFFSET` | 131 | `DepositLayout.signatureOffset` | 384 |
| `forks/amsterdam/requests.py::INDEX_OFFSET` | 136 | `DepositLayout.indexOffset` | 512 |
| `forks/amsterdam/requests.py::PUBKEY_SIZE` | 141 | `DepositLayout.pubkeySize` | 48 |
| `forks/amsterdam/requests.py::WITHDRAWAL_CREDENTIALS_SIZE` | 147 | `DepositLayout.wcSize` | 32 |
| `forks/amsterdam/requests.py::AMOUNT_SIZE` | 153 | `DepositLayout.amountSize` | 8 |
| `forks/amsterdam/requests.py::SIGNATURE_SIZE` | 158 | `DepositLayout.signatureSize` | 96 |
| `forks/amsterdam/requests.py::INDEX_SIZE` | 163 | `DepositLayout.indexSize` | 8 |
| `forks/amsterdam/requests.py::extract_deposit_data` | 170–271 | `extractDepositData : ByteArray → Except DepositError ByteArray` | Supplied on every finite input; eleven ordered checks, R-RQ; complete result/size laws below |
| `forks/amsterdam/requests.py::parse_deposit_requests` | 274 | `parseDepositRequests` | reads receipts, not a log list |
| `forks/amsterdam/requests.py::compute_requests_hash` | 307–328 | `computeRequestsHash : List ByteArray → Hash32` | Supplied ordered complete SHA-256-of-digests result law; no request validation; Q46/host limits below |
| `forks/amsterdam/block_access_lists.py::StorageChange` | 34 | `StorageChange` |  |
| `forks/amsterdam/block_access_lists.py::BalanceChange` | 61 | `BalanceChange` |  |
| `forks/amsterdam/block_access_lists.py::NonceChange` | 88 | `NonceChange` |  |
| `forks/amsterdam/block_access_lists.py::CodeChange` | 115 | `CodeChange` |  |
| `forks/amsterdam/block_access_lists.py::SlotChanges` | 142 | `SlotChanges` |  |
| `forks/amsterdam/block_access_lists.py::AccountChanges` | 167 | `AccountChanges` | RLP field order fixed |
| `forks/amsterdam/block_access_lists.py::AccountData` | 244 | `AccountData` | builder payload (§6) |
| `forks/amsterdam/block_access_lists.py::BlockAccessListBuilder` | 285 | `BalBuilder` | ExtTreeMap-based (§6) |
| `forks/amsterdam/block_access_lists.py::ensure_account` | 337 | `BalBuilder.ensureAccount` |  |
| `forks/amsterdam/block_access_lists.py::add_storage_write` | 351 | `BalBuilder.addStorageWrite` | last write per index wins |
| `forks/amsterdam/block_access_lists.py::add_storage_read` | 388 | `BalBuilder.addStorageRead` |  |
| `forks/amsterdam/block_access_lists.py::add_balance_change` | 402 | `BalBuilder.addBalanceChange` | last wins |
| `forks/amsterdam/block_access_lists.py::add_nonce_change` | 439 | `BalBuilder.addNonceChange` | **max** wins |
| `forks/amsterdam/block_access_lists.py::add_code_change` | 476 | `BalBuilder.addCodeChange` | last wins |
| `forks/amsterdam/block_access_lists.py::remove_storage_write` | 516 | `BalBuilder.removeStorageWrite` | deletes empty slot entry |
| `forks/amsterdam/block_access_lists.py::remove_balance_change` | 543 | `BalBuilder.removeBalanceChange` |  |
| `forks/amsterdam/block_access_lists.py::remove_nonce_change` | 564 | `BalBuilder.removeNonceChange` |  |
| `forks/amsterdam/block_access_lists.py::remove_code_change` | 585 | `BalBuilder.removeCodeChange` |  |
| `forks/amsterdam/block_access_lists.py::add_touched_account` | 606 | `BalBuilder.addTouchedAccount` |  |
| `forks/amsterdam/block_access_lists.py::_build_from_builder` | 625 | `BalBuilder.build` | sorted output |
| `forks/amsterdam/block_access_lists.py::_get_pre_tx_account` | 690 | `preTxAccount` | internal; needs EthState observer |
| `forks/amsterdam/block_access_lists.py::_get_pre_tx_storage` | 708 | `preTxStorage` | internal; needs EthState observer |
| `forks/amsterdam/block_access_lists.py::_index_start_account` | 727 | `BalBuilder.indexStartAccount` | memo per (index, address) |
| `forks/amsterdam/block_access_lists.py::_index_start_storage` | 747 | `BalBuilder.indexStartStorage` | memo per (index, address, slot) |
| `forks/amsterdam/block_access_lists.py::update_builder_from_tx` | 765 | `updateBuilderFromTx` | called from `incorporate_tx_into_block` (seam, §8) |
| `forks/amsterdam/block_access_lists.py::build_block_access_list` | 831 | `buildBlockAccessList` |  |
| `forks/amsterdam/block_access_lists.py::hash_block_access_list` | 854 | `hashBlockAccessList` | keccak(rlp) |
| `forks/amsterdam/block_access_lists.py::validate_block_access_list_gas_limit` | 863 | `validateBlockAccessListGasLimit` | items ≤ gasLimit / 2000 |
| `forks/amsterdam/exceptions.py::WrongChainIdError` | 15 | `TxError.wrongChainId` |  |
| `forks/amsterdam/exceptions.py::WrongChainIdError.__init__` | 23 | (constructor fields) | fields carried as constructor arguments |
| `forks/amsterdam/exceptions.py::TransactionTypeError` | 29 | `TxDecodeError.unsupported` (via `BlockError.txDecode`) | an `InvalidTransaction` subclass, but raised only by `decode_transaction`; one constructor for the one site |
| `forks/amsterdam/exceptions.py::TransactionTypeError.__init__` | 41 | (constructor fields) | fields carried as constructor arguments |
| `forks/amsterdam/exceptions.py::TransactionTypeContractCreationError` | 46 | `TxError.transactionTypeContractCreation` |  |
| `forks/amsterdam/exceptions.py::TransactionTypeContractCreationError.__init__` | 56 | (constructor fields) | fields carried as constructor arguments |
| `forks/amsterdam/exceptions.py::BlobGasLimitExceededError` | 64 | `TxError.blobGasLimitExceeded` |  |
| `forks/amsterdam/exceptions.py::InsufficientMaxFeePerBlobGasError` | 70 | `TxError.insufficientMaxFeePerBlobGas` |  |
| `forks/amsterdam/exceptions.py::InsufficientMaxFeePerGasError` | 76 | `TxError.insufficientMaxFeePerGas` |  |
| `forks/amsterdam/exceptions.py::InsufficientMaxFeePerGasError.__init__` | 91 | (constructor fields) | fields carried as constructor arguments |
| `forks/amsterdam/exceptions.py::InvalidBlobVersionedHashError` | 102 | `TxError.invalidBlobVersionedHash` |  |
| `forks/amsterdam/exceptions.py::NoBlobDataError` | 108 | `TxError.noBlobData` |  |
| `forks/amsterdam/exceptions.py::BlobCountExceededError` | 114 | `TxError.blobCountExceeded` |  |
| `forks/amsterdam/exceptions.py::PriorityFeeGreaterThanMaxFeeError` | 120 | `TxError.priorityFeeGreaterThanMaxFee` |  |
| `forks/amsterdam/exceptions.py::EmptyAuthorizationListError` | 126 | `TxError.emptyAuthorizationList` |  |
| `forks/amsterdam/exceptions.py::InitCodeTooLargeError` | 132 | `TxError.initCodeTooLarge` |  |
| `forks/amsterdam/exceptions.py::TransactionGasLimitExceededError` | 138 | `TxError.transactionGasLimitExceeded` |  |
| `forks/amsterdam/exceptions.py::BlockAccessListGasLimitExceededError` | 148 | `BlockError.balGasLimitExceeded` |  |
| `exceptions.py::EthereumException` | 6 | (root; no constructor) |  |
| `exceptions.py::InvalidBlock` | 13 | `BlockError` (each raise site its own constructor) |  |
| `exceptions.py::StateWithEmptyAccount` | 19 | none (not raised in Amsterdam at the pin) |  |
| `exceptions.py::InvalidTransaction` | 25 | `TxError` (wrapped as `BlockError.invalidTransaction`) |  |
| `exceptions.py::InvalidSenderError` | 31 | `TxError.invalidSender` |  |
| `exceptions.py::InvalidSignatureError` | 38 | `TxError.invalidSignature` |  |
| `exceptions.py::InsufficientBalanceError` | 44 | `TxError.insufficientBalance` |  |
| `exceptions.py::NonceMismatchError` | 51 | `TxError.nonceMismatch` |  |
| `exceptions.py::GasUsedExceedsLimitError` | 58 | `TxError.gasUsedExceedsLimit` |  |
| `exceptions.py::InsufficientTransactionGasError` | 65 | `TxError.insufficientTransactionGas` |  |
| `exceptions.py::NonceOverflowError` | 72 | `TxError.nonceOverflow` |  |

**External semantics.** `EthBlock` must specify the behaviour it relies on from:
- `ethereum_rlp` (`rlp.encode`, `rlp.decode_to` for the five transaction types, the receipt and `Uint`, with canonical-integer, no-trailing-bytes and union-variant rules). These are owned by `EthCodec`; this module states only which structures are encoded and in what field order.
- `ethereum_types` numeric semantics: the non-wrapping, raising arithmetic described above. It is the basis of the `arith` constructors, and each reachable site is listed in §2 and §10.
- `hashlib.sha256`, in `compute_requests_hash` (`EthHash`).
- `slotted_freezable`/dataclass truthiness (`any(authorizations)`, R-VT 7).
- `Bytes0` as the creation marker, which is `Option Address` here.

The review reproducer now uses `uv.lock`, including `ethereum-rlp` 0.1.6; see [REVIEW](../REVIEW.md). Earlier experiments using 0.1.7 remain historical evidence and must be rerun when load-bearing.

### Clarified root-input seam (Q53; unimplemented)

| Exact pinned EELS source | Planned declaration/domain | Success/effects | Ordered failure/domain boundary | Required model/composition law | Required validation |
|---|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/vm/__init__.py:107–117`; `transactions.py:540–559`; `blocks.py:394–414`; `fork.py:1084–1088,1119–1130,1152–1157,351–354` | EthBlock-owned `TrieValue` bridges for optional transaction/receipt values and already-encoded withdrawal Bytes; dense array representation unchanged | Unsecured/default-None inputs; legacy RLP once, Bytes identity; RLP ordinal byte keys and supplied F20 empty root; C8 effects retained | `none` means default deletion; nondefault empty Bytes is unsafe, not silently deleted; no new preparation error/O-row; source-schema/assembled `Encodable` and host premises remain caller obligations | Arrays equal the encoded prepared map of the corresponding safe typed trie; existing EthCommit `root`/`mathRoot` equation, no second root API | Legacy and each typed transaction (0x01–0x04), legacy/typed receipts, withdrawal already-RLP, ordinal keys 0/1/127/128/256, empty/nonempty blocks and nonliteral empty constants; proof-only consumer clients |

### Implemented calldata token count

| EELS operation/domain | Lean definition | Ordinary law | Tests / limits |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/transactions.py:804–814`, every finite bytes value; result unbounded `Uint` | `STFSpec/Block/CalldataTokens.lean`: `countTokensInData : ByteArray → Nat` | `countTokensInData_eq`: zeros + 4·(size − zeros); private packed-fold/reference equality | `STFSpec/Conformance/Block/CalldataTokensCallerProofs.lean` uses the public law for empty, concatenation and size bounds; `CalldataTokensGuards.lean` supplies small complete results; `scripts/CalldataTokensNativeTests.lean` emits all 266 complete input/result rows from the preimplementation catalog, including all 256 singletons and 10 KiB cases; `count_tokens_differential.py` checks whole rows and optionally compares actual pinned source observations; `scripts/test_count_tokens_output_parser.py` rejects malformed/duplicate/missing/extra rows and keys, malformed hex, wrong results and bool/float-as-int in normal and optimized Python. Finite source coupling retains locked-interpreter, used-module/runtime and host-resource limits; no universal runtime authentication, cost, full R-IG or guest result is supplied. |

### Supplied raw block parameters

`STFSpec.Block.BlockParams` is exported through `STFSpec.Block`, with exactly the
three independent Nat fields in §5 order. This guided runtime abstraction is not
an EELS record. EthFork retains all five R-F1 source-quantity obligations:
`fork.py:114–115` supply the denominator and elasticity; `:144–145` are private
Fork-owned `MAX_BLOCK_SIZE` and `SAFETY_MARGIN` operands; `:146` supplies their
subtraction as the third public field ([EthFork §3](EthFork.md#3-eels-source-map)).
There are no `maxBlockSize` or `safetyMargin` fields or public operand accessors.

| Guided provider / source context | Lean declaration and domain | Effects / failures | Law / validation / status |
|---|---|---|---|
| §5; EELS `fork.py:114–115,144–146` parameter context, all values owned by EthFork | `STFSpec.Block.BlockParams : Type`; `BlockParams.mk : Nat → Nat → Nat → BlockParams`; projections `baseFeeMaxChangeDenominator`, `elasticityMultiplier`, `maxRlpBlockSize : BlockParams → Nat` | Every raw Nat triple, including zero, unrelated and arbitrarily large values; exact stored inputs, no effects, errors or proof premises | **supplied:** ordinary structure construction/projections. Private `Conformance/Block/BlockParamsCallerProofs.lean` clients check exact public types, all arbitrary projections, complete reconstruction and every single-field update preserving both other fields; complete zero/distinct/large guards. No extra public law, default, instance or WF/coherence predicate. |

Within the fork module, the source reads only the derived RLP limit in `fork.py:309`,
elasticity in `:412` and the denominator in `:425,439`. The raw record supplies none of the size or
base-fee operations, their errors, division safety or complete configuration.
EthFork §3 maps and checks the two actual private operands as well as all three
actual public projections, retaining the subtraction rather than a literal.

### Supplied raw transaction parameters

`STFSpec.Block.TxParams` is exported through `STFSpec.Block`; its three independent
fields are `Nat`, in the §5 order. This is the guided parameter abstraction, not
an EELS transaction class. EthFork retains source-inventory ownership of the
three Amsterdam constants and supplies their value ([EthFork §3](EthFork.md#3-eels-source-map)).

| Guided provider / source context | Lean declaration and domain | Effects / failures | Law / validation / status |
|---|---|---|---|
| §5; EELS `transactions.py:64,74,82` parameter context, values owned by EthFork | `STFSpec.Block.TxParams : Type`; `TxParams.mk : Nat → Nat → Nat → TxParams`; projections `blobCountLimit`, `accessListAddressFloorTokens`, `accessListStorageKeyFloorTokens : TxParams → Nat` | Every raw Nat triple, including zero, unrelated and arbitrarily large values; exact stored inputs, no state effects, errors or proof premises | **supplied:** ordinary structure construction/projections. Private `Conformance/Block/TxParamsCallerProofs.lean` clients check exact public types, all arbitrary projections, complete reconstruction and each single-field update preserving both other fields; zero/distinct/large guards. No extra public law or WF predicate. |

The floor inputs count tokens per access-list occurrence, before multiplication
by the separate VM floor-token gas price (`transactions.py:752–769`). Blob admission
reads the current module global (`:653–659`). Future consumer/source correspondence
must bind those original globals and dependency interpretation; constructing this
record implements neither admission nor intrinsic costing.

### Supplied raw system addresses and budgets

`STFSpec.Block.SystemAddrs` is exported through `STFSpec.Block`, with the exact
§5 order: eight independent `EthBase` `Address` fields followed by two independent
`Nat` fields. This is the guided runtime parameter abstraction; EELS has no
corresponding record. EthFork retains R-F2 source-constant and concrete-value
ownership ([EthFork §2–§3](EthFork.md#2-requirements)).

| Guided provider / source context | Lean declaration and domain | Effects / failures | Law / validation / status |
|---|---|---|---|
| §5; EELS `fork.py:117–143` and `requests.py:49–51` parameter context, values owned by EthFork | `STFSpec.Block.SystemAddrs : Type`; `SystemAddrs.mk` takes eight `Address` arguments and two `Nat` arguments; exact §5 projections | Every well-typed ten-field record, including equal/zero/unrelated addresses and zero or arbitrarily large independent budgets; exact stored inputs, no effects, errors or proof premises | **supplied:** ordinary structure construction/projections. Private `Conformance/Block/SystemAddrsCallerProofs.lean` clients check the complete constructor/projection types, every arbitrary projection, complete reconstruction and all ten single-field updates preserving all nine unrelated fields. Complete nominal-address and twenty-byte-list observations cover zero, distinct field markers and large independent budgets. No extra public law, default, instance or WF predicate. |

EthFork §3 supplies the concrete R-F2 value and its full-field controls. Actual
system-call/request consumers, configuration coherence and the remaining `BlockConfig`
are unimplemented. The raw record alone does not implement routing. F8 specifies Fork's
`systemAddrs.systemAddress` through `BlockConfig.runnerEnv` to
`RunnerEnv.systemAddress`, copied into immutable `FrameCtx.systemAddress` and inherited
by children; both producers pass it explicitly to `emitTransferLog` after Frame (local
helper supplied: EthVmCore §3/§7). Actual transport and source coherence remain
implementation obligations under that selected guidance.

### Implemented fixed deposit extraction

| EELS operation/domain | Lean definition | Ordinary laws | Tests / limits |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/requests.py:170–271`, every finite bytes value | `STFSpec/Block/DepositData.lean`: existing eleven-tag `DepositError`; `extractDepositData : ByteArray → Except DepositError ByteArray` | `extractDepositData_eq`: complete length/offset/size priority and all successful bytes through public Base Bytes and Uint models; `size_extractDepositData`: success implies size 192 | `DepositDataCallerProofs.lean` privately checks the exact full public-law type, length-first and offset-before-size consequences and size; `DepositDataGuards.lean` checks all eleven constructor identities and complete zero-field output. `scripts/DepositDataNativeTests.lean` emits complete inputs and results for the independently frozen 142-case `deposit_cases.json`. `deposit_data_differential.py` admits exact full bytes and tags; optional original-source packet coupling checks the exact eleven `InvalidBlock` messages/class/args. `scripts/test_deposit_data_output_parser.py` checks malformed framing/keys/types, every successful output byte position and wrong error identities/messages in normal and optimized Python. The catalog includes pinned `test_modified_contract.py`'s default 576-byte log, independently matched to the pinned fixture's literal emitter, eleven single corruptions, empty/575/577 lengths, high word bits, simultaneous failure priority and ignored nonzero padding. No EVM/fixture/guest execution pass, source allocation/resource equivalence or runtime authentication follows. |

The standalone helper supplies the existing R-RQ extraction only. Its constants
are local literals, not a new `DepositLayout` public API. The readable definition
uses public packed slices and unbounded Uint reads directly; no separate fast path,
representation substitution or additional public helper is introduced. Each word
window has at most 32 bytes, and each assembled output buffer has at most
192 bytes; these per-buffer bounds make no total allocation-volume claim. The independently sealed
source observations retain interpreter/installed-RECORD/native-library/host trust
limits; the committed parser checks their observation projection, not the seal.

The frozen catalog identity is SHA-256
`1d1388e3d29c39e373fbcb7c423e744d3badfd97de7facb5e4593c571c717b85`.
Its `pinned_test_default_log` is the complete default log in EELS
`tests/prague/eip6110_deposits/test_modified_contract.py:48–75`, emitted at
`:142–155`. Independent literal PUSH/MSTORE/LOG inspection matched every byte to
fixture member
`fixtures/blockchain_tests/for_amsterdam/prague/eip6110_deposits/modified_contract/extra_logs.json`
(SHA-256 `eb0633cedf46233f7e577721f85f18b676fbcd29a1a000aa145cace5ca0d57a8`),
test `test_extra_logs` with `include_deposit_event_True` and
`extra_event_type_no_topics`. The original helper was called on that exact payload;
the inspection did not execute the fixture transaction or EVM.

### Implemented ordered execution-request commitment

| EELS operation/domain | Lean definition | Ordinary law | Tests / limits |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/requests.py:307–328`, every finite ordered list of finite bytes | `STFSpec/Block/RequestsHash.lean`: `computeRequestsHash : List ByteArray → Hash32`; pure value, no failure channel/consumer; **discharged for provider composition** | `computeRequestsHash_eq` identifies every ordered inner SHA digest byte, the exact concatenated outer preimage, outer SHA and `Hash32.ofBytes32`; private packed/List equality | `RequestsHashCallerProofs.lean` privately checks the whole facade law and derives full output bytes, empty/singleton/pair equations and exact model preimage size via public providers. `RequestsHashGuards.lean` checks complete empty/one-empty/two-empty/three-empty/abc anchor digests. `scripts/RequestsHashNativeTests.lean` emits all ordered request byte strings and all 32 actual output bytes for 298 independently frozen cases. `requests_hash_differential.py` checks complete rows and optionally both original-source modes; `scripts/test_requests_hash_output_parser.py` rejects altered digest bytes, request bytes/order/length, omitted/extra/duplicate rows, malformed framing/keys/hex and wrong types including bool-as-int counts, in normal and optimized Python. Source/environment/seal authentication is separate from observation admission. |

The catalog `STFSpec/Conformance/Block/requests-hash-cases.json` has SHA-256
`98796c0f42b6672d35b706372f4af409e0197ea98f1fa35bda8660ac23e43be2`.
Its expected bytes were frozen before EELS or Lean observations, using separate
OpenSSL CLI inner/outer composition and fixed empty/abc anchors. The CLI and
Python hashlib share OpenSSL; this supplies no independent cryptographic
implementation claim. Both exact original-source observation projections are
checked separately from their packet/interpreter/native-library authentication.
Cases retain empty and repeated requests, reverse order, every singleton prefix,
unknown prefixes, split-boundary contrasts, inner lengths at the 55/56 and 64 SHA-256
padding boundaries and outer count 256. These are finite observations, not a universal
host/source equivalence proof.

The private packed builder reserves `32 * requests.length` and emits all 32 bytes
of each inner digest through public byte folds. Its ordinary equality identifies
the readable private List model. Assembly pushes each inner byte once without
repeated whole-prefix copying. The materialized preimage has exactly 32 bytes per
request; this analytical storage statement is separate from EELS's incremental
hashlib API and from SHA provider working storage, total allocation volume,
compiled ownership, throughput and C1–C4 cost claims. No public helper, hash seam,
carrier instance, validator, prefix guard or Keccak query is added.

### Implemented ordered logs bloom

| EELS operation/domain | Lean definition and effects/failures | Ordinary laws / status | Validation and limits |
|---|---|---|---|
| `src/ethereum/forks/amsterdam/bloom.py:29–87`; every finite array of existing `Core.Log`, with arbitrary topic counts and duplicates | `STFSpec/Block/LogsBloom.lean`: `logsBloom {m} [Monad m] [KeccakQuery m] (logs : Array Core.Log) : m Bloom`; query each exact 20-byte address, then its exact ordered 32-byte topics, once per occurrence; ignore data; underlying failures stop traversal and retain the supplied monad's effects without translation, retries or queries after failure | `logsBloom_eq` identifies the complete flattened ordered query/fold action and all 256 result bytes; `logsBloom_empty` and `logsBloom_append` give zero/no-query and same-context sequential composition. All three ordinary laws are discharged under `LawfulMonad` for sequencing normalization; the operation needs only `Monad`. Private packed-size/bit-update/Hash32-selector/full-action reference equality is discharged; no oracle purity/stability/concrete-answer premise | `LogsBloomCallerProofs.lean` privately checks each complete facade type and derives data irrelevance and the address-only action through public providers. `LogsBloomGuards.lean` checks 74 interpreted controls (72 synthetic/effect controls, concrete empty and the complete single-log known answer in §4); `scripts/LogsBloomNativeTests.lean` emits all 112 complete frames described below, retaining synthetic answers and complete state/error/query observations. All 20 frozen cases retain every input byte, 85 ordered complete preimages/digests and complete 256-byte results; `logs_bloom_differential.py --check-target` strictly checks exact full native rows against the frozen catalogue; it imports no EELS and runs no source observations. `scripts/test_logs_bloom_output_parser.py` rejects malformed framing/schema/types, duplicate/omitted/extra/order/value changes in normal and optimized Python. Tests and finite source coupling do not establish generic oracle interpretation coupling or host/crypto/resource equivalence. |

The independent 20-case source catalog has SHA-256
`c71977a78af98659336dc051fbcb00c6d9df0856a289eeb1d4d7d0dea70aa940`.
It is retained unchanged as `source_catalogue` within
`STFSpec/Conformance/Block/logs_bloom_cases.json`; the complete combined file has
SHA-256 `6fe020501102507a348d249da59332a822f691a867279e1153f092249a91160a`.
The combined catalog freezes 112 complete target frames: 20 actual `Id` runs,
20 recording-State runs whose oracle delegates to `KeccakQuery Id`, and 72
synthetic/effect controls. Frames retain each actual call's complete inputs, result,
query preimages/digests, cursor and forwarding state. The `logs-bloom-v1` header
binds count 112, source count 20, source query count 85 and synthetic count 72;
the footer binds the complete catalog identity and frame count. Its synthetic inputs,
answers and full expected frames were frozen before the conformance engineer read
or executed the new operation. The source catalog's full inputs, complete expected
outputs, digests and bit positions were prepared
before reading/invoking original Bloom source or new Lean Bloom code. Expectations
use integer bitset composition and PyCryptodome Keccak; the actual original source
uses mutable-byte updates and observed OpenSSL Keccak dispatch. The independent
composition and distinct observed backend dispatches do not prove cryptographic
correctness. Original-source/runtime authentication is a separate evidence gate
from strict admission of those observation projections. The source-catalogue
preparation, the original-source runs and their authentication are out of tree: in
this repository, `logs_bloom_differential.py --check-target` compares the native
output with the frozen catalogue only.

Production threads one fixed-size packed byte buffer through log/topic array
folds. Each answer selects byte pairs 0/1, 2/3 and 4/5, masks to eleven bits and
performs three byte OR updates; exact index bounds and big-endian orientation
are proved with public Base/Hash32 contracts. Final checked fixed-byte construction
is proved successful at size 256. List and growing-Nat bitset models stay outside
the production call path. The code and generated C expose bounded buffer updates
and array traversal; they establish no compiled uniqueness, allocation-volume,
peak-space, source-host failure, timing or C1–C4 claim. Receipt/header/BlockOutput
integration, F20 coherence, full block execution and guest/EEST readiness remain
separate obligations.

## 4. Tests

- **Raw BlockParams.** The private public-facade clients in §3 quantify all three arbitrary Nat fields, reconstruct the complete record and update each field independently. Complete zero/distinct/large controls retain the unrestricted domain. All five R-F1 quantity controls and the actual subtraction expression belong to EthFork §3–§4.

**F8 runner-entry controls (unimplemented).** Vary cfg.system.systemAddress
independently of the F20 topic and check the exact runnerEnv projection and complete
logs at both user and unchecked-system entries. The checked-system path must use
the same delegated environment after its existing code check, preserving first
failures and effect order.

- **Raw SystemAddrs.** The complete private public-facade clients and zero/distinct/large controls in §3 preserve all eight nominal addresses, all twenty bytes of each address, and both independent budgets; each update observes every unrelated field. Concrete R-F2 value controls are supplied by EthFork §3; consumer controls remain separate.
- **Raw TxParams.** The private public-facade clients and complete zero/distinct/large controls in §3 preserve the unrestricted raw domain. Amsterdam literal controls belong to EthFork §3–§4.

Q53's root-input seam remains unimplemented. Require complete bytes for legacy and all
typed transaction/receipt forms, already-RLP withdrawal identity and keys
`80/01/7f/8180/820100` for ordinals `0/1/127/128/256`. Prove validity/nonempty
encoding once and the dense-array/prepared-map equation through public owner contracts.
Distinguish absent `none` from unsafe nondefault empty bytes. Empty roots must use a
synthetic nonliteral context constant without acquisition or a new local query; nonempty
roots preserve C8's original errors and prior state. Authenticated source comparisons
retain exact schema/dispatch, complete `Encodable`, F20 coherence and host premises.
These are future consumer checks; the guidance clarification claims no new conformance.

- **EEST fixture areas** (`STFSpec/informal/eest-fixture-index.txt`, in both `blockchain_tests` and `blockchain_tests_engine`, under `for_amsterdam` and the transition `for_bpo2toamsterdamattime15k`):
  - Amsterdam: `eip2780_reduce_intrinsic_tx_gas` (59), `eip7778_block_gas_accounting_without_refunds` (9), `eip7843_slotnum` (10), `eip7928_block_level_access_lists` (202/204), `eip7976_increase_calldata_floor_cost` (21), `eip7981_increase_access_list_cost` (19), `eip8037_state_creation_gas_cost_increase` (268, for block gas and settlement), `eip8246_selfdestruct_no_burn` (7), `eip8282_builder_execution_requests` (22), `eip8025_optional_proofs` (100: public-key hints, chain id, versioned hashes);
  - Prague: `eip6110_deposits`, `eip7002_el_triggerable_withdrawals`, `eip7251_consolidations`, `eip7685_general_purpose_el_requests`, `eip7623_increase_calldata_cost`, `eip7702_set_code_tx` (86), `eip2935_historical_block_hashes_from_state`;
  - Cancun: `eip4788_beacon_root`, `eip4844_blobs` (42), `eip7516_blobgasfee`, `eip6780_selfdestruct`;
  - Osaka: `eip7825_transaction_gas_limit_cap`, `eip7918_blob_reserve_price`, `eip7934_block_rlp_limit`, `eip7594_peerdas`;
  - Shanghai `eip4895_withdrawals`, `eip3860_initcode`; London `eip1559_fee_market_change`, `validation`; Frontier `validation`, `eip2681_limit_account_nonce`; Istanbul `eip1344_chainid`; Berlin `eip2930_access_list`; `ported_static/stTransactionTest`, `stEIP1559`, `stEIP3607`, `stEIP4844_blobtransactions`, `stRefundTest`, `stLogTests`.
- **EELS unit tests** (pinned checkout, `tests/json_loader/`): `test_get_last_256_block_hashes.py`, `test_transaction_codec.py` (legacy transaction as bytes), `test_fork_blob_schedule.py`, and the G6-owned `test_execution_requests.py` / `test_withdrawal_codec.py` for the payload codecs that feed R-RQ and R-WD. The spec-level test sources (`tests/amsterdam/eip7928_…/test_block_access_lists_invalid.py`, `…/eip7778_…/test_gas_accounting.py`, `…/eip8282_…`) are the generators of the fixtures above, not Python unit tests of `fork.py`.
- **`core` `#guard` cases to write.**
  - Intrinsic gas: one value for each branch of R-IG (creation with 33-byte init code, self-transfer with value, 2 addresses × 3 slots, 1 and 2 authorizations), plus the floor exceeding the execution cost for a 10 KiB zero calldata.
  - `calculateBaseFeePerGas`: at, above and below target; the minimum increase of 1; a parent gas limit below 1024, where `checkGasLimit` is always false.
  - `checkGasLimit` at `parent ± parent/1024` exactly (both rejected).
  - Bloom (supplied locally): the independently frozen complete single-log known answer
    `zero_address_zero_topic` in `logs_bloom_cases.json`: one all-zero 20-byte
    address, one all-zero 32-byte topic, empty data. The complete 256-byte expected
    result, both full preimages/digests and all six bit positions are retained.
    This replaces the unsupported phrase “the EIP known-answer vector for one log”,
    which identified no EIP, input or output. A bounded primary-source search did
    not identify its intended literal; historical EIP attribution remains unknown.
    EIP-2481's ReceiptsPacket illustration has an all-zero Bloom for a nonempty
    log and explicitly tests RLP message encoding; it is not used as a Bloom KAT.
    No published-EIP vector or broader EIP coverage is claimed. The independent
    complete case and normal fixture/pinned-source authority are retained.
    Synthetic controls cover bits 0/1/7/8/2047, all three selectors, eleven-bit
    masking, equal selectors and irrelevant digest bytes 6–31. Stateful duplicate
    answers and same-context append distinguish restarting, deduplication and
    reordering. Failures at each address/topic query preserve complete original
    errors, exact prefixes and no later query across both transformer orders and
    forwarding layers. Interpreted and native controls are required alongside the
    complete 20-case source catalog, without inferring universal coupling from tests.
  - `HashConsts.query` at `Id`: `emptyOmmerHash = 1dcc4de8…9347`.
  - `computeRequestsHash`: complete ordered request/digest native rows, empty-list versus one-empty, duplicates, order reversals, arbitrary prefixes, split boundaries, inner lengths at the 55/56 and 64 SHA-256 padding boundaries and count 256; private facade-law clients and strict normal/optimized parser controls as in §3. Source coupling compares both original-source modes, separately from authenticated packet/host provenance.
  - `extractDepositData`: supplied complete 142-case catalog and interpreted controls in §3, including the pinned default 576-byte test/fixture literal payload and all eleven corruptions; actual whole-fixture execution remains open.
  - BAL `build`: out-of-order inserts; reads that overlap writes; nonce-maximum versus balance-last-wins in one index; a write reverted to its pre-value (removed); two incorporations in index `n + 1`.
  - `validateBlockAccessListGasLimit` at the limit and one past it.
  - Signing hashes against EEST transaction vectors.
- **Adversarial transactions:**
  - `s = N/2 + 1`, `r = 0`, `r = N`;
  - legacy `v = 29`, `v = 34`, `v = 35 + 2c + 2`, `v = 2⁶⁵ + 35` (the `chainIdOverflow` path);
  - typed `yParity = 2`; type bytes `0x00`, `0x05`, `0xBF` (`txDecode .unsupported`), `0xFF` (`txDecode .reservedFF`), and the empty byte string;
  - a legacy transaction wrapped as a typed byte string starting with `0xC0` (decoded as legacy);
  - blob transactions with 0 and 7 blobs and a hash starting with 0x02; type 4 with no authorizations;
  - `nonce = 2⁶⁴ − 1`; `gas = 2³²`; `maxPriority > maxFee`;
  - a legacy transaction with `gasPrice < baseFee` (**`BlockError`, not `TxError`**);
  - a sender with non-delegation code;
  - a public-key hint that is the other recovery candidate; hint count ±1.
- **Adversarial headers:**
  - each R-VH check failing alone, and pairs failing together (order);
  - a bpo5 parent (the transition fixtures);
  - a parent with `excessBlobGas + blobGasUsed ≥ 2⁶⁴` (`arith`);
  - `extraData` of 33 bytes; `gasLimit = 4999`; `timestamp = parent`;
  - a BAL-hash-only mismatch; `gasUsed` equal to the execution total when the state total is larger;
  - 0 transactions with withdrawals only; a block exactly at `maxRlpBlockSize`.
- **Property and differential checks.** Codec round-trips; `rlp (rlp⁻¹ b) = b` for canonical transaction bytes; BAL output sorted and deduplicated for random builder traces; replaying the EELS order of `add/remove` on random traces against the Python builder (bug-finding only, CONTRIBUTING §1).
- **F20 composition cases to implement.** Use a synthetic oracle whose four constant
  answers each differ from the literals:
  - Run the standalone wrapper with both full-state and witness provider factories; its query trace follows §2.7 and each factory receives the acquired record.
  - Fail the size, key-count and header checks separately; the trace still contains acquisition and factory effects, in R-EB order.
  - Run the kernel directly; it makes no acquisition and stores the supplied record at step 5.
  - Change the stored fields; body and state consumers observe the corresponding empty-root, empty-code and transfer-topic values.
  - Use a provider factory or kernel that substitutes literals for the acquired record;
    its empty-root or empty-code observations differ from the synthetic oracle-derived
    record. The required coherence premise cannot be established; no runtime coherence
    check or new rejection is introduced.
  - Run the wrapper twice; each run acquires independently. Ordinary later queries of a constant preimage remain ordinary queries, not record acquisitions.
  - Raise a provider fault or internal/fuel error; it stays in the inner or outer checked channel, respectively.

- **Calldata token count:** empty, zero/nonzero and mixed inputs, every UInt8 singleton, all-byte and all-nonzero sequences, 10 KiB zero/nonzero buffers, alternating and asymmetric endpoint cases. Compare every actual input byte and the complete result with the independent 266-case catalog and, separately, the original pinned function in isolated normal/optimized locked Python. Strict-reader negative controls remain effective under `-O`.

## 5. Interface

Reference field order, widths and inherited records are catalogued in [REFERENCE-RECORDS](../REFERENCE-RECORDS.md), generated from the exact pin. Wire-schema owners must use those layouts and prove their codec instances. Runtime records may use the explicit abstraction below; omitted fields or `…` remain implementation blockers, not implicit freedom to choose semantics.

All items are public unless marked (internal). Namespace `STFSpec.Block`.

```lean
-- configuration (types here; the Amsterdam value is EthFork's)
structure BlockParams where
  baseFeeMaxChangeDenominator elasticityMultiplier maxRlpBlockSize : Nat
structure TxParams where
  blobCountLimit accessListAddressFloorTokens accessListStorageKeyFloorTokens : Nat
structure SystemAddrs where
  systemAddress beaconRoots historyStorage withdrawalRequests consolidationRequests
    builderDeposits builderExits depositContract : Address
  txGas maxSstoresPerCall : Nat
structure BlockConfig where
  gas : Vm.GasCosts; stateGas : Vm.StateGasCosts   -- EthVmCore records
  block : BlockParams; tx : TxParams; system : SystemAddrs
  precompiles : Vm.PrecompileTable                  -- EthVmCore's shared table type
  limits : Vm.VmLimits                             -- supplies FrameCtx.config via RunnerEnv

def BlockConfig.runnerEnv (cfg : BlockConfig) : RunnerEnv :=
  { precompiles := cfg.precompiles
    vm := ⟨cfg.gas, cfg.stateGas, cfg.limits⟩
    systemAddress := cfg.system.systemAddress }

-- types (§2.1)
structure Withdrawal; structure Header; structure PrevHeader
inductive ParentHeader | amsterdam (h : Header) | bpo5 (h : PrevHeader)
def ParentHeader.{gasLimit,gasUsed,baseFeePerGas,timestamp,number,stateRoot,
                  excessBlobGas,blobGasUsed,parentHash} : ParentHeader → _
structure Access where account : Address; slots : Array Bytes32
structure LegacyTransaction; structure AccessListTransaction; structure FeeMarketTransaction
structure BlobTransaction; structure SetCodeTransaction
inductive Transaction | legacy | accessList | feeMarket | blob | setCode
inductive BlockTx | legacy (t : LegacyTransaction) | typed (b : ByteArray)
structure Block; structure Receipt   -- `Log` is declared in EthVmCore (D27) and re-exported here
inductive EncodedReceipt | legacy (r : Receipt) | typed (b : ByteArray)
structure IntrinsicGasCost where execution calldataFloor : Nat
structure ChainContext where chainId : U64; blockHashes : Array Hash32; parentHeader : ParentHeader

-- errors (§2.12); one constructor per EELS class / raise site
inductive GasDim | execution | state
inductive HeaderError | numberZero | excessBlobGas | gasUsedExceedsGasLimit | gasLimit
  | baseFee | timestamp | number | extraData | difficulty | nonce | ommersHash | parentHash
inductive DepositError | length | pubkeyOffset | wcOffset | amountOffset | signatureOffset
  | indexOffset | pubkeySize | wcSize | amountSize | signatureSize | indexSize
inductive ArithFault | chainIdOverflow | excessBlobGasOverflow   -- O13 members (§2.12)
  | balanceOverflow    -- reserved: the create_ether/move_ether sites surface as .state .balanceOverflow (EthState R29)
  | negativeRefund     -- consumed from G4's U256(refund_counter); :285 unreachable, :318 unresolved (Gaps)
inductive TxError
  | wrongChainId (expected actual : U64)
  | transactionTypeContractCreation | blobGasLimitExceeded | insufficientMaxFeePerBlobGas
  | insufficientMaxFeePerGas (maxFee baseFee : Nat) | invalidBlobVersionedHash | noBlobData
  | blobCountExceeded | priorityFeeGreaterThanMaxFee | emptyAuthorizationList
  | initCodeTooLarge | transactionGasLimitExceeded | invalidSender | invalidSignature
  | insufficientBalance | nonceMismatch (tooLow : Bool) | gasUsedExceedsLimit (d : GasDim)
  | insufficientTransactionGas (reason : Fin 4) | nonceOverflow
inductive BlockError
  | invalidTransaction (index : Nat) (e : TxError)
  | txDecode (index : Nat) (e : TxDecodeError) -- RLP DecodingError / 0xFF assert / empty bytes
  | invalidPublicKeyHint (index : Nat) (e : TxError)
  | header (e : HeaderError) | rlpSizeExceeded | publicKeyCountMismatch | ommersNotEmpty
  | gasPriceBelowBaseFee (index : Nat)    -- InvalidBlock raised inside tx admission
  | missingParentHash | systemContractNoCode (a : Address) | systemContractFailed (a : Address)
  | deposit (e : DepositError) | balGasLimitExceeded (items limit : Nat)
  | gasUsedMismatch | transactionsRootMismatch | stateRootMismatch | receiptRootMismatch
  | bloomMismatch | withdrawalsRootMismatch | blobGasUsedMismatch | requestsHashMismatch
  | blockAccessListHashMismatch
  | witness (e : WitnessError)            -- D8, O4
  | state (e : StateError) | vmFault (e : VmFault) -- explicit adapters; retain non-EVM faults
  | arith (f : ArithFault)                -- reachable OverflowError sites (O13)

-- Everything that hashes or reads the pre-state is generic in the oracle monad (D5):
variable {m : Type → Type} [Monad m] [KeccakQuery m]
abbrev BlockM (m) := CheckedT BlockError m                  -- CheckedT from EthVmRunner (F14)

-- codecs and hashes
def encodeTransaction : Transaction → BlockTx
inductive TxDecodeError | empty | unsupported (byte : UInt8) | reservedFF | rlp (e : RlpError)
def decodeTransaction : BlockTx → Except TxDecodeError Transaction
def BlockError.ofStateError : StateError → BlockError -- witness maps to .witness, otherwise .state
def BlockError.ofVmFault : VmFault → BlockError       -- state delegates to ofStateError, otherwise .vmFault
def getTransactionHash : BlockTx → m Hash32
def signingHashPre155 signingHash155 signingHash2930 signingHash1559 signingHash4844 signingHash7702  -- each … → m Hash32
def encodeReceipt : Transaction → Receipt → EncodedReceipt
def decodeReceipt : EncodedReceipt → Option Receipt
def hasAccessList : Transaction → Bool
-- senders
def chainId : Transaction → Except BlockError (Option U64)
def recoverTransactionPublicKey : U64 → Transaction → m (Except TxError ByteArray)
def recoverSender : U64 → Transaction → m (Except BlockError Address)
def recoverSenderFromPublicKey : U64 → Transaction → ByteArray → m (Except TxError Address)
-- gas and validity
def countTokensInData : ByteArray → Nat
def calculateIntrinsicCost (cfg : BlockConfig) : Transaction → Address → IntrinsicGasCost
def validateTransaction (cfg) : Transaction → Address → Except TxError IntrinsicGasCost
def calculateEffectiveGasPrice : Transaction → Nat → Except BlockError Nat
def calculateMaxGasFee : Transaction → Nat → Nat
def checkNonce : Transaction → Nat → Except TxError Unit
def checkGasLimit (cfg) : Nat → Nat → Bool
def calculateBaseFeePerGas (cfg) : Nat → Nat → Nat → Nat → Except BlockError Nat
def validateHeader (cfg) (consts : HashConsts) : ParentHeader → Header → BlockM m Unit   -- parent hash queried
-- bloom, requests
def logsBloom {m : Type → Type} [Monad m] [KeccakQuery m] : Array Vm.Core.Log → m Bloom
def extractDepositData : ByteArray → Except DepositError ByteArray
def parseDepositRequests (cfg) : BlockOutput → Except BlockError ByteArray
def computeRequestsHash : List ByteArray → Hash32
-- BAL (§6)
structure BalBuilder; structure AccountChanges; abbrev BlockAccessList := Array AccountChanges
structure BlockOutput where
  blockGasUsed blockStateGasUsed cumulativeGasUsed : Nat
  transactionValues receiptValues withdrawalValues : Array ByteArray
  blockLogs : LogRope
  blobGasUsed : U64
  requests : Array ByteArray
  blockAccessList : BlockAccessList
-- Dense array position i denotes the reference trie key RLP(i); receiptKeys = range size.
def BalBuilder.{empty, setIndex, addStorageWrite, addStorageRead, addBalanceChange,
  addNonceChange, addCodeChange, removeStorageWrite, removeBalanceChange, removeNonceChange,
  removeCodeChange, addTouchedAccount, build}
def updateBuilderFromTx : BalBuilder → TxState m → m (Except WitnessError (BalBuilder × TxState m))
def buildBlockAccessList : BalBuilder → BlockState m → BlockAccessList
def hashBlockAccessList : BlockAccessList → m Hash32
def validateBlockAccessListGasLimit : BlockAccessList → Nat → Except BlockError Unit
-- pipeline (the seam)
abbrev BlockAcc (m) := BlockOutput × BlockState m × BalBuilder      -- threaded linearly
def checkTransaction (cfg) : BlockEnvironment → BlockAcc m → Transaction → Nat
    → m (Except BlockError (TransactionEnvironment × TxState m))
def processTransaction (cfg) : BlockEnvironment → BlockAcc m → Transaction → Nat
    → BlockM m (BlockAcc m)
def processUncheckedSystemTransaction (cfg) : BlockEnvironment → BlockAcc m → Address
    → ByteArray → BlockM m (TransactionOutput × BlockAcc m)
def processCheckedSystemTransaction (cfg) : BlockEnvironment → BlockAcc m → Address
    → ByteArray → BlockM m (TransactionOutput × BlockAcc m)
def updateSenderState (cfg) : BlockEnvironment → TransactionEnvironment → Transaction
    → StateM m Unit
def disburseGasFees : BlockEnvironment → TransactionEnvironment → TransactionGasSettlement
    → Address → StateM m Unit
def makeReceipt : Transaction → Option VmError → Nat → Array Vm.Core.Log → m EncodedReceipt   -- bloom hashes
def processWithdrawals (cfg) : BlockEnvironment → BlockAcc m → Array Withdrawal → BlockM m (BlockAcc m)
def processGeneralPurposeRequests (cfg) : BlockEnvironment → BlockAcc m → BlockM m (BlockAcc m)
def applyBody (cfg) : BlockEnvironment → Array BlockTx → Array Withdrawal
    → BlockState m → BlockM m (BlockAcc m)
def executeBlockM (cfg : BlockConfig) (consts : HashConsts) (block : Block) (preState : PreState m)
    (ctx : ChainContext) (publicKeys : Option (Array ByteArray)) : BlockM m BlockDiff
def executeBlock (cfg : BlockConfig) (consts : HashConsts) (block : Block) (preState : PreState m)
    (ctx : ChainContext) (publicKeys : Option (Array ByteArray)) : m (CheckedResult BlockError BlockDiff)
    := (executeBlockM cfg consts block preState ctx publicKeys).run.run
-- standalone caller: acquisition precedes provider construction and all validation (F20)
def executeBlockStandalone (cfg : BlockConfig) (mkPre : HashConsts → m (PreState m))
    (block : Block) (ctx : ChainContext) (publicKeys : Option (Array ByteArray)) :
    m (CheckedResult BlockError BlockDiff) := do
  let consts ← HashConsts.query
  let preState ← mkPre consts
  executeBlock cfg consts block preState ctx publicKeys
-- full-state driver (instantiated by EthConformance, at m := Id)
structure BlockChain (σ : Type) where blocks : Array Block; state : σ; chainId : U64
def getLast256BlockHashes : BlockChain σ → m (Array Hash32)      -- hashes the most recent header
def stateTransition (cfg) (toPre : σ → HashConsts → PreState m) (apply : σ → BlockDiff → σ)
    : BlockChain σ → Block → m (CheckedResult BlockError (BlockChain σ))
```

Constants-consuming entry and header helpers use `consts : HashConsts` and local EELS notation (CONTRIBUTING §7.2, F20). `validateHeader` takes the record explicitly because it runs before `BlockState.new`. Body, transaction, BAL and state consumers project `BlockState.consts` through their existing accumulator, state or world arguments. Construction and validation order follow R-EB (§2.7); the provider factory's type alone does not prove coherence.

**Typed root inputs (Q53; unimplemented).** EthBlock supplies the concrete `TrieValue`
bridges for `Option BlockTx`, `Option EncodedReceipt` and optional already-encoded
withdrawal Bytes. `none` interprets Python `None` and is invalid for preparation;
legacy records encode by RLP, and `some` actual Bytes encode by identity and are valid
only when nonempty. Total encoding on `none` or other invalid Lean values supplies no
Python-success claim. Valid legacy interpretations and source agreement retain exact
schema/dispatch and Q47 premises. Lawful optional value equality must agree with
Python for default comparisons; lawful RLP-index byte keys satisfy EthCommit's
injective byte-lex `KeyBytes` contract. If those concrete keys use the existing
Base `Bytes`, the conditional EthCommit adapter uses Q54's supplied
EthBase order/export laws (EthBase §5/§7; EthCommit §7.0.3). Compare the actual
RLP ordinal bytes, not their numeric indices: zero is `[128]`, one is `[1]`, so
zero's key follows one's. This provider choice supplies none of EthBlock's value
encoding, source equality/schema, safety, F20 or host premises. No context-free
Account instance is introduced.

`BlockOutput` retains dense `Array ByteArray` values. The planned public composition
equation identifies `i ↦ values[i]` under key `bytesToNibbleList (rlp i)` with
`prepareTrieModel` of the corresponding default-None, unsecured, safe typed trie.
Every dense encoded entry must be nonempty; a typed bridge proves the corresponding
`PrepareSafe`. Existing `mathRoot` consumes this already encoded map, or the existing
typed `root emptyRoot t unsecured safe` composes it with preparation. Both use the
same empty root projected from the caller's existing context, using F20 notation.
Serialize envelopes/withdrawals once; no additional root API or validity runtime guard
is implied. Equality to a separately sequenced preparation reference needs
`LawfulMonad`, as specified by EthCommit §7.0.3.

Execution threads `BlockState`, transaction observations and `BalBuilder` explicitly. Pure admission/codec checks return `Except BlockError`; functions that hash return in `m`; functions enclosing a runner call run in `BlockM m`, retaining the outer `InternalError` through system calls, body execution and stateful drivers. `runVmChecked` returns `m (CheckedResult …)` (F14); its `VmFault` is mapped through `BlockError.ofVmFault` into the inner channel, and an internal error passes through unchanged (see COMPOSITION.md). No global `IO` or mutable reference is used. Decoding (`decodeTransaction`, `decodeReceipt`, `extractDepositData`) stays pure.

**Supplied calldata-token law.** `countTokensInData_eq data` states the whole result
`zeros + 4 * (data.size - zeros)`, where `zeros` is the length of
`data.data.toList.filter (fun byte => byte == 0)`. It has no domain premise.
The implementation uses the public Base packed fold; references, zero counting
and derived clients are private. No transaction/configuration/error carrier is
introduced by this helper.

**Supplied deposit laws.** `extractDepositData_eq data` states the entire ordered
result on every finite byte array: length 576 first; five complete 32-byte BE
offsets 160/256/320/384/512; then sizes 48/32/8/96/8; then the concatenated
windows `[192:240]`, `[288:320]`, `[352:360]`, `[416:512]`, `[544:552]`.
`size_extractDepositData data result h` concludes `result.size = 192` when
`h : extractDepositData data = .ok result`. No carrier instances or convenience
API are supplied; private clients use the public laws.

**Supplied execution-request commitment law.** `computeRequestsHash_eq requests`
states the entire result as `Hash32.ofBytes32` of the outer SHA of the ordered
flattened complete inner digest byte lists. The equation has no domain premise.
`Hash32.toBytes_ofBytes32` preserves the exact digest bytes. Q46's all-finite
total extension does not establish FIPS/pinned-host agreement above either inner
or outer bound in R-RQ. No new error/result/guard is introduced; production,
filtering, BlockOutput/header/BlockError and guest integration remain separate.

## 6. Data structures

| Type | Representation | Model | Abstraction / invariant | Persistence | Cost |
|---|---|---|---|---|---|
| `BlockParams` | three unrestricted `Nat` fields in §5 order | itself | none beyond field types | read-only, shared freely | O(1) projection/update |
| `SystemAddrs` | eight `Address` fields and two unrestricted `Nat` fields in §5 order | itself | none beyond field types | read-only, shared freely | O(1) projection/update |
| Header, transactions, withdrawals, receipts | structures of `EthBase` types | themselves | none beyond field types | read-only, shared freely | codec linear in size |
| `BlockOutput` counters | `Nat` fields | themselves | `blockGasUsed ≤ gasLimit`, `blockStateGasUsed ≤ gasLimit`, `blobGasUsed ≤ MAX_BLOB_GAS` after every successful `processTransaction` [C] | linear (threaded once per block) | O(1) |
| Transaction, receipt and withdrawal tries | an `Array ByteArray` of values in index order, built linearly; the root is computed once by `EthCommit` over `rlp i ↦ v` | finite map `Nat ⇀ Bytes` with domain `[0, n)` | α = `fun a i => a[i]?`; invariant: dense | linear-only (`Array`), never snapshotted | O(1) amortised append; root O(n log n) or better (EthCommit) |
| `receiptKeys` | implicit (`0…n−1`) | list of `rlp i` | α = `(List.range n).map rlp` | — | — |
| `blockLogs` and per-transaction logs | **rope** (D24, owned by `EthState`/`EthVmCore`); flattened once, per receipt and for the bloom, by the linear traversal of ARCHITECTURE §5.3 | `List Log` | rope → list | persistent, O(1) concat | flatten O(total) |
| Bloom builder | fixed 256-byte `ByteArray`, latest-owner byte updates | private positional Nat bitset and ordered `m Bloom` action | exact size and complete action equality; three selected bits per answer | threaded linearly; compiled uniqueness unclaimed | O(entries), excluding oracle/provider costs; no measured C gate |
| `BalBuilder` | `accounts : Std.ExtTreeMap Address AccountData`; `AccountData = {storageChanges : ExtTreeMap U256 (ExtTreeMap U32 U256), storageReads : ExtTreeSet U256, balance : ExtTreeMap U32 U256, nonce : ExtTreeMap U32 U64, code : ExtTreeMap U32 ByteArray}`; memo tables `ExtTreeMap (U32 × Address) (Option Account)` and `ExtTreeMap (U32 × Address × Bytes32) U256`; `index : U32` | `Address ⇀ (slot ⇀ idx ⇀ value) × Set slot × (idx ⇀ bal) × (idx ⇀ nonce) × (idx ⇀ code)` | α forgets the tree structure; invariant: Std's `Ordered`/WF, **no empty inner storage map** (matching `:539`), and memo entries equal the pre-values at their index | linear (threaded once through the block; never inside a call snapshot) | each add/remove O(log n); build O(N) through ordered `toList` |
| `BlockAccessList` | `Array AccountChanges` | a sorted list | invariants: addresses strictly increasing; per account, slots strictly increasing, reads strictly increasing and disjoint from written slots, change lists strictly increasing by index | read-only | hash O(size) |

EELS keeps change *lists* and sorts at the end (`:649–685`). A map keyed by index gives the same result, because EELS itself keeps at most one entry per index: replace-in-place, or maximum for nonces. It is also sorted by construction. The equivalence is a [C] lemma (§7). The builder is not reachable from a call snapshot (it is touched only at incorporation), so ARCHITECTURE §5.0 permits a `HashMap`. The ordered tree is chosen so that `build` needs no sort and its output order follows from `ordered_keys_toList` (ARCHITECTURE §5.6). `ofList`/`union` are not used on the hot path (ARCHITECTURE §5.0 caveat); per-transaction updates are single inserts.

## 7. Contract and laws

The supplied raw `BlockParams`, `TxParams` and `SystemAddrs` have ordinary structure
reduction and reconstruction; §3 records private arbitrary-input projection/update clients for
every field. No additional public law package or global configuration predicate is supplied.

**System-address construction** [C] (F8; unimplemented): for every raw cfg, `cfg.runnerEnv.systemAddress = cfg.system.systemAddress`. Both actual runner entries, `processTransaction` and `processUncheckedSystemTransaction`, pass this environment; the checked-system path delegates to the unchecked path after its code check. Runner creation and child inheritance then preserve the field. Raw SystemAddrs and BlockConfig stay unrestricted: pinned-source coherence is an intended assembly/refinement obligation, without a runtime validator or new gas/admission premise. BlockEnvironment, VmWorld, HashConsts and existing block/runner function parameter lists are unchanged.

Per operation (model-based, D25):

- **Calldata tokens (supplied).** `countTokensInData_eq` gives the complete zeros + 4·(size − zeros) equation on every finite `ByteArray`. The private ordinary packed/reference equality relates a linear packed weighted fold to a structural list reference; the reference formula identifies the exact source expression. Filter length ≤ input length discharges the source `Uint` subtraction, and `Nat` preserves its unbounded result. Private public-law clients establish empty = 0, concatenation additivity and size ≤ tokens ≤ 4·size. This helper's zero-sensitive token count does not change the separate all-bytes calldata-floor rule in R-IG. [R][T]

- **Deposit extraction (supplied).** `extractDepositData_eq` preserves the first reached constructor among the eleven source guards and every successful output byte, without a domain premise. Full unbounded BE reads reject high-bit corruptions. All offsets are admitted before size checks, so fixed size/data windows equal the source's reached dynamic offsets. `size_extractDepositData` derives exact 192-byte output from success and the admitted 576-byte length using public slice/append/export laws. No ignored-padding or field-content check is added. Source intermediate slice allocation/failure and O12 host resources remain separate. [R][T]

- **Execution-request commitment (supplied).** `computeRequestsHash_eq` identifies the complete ordered SHA-of-SHA result through the existing pure SHA provider and exact `Hash32.ofBytes32` bridge. A private ordinary packed/List equality proves that reservation and per-digest byte emission preserve the entire outer preimage. Empty requests and duplicates are retained; no request typing, order normalization or content validation occurs. Private facade clients derive complete output-byte, empty/singleton/pair and exact model-preimage-size consequences using public contracts only. Source/FIPS agreement retains each inner and outer Q46 bound and host/API/native premises; source streaming storage and crypto binding are separate. [R][T]
- **BAL builder.** Every `BalBuilder` operation preserves the invariant and commutes with α, where the model operations are finite-map update/erase with "last wins" (storage, balance, code) and "max wins" (nonce). [C]
  - `build_sorted`: the output of `build` satisfies the `BlockAccessList` invariant. [C]
  - `build_eq_eels`: `build b = sortBy… (eelsBuild (αList b))`. That is, it equals EELS's list-and-sort result for any trace of EELS operations, by uniqueness of sorted lists over a strict order (Nipkow et al. Thm 2.9). [C]
  - `readsDisjoint`: read slots minus written slots. [C]
- **Logs bloom (supplied).** `logsBloom_eq` gives the complete `m Bloom` action:
  flatten each address-byte preimage followed by its ordered topic-byte preimages,
  fold left from Nat zero, bind exactly one `KeccakQuery.keccak` per entry, and
  OR the accumulator with `2^((h.toNat / 2^240) % 2048)`,
  `2^((h.toNat / 2^224) % 2048)` and `2^((h.toNat / 2^208) % 2048)`;
  return `(FixedBytes.ofNat result : Bloom)`. The private packed/reference theorem
  proves this full result/action equality for all inputs. `logsBloom_empty` is
  `logsBloom #[] = pure (FixedBytes.ofNat 0 : Bloom)`. Under lawful sequencing,
  `logsBloom_append` is `logsBloom (a ++ b) = do let ba ← logsBloom a;
  let bb ← logsBloom b; pure (FixedBytes.ofNat (ba.toNat ||| bb.toNat) : Bloom)`.
  Both calls share the same evolving oracle context. `LawfulMonad` is used only by
  these ordinary sequencing-normalization proofs; the operation remains under
  plain `Monad`. No oracle law, stable answer or reset is assumed. Duplicates and
  arbitrary topic counts remain observable, and data is irrelevant. [R][T]
- **Receipts.** The receipt of transaction `i` carries the cumulative gas
  `Σ_{j≤i} gasUsed_j`; actual receipt/transaction integration remains unimplemented. [C]
- **Tries (Q53; unimplemented).** Each root is `mathRoot emptyRoot` of the dense encoded ordinal map specified in §5, equal to EthCommit's typed `root emptyRoot t unsecured safe` by its pure preparation equation. EthBlock establishes value validity, lawful byte keys (conditionally using Q54 providers when choosing existing Bytes), source equality/encoding and complete schema/assembled `Encodable` premises, and supplies the coherent F20 context root. The stateless-path header derives it from the same bytes, so for canonical encodings the comparison is [I] a tautology. [C, once the required provider/consumer and EthCodec round-trip laws exist]
- **Arithmetic safety.** Each lemma discharges an EELS `-` that would raise:
  - `updateSenderState` never underflows after `checkTransaction` succeeds, since `maxGasFee ≥ gas·price + blobFee`;
  - `priorityFee = price − baseFee ≥ 0`;
  - the base-fee decrease never underflows (`Δ ≤ baseFee/8`);
  - `checkGasLimit p g = false` for all `g` when `p < 1024`, so `target = 0` is never divided by;
  - the block-capacity subtractions never underflow, because the counters stay ≤ `gasLimit`. This is [I] and needs G4's bound `execUsed ≤ min(TX_MAX_GAS_LIMIT, gas)` and `stateUsed ≤ gas`.
  
  Each is [T]: it justifies computing with `Nat` truncated subtraction where EELS would raise.
- **Order.** `validateHeader` returns the error of the first failing check in R-VH order, and similarly for R-VT, R-CT and R-EB. These are stated as equations that unfold one check at a time. [R]
- **Hint equivalence.** If `chainId tx ∈ {none, some ctx.chainId}` and `ks[i] = recoverTransactionPublicKey ctx.chainId tx`, then the hint path and `recoverSender` return the same sender. Otherwise the hint path raises `invalidSignature`. [C] It is used by consumers that replace full recovery (CONTRACT §2). [R]
- **Seam.** `executeBlock cfg consts b ps ctx ks` depends on `ps` only through the `PreState m` operations. At `m := Id`, a **successful witness execution** over `ps` is simulated by a progressive full backend of σ, assuming `Models ps σ`, code authenticity, reachable caller invariants, and agreement on every successful answer; the post-state root agrees or yields a named hash collision. This is the directional block-level agreement obligation for EthSecurity (COMPOSITION §5), not equality of success and failure for arbitrary `Models` providers. [R][S] The oracle coupling at generic `m` is open (D5).
- **Constants lifetime (F20).** Prove the acquisition and effect order in §2.7 as implementation equations. The kernel preserves the supplied record in `BlockState.new`; context consumers read the stored fields, including under synthetic constants differing from the Id literals. These laws are unimplemented; generic oracle and backend coupling remains D5/X7. [R]
- **Determinism and totality.** Every function here is total. The only recursion is structural over the transaction, withdrawal, log and BAL arrays, apart from the runner calls, whose totality is `EthVmRunner`'s obligation (O11). [T]
- **Conservation** (generic, a hypothesis on `cfg`; discharged for Amsterdam in `EthFork`): the sum of balance changes over sender, coinbase and burn in one transaction is 0 when the frame's value transfers are counted. [C] The strategy is open (Gaps).

### Informal correctness argument

**Claim.** The ordered block pipeline reproduces validation, transaction/system execution, receipts, requests, BAL and final commitments, provided the runner/backend contracts and error adapters hold.

**Premises.** Exact record schemas and check order; well-formed fork configuration; runner fuel sufficiency; reachable state invariants; backend successful-answer/root agreement and data availability; checked arithmetic rather than silently widened reference values.

**Argument.** Induct over pipeline stages and then over transactions, maintaining the accumulated diff, gas counters, receipt sequence and BAL builder relation. Admission establishes sender balance/nonce and intrinsic-gas premises before execution. Sender hints must be verified against the same signing hash and recovered key; mere hint length is insufficient. Settlement updates fees and receipts using the runner's distinction between success, revert and halt. Update BAL from the unmerged transaction and block views before incorporation: first-index pre-values remain fixed, balance/code keep the last change and nonce the maximum. Ordered dense trie inputs reproduce index-keyed transaction/receipt/withdrawal roots. System calls omit user gas counters; unchecked calls ignore FrameError but propagate backend faults and InternalError. Finish by computing requests and asking the backend for the ordered diff root, then perform the reference's commitment checks.

**Open obligations.** Instantiate every schema, arithmetic failure and ordered adapter; prove BAL read side effects and index bounds; establish backend-parametric trace simulation. Success against an unanchored supplied parent is not a statement of accepted-chain validity.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthVmRunner`, `EthCodec`, `EthCommit`
- **Used by:** `EthFork` (instantiation), then `EthStateless` and `EthConformance` through it. `EthConformance` also instantiates `stateTransition` with `EthStateFull`.
- **Seams consumed.**
  - `PreState m` and `ModelsLookups` (EthState, D9; stated at `PreState Id`), assumed and not checked: every `PreState` passed in satisfies `Models` for the property statements, while execution works for any `PreState m`.
  - `HashConsts` (EthBase) and `HashConsts.query`, `KeccakQuery` with its `ExceptT`/`StateT` lifts (EthHash).
  - `CheckedT`, `runVmChecked` (EthVmRunner, F14).
  - `BlockState`/`TxState` operations and observers from `EthState`: `getAccount`, `getCode`, `incrementNonce`, `setAccountBalance`, `createEther`, `clearAccountPreservingBalance`, `incorporateTxIntoBlock`, `extractBlockDiff`, `trackAncestorAccess`.
  - `processTopLevel`, `TransactionEnvironment`, `BlockEnvironment`, `BlockOutput`, `settleTransactionGas`, `allocateEvmGas`, the blob-gas helpers and `isValidDelegation` from `EthVmCore`/`EthVmRunner`/instructions.
  - `secp256k1Recover` through `EthVmRunner`'s transitive closure (`EthCurve`).
  - EthCommit's existing `root`/`mathRoot` over the safe typed/prepared dense maps (§5, Q53), with caller context empty root and lawful byte keys; EthBlock supplies its concrete validity/encoding bridges. RLP from `EthCodec`; keccak (`KeccakQuery`) and SHA-256 from `EthHash`.
- **Dependency inversion (required).** EELS's `incorporate_tx_into_block` (`state_tracker.py:842–847`, G3) calls `update_builder_from_tx`, but `EthState` must not see the BAL. The spec therefore splits it:
  1. `EthBlock` calls `updateBuilderFromTx` **first**, reading the un-merged block state;
  2. it then calls `EthState.incorporateTxIntoBlock`.
  
  A law must show that the pair equals the EELS function. `EthState` must export read-only observers for `preTxAccount`/`preTxStorage`: the block-level account write, storage write, clear set and pre-state for one key, plus the block-level read sets consumed by `buildBlockAccessList`. **This is a requirement on G3.**
- **Precompile table.** The runner needs the table (`vm/interpreter.py:172, 438` also uses its key set to warm addresses), and `EthBlock` may not import `EthPrecompiles`. It is therefore a field of `BlockConfig`, filled by `EthFork`.
- **Guaranteed to callers.** On `.ok (.ok diff)`, the header's commitments equal the recomputed ones; `diff` is the block diff whose root is `header.stateRoot`, via `ModelsRoot`.

## 9. Open decisions

- **D3** (accepted): Amsterdam only. `PrevHeader` is the one bpo5 artefact, and exists because parents may be pre-fork.
- **D8**: `WitnessError` is carried as `BlockError.witness`, kept separate from invalidity inside the spec, although the output collapses them.
- **D5** (provisional, broad): every keccak goes through `KeccakQuery`; signatures are monad-parametric; the keccak-derived constants (`emptyOmmerHash` here) are `HashConsts`.
- **D14** (accepted): the constructors in §5 refine O4–O7; the reachable deterministic Python runtime faults are CONTRACT O13 members with named constructors (§2.12). Error types are frozen once this module's entries in the failure ledger (maintained outside this repository) close (DECISIONS B14); several implicit sites are still unresolved.
- **D2**: BAL sorting requires `compare` on `Address` to be big-endian lexicographic, and `U256` to be numeric.
- **D22/D23/D24/D25**: persistence of `BlockState`, observation sets outside the snapshot, logs as a rope, and model-based BAL laws.
- **D13/D17**: `processTopLevel` is consumed only through the runner.
- **D18** (accepted): no debt entry needed yet.
- **D26/D27** (accepted): sender and authority recovery reach `EthCurve` through `EthVmRunner`; `Log` is in `EthVmCore`, `BlockOutput` here.
- Parameter values: resolved, DECISIONS B8 (Q1): types here, values in `EthFork`.
- Named runtime-fault constructors: resolved, DECISIONS B14 (Q2) and CONTRACT O13: named constructors, no `runtimeFault` catch-all.
- Blob-price feasibility: tracked as DISC-002 (Q3).
- Q53: typed root input/default/validity and key contracts follow R-TRIE/§5; consumer bridges and dense-map composition remain unimplemented.

## 10. Gaps

- **Implemented bounded scope:** `countTokensInData`, `extractDepositData`, `computeRequestsHash` and `logsBloom`, with their complete all-finite result/action laws, extraction success-size law and lawful Bloom empty/sequential-append laws, are supplied (§3/§5/§7). Their 266-case, 142-case, 298-case and 20-case complete native/source observations supply finite coupling only. Bloom observations retain all 85 ordered query occurrences of its 20-case catalogue; the operation requires no oracle law or `LawfulMonad`, while the action laws use lawful sequencing. Its independent single-log test attribution repair is owned by §4. Actual receipt/block integration, generic oracle coupling, compiled ownership and all C1–C4 claims remain open. The request commitment retains each inner and outer Q46 bound for source/FIPS agreement, host/API/native premises, separate streaming/materialized-storage limits and no cryptographic binding claim. Original fixture literal provenance adds no fixture/EVM execution claim. Source/runtime authentication, intermediate allocation and host-resource guarantees, BlockError/request collection integration, composed intrinsic gas/floor and the remaining block pipeline remain open. No readiness or resource gate closes.

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Block parameters:** the raw three-field `BlockParams` is supplied (§3), with all five R-F1 source quantities owned by EthFork. Actual size/base-fee consumers, division safety, full `BlockConfig`, configuration coherence and index adequacy remain open.
- **System addresses and budgets:** the raw ten-field `SystemAddrs` is supplied (§3); actual system-call/request consumers, F8 runnerEnv projection at both runner entries and construction/source coherence remain open. Controls must vary the supplied address independently of the F20 topic, through user and unchecked/checked system paths; unchanged checked-system guard/error ordering and request processing remain separate.
- **Transaction parameters:** the raw three-field `TxParams` is supplied (§3); actual admission/intrinsic-cost consumers, full `BlockConfig`, configuration coherence and blob-budget premises remain open.
- **F20 implementation/refinement:** acquire and thread the F20 record, prove constructor/context preservation and wrapper effect order, and establish backend coherence. DECISIONS §6 records the design; these production obligations remain open.
- **Typed root consumers (Q53):** implement the actual Bytes-identity/legacy-RLP/typed-envelope/withdrawal-already-RLP bridges, prove stored-value validity and dense-array/prepared-map equality with lawful byte keys, default-None semantics and caller-context empty root, and run §4's exact-byte/public-client validation. All remain unimplemented; Q53 discharges none of the schema/assembled `Encodable`, equality, F20 or host premises.
- **Fork activation is not checked** (CONTRACT §5). `executeBlock` never compares the timestamp with an activation time; blocks are executed as Amsterdam unconditionally. This is an explicit exclusion that follows the reference, and the L1 consumer supplies activation outside this guest.
- **Slot number** (EIP-7843) is not validated against the parent or any rule in `validateHeader`. It is only passed to the environment. The same is true of `prevRandao`, `parentBeaconBlockRoot` and an upper bound on the timestamp. This follows the reference; whether it is intended is unconfirmed upstream.
- **Adversarial `excessBlobGas`, feasibility.** For an unanchored parent header (CONTRACT §7: the parent is authenticated only by hash to the payload's `parent_hash`), `calculate_excess_blob_gas` calls `calculate_blob_gas_price(parent.excess)`, whose Taylor loop (`utils/numeric.py:199–207`) needs about `e·excess/11 684 671` iterations over numbers with about as many bits. At `excess ≈ 2⁶⁴` that is about 4×10¹² iterations (DISC-002), and EELS would hang or fail with `MemoryError` (O12). Ordinary totality of the Taylor helper for a positive denominator is supplied by [EthBase §3/§7](EthBase.md#implemented-taylor-exponential). Completion of the price wrapper, its callers’ domain and exception obligations, and practical feasibility remain open. DISC-002 records measured smaller-input behaviour and large-input extrapolation; the maximum input was not executed.
- **O13 overflow sites** (evidence from the pinned EELS; sites shared with `EthState` and `EthVmCore`). The legacy-`v` `U64` overflow in `chainId` (`transactions.py:878`) is witnessed by a probe input. The parent-header `U64` overflows in `calculate_excess_blob_gas` (`vm/gas.py:931, 945`) and the `U256` balance overflow in `createEther`/`moveEther` (`state_tracker.py:663, 687`: a balance near 2²⁵⁶ plus a fee refund, coinbase fee or withdrawal) are argued reachable, not corpus-witnessed. All map to `(root, false, …)` through named constructors (§2.12).
- **Negative refund counter.** `U256(gas_meter.refund_counter)` (`vm/interpreter.py`, G4) raises if the counter is negative: the cast at `:285` is proved unreachable; the one at `:318` is unresolved. `negativeRefund` is reserved for it.
- **EEST exception labels.** Mapping `blockchain_tests` `expectException` strings to constructors (for example the legacy `gasPrice < baseFee`, which EELS raises as `InvalidBlock`, and `txDecode`) is warning-only; validity is decisive (DECISIONS Q9).
- **`TransactionTypeContractCreationError`** is believed unreachable after RLP decoding [I]. It needs an EthCodec lemma (`Address` cannot decode from the empty string).
- **Lazy decode order** (R-AB 4) matters only for which error is reported. The guest output is the same; `blockchain_tests` may observe it.
- **`create_ether` of 0 to the coinbase and origin**: the BAL and state effects of a zero-amount touch depend on `EthState`'s `modify_state` and account-deletion rules, which were not re-read here.
- **The `SYSTEM_ADDRESS` in the BAL**: whether the system caller is recorded as touched depends on G4's `process_top_level` reads. It is not pinned down here and needs a fixture check (`test_block_access_lists_system_call_reads.py` is the likely generator).
- **Reference evidence:** rerun load-bearing historical codec experiments against locked 0.1.6; the review environment now matches the lock, but has not exhaustively validated transaction codecs.
- **Transition fixtures** `for_bpo2toamsterdamattime15k`: `blockchain_tests` over the full-state backend need bpo2 execution for pre-transition blocks, which D3 excludes. They are skipped and counted in the stateful runner until a bpo2 instantiation exists (DECISIONS Q8); only the stateless variants whose executed block is Amsterdam run.
- **The G3 dependency inversion** (§8) uses the read-only BAL views already listed in `EthState` §5. Their completeness for every builder input and the equivalence lemma with EELS's single `incorporate_tx_into_block` remain unproved; expand the views if the BAL implementation exposes a missing observation.
- **Conservation law** (§7): no proof strategy yet; it depends on G4's frame-level value-transfer and SELFDESTRUCT (EIP-8246) contracts.
- **Complexity**: the BAL build cost with `ExtTreeMap` is expected to be O(N log N), but no `Std` cost theorem exists (ARCHITECTURE §5.0). Trie roots are built from scratch per block (EthCommit's cost) and not measured.
- **Not specified here (owned elsewhere)**: EIP-7702 authorization processing (`set_delegation`, G4); settlement internals and the 2-D gas meter (G4); `NewPayloadRequest` → `Block` conversion, `is_valid_block_hash` and versioned-hash checks (G6); account and storage trie roots (G3).
