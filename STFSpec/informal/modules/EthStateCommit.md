# `EthStateCommit`: account and storage encodings, the state-root law, code-hash agreement, `Models`

*Status: informal specification, draft. Date: 2026-09-30. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F2, F4, F16, F20 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D5, D9, D16, D20 · questions: B2 (Q30), Q16.*

## 1. Purpose

`EthStateCommit` is the small integration component (ARCHITECTURE §3, v2.1; D20) between state semantics (`EthState`) and the generic trie (`EthCommit`). It owns the account and storage leaf encodings and their (lenient) witness decodings, the state root of a mathematical state `mathStateRoot`, code-hash agreement, and the full backend contract `Models ps σ := MathState.WF σ ∧ CodeAuthentic σ ∧ ModelsLookups ps σ ∧ ModelsCode ps ∧ ModelsRoot ps σ`. Both backends prove `Models` against these definitions; neither `EthState` nor `EthCommit` imports the other.

## 2. Requirements

- SC1. **Account leaf encoding** (`merkle_patricia_trie.py:193–210`): `rlp [nonce, balance, storageRoot, codeHash]`, integers as minimal big-endian RLP strings, `storageRoot` and `codeHash` as 32-byte strings. The same function appears in `forks/amsterdam/fork_types.py` (claimed here); the two must be one Lean definition or proved equal.
- SC2. **Storage leaf encoding**: `encode_node(U256)` is `rlp.encode` of the integer (`merkle_patricia_trie.py:268–269`), i.e. the minimal big-endian bytes as an RLP string; value `0` is never stored (the trie default, `state_mpt.py:106`, `witness_state.py:258`).
- SC3. **Secured keys**: account keys are `keccak256(address)`, storage keys `keccak256(slot)` (`Trie(secured=True, …)`, `state_mpt.py:40`, `:106`; `witness_state.py:156`, `:168`, `:191`).
- SC4. **`mathStateRoot σ`** = `mathRoot` of `{keccak256 a ↦ encodeAccount (σ.accounts a) (storageRoot σ a)}` where `storageRoot σ a = mathRoot {keccak256 k ↦ rlp v | σ.storageAt a k = v ≠ 0}`, which is `EMPTY_TRIE_ROOT` for no storage (`state_mpt.py:113–118`; `merkle_patricia_trie.py:429–433`). Storage of absent accounts does not contribute. Every hash here (secure keys, node references, the root) goes through `KeccakQuery` (D5), and the empty constants come from `HashConsts` (`EthBase`); the model definitions are stated at `m := Id` (§5).
- SC5. **Account leaf decoding** (`witness_state.py:103–127`), lenient [executed against pinned `ethereum_rlp`]: the leaf must RLP-decode to a list of exactly 4 items (else malformed); each field that is falsy (the empty string **or the empty list**) takes its default (`0`, `0`, `EMPTY_TRIE_ROOT`, `EMPTY_CODE_HASH`, i.e. the `HashConsts` fields, which the decoder therefore takes as a parameter); otherwise nonce and balance are big-endian with **leading zeros accepted**, nonce unbounded, balance ≥ 2²⁵⁶ fails (`OverflowError`); a non-empty storage root or code hash of length ≠ 32 fails (`ValueError`); a non-empty list in any field fails (`TypeError`). An empty leaf value fails (`rlp.decode(b"")`). All failures are witness failures (O4).
- SC6. **Storage leaf decoding** (`witness_state.py:198–203`): RLP-decode; a string → its big-endian value (leading zeros accepted; > 32 significant bytes fails with `OverflowError`); the empty string → `0`; **a list → `0`** silently. RLP failure → witness failure.
- SC7. **Code-hash agreement**: the empty constants are `HashConsts` fields (`EthBase`; D5), and `EthHash` checks that `HashConsts.query` at `Id` yields `HashConsts.literals`, in particular `emptyCodeHash = keccak256 ByteArray.empty` (`state.py:36`) and `emptyTrieRoot = keccak256 (rlp b"")` (`EthHash` §7); a code DB entry is keyed by the keccak of its bytes (`witness_state.py:45–50`; `state_mpt.py:168–170`); `EthState.setCode` callers pass `keccak256 code` (ARCHITECTURE §5.3). `ModelsCode ps` (for `ps : PreState Id`; B2: `getCode` has no absent case): `ps.getCode consts.emptyCodeHash = .ok ByteArray.empty` (with `consts = Id.run HashConsts.query`) and `ps.getCode h = .ok c → keccak256 c = h`. Missing code is `.error`, which `ModelsCode` leaves unconstrained (a progress question).
- SC8. **`ModelsRoot ps σ`** (for `ps : PreState Id`): for every `d` with `BlockDiff.WF σ d`, `ps.stateRoot d = .ok r → r = mathStateRoot (σ.apply d)`. `code_changes` never affects the root (the MPT commits to code hashes only, `state_mpt.py:87–89`; `state.py:129–135`).
- SC9. **`Models ps σ`** is stated for `ps : PreState Id` (D5, F1); the oracle coupling for a generic `m` is open (D5, `EthSecurity`). It requires `MathState.WF σ` and `CodeAuthentic σ`. For a witness backend with authenticated node/code DBs, coherent HashConsts and the specified decode thunk (WitnessBackend.WF), it holds **up to a computable collision** (§7): for every structurally WF, code-authentic σ whose `mathStateRoot` is the parent root, `Models ps σ` or a Keccak collision is found among node/key/code preimages, including the witness code DB and σ’s code bytes. Backend **progress** is separate (ARCHITECTURE §5.3) and stated in each backend.
- SC10. The encodings are canonical: `decodeAccountLeaf (encodeAccount a r) = .ok (a, r)` and `decodeStorageLeaf (encodeStorage v) = .ok v` for `v ≠ 0`; lenient decodings of non-canonical leaves are reachable only under a collision (§7.2).

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `merkle_patricia_trie.py::encode_account` | 193 | `encodeAccount` | also `fork_types.py` (G1) |
| `forks/amsterdam/fork_types.py::encode_account` | 67 | `encodeAccount` | the fork-local copy; same RLP `(nonce, balance, storage_root, code_hash)` as the shared one (verified by reading both); one Lean definition serves both |
| `forks/amsterdam/witness_state.py::_decode_account_from_leaf` | 103 | `decodeAccountLeaf` | lenient, SC5 |

Also specified here without their own inventory items: the storage-leaf decoding inlined in `WitnessState.get_storage` (`witness_state.py:198–203`, `decodeStorageLeaf`), the `Account` instance of `encode_node` (`merkle_patricia_trie.py:263–265`) and the storage-root callback of `root`/`_prepare_data` (`merkle_patricia_trie.py:410`, `:430–433`).

**External semantics.** `ethereum_rlp.rlp` (strict decode; integer encoding of `Uint`/`U256` as minimal big-endian strings); `int.from_bytes(·, "big")` (leading zeros allowed); `ethereum_types` `U256`/`Uint` constructors (`U256` rejects ≥ 2²⁵⁶ with `OverflowError`) and `Bytes32`/`Hash32` constructors (reject wrong lengths with `ValueError`) — all [executed].

## 4. Tests

- **EEST fixture areas:** every blockchain fixture's post-state root exercises `mathStateRoot` (through `EthStateFull`) and its witness variant; `amsterdam/eip8025_optional_proofs` for leaves read from witnesses; `prague/eip7702_set_code_tx` and `cancun/create` for code-hash handling.
- **EELS unit tests:** `tests/json_loader/test_witness_state.py` `TestGetAccountOptional`, `TestGetStorage`, `TestComputeStateRoot` (leaf decoding and roots through the backend).
- **`core` `#guard` cases** (all dependencies must be implemented before evaluation, F16; core proof holes are banned): `encodeAccount (emptyAccount consts) consts.emptyTrieRoot` bytes, with `consts = HashConsts.literals`; `mathStateRoot` of the empty state is `emptyTrieRoot`; a one-account, one-slot state against a fixture root; round trips SC10; lenient cases of SC5/SC6 (all-empty-string and all-empty-list leaves decode to the defaults; nonce `0x0001`; 31-byte storage root fails; balance ≥ 2^256 fails (a longer encoding with leading zeros can still fit); list-valued storage leaf decodes to `0`; empty leaf value fails).
- **Property tests:** round trips on random accounts and values; `mathStateRoot` invariant under insertion order; `mathStateRoot σ` unchanged by adding storage for an absent account.

## 5. Interface

```lean
-- public. Encodings and leaf decodings are pure; anything that hashes is generic in the
-- oracle monad (D5). The model roots are parametric in m and are used at m := Id, where
-- mathStateRoot etc. abbreviate their Id.run values; Models is stated at PreState Id.
variable {m : Type → Type} [Monad m] [KeccakQuery m]
def encodeAccount (acc : Account) (storageRoot : Hash32) : ByteArray
def encodeStorage (v : U256) : ByteArray                      -- v ≠ 0
def decodeAccountLeaf (consts : HashConsts) (leaf : ByteArray) : Except WitnessError (Account × Hash32)  -- SC5 defaults from consts
def decodeStorageLeaf (leaf : ByteArray) : Except WitnessError U256                 -- SC6
def storageTrieMap (σ : MathState) (a : Address) : m (Std.ExtTreeMap Nibbles ByteArray)   -- secure keys
def storageRoot (consts : HashConsts) (σ : MathState) (a : Address) : m Hash32
def accountTrieMap (consts : HashConsts) (σ : MathState) : m (Std.ExtTreeMap Nibbles ByteArray)
def mathStateRoot (consts : HashConsts) (σ : MathState) : m Hash32
def CodeAuthentic (σ : MathState) : Prop -- every stored (h,c) has keccak256 c = h; no availability claim
def CodeChangesAuthentic (d : BlockDiff) : Prop -- same property for codeChanges
def ModelsCode (ps : PreState Id) : Prop                        -- SC7
def ModelsRoot (ps : PreState Id) (σ : MathState) : Prop        -- SC8
def Models (ps : PreState Id) (σ : MathState) : Prop :=
  MathState.WF σ ∧ CodeAuthentic σ ∧ ModelsLookups ps σ ∧ ModelsCode ps ∧ ModelsRoot ps σ
-- The Id check HashConsts.query (m := Id) = HashConsts.literals is EthHash's (EthHash §7).
-- for the witness backend and EthSecurity
def StateCollision (db : NodeDB) (codes : List (Hash32 × ByteArray)) (σ : MathState)
    : Option (ByteArray × ByteArray) -- include node, secure-key AND code preimages
instance : TrieValue U256                                      -- EthCommit class, storage values
```

These decoding and model-root helpers receive the caller's record (F20), using `variable (consts : HashConsts)` and local EELS notation for defaults. Backend callers with an existing constants field project that field; the helpers never acquire constants or substitute `HashConsts.literals` in generic execution. The Id laws here keep their concrete interpretation premise; F20 does not discharge generic oracle coupling.

## 6. Data structures

No new containers. `accountTrieMap`/`storageTrieMap` are `ExtTreeMap Nibbles ByteArray` views computed on demand (model definitions, O(n log n) to build; used by `EthStateFull` and in proofs, never on the witness path). Persistence: values only.

## 7. Contract and laws

### 7.1 Encoding laws [C], feeds [S]

- Round trips SC10; injectivity of `encodeAccount` in `(acc, root)` and of `encodeStorage` (from RLP injectivity, `EthCodec`).
- `storageRoot σ a = emptyTrieRoot ↔ σ.storage a` is empty (given `WF`; ⇐ by definition, ⇒ needs collision freedom and is stated as "or collision").
- `mathStateRoot` depends only on `σ.accounts` and the storage of existing accounts; it ignores `σ.code`.

### 7.2 Root and apply [C], [R]

- `mathStateRoot (σ.apply d)` is the root after `apply_changes_to_state` (`state_mpt.py:133–161`) and after `State.compute_state_root` (`state_mpt.py:82–120`) — the full backend's commuting equation.
- **Lenient decodings are collision-guarded:** if a leaf decoded by `decodeAccountLeaf` is not the canonical encoding of the result, then no WF σ with the same root has it without a collision, since the leaf bytes are part of an authenticated node.
- **Witness agreement (lifting `EthCommit.decode_agreement`):** for the witness backend `ps` built from authenticated `db` and `codes`, coherent HashConsts and parent root `r`, and every structurally WF, code-authentic σ with `mathStateRoot σ = r`: `Models ps σ ∨ (StateCollision db codes σ).isSome`. The storage-trie part applies `decode_agreement` per account, with the storage root taken from the authenticated account leaf. Code-store authenticity is an additional premise because the state root does not commit to the code store's values.

### 7.3 Code [C]

- **Empty constants.** Under D5 the constants are `HashConsts` fields queried through the oracle; the literals (`HashConsts.literals`, `EthBase`) are only their values at `Id`. This module's laws use `consts = Id.run HashConsts.query`. `EthHash` owns the check `HashConsts.query (m := Id) = HashConsts.literals` (`EthHash` §7), so this module states no separate literal-equality theorem.
- `setCode` agreement: if every `EthState.setCode` call passes `keccak256 code`, every `BlockDiff.codeChanges` entry `(h, c)` has `keccak256 c = h` and `h ≠ consts.emptyCodeHash`.

### Informal correctness argument

**Claim.** The account/storage adapters connect successful provider answers and roots to MathState, with code authenticity and collisions treated explicitly rather than inferred from structural state well-formedness.

**Premises.** EthState structural laws, EthCommit canonical root laws, exact account RLP field order, CodeAuthentic σ, and CodeChangesAuthentic for updates that introduce code.

**Argument.** Canonical account encoding is injective by the four field codecs; storage encoding omits zero values and preserves the canonical integer encoding. Apply the trie equation first to each storage map, then to the account map whose leaves include those storage roots. This yields mathStateRoot and the root clause of Models. Code storage is a separate map: state roots bind account code hashes, but do not authenticate the bytes stored under them. CodeAuthentic supplies that missing equation. Compare successful witness paths with the mathematical paths: equal encoded preimages permit descent; differing preimages with equal hashes yield a collision. The extractor must include trie nodes, secure-key preimages and code preimages from both the witness and σ, not only node DB entries.

**Open obligations.** Complete the collision extractor and its finite query set, lenient leaf-decoding refinement and the hash-relative code-authenticity model. Backend progress is additional to Models: a backend that always errors would otherwise satisfy successful-answer implications vacuously.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthState`, `EthCommit`
- **Used by:** `EthStateFull`, `EthStateWitness`, `EthSecurity` (proofs).
- **Seams:** the `Models` predicate is the contract every backend proves and every refinement theorem over `executeBlock` assumes; `mathStateRoot` is what `EthBlock`'s state-root check means semantically.
- **Relies on:** `EthCommit`'s `mathRoot`, `represents` and `decode_agreement`; `EthState`'s `apply`, `BlockDiff.WF` and `ModelsLookups`; RLP injectivity from `EthCodec`.

## 9. Open decisions

- D5 (broad scope, monad-parametric): the model roots hash through `KeccakQuery` and take `HashConsts`; `Models`, `ModelsCode` and `ModelsRoot` are stated at `PreState Id`. Open: the coupling at generic `m`, and phrasing `StateCollision` over the same oracle as the trie.
- D9, D20 (accepted): `Models` is split exactly as here.
- D16 (accepted): this is the only place encodings meet semantics.
- NEW-STATE-2 (from `EthState`): resolved: DECISIONS B2 (Q30); SC7 has no `.ok none` case.

## 10. Gaps

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Lenient leaf decodings** (SC5, SC6) are verified by execution on examples only; CONTRACT O4(e) lists their failure classes, but constructor/precedence proofs and malformed-leaf regressions remain required (X1).
- **Silent list-to-zero** in storage leaves (SC6) and falsy empty lists in account leaves (SC5) look accidental; not reported upstream (P2/§6 discrepancy policy).
- **Duplicate `encode_account`** in `fork_types.py` (G1) must be reconciled with SC1.
- **`StateCollision`** is not yet defined: which pairs (DB entries, inline subterms, canonical encodings of both trie levels) and in which order; its computability and its connection to VCV-io's collision games are open.
- **`storageRoot = emptyTrieRoot ⇒ empty`** needs a collision disjunct; proof strategy follows the trie theorem but is not written.
- **Blockchain-test pre-states** (`EthStateFull`) must satisfy `MathState.WF` (no orphan storage); this is argued from `state_mpt.set_storage`'s assertion (`state_mpt.py:198`) and genesis loading, not checked on the corpus.
