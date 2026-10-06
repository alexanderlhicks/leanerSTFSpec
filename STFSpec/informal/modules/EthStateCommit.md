# `EthStateCommit`: account and storage encodings, the state-root law, code-hash agreement, `Models`

*Status: informal specification, draft. Date: 2026-10-06. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F2, F4, F16, F20 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D5, D9, D16, D20 · questions: B2 (Q30), Q16, Q53, Q55, Q57.*

## 1. Purpose

`EthStateCommit` is the small integration component (ARCHITECTURE §3, v2.1; D20) between state semantics (`EthState`) and the generic trie (`EthCommit`). It owns the account and storage leaf encodings and their (lenient) witness decodings, the state root of a mathematical state `mathStateRoot`, code-hash agreement, and the binary full backend contract `Models ps σ := MathState.WF σ ∧ CodeAuthentic σ ∧ ModelsLookups constsId ps σ ∧ ModelsCode ps ∧ ModelsRoot ps σ`. Here `constsId` names `Id.run (HashConsts.query (m := Id))`, the existing concrete interpretation in SC7/§7.3 (Q57). Both backends prove `Models` against these definitions; neither `EthState` nor `EthCommit` imports the other.

## 2. Requirements

- SC1. **Account leaf encoding** (`merkle_patricia_trie.py:193–210`): `rlp [nonce, balance, storageRoot, codeHash]`, integers as minimal big-endian RLP strings, `storageRoot` and `codeHash` as 32-byte strings. The same function appears in `forks/amsterdam/fork_types.py` (claimed here); the two must be one Lean definition or proved equal.
- SC2. **Storage leaf encoding**: `encode_node(U256)` is `rlp.encode` of the integer (`merkle_patricia_trie.py:268–269`), i.e. the minimal big-endian bytes as an RLP string; value `0` is never stored (the trie default, `state_mpt.py:106`, `witness_state.py:258`).
- SC3. **Secured keys**: account keys are `keccak256(address)`, storage keys `keccak256(slot)` (`Trie(secured=True, …)`, `state_mpt.py:40`, `:106`; `witness_state.py:156`, `:168`, `:191`).
- SC4. **`mathStateRoot σ`** = `mathRoot` of `{keccak256 a ↦ encodeAccount (σ.accounts a) (storageRoot σ a)}` where `storageRoot σ a = mathRoot {keccak256 k ↦ rlp v | σ.storageAt a k = v ≠ 0}`, which is `EMPTY_TRIE_ROOT` for no storage (`state_mpt.py:113–118`; `merkle_patricia_trie.py:429–433`). Storage of absent accounts does not contribute. Every hash here (secure keys, node references, the root) goes through `KeccakQuery` (D5), and the empty constants come from `HashConsts` (`EthBase`); the model definitions are stated at `m := Id` (§5).
- SC5. **Account leaf decoding** (`witness_state.py:103–127`), lenient [executed against pinned `ethereum_rlp`]: the leaf must RLP-decode to a list of exactly 4 items (else malformed); each field that is falsy (the empty string **or the empty list**) takes its default (`0`, `0`, `EMPTY_TRIE_ROOT`, `EMPTY_CODE_HASH`, i.e. the `HashConsts` fields, which the decoder therefore takes as a parameter); otherwise nonce and balance are big-endian with **leading zeros accepted**, nonce unbounded, balance ≥ 2²⁵⁶ fails (`OverflowError`); a non-empty storage root or code hash of length ≠ 32 fails (`ValueError`); a non-empty list in any field fails (`TypeError`). An empty leaf value fails (`rlp.decode(b"")`). All failures are witness failures (O4).
- SC6. **Storage leaf decoding** (`witness_state.py:198–203`): RLP-decode; a string → its big-endian value (leading zeros accepted; > 32 significant bytes fails with `OverflowError`); the empty string → `0`; **a list → `0`** silently. RLP failure → witness failure.
- SC7. **Code-hash agreement**: the empty constants are `HashConsts` fields (`EthBase`; D5), and `EthHash` checks that `HashConsts.query` at `Id` yields `HashConsts.literals`, in particular `emptyCodeHash = keccak256 ByteArray.empty` (`state.py:36`) and `emptyTrieRoot = keccak256 (rlp b"")` (`EthHash` §7); a code DB entry is keyed by the keccak of its bytes (`witness_state.py:45–50`; `state_mpt.py:168–170`); `EthState.setCode` callers pass `keccak256 code` (ARCHITECTURE §5.3). `ModelsCode ps` (for `ps : PreState Id`; B2: `getCode` has no absent case): `ps.getCode consts.emptyCodeHash = .ok ByteArray.empty` (with `consts = Id.run HashConsts.query`) and `ps.getCode h = .ok c → keccak256 c = h`. Missing code is `.error`, which `ModelsCode` leaves unconstrained (a progress question).
- SC8. **`ModelsRoot ps σ`** (for `ps : PreState Id`): for every `d` with `BlockDiff.WF σ d`, `ps.stateRoot d = .ok r → r = Id.run (mathStateRoot (m := Id) constsId (σ.apply d))`. This spells out the existing concrete root interpretation. `code_changes` never affects the root (the MPT commits to code hashes only, `state_mpt.py:87–89`; `state.py:129–135`).
- SC9. **`Models ps σ`** is stated for `ps : PreState Id` (D5, F1); the oracle coupling for a generic `m` is open (D5, `EthSecurity`). It requires `MathState.WF σ` and `CodeAuthentic σ`. For a witness backend with authenticated node/code DBs, coherent HashConsts and the specified Id-run decoder/thunk agreement via the existing error-adapter obligation (WitnessBackend.WF, Q55), it holds **up to a computable collision** (§7): for every structurally WF, code-authentic σ whose `mathStateRoot` is the parent root, `Models ps σ` or a Keccak collision is found among node/key/code preimages, including the witness code DB and σ’s code bytes. Backend **progress** is separate (ARCHITECTURE §5.3) and stated in each backend.
- SC10. The encodings are canonical: `decodeAccountLeaf (encodeAccount a r) = .ok (a, r)` and `decodeStorageLeaf (encodeStorage v) = .ok v` for `v ≠ 0`; lenient decodings of non-canonical leaves are reachable only under a collision (§7.2).

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `merkle_patricia_trie.py::encode_account` | 193 | `encodeAccount` | also `fork_types.py`; supplied by the same Lean definition |
| `forks/amsterdam/fork_types.py::encode_account` | 67 | `encodeAccount` | the fork-local copy; same RLP `(nonce, balance, storage_root, code_hash)` as the shared one (verified by reading both); one Lean definition serves both |
| `forks/amsterdam/witness_state.py::_decode_account_from_leaf` | 103 | `decodeAccountLeaf` | lenient, SC5 |

Also specified here without their own inventory items: the storage-leaf decoding inlined in `WitnessState.get_storage` (`witness_state.py:198–203`, `decodeStorageLeaf`), contextual `Account` encoding in `encode_node` (`merkle_patricia_trie.py:263–265`) and the storage-root callback of `root`/`_prepare_data` (`merkle_patricia_trie.py:410`, `:430–433`). Q53 does not supply a bare Account class instance.

**External semantics.** `ethereum_rlp.rlp` (strict decode; integer encoding of `Uint`/`U256` as minimal big-endian strings); `int.from_bytes(·, "big")` (leading zeros allowed); `ethereum_types` `U256`/`Uint` constructors (`U256` rejects ≥ 2²⁵⁶ with `OverflowError`) and `Bytes32`/`Hash32` constructors (reject wrong lengths with `ValueError`) — all [executed].

### Implemented total storage encoder (SC2, Q53)

`STFSpec/StateCommit/Storage.lean` supplies exactly `encodeStorage`,
`encodeStorage_ne_empty`, `encodeStorage_inj` and `TrieValue U256`. All supporting
codec-domain/composition proofs are private and consume public provider laws.

| Source at the pin | Public declaration/type and status | Domain, success and effects | Ordered failures | Public laws and evidence |
|---|---|---|---|---|
| `src/ethereum/merkle_patricia_trie.py:268–269`; `ethereum_rlp/rlp.py:66–109` (0.1.6); `ethereum_types/numeric.py:477–484` (0.4.1) | `STFSpec.StateCommit.encodeStorage : U256 → ByteArray`; **discharged total composition** | Every U256: `Rlp.encodeBytes v.toBeBytes.toByteArray`; minimal unsigned payload, zero wire `80`, ≤32 payload bytes/≤33 wire bytes; pure, no state/hash effects | None: total on every U256; host resource failures are O12 | `encodeStorage_ne_empty (v : U256) : encodeStorage v ≠ ByteArray.empty`; `encodeStorage_inj (a b : U256) : encodeStorage a = encodeStorage b ↔ a = b`; private Q47 domain proof, public-only symbolic clients and complete-wire guards |
| Q53 adapter of the same source dispatch | `TrieValue U256`; **discharged** | `encode = encodeStorage`, `Valid := True`; ordinary all-value nonempty proof including zero and supplied defaults | No deletion/validity branch in encoding; setter deletion follows supplied-default equality separately | `StorageCallerProofs` consumes every law/instance field and public Trie safety/deletion/NoDefault contracts; `StorageGuards` checks nonzero supplied-default deletion, zero insertion and directly stored defaults |

`StorageGuards.lean` checks complete bytes at 0/1/127/128/255/256,
2^(8k)−1/2^(8k)/2^(8k)+1 for k = 1–31, every bit in 0–255, the maximum,
asymmetric full-width and interior/trailing-zero payloads. Expected payloads use
explicit unsigned radix-256 patterns and independently constructed RLP tags.
`StorageCallerProofs.lean` uses ordinary all-value laws, recovers value equality
from wire equality, and proves the 33-byte bound through public provider sizes.
These committed guards compare complete wires; the symbolic clients consume public
provider laws on every U256. They supply component encoding and typed-trie evidence.
EEST guest and assembled-root coverage and whole-source/host agreement remain open.
The lenient storage decoder and storage SC10 are supplied below; a strict typed
RLP/U256 decoder does not substitute for that witness behavior.

### Implemented contextual account encoder (SC1, Q47, Q53)

`STFSpec/StateCommit/Account.lean` supplies exactly `encodeAccount`,
`encodeAccount_ne_empty` and `encodeAccount_inj`; all proof support is private.
One definition implements both shared and Amsterdam source functions.

| Source at the pin | Public declaration/type and status | Domain, success and effects | Ordered failures | Public laws and evidence |
|---|---|---|---|---|
| `src/ethereum/merkle_patricia_trie.py:193–210`; `src/ethereum/forks/amsterdam/fork_types.py:67–81`; `ethereum_rlp/rlp.py:66–135` (0.1.6); `ethereum_types/numeric.py:477–484` (0.4.1) | `STFSpec.StateCommit.encodeAccount : Account → Hash32 → ByteArray`; **discharged total composition** | Every account and supplied complete 32-byte root: RLP list of minimal unbounded nonce, minimal balance, complete root and complete code hash, in that order. Pure; no hashing, callback, traversal or state effects. Existing Q47 completion applies outside Encodable | No typed error or nonce rejection. Python correspondence covers supplied 32-byte roots, supported Uint/U256 dispatch and bounded host execution; source itself accepts a broader Bytes root parameter | `encodeAccount_ne_empty (a : Account) (r : Hash32) : encodeAccount a r ≠ ByteArray.empty`, unconditional; `encodeAccount_inj` below, with both exact assembled domain premises. Private public-law clients and complete-wire guards |

The exact binding law is:

```lean
theorem encodeAccount_inj (acc₁ acc₂ : Account) (root₁ root₂ : Hash32)
    (h₁ : Rlp.Encodable (.list [Rlp.ofNat acc₁.nonce, Rlp.ofNat acc₁.balance.toNat,
      .bytes root₁.toBytes.toByteArray, .bytes acc₁.codeHash.toBytes.toByteArray]))
    (h₂ : Rlp.Encodable (.list [Rlp.ofNat acc₂.nonce, Rlp.ofNat acc₂.balance.toNat,
      .bytes root₂.toBytes.toByteArray, .bytes acc₂.codeHash.toBytes.toByteArray])) :
    encodeAccount acc₁ root₁ = encodeAccount acc₂ root₂ ↔ acc₁ = acc₂ ∧ root₁ = root₂
```

Each premise includes every child and the total **encoded** child-payload length
<2^64 (`Rlp.encodable_list_iff`), not just child widths. There is no nonce cap
or public account-domain helper. Nonempty uses the public list-size equation;
binding uses public RLP injectivity, integer round trips, byte-export injectivity
and Account extensionality. Neither law unfolds foreign provider internals.

`AccountCallerProofs.lean` consumes both laws on arbitrary accounts/roots and
independently varies nonce, balance, root and code hash under the explicit domains.
A private client also discharges the complete domain for every supplied emptyAccount
and Hash32 root, then consumes the binding law without a domain hypothesis.
`AccountGuards.lean` compares complete bytes to an independent unsigned division
and RLP-prefix model, plus literal exact expansions: supplied/literal emptyAccount,
zero/max balance, separate 127/128 fields, nonce 2^256 and 2^1024+17, nonce payload
55/56, reachable outer payload 255/256, byte boundaries through nonce width 188,
balance widths 1–32, every fixed-byte position with 00/01/7f/80/ff markers, swapped
roots/hashes and asymmetric/interior/leading/trailing zeros. Both hash items
contribute 66 bytes, so account payload ≥68; outer 55/56 is impossible here.
These committed guards compare complete wires; the private symbolic clients compose
the public laws with their exact assembled premises. Whole-source/host agreement,
SC5/account SC10 and contextual callback/root integration remain open.

### Implemented lenient storage decoder (SC6, storage SC10)

`STFSpec/StateCommit/StorageDecode.lean` supplies exactly `decodeStorageLeaf`
and four public laws below (five declarations); all numeric/reference/domain support
is private. The nominal `State.WitnessError` carrier is owned by
[EthState §3/§5](EthState.md#3-eels-source-map).

| Source at the pin | Public declaration/type and status | Domain, success and effects | Ordered failures | Laws and tests |
|---|---|---|---|---|
| `src/ethereum/forks/amsterdam/witness_state.py:198–203`; `ethereum_rlp/rlp.py:143–156,387–543` (0.1.6); `ethereum_types/numeric.py:44–48,690–712` (0.4.1) | `decodeStorageLeaf : ByteArray → Except State.WitnessError U256`; **discharged local composition** | Every finite raw leaf; complete strict RLP first, then every list → zero or complete unsigned byte payload checked against 2^256; empty payload → zero; unrestricted leading zeros. Pure, no state/hash/cache effects | RLP error first → `.malformed .leaf`; only successfully parsed bytes can then overflow → `.malformed .leaf`. These enumerate two local O4(e) classes, not a global adapter or diagnostic freeze | `decodeStorageLeaf_of_rlp_error`, `_of_rlp_list`, `_of_rlp_bytes`; private ordinary all-Bytes packed/reference equality, prefix invariant, absorbing overflow and candidate <2^264; complete parser/local-result guards and public-law clients |
| SC10 of the same operation | `decodeStorageLeaf_encodeStorage (v : U256) (h : v ≠ U256.zero) : decodeStorageLeaf (encodeStorage v) = .ok v`; **discharged** | Exactly nonzero words; local Q47 byte domain proved from public 32-byte width bound | None on this domain | Public-contract symbolic client and full values at 1/127/128/255/256, every bit, maximum; no new stored-zero policy or instance |

The three behavior statement types are:

```lean
theorem decodeStorageLeaf_of_rlp_error (leaf : ByteArray) (e : RlpError)
    (h : Rlp.decode leaf = .error e) :
    decodeStorageLeaf leaf = .error (.malformed .leaf)
theorem decodeStorageLeaf_of_rlp_list (leaf : ByteArray) (items : List RlpItem)
    (h : Rlp.decode leaf = .ok (.list items)) :
    decodeStorageLeaf leaf = .ok U256.zero
theorem decodeStorageLeaf_of_rlp_bytes (leaf payload : ByteArray)
    (h : Rlp.decode leaf = .ok (.bytes payload)) :
    decodeStorageLeaf leaf =
      match U256.ofNat? (Uint.ofBeBytes (Bytes.ofByteArray payload)) with
      | some v => .ok v
      | none => .error (.malformed .leaf)
```

The executable numeric path is `Bytes.foldl` over `Option U256`, initialized
at `some zero`: success checks `256 * acc.toNat + byte.toNat`, overflow retains
`none` over every suffix. Each candidate is <2^264; retained values are <2^256.
The legible reference `U256.ofNat? (Uint.ofBeBytes payload)` is proof-facing;
ordinary public-model fold commutation proves equality on every finite Bytes.
No numeric-path list conversion, growing overflowing Nat, byte-count/minimality
cap, wrapping, clipping or child numeric traversal occurs. Full parser allocations
and traversal remain upstream; fixed numeric bounds establish no measured
allocation/throughput, host/resource or composed C1–C4 result.

`StorageDecodeCallerProofs.lean` derives arbitrary-input success iff the complete
integer fits, exact full success values, overflow iff ≥2^256, list/error equations
and nonzero SC10 solely through public contracts. `StorageDecodeGuards.lean`
retains exact parser errors and complete local results, including raw empty versus
empty payload, canonical framing, malformed nested children, trailing wire bytes,
33-significant-byte list children, 55/56/57 and 255/256/257 length thresholds,
long leading zeros/late digits, every significant position, maximum, overflow and
absorbing arbitrary suffix patterns. The nonzero fitting-byte and empty-list
trailing cases check exact parser errors before otherwise successful value branches.
These committed component cases preserve parser/local-result failure order. The
ordinary all-Bytes packed/reference proof is separate from finite guard coverage.
SC5/account SC10, secure roots/callbacks, authentication, backend progress, generic
coupling and global errors/resources remain open.

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
def encodeStorage (v : U256) : ByteArray                      -- total; storage maps omit zero
def decodeAccountLeaf (consts : HashConsts) (leaf : ByteArray) : Except WitnessError (Account × Hash32)  -- SC5 defaults from consts
def decodeStorageLeaf (leaf : ByteArray) : Except WitnessError U256                 -- SC6
def storageTrieMap (σ : MathState) (a : Address) : m (Std.ExtTreeMap Nibbles ByteArray)   -- secure keys
def storageRoot (consts : HashConsts) (σ : MathState) (a : Address) : m Hash32
def accountTrieMap (consts : HashConsts) (σ : MathState) : m (Std.ExtTreeMap Nibbles ByteArray)
def mathStateRoot (consts : HashConsts) (σ : MathState) : m Hash32
def CodeAuthentic (σ : MathState) : Prop -- every stored (h,c) has keccak256 c = h; no availability claim
def CodeChangesAuthentic (d : BlockDiff) : Prop -- same property for codeChanges
-- constsId names Id.run (HashConsts.query (m := Id)); a proof interpretation,
-- not State execution-time acquisition or a new public constants definition (Q57).
def ModelsCode (ps : PreState Id) : Prop :=                    -- SC7
  ps.getCode constsId.emptyCodeHash = .ok ByteArray.empty ∧
  (∀ h code, ps.getCode h = .ok code → keccak256 code = h)
def ModelsRoot (ps : PreState Id) (σ : MathState) : Prop :=     -- SC8
  ∀ d r, BlockDiff.WF σ d → ps.stateRoot d = .ok r →
    r = Id.run (mathStateRoot (m := Id) constsId (σ.apply d))
def Models (ps : PreState Id) (σ : MathState) : Prop :=
  MathState.WF σ ∧ CodeAuthentic σ ∧
  ModelsLookups constsId ps σ ∧ ModelsCode ps ∧ ModelsRoot ps σ
-- The Id check HashConsts.query (m := Id) = HashConsts.literals is EthHash's (EthHash §7).
-- for the witness backend and EthSecurity
def StateCollision (db : NodeDB) (codes : List (Hash32 × ByteArray)) (σ : MathState)
    : Option (ByteArray × ByteArray) -- include node, secure-key AND code preimages
instance : TrieValue U256   -- discharged Q53: encodeStorage; Valid v := True
                           -- ordinary encode_ne_empty for every v, including RLP zero
```

These decoding and model-root helpers receive the caller's record (F20), using `variable (consts : HashConsts)` and local EELS notation for defaults. Backend callers with an existing constants field project that field; the helpers never acquire constants or substitute `HashConsts.literals` in generic execution. The Id laws here keep their concrete interpretation premise; F20 does not discharge generic oracle coupling.

Q57 leaves full `Models` and `ModelsRoot` binary and `ModelsCode` unary at this
concrete Id interpretation. When the execution record equals `constsId`, rewriting its lookup
conjunct supplies `ModelsLookups` at that record. Only `emptyCodeHash` affects the
local lookup predicate; equality of that field alone cannot establish the full
record/root/decoder coherence premises. Arbitrary-record lookup agreement gives
no concrete root/hash agreement for a noncoherent record.

Q53's supplied U256 instance proves `encodeStorage v ≠ empty` for every value: zero
encodes as `80`, independently of supplied-default deletion. Actual storage maps omit
zero by their caller semantics (SC2); that is a `NoDefault` obligation, distinct from
stored-value `PrepareSafe`. The U256 instance and its all-value encoding laws, plus
the contextual Account encoder and its complete-domain binding law, are discharged;
callback/traversal and complete
root/source bridges remain unimplemented.
Bare `Account` requires the per-address storage root/callback (`merkle_patricia_trie.py:429–433`);
EthStateCommit owns that contextual integration, its exact encoding, address/callback
ordering and source correspondence. `TrieValue.encode : Account → ByteArray` alone
cannot supply the missing context. This clarification invents no Account instance,
root API or secured traversal/collision policy. Concrete source agreement retains
supported non-`None` interpretation, exact equality/dispatch, complete source-schema
and assembled-node `Encodable` (Q47), coherent F20 constants and host premises.

Q55's unimplemented complete decoder is a generic `KeccakQuery` action, with
its cache/acquisition contract owned by EthCommit C13–C14/§7.6. Concrete witness
agreement uses `Id.run (decodeRoot consts.emptyTrieRoot db r) = .ok t` and the
actual Id interpretation with coherent caller-supplied F20 constants. A decoded
cache equals a referenced DB key only under authenticity and raw length ≥32;
arbitrary alias-keyed DB admission still retains the actual raw-preimage digest.
The Id witness thunk is not a generic result-cache representation. Generic
`PreState m` agreement needs a real query interpretation/action-lifetime bridge;
Q55 chooses none and adds no local constants acquisition.

## 6. Data structures

The storage decoder uses a private packed `Option U256` fold; its reference is
proof-facing and its fixed numeric bound is specified in §3. No new containers. `accountTrieMap`/`storageTrieMap` are `ExtTreeMap Nibbles ByteArray` views computed on demand (model definitions, O(n log n) to build; used by `EthStateFull` and in proofs, never on the witness path). Persistence: values only.

## 7. Contract and laws

### 7.1 Encoding laws [C], feeds [S]

- Storage-wire nonempty and injectivity laws are discharged in §3 on every U256, with the Q47 domain proved from the public 32-byte payload bound. Account-wire nonempty is unconditional; injectivity in `(acc, root)` is discharged under both exact assembled Q47 premises in §3. Storage SC10 is discharged above on nonzero words; account SC10 remains open.
- `storageRoot σ a = emptyTrieRoot ↔ σ.storage a` is empty (given `WF`; ⇐ by definition, ⇒ needs collision freedom and is stated as "or collision").
- `mathStateRoot` depends only on `σ.accounts` and the storage of existing accounts; it ignores `σ.code`.

### 7.2 Root and apply [C], [R]

- `mathStateRoot (σ.apply d)` is the root after `apply_changes_to_state` (`state_mpt.py:133–161`) and after `State.compute_state_root` (`state_mpt.py:82–120`) — the full backend's commuting equation.
- **Lenient decodings are collision-guarded:** if a leaf decoded by `decodeAccountLeaf` is not the canonical encoding of the result, then no WF σ with the same root has it without a collision, since the leaf bytes are part of an authenticated node.
- **Witness agreement (lifting `EthCommit.decode_agreement`):** for the witness backend `ps` built from authenticated `db` and `codes`, coherent HashConsts, explicit `Id.run (decodeRoot consts.emptyTrieRoot db r) = .ok t` premises at the triggered roots, and parent root `r`, and every structurally WF, code-authentic σ with `mathStateRoot σ = r`: `Models ps σ ∨ (StateCollision db codes σ).isSome`. The storage-trie part applies `decode_agreement` per account, with the storage root taken from the authenticated account leaf. Code-store authenticity is an additional premise because the state root does not commit to the code store's values.

### 7.3 Code [C]

- **Empty constants.** Under D5 the constants are `HashConsts` fields queried through the oracle; the literals (`HashConsts.literals`, `EthBase`) are only their values at `Id`. This module's laws use `consts = Id.run HashConsts.query`. `EthHash` owns the check `HashConsts.query (m := Id) = HashConsts.literals` (`EthHash` §7), so this module states no separate literal-equality theorem.
- `setCode` agreement: if every `EthState.setCode` call passes `keccak256 code`, every `BlockDiff.codeChanges` entry `(h, c)` has `keccak256 c = h` and `h ≠ consts.emptyCodeHash`.

### Informal correctness argument

**Claim.** The account/storage adapters connect successful provider answers and roots to MathState, with code authenticity and collisions treated explicitly rather than inferred from structural state well-formedness.

**Premises.** EthState structural laws, EthCommit canonical root laws, exact account RLP field order, CodeAuthentic σ, and CodeChangesAuthentic for updates that introduce code.

**Argument.** Canonical account encoding is injective under both complete assembled Q47 domains by the four field codecs; storage maps omit zero values, while the total storage encoder preserves the canonical integer encoding even at zero. Apply the trie equation first to each storage map, then to the account map whose leaves include those storage roots. This yields mathStateRoot and the root clause of Models. Code storage is a separate map: state roots bind account code hashes, but do not authenticate the bytes stored under them. CodeAuthentic supplies that missing equation. Compare successful witness paths with the mathematical paths: equal encoded preimages permit descent; differing preimages with equal hashes yield a collision. The extractor must include trie nodes, secure-key preimages and code preimages from both the witness and σ, not only node DB entries.

**Open obligations.** Complete the collision extractor and its finite query set, lenient leaf-decoding refinement and the hash-relative code-authenticity model. Backend progress is additional to Models: a backend that always errors would otherwise satisfy successful-answer implications vacuously.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthState`, `EthCommit`
- **Used by:** `EthStateFull`, `EthStateWitness`, `EthSecurity` (proofs).
- **Seams:** the `Models` predicate is the contract every backend proves and every refinement theorem over `executeBlock` assumes; `mathStateRoot` is what `EthBlock`'s state-root check means semantically.
- **Relies on:** `EthCommit`'s `mathRoot`, `represents` and `decode_agreement`; `EthState`'s `apply`, full `BlockDiff.WF` and `ModelsLookups constsId ps σ`; RLP injectivity from `EthCodec`. Q58's structural-only premise does not replace full WF in the root law.
- **Typed encoding seam (Q53):** U256 `Valid`/nonempty laws and storage-wire injectivity are supplied in §3 independently of zero deletion. Contextual Account/storage-root encoding and binding under both complete Q47 domains are supplied in §3; callback/root/source composition remains open. The initial unsecured typed root domain supplies no secured state/storage root implementation; secure traversal, collisions, source history and generic coupling retain their existing obligations.

## 9. Open decisions

- D5 (broad scope, monad-parametric): the model roots hash through `KeccakQuery` and take `HashConsts`; `Models`, `ModelsCode` and `ModelsRoot` are stated at `PreState Id`. Open: the coupling at generic `m`, and phrasing `StateCollision` over the same oracle as the trie.
- D9, D20 (accepted): `Models` is split exactly as here.
- D16 (accepted): this is the only place encodings meet semantics.
- NEW-STATE-2 (from `EthState`): resolved: DECISIONS B2 (Q30); SC7 has no `.ok none` case.
- Q53: U256 preparation validity and contextual Account integration follow §5/§8, with no bare Account instance or secured policy supplied.
- Q57: the explicit lookup record follows §5; full model/code/root contracts retain the existing concrete Id interpretation and all authentication/collision/progress premises.

## 10. Gaps

- **Decoder consumer bridge (Q55):** implement the explicit concrete Id-run agreement premises and existing error adaptation; prove cache provenance under authenticity/eligible length. Generic action ownership/lifetime, oracle interpretation/coupling and whole state agreement remain open.

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Typed encoding integration (Q53):** the all-value U256 encoder/instance and wire injectivity, plus contextual Account encoding, unconditional nonempty and binding under both complete Q47 domains, are discharged in §3; implement/prove callback/root integration without assuming a bare Account instance. Whole source equality/schema/dispatch, assembled-node `Encodable`, F20 and host premises, and secured traversal/collision/source-history/generic-coupling obligations remain open.

- **Lenient account decoding** (SC5/account SC10) remains open, including constructor/precedence proofs and malformed-leaf regressions (X1). SC6 and nonzero storage SC10 are discharged locally in §3; backend/authentication/progress, collision-guarded agreement and the shared error-adapter/granularity obligations remain open.
- **Silent list-to-zero** in storage leaves (SC6) and falsy empty lists in account leaves (SC5) look accidental; not reported upstream (P2/§6 discrepancy policy).
- **`StateCollision`** is not yet defined: which pairs (DB entries, inline subterms, canonical encodings of both trie levels) and in which order; its computability and its connection to VCV-io's collision games are open.
- **`storageRoot = emptyTrieRoot ⇒ empty`** needs a collision disjunct; proof strategy follows the trie theorem but is not written.
- **Blockchain-test pre-states** (`EthStateFull`) must satisfy `MathState.WF` (no orphan storage); this is argued from `state_mpt.set_storage`'s assertion (`state_mpt.py:198`) and genesis loading, not checked on the corpus.
