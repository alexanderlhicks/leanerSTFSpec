# `EthCodec`: RLP, SSZ, `hash_tree_root` and derived addresses

*Status: informal specification, draft. Date: 2026-09-29. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F1, F13, F17, F18 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D5, D14, D18, D21 · questions: B5/Q21/Q22, B10/Q12, Q20, F13, F17, O2.*

Unprefixed paths are relative to `src/ethereum/` at the pin. Two external libraries are part of the semantics:
- **`ethereum_rlp`**: `rlp.py` from `ethereum-rlp` 0.1.6, as locked in `uv.lock`. The scratch venv has 0.1.7; I diffed the two wheels, and `rlp.py` and `exceptions.py` are byte-identical (only `__version__` differs). The D1r mutation fuzzing ran under 0.1.7; the D2r nesting probes ran under the locked 0.1.6.
- **`remerkleable`**: `eth-remerkleable` 0.1.31.

## 1. Purpose

`EthCodec` (layer L0) owns the two wire formats:
- **RLP**: headers, transactions, receipts, trie nodes, account leaves, CREATE preimages and the BAL encoding.
- **SSZ**: the guest's input and output (`StatelessInput`, `StatelessValidationResult`), `NewPayloadRequest` and its `hash_tree_root` (the guest's committed output), and withdrawals and requests.

It also owns **contract-address derivation** (CREATE/CREATE2). That derivation needs RLP and Keccak, and it must be visible to both `EthVmInstructions` and `EthBlock` (`fork.py:638`). `EthCodec` is the lowest library both may import. Concrete schemas (which fields, which limits) belong to their owners (`EthBlock`, `EthStateless`). `EthCodec` supplies the generic machinery and its laws.

## 2. Requirements

### RLP encoding (`ethereum_rlp/rlp.py:66–135`)

- **E1. Byte strings.**
  - A single byte `< 0x80` encodes as itself.
  - A string of length `< 56` encodes as `0x80+len ‖ data`.
  - A longer string encodes as `0xB7+|L| ‖ L ‖ data`, where `L` is the minimal big-endian length.
- **E2. Lists.** The payload is the concatenation of item encodings. A payload of length `< 56` gets the header `0xC0+len`; a longer one gets `0xF7+|L| ‖ L`.
- **E3. Typed values.**
  - `Uint`/`FixedUnsigned` encode as the byte string `to_be_bytes()`, which is minimal. **Zero is the empty string (`0x80`), never `0x00`** (`:77–78`; `ethereum_types/numeric.py:477`).
  - `bool` encodes as `0x01` or the empty string (`:79–83`).
  - `str` encodes as its UTF-8 bytes.
  - Dataclasses encode as the list of their fields (`:84–85`).
  - A plain Python `int` raises `EncodingError`; this is unreachable in well-typed EELS.

### RLP decoding (`rlp.py:143–543`)

- **D1r. Untyped decode.** `decode(b)` succeeds **iff `b` is exactly the encoding of some item**. It rejects, all with `DecodingError`:
  - empty input (`:148`);
  - trailing bytes after any item (`:400,422,436,455`), including after a single byte `< 0x80`, which is reported as "negative length" (`:394–397`);
  - declared lengths exceeding the input (`:398,410,419,434,441,453,476,519,535`);
  - a one-byte string `< 0x80` in prefixed form (`:403–404`);
  - a long-form length with a leading zero byte (`:412,443,521,537`);
  - a long form used for a length `< 56` (`:417,448`).

  Items inside a list are decoded recursively from their exact extent (`:464–484`). *Verified empirically on ethereum-rlp 0.1.7 (`rlp.py` byte-identical to the locked 0.1.6):* 200k structured mutations of random encodings plus 300k random ≤5-byte strings produced no accepted non-canonical input, and no exception other than `DecodingError`. This is evidence, not a proof; the proof is the [C] canonicality obligation in §7.
- **D2r. Deep nesting is a host-limit case (O12).** Decoding recurses about 3 Python frames per nesting level. `ethereum/__init__.py:30` sets the recursion limit to `max(12288, current)`, but the guest also imports py_ecc, which raises it, so the **guest-process limit is 100,000**. Deterministic probe inputs (payload transactions with deep RLP nesting) showed that 20,000 nested lists in a payload transaction decode, while 40,000 and 120,000 raise **`RecursionError`**, not `DecodingError`. (With only `import ethereum`, the threshold is between 4,000 and 5,000 levels.)
  - Witness nodes and headers are at most 2^10 bytes (`stateless.py:35–36`), so they cannot reach this.
  - Transactions are `progressive_byte_list` with no size limit (`execution_engine/types.py:64–67`), so a deep-nesting transaction reaches it inside `decode_transaction` (`transactions.py:573–585`). **On the complete guest path** the first decode is in `is_valid_versioned_hashes` (`execution_engine/new_payload.py:60–68`), whose local catch-all consumes the `RecursionError`, so the output is O6 `(root, false, …)` (DISC-006). A standalone `execute_block` call would raise it from its own decode.

  The spec's total decoder returns a nested `RlpItem` there, and the **typed** decode then fails, because no transaction schema nests more than about 4 levels. On the guest path both sides then give O6, so the output agrees. The reference side is witnessed by probe `tx-deep-rlp-40000`, the DISC-001 reproducer; the typed-depth bound on the spec side is argued, not proved (§10). The case stays under CONTRACT O12 / DISC-001 (DECISIONS Q20), which is unresolved by design.
- **D3r. Typed decode (`decode_to` / `deserialize_to`, `:162–384`).**
  - Integers must be byte strings with **no leading zero** (`:270–271`), and for fixed widths **at most `width` bytes** (`FixedUnsigned.from_be_bytes` length check, `numeric.py:573`).
  - Fixed bytes require the exact length (`bytes.py:34`). `Bytes` requires a string, not a list.
  - `bool` accepts only the empty string or `0x01` (`:245–251`).
  - A dataclass requires a list with exactly as many items as it has fields (`:222–228`).
  - `Tuple[T, ...]` and `List[T]` accept any length.
  - A `Union` requires **exactly one** alternative to succeed (`:325–343`; used for `to: Bytes0 | Address`).
  - `decode_to` **wraps every exception raised during typed deserialization into `DecodingError`** (`:167–171`). The header fallback in `stateless.py:234–237` (Amsterdam `Header`, then `PreviousForkHeader`) depends on this. The raw `decode` step is *outside* that wrapper, so a `RecursionError` there is not converted (D2r).
- **D4r. Naive-reading trap.** A fixed-arity `Tuple[A, B]` target is decoded with `zip` (`:346–367`), which has **no length check**: extra items are dropped, and missing items give a shorter tuple. I found no fixed-arity RLP tuple target in the Amsterdam decode sites (`transactions.py:573–585`, `blocks.py:434`, `stateless.py:235–237`); all use dataclasses. The spec therefore does not model this laxity. Any future use must be flagged.

### Contract addresses (`forks/amsterdam/utils/address.py`)

- **A1.** `compute_contract_address(a, n) = keccak256(rlp([a, n]))[12:32]`, with `n : Uint` minimally encoded (`:42–63`). The final `left_pad_zero_bytes(…, 20)` is a no-op.
- **A2.** `compute_create2_contract_address(a, s, c) = keccak256(0xff ‖ a ‖ s ‖ keccak256(c))[12:32]` (`:66–93`).
- **A3.** Both keccaks of A1 and A2 go through `KeccakQuery` (D5): the derivations are generic in `{m} [Monad m] [KeccakQuery m]` (CREATE2 makes two queries), and the pure forms are their `Id` specialisations.

### SSZ (`utils/ssz.py` over `remerkleable`)

- **S1. Schema language.** EELS dataclasses map to SSZ types by `_infer` (`ssz.py:179–205`):
  - `FixedBytes` subclasses become `ByteVector[LENGTH]`;
  - `FixedUnsigned` subclasses become `uint(bitlen(MAX))`;
  - `bool` becomes `boolean`;
  - `SszContainer` subclasses become containers, and `ProgressiveSszContainer` subclasses become progressive containers with **all active fields = 1** (`:250–251`);
  - `Annotated` markers select `uint(bits)` for `bits ∈ {8,16,32,64,128,256}` (`:91–95`), `byte_vector(n)`, `byte_list(N)`, `ssz_list(N)`, `progressive_list()` or `progressive_byte_list()`.

  An unannotated `Uint` is a schema `TypeError`, not a runtime case. Annotated fields may be *wider* in Python than on the wire, e.g. `timestamp: Annotated[U256, uint(64)]` and `block_number: Annotated[Uint, uint(64)]` (`execution_engine/types.py:57–62`). Decoding converts with `base(int(v))` (`ssz.py:309–310`), which cannot fail for decoded values.
- **S2. Serialization** is standard SSZ:
  - fixed-size fields are written inline, and each variable-size field is a 4-byte little-endian offset followed later by its payload;
  - lists of fixed-size elements are concatenated, and lists of variable-size elements get an offset table;
  - `uintN` is little-endian and `boolean` is `0x00`/`0x01`.

  **Progressive lists serialize exactly like lists, and progressive containers exactly like containers.** `active_fields` is not serialized; I checked this on remerkleable.
- **S3. Decoding.** It must accept **exactly the canonical encodings.** EELS gets this by decoding with remerkleable and then requiring `view.encode_bytes() == data` (`ssz.py:137–146`). This matters because remerkleable alone is permissive:
  - `Container.deserialize` checks only `first_offset ≥ fixed_size` (`remerkleable/complex.py:948–950`), not equality;
  - it then reads variable fields *sequentially from the stream position*, not from their offsets.

  So an offset gap silently misaligns the fields. I checked this: `C{a: uint16, b: ByteList[10], c: ByteList[10]}` with a 1-byte gap decodes to `b = 0x0061, c = 0x6263`. The re-encode check then rejects it. The spec's decoder must be a **strict canonical decoder** whose accept set is proved equal to the image of `encode` (§7).

  The consequences cover all O1 SSZ cases (CONTRACT §4). A decoder must reject all of the following:
  - wrong total length for fixed-size types;
  - a first offset other than the fixed-part size;
  - decreasing offsets, or offsets beyond the scope;
  - a variable-element list whose first offset is not `4·count`, including a non-empty scope with first offset 0 (`tests/json_loader/test_ssz.py:126`);
  - an element or field size outside `[min, max]` (`complex.py:186–220`);
  - `ByteList`/`List` over its limit (`byte_arrays.py:173–178`; `complex.py` `is_valid_count`);
  - a `boolean` byte other than `0x00`/`0x01` (`basic.py:56–61`);
  - trailing bytes.
- **S4. `hash_tree_root`**, with `H(a, b) = sha256(a ‖ b)` (`remerkleable/settings.py:16–17`), `pack` = right-zero-padded 32-byte chunks, and `mix(r, n) = H(r, n as uint256 LE)`:
  - `uintN`/`boolean`: the value as little-endian bytes, padded to 32. Lists of basic values are packed.
  - `ByteVector[n]`: `merkleize(pack(b), ⌈n/32⌉)`.
  - `ByteList[N]`: `mix(merkleize(pack(b), ⌈N/32⌉), |b|)`.
  - `List[T, N]`: `mix(merkleize(roots or packed chunks, limit), count)`.
  - `Container`: `merkleize(field roots, #fields)`.
  - **Progressive list / byte list** (EIP-7916): `mix(prog(chunks), count)`. Here `prog([]) = 0^32` and `prog(c, k) = H(merkleize(c[:k], k), prog(c[k:], 4k))`, starting from `k = 1` (`remerkleable/progressive.py:25–32,118`).
  - **Progressive container** (EIP-7495): `H(prog(field roots, with 0^32 at inactive positions), active_fields as a 256-bit little-endian bitvector chunk)` (`progressive.py:500–530`).
  - `merkleize(c, L)` pads to the next power of two ≥ `L` using precomputed zero hashes.

  *Verified empirically*: I checked every formula above against remerkleable 0.1.31 on 200 random instances each of `ProgressiveByteList`, `ProgressiveList[ByteList[1024]]`, `List[ByteList[1024], 256]` and `ProgressiveList[uint64]`, plus a 3-field progressive container. The spec follows remerkleable, the pinned dependency. Agreement with the EIP texts was **not** checked (§10).
- **S5. Totality of the committed root.** `compute_new_payload_request_root` (`stateless.py:226`) is outside the inner handler, so a failure there would give the zero sentinel (O2). The spec must prove that `hashTreeRoot` is total on every decoded value, which would make O2 unreachable; a constructor is added only if that proof fails (CONTRACT O2; DECISIONS §3, O2, open). The `_to_view` conversion observation is evidence only: prove the actual decoded domain is Rootable, including progressive counts/mix-ins and schema adapters; resolve host-resource differences separately. No unrestricted O2-freedom theorem is established.
- **S6. Output encoding.** The only SSZ value the guest *encodes* is the fixed-size 43-byte `StatelessValidationResult` (CONTRACT §3). Encoding arbitrary values can fail in remerkleable when an offset reaches 2^32 (`encode_offset` via `uint32`, `complex.py:23–24`). The spec's `encode` is total over well-typed values whose encoding has offsets `< 2^32`, and is stated with that hypothesis.

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `utils/ssz.py::_SszType` | 32 | `SszType` (inductive) | marker base class |
| `utils/ssz.py::_Uint` | 38 | `SszType.uint` | widths 1..32 bytes |
| `utils/ssz.py::_ByteVector` | 44 | `SszType.byteVector` | |
| `utils/ssz.py::_ByteList` | 50 | `SszType.byteList` | |
| `utils/ssz.py::_List` | 56 | `SszType.list` | |
| `utils/ssz.py::_ProgressiveList` | 63 | `SszType.progressiveList` | |
| `utils/ssz.py::_Container` | 69 | `SszType.container` | |
| `utils/ssz.py::_Bool` | 73 | `SszType.bool` | |
| `utils/ssz.py::_ProgressiveByteList` | 77 | `SszType.progressiveByteList` | |
| `utils/ssz.py::_ListLimit` | 83 | `SszType.list` (limit argument) | annotation marker only |
| `utils/ssz.py::_ProgressiveListMarker` | 87 | `SszType.progressiveList` | annotation marker only |
| `utils/ssz.py::uint` | 91 | `SszType.uint` + width check | rejects unsupported widths at schema time |
| `utils/ssz.py::byte_vector` | 98 | `SszType.byteVector` | |
| `utils/ssz.py::byte_list` | 103 | `SszType.byteList` | |
| `utils/ssz.py::ssz_list` | 108 | `SszType.list` | |
| `utils/ssz.py::progressive_list` | 113 | `SszType.progressiveList` | |
| `utils/ssz.py::progressive_byte_list` | 118 | `SszType.progressiveByteList` | |
| `utils/ssz.py::_C` | 123 | none (type variable) | |
| `utils/ssz.py::SszContainer` | 126 | `class SszSchema` | |
| `utils/ssz.py::SszContainer.encode_bytes` | 129 | `SszSchema.encodeBytes` | |
| `utils/ssz.py::SszContainer.hash_tree_root` | 133 | `SszSchema.hashTreeRoot` | |
| `utils/ssz.py::SszContainer.decode_bytes` | 138 | `SszSchema.decodeBytes` (strict) | re-encode check becomes a theorem (S3) |
| `utils/ssz.py::ProgressiveSszContainer` | 149 | `SszType.progressiveContainer` (all fields active) | |
| `utils/ssz.py::_annotated` | 153 | none (schema construction) | Python reflection; schemas are written explicitly in Lean |
| `utils/ssz.py::_collection_element` | 169 | none (schema construction) | as above |
| `utils/ssz.py::_infer` | 179 | schema-authoring rule (S1) | followed by hand in each `SszSchema` instance; checked by `#guard` against EELS type roots |
| `utils/ssz.py::_rmk_type` | 208 | `SszType` semantics | |
| `utils/ssz.py::_FIELD_TYPES` | 228 | none (Python cache) | |
| `utils/ssz.py::_field_types` | 231 | none (reflection) | |
| `utils/ssz.py::_CONTAINER_TYPES` | 240 | none (Python cache) | |
| `utils/ssz.py::_container_type` | 243 | `SszSchema.type` | active fields `[1]*n` |
| `utils/ssz.py::_to_ssz_value` | 263 | `SszSchema.toValue` | byte-vector length check becomes a type invariant |
| `utils/ssz.py::_to_view` | 288 | `SszSchema.toValue` | |
| `utils/ssz.py::_from_ssz_value` | 299 | `SszSchema.ofValue?` | `base(int(v))` widening (S1) |
| `utils/ssz.py::_from_view` | 318 | `SszSchema.ofValue?` | |
| `forks/amsterdam/utils/address.py::compute_contract_address` | 42 | `computeContractAddress` | A1 |
| `forks/amsterdam/utils/address.py::compute_create2_contract_address` | 66 | `computeCreate2ContractAddress` | A2 |

`to_address_masked` from the same file is claimed by `EthBase` (a pure conversion). `encode_account` (in `fork_types.py`) is claimed by `EthStateCommit`; its state-dependent encoding remains outside EthCodec.

**External semantics.** This module must specify these libraries completely:
- `ethereum_rlp.rlp` (`encode`, `decode`, `decode_to`, `With`) and `ethereum_rlp.Extended`, as E1–E3 and D1r–D4r. `With` custom decoders are not used in Amsterdam decode sites; I checked with a grep.
- `remerkleable.basic`, `.byte_arrays.{ByteList, ByteVector}`, `.complex.{Container, List}`, `.progressive.{ProgressiveList, ProgressiveByteList, ProgressiveContainer}`, as S2–S6.
- `hashlib.sha256` via `EthHash`.

## 4. Tests

- **EEST fixture areas.**
  - All 29030 guest records decode SSZ and compute the output root.
  - **O1 SSZ/schema rejection:** `amsterdam/eip8025_optional_proofs/stateless_input_bytes`. I checked all 9 records in the `blockchain_tests` copy, and each expects the zero sentinel: empty input, incomplete schema id, invalid first SSZ offset, missing SSZ body, shifted SSZ offsets, trailing garbage, truncated SSZ body, unsupported schema fork, unsupported schema revision. These are the only 9 zero-sentinel outputs in the corpus (a streamed count found 9 zero, 1199 false and 27822 true).
  - RLP headers: `eip8025_optional_proofs/witness_validation_headers` (malformed RLP header, non-contiguous chain, missing parent).
  - Transactions: `ported_static/stTransactionTest`, `prague/eip7702_set_code_tx`, `berlin/eip2930_access_list`, `cancun/eip4844_blobs`, `osaka/eip7934_block_rlp_limit`.
  - Receipts and withdrawals: `shanghai/eip4895_withdrawals`. Requests: `prague/eip6110_deposits`, `eip7002_el_triggerable_withdrawals`, `eip7251_consolidations`, `amsterdam/eip8282_builder_execution_requests`.
  - Addresses: `frontier/create`, `cancun/create`, `ported_static/stCreateTest`, `stCreate2`, `stRecursiveCreate`, `constantinople/eip1014_create2`.
- **EELS unit tests** (`tests/json_loader/`), to port as `#guard`s:
  - `test_rlp.py`: canonical integers `0x80`↦0, `0x01`, `0x7f`, `0x81 80`, `0x82 01 00`; `0x00`, `0x82 00 01` and `0x83 00 00 01` rejected for `Uint`, `U64` and `U256`.
  - `test_ssz.py`: nested round trip, collection limits, fixed-width integer round trip, offset-gap rejection (standard and nested progressive), non-empty list with zero first offset.
  - `test_transaction_codec.py`, `test_withdrawal_codec.py` (maximum and oversized `amount`), and `test_stateless_guest.py` (schema id).
- **`core` `#guard` cases.**
  - RLP encode:
    - `""`↦`80`, `00`↦`00`, `7f`↦`7f`, `80`↦`81 80`;
    - a 55-byte string ↦ `b7 ‖ …`, a 56-byte string ↦ `b8 38 ‖ …`;
    - `[]`↦`c0`, a 56-byte payload ↦ `f8 38 ‖ …`;
    - `Uint 0`↦`80`, `Uint 1024`↦`82 04 00`.
  - RLP decode rejects:
    - `""`, `81 05`, `b8 05 …` (long form for a short string), `b9 00 40 …` (leading-zero length);
    - `c1` (truncated), `05 06` and `c0 00` (trailing bytes), `c2 82 00` (truncated inner item);
    - `bf ff…ff` (a huge declared length, which must be rejected without allocating).
  - Typed decode rejects: `bool 02`, a 33-byte `U256`, a 19-byte `Address`. A `Bytes0 | Address` union succeeds on exactly one alternative.
  - Adversarial: 40,000-deep nesting. The spec decodes it, where the reference raises `RecursionError`; the typed decode then rejects it (D2r). 20,000-deep nesting, which the reference decodes, must also be rejected by the typed decode.
  - SSZ: a 43-byte `StatelessValidationResult` round trip; the zero sentinel encoding; boolean `02` rejected; offset gap rejected; offset below the fixed size; an offset beyond the scope; decreasing offsets; `ByteList` over its limit; 257 headers (`ssz_list(256)`) rejected at decode (O1).
  - SSZ roots: the empty progressive list root `= H(0^32, 0^32)`; a 3-field progressive container root; `ByteList[2^16]` roots near chunk boundaries (31/32/33 bytes).
  - Addresses: CREATE for a fixed sender at nonces 0–3, the four EIP-1014 CREATE2 examples, and nonce `2^64−1` (which makes the RLP integer 8 bytes long).
- **Property / differential tests.**
  - Random `RlpItem` round trip, and canonicality under mutation fuzzing.
  - Random well-typed SSZ values round trip.
  - SSZ mutation fuzzing comparing the strict decoder with "remerkleable decode plus re-encode check". This is differential only; the fixtures and the EELS source decide.

## 5. Interface

The namespace is `STFSpec.Codec`. All items are public unless marked internal.

```lean
-- RLP
inductive RlpItem where
  | bytes (b : ByteArray)
  | list  (items : List RlpItem)
inductive RlpError where                     -- diagnostic only: EELS has one DecodingError
  | empty | truncated | trailing | nonCanonical (why : String) | shape (ctx : String)
namespace Rlp
  def Encodable : RlpItem → Prop       -- every encoded item length has an at-most-eight-byte length prefix
  def encode       : RlpItem → ByteArray      -- two-pass: size, then write (§6)
  def encodeBytes  : ByteArray → ByteArray
  def encodeLengthPrefix (short long : UInt8) (len : Nat) : ByteArray   -- internal
  def decode       : ByteArray → Except RlpError RlpItem                 -- total, cursor-based
  def decodeItemLength : ByteArray → (pos : Nat) → Except RlpError Nat  -- internal
  -- typed layer
  def ofNat : Nat → RlpItem                    -- .bytes (Uint.toBeBytes n)
  def toNat : RlpItem → Except RlpError Nat    -- rejects lists and leading zero
  def toNatBounded (widthBytes : Nat) : RlpItem → Except RlpError Nat
  def toBool : RlpItem → Except RlpError Bool
  def toBytes : RlpItem → Except RlpError ByteArray
  def toFixed (n : Nat) : RlpItem → Except RlpError (FixedBytes n)
  def toList : RlpItem → Except RlpError (List RlpItem)
  def toFields (n : Nat) : RlpItem → Except RlpError (Vector RlpItem n)  -- dataclass arity check
  def union2 (f : RlpItem → Except RlpError α) (g : RlpItem → Except RlpError α) :
      RlpItem → Except RlpError α              -- exactly-one-success semantics
end Rlp
class RlpEncode (α : Type) where toRlp : α → RlpItem
class RlpDecode (α : Type) where ofRlp : RlpItem → Except RlpError α
-- instances: Nat, U256, U64, U32, U8, Bool, ByteArray, FixedBytes n, Address, Hash32, List α
def Rlp.encodeOf [RlpEncode α] (a : α) : ByteArray
def Rlp.decodeTo [RlpDecode α] (b : ByteArray) : Except RlpError α     -- decode then ofRlp

-- Derived addresses
def computeContractAddress (sender : Address) (nonce : Nat) : Address
def computeCreate2ContractAddress (sender : Address) (salt : Bytes32) (initCode : ByteArray) : Address
-- Query-generic forms (D5); the pure forms above are these at m := Id (definitional)
def computeContractAddressQ [Monad m] [KeccakQuery m] : Address → Nat → m Address
def computeCreate2ContractAddressQ [Monad m] [KeccakQuery m] :
    Address → Bytes32 → ByteArray → m Address     -- two queries: keccak initCode, then the preimage

-- SSZ
inductive SszType where
  | uint (bytes : Nat) | bool
  | byteVector (n : Nat) | byteList (limit : Nat)
  | list (elem : SszType) (limit : Nat) | progressiveList (elem : SszType)
  | progressiveByteList
  | container (fields : List SszType)
  | progressiveContainer (activeFields : List Bool) (fields : List SszType)
inductive SszValue where
  | uint (n : Nat) | bool (b : Bool) | bytes (b : ByteArray)
  | list (xs : List SszValue) | container (xs : List SszValue)
def SszType.WellFormed : SszType → Prop      -- widths ∈ {1,2,4,8,16,32}; active fields end in 1, count = #fields ≤ 256
def SszValue.WellTyped : SszType → SszValue → Prop   -- ranges, exact lengths, limits
def SszType.fixedSize? : SszType → Option Nat
inductive SszError where | length | offset | limit | boolByte | trailing | shape
namespace Ssz
  def encode : SszType → SszValue → ByteArray
  def decode : SszType → ByteArray → Except SszError SszValue          -- strict canonical
  def hashTreeRoot : SszType → SszValue → Bytes32
  def pack : ByteArray → Array Bytes32                                  -- internal
  def merkleize (chunks : Array Bytes32) (limit : Nat) : Bytes32        -- zero-hash padded
  def merkleizeProgressive (chunks : Array Bytes32) : Bytes32
  def mixInLength (root : Bytes32) (len : Nat) : Bytes32
  def mixInActiveFields (root : Bytes32) (active : List Bool) : Bytes32
  def zeroHashes : Array Bytes32                                        -- constant, depth 0..64
  def Rootable (t : SszType) (v : SszValue) : Prop -- actual schema interpretation and representable mix-in lengths
  def zeroHash : Nat → Bytes32    -- recurrence for every depth; array prefix is only an optimisation
end Ssz
class SszSchema (α : Type) where
  type : SszType
  fieldNames : List String   -- source field names in order (F13); checked against REFERENCE-RECORDS
  valid : α → Prop           -- the owner's wire-domain predicate, not an execution-validity test
  toValue : α → SszValue
  ofValue? : SszValue → Option α
def SszSchema.decodeBytes [SszSchema α] : ByteArray → Except SszError α
def SszSchema.encodeBytes [SszSchema α] : α → ByteArray
def SszSchema.hashTreeRoot [SszSchema α] : α → Bytes32
```

## 6. Data structures

| Type | Representation | Model / abstraction | Invariant | Persistence | Complexity |
|---|---|---|---|---|---|
| `RlpItem` | nested inductive over `ByteArray` and `List` | itself (it is the public model) | none | immutable; decoded nodes may be shared by snapshots read-only | `encode` O(n) via a size pass and one pre-sized write. A naive recursive `++` is O(n·depth), which is also what Python's slicing and joining cost, so it should be avoided. `decode` O(n) with a cursor, instead of Python's re-slicing at each level (O(n·depth)) |
| encoded bytes | `ByteArray` | `List UInt8` | canonical (image of `encode`) | linear while being built, then frozen | — |
| `SszType` | inductive | itself | `WellFormed` | immutable constant per schema | — |
| `SszValue` | nested inductive | itself; typed views via `SszSchema` | `WellTyped t v` | immutable | `encode`/`decode` O(n · type depth) |
| `zeroHashes` | `Array Bytes32` built once | `z₀ = 0^32`, `z_{i+1} = H(z_i, z_i)` | the recurrence | read-only constant (not a cache in the §7 sense) | O(1) lookup |
| merkleization | `Array Bytes32` layers | the full padded binary tree | — | local, linear | O(chunks) hashes + O(log limit) zero-hash lookups. **Never O(limit)**: `ByteList[2^16]` has 2048 chunk leaves, and `List[_, 256]` must not hash 256 leaves when it has 3 elements |

**No derived instances on the nested inductives** (F17). `deriving BEq`, `Repr` or `DecidableEq` on `RlpItem`, `SszType` or `SszValue` generates `partial` constants (for example `instBEqT.beq`), which D21 bans and only the compiled declaration check catches. Write structural instances by hand, as mutual structural recursions (a compiled prototype of the interfaces showed the pattern works). Non-nested types such as `RlpError` and `SszError` may derive them.

## 7. Contract and laws

**RLP.**
- [T] `decode` is total: well-founded recursion on the remaining byte count, where each item consumes at least one byte. It allocates nothing proportional to a *declared* length before checking that length against the input.
- [C] Round trip: `Encodable x → decode (encode x) = .ok x`.
- [C] **Canonicality:** `decode b = .ok x → Encodable x ∧ encode x = b`. Together with the round trip, `decode b = .ok x ↔ Encodable x ∧ encode x = b`. This is the Lean form of D1r.
- [C] **Injectivity and prefix-freeness:** `Encodable x ∧ Encodable y ∧ encode x ++ r = encode y ++ s → x = y ∧ r = s`. These feed [S]: witness and header binding under Keccak collision resistance.
- [C] Integer canonicality: `toNat (.bytes b) = .ok n ↔ b = Uint.toBeBytes n`; `toNatBounded w` additionally requires `b.size ≤ w`.
- [R] Typed round trips for each instance: `Encodable (toRlp a) → decodeTo (encodeOf a) = .ok a` (where toRlp is the instance adapter). This is used by `EthBlock` (transaction, header and receipt codecs) and `EthStateCommit` (account leaves).
- [R] `union2 f g x = .ok a` implies that exactly one of `f x`, `g x` succeeds.

**SSZ.**
- [T] `decode` is total: recursion on the type, with each sub-decode on a strictly smaller slice. Offsets are validated against the slice length before use.
- [C] Round trip: `WellTyped t v → (encode t v).size < 2^32 → decode t (encode t v) = .ok v`.
- [C] **Canonicality:** `decode t b = .ok v → WellTyped t v ∧ encode t v = b`. This theorem is the Lean replacement for EELS's re-encode check (`ssz.py:144`). It pins the accept set to the image of `encode`, which is exactly the set EELS accepts. That EELS's set is exactly the image of `encode` is itself a claim about the reference, argued in S3 and tested differentially.
- [T] `hashTreeRoot` must terminate, and its reference refinement requires the schema’s Rootable domain (length mix-ins fit uint256 and fields have the exact interpretation). O2 freedom requires proving every successfully decoded guest request belongs to that domain; S5 alone does not establish this.
- [C] `merkleize` with `zeroHashes` equals naive merkleization over the full power-of-two padding. `merkleizeProgressive` is characterised by the recurrence in S4.
- [C] Schema laws per `SszSchema α` instance: `valid a → ofValue? (toValue a) = some a ∧ WellTyped type (toValue a)`; conversely `WellTyped type v ∧ ofValue? v = some a → valid a ∧ toValue a = v`. This second direction prevents lossy schema conversions from changing the decoded request's commitment. The schema type itself is well formed.
- [S] **Binding:** on the actual guest schemas, with well-typed values, exact active-field interpretation and every length mix-in representable in uint256, equal `hashTreeRoot`s imply equal values or an explicit SHA-256 collision. This is the request-binding theorem of CONTRACT §7. Induct over the schema and Merkle tree: equal child preimages permit descent; unequal preimages with equal hash give the collision. Fixed widths and mixed-in lengths disambiguate padding. Extending this law to arbitrary `SszType` requires specifying inactive fields and the domain of unbounded progressive lengths; it is not asserted without those premises.

**Addresses.**
- [C] `computeContractAddress a n = lastBytes20 (keccak256 (encode (.list [.bytes a.toBytes, ofNat n])))`, and likewise for CREATE2. The `…Q` forms at `m := Id` equal these by `rfl`.

### Informal correctness argument

**Claim.** On the encodable domain, decoding accepts precisely the reference encodings, returns the same typed value or error, and the guest-schema roots use the specified Merkle layout.

**Premises.** EthBase/Hash laws, exact schema field order and widths, both directions of each schema adapter, representable offsets/length mix-ins, and a resolved policy for reference host-resource exceptions.

**Argument.** RLP prefix cases determine one extent; recurse only inside that extent and require full consumption. The shortest-length and integer checks give canonicality and prefix-freeness. Typed decoders then check constructor shape, arity and integer ranges. SSZ induction over types establishes fixed-size layouts and variable-offset boundaries; the strict decoder's accepted bytes must re-encode identically, while the reverse implication needs a separate proof that every canonical encoding decodes. The schema adapter transfers both results to the caller's type. Merkleization induction replaces padded subtrees with the zero-hash recurrence; progressive zero hashes are defined for every required depth, not just the cached prefix. Binding descends through equal child preimages; unequal preimages with equal digests expose a collision. Exact field interpretation and mixed-in lengths distinguish zero padding.

**Open obligations.** Rootability of every accepted guest input, unbounded progressive-length domains, RLP encodability and all schema instances need proof. These domains must not become new acceptance limits without an explicit protocol decision. Generic inactive-field binding is not implied by the guest-schema result.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** `EthHash`.
- **Used by:** `EthCommit` (node RLP), `EthVmInstructions` (CREATE/CREATE2 addresses), `EthBlock` (transaction/header/receipt RLP, withdrawal and request SSZ, BAL encoding), and transitively `EthStateCommit` (account leaf RLP), `EthStateWitness` and `EthStateless` (`StatelessInput` schema, output encoding, the request root).
- **Seams provided.** Generic RLP and SSZ with canonicality theorems. Schema owners write `SszSchema`/`RlpDecode` instances and prove only the per-instance schema laws. Contract-address derivation.
- **Cross-module invariants.** Consumers must decode with `decodeTo` (typed) wherever EELS uses `decode_to`, so that D2r stays unobservable. Schema owners must mirror `_infer` exactly: field order, widths, limits, and progressive versus plain types.
- **Relies on.** `EthHash.sha256` and `keccak256`, and `EthBase` byte conversions (in particular `Uint.toBeBytes 0 = empty`).

## 9. Open decisions

- **SSZ reference implementation** (DECISIONS B5, Q21/Q22; adopted provisionally): [ethereum/ssz-specs `lean/`](https://github.com/ethereum/ssz-specs/tree/main/lean) (@d4a0d75, MIT, Lean v4.33.1, no dependencies, `warningAsError`).
  - **Why it fits:** its types-as-data design (`Desc` declarations plus separate values) matches the `SszValue` + `WellTyped` resolution. It proves codec canonicality ("every accepted byte string is canonical"), round trips, admissibility, whole-value binding in SHA-256 collision form, progressive trees (EIP-7916/7495), and a merkleization cost bound.
  - **Status:** inspiration and reference now. It becomes a dependency only if the modules we import pass `check-decls` (D26) and match our decisions: strict decoding, error constructors per D14, and the schemas our guest needs (`StatelessInput` progressive lists, `NewPayloadRequest`).
  - **To check:** its handling of the offset-gap and misalignment cases that remerkleable accepts and EELS's re-encode check rejects, and its SHA-256 speed.

- **D5** (provisional, broad scope; B10): address derivation and transaction/header hashing go through `KeccakQuery` (A3). The public pure forms are the `Id` specialisations.
- **D14** (accepted): O1 (decode failures) needs explicit constructors. O2 (root failure) is **open**: prove it unreachable (S5; EthStateless L-root) and add a constructor only if that proof fails (DECISIONS §3, O2). The precedence between SSZ decode failure and schema-id failure is owned by `EthStateless`.
- **D18/D21** (accepted): no fast paths are planned. `@[csimp]` is banned; any later fast path is a representation replacement, or an executable definition with a legible reference and an equality proof.
- **P2:** the fixtures decide where they speak (9 O1 fixtures). Elsewhere the EELS re-encode check is the authority.
- RLP `RecursionError` (D2r): tracked under DISC-001 (DECISIONS Q20; O12, unresolved by design). The reproducer is probe `tx-deep-rlp-40000`.
- SSZ decoder formulation and value representation: resolved, DECISIONS B5 (Q21, Q22).

## 10. Gaps

- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **EIP cross-check missing.** The progressive merkleization order (subtree left, rest right) and the placement of the active-fields chunk were checked only against remerkleable, the pinned dependency. They have not been compared with EIP-7916 or EIP-7495 at the versions the fixtures were generated with. If they disagree, the fixtures still decide, but the discrepancy should be reported.
- **"EELS accepts exactly the image of `encode`" (S3)** is argued from the re-encode check. It is not proved for remerkleable's `decode_bytes`, which could raise (and so reject) on some canonical input. This is unlikely but unverified. The differential round-trip fuzzing should cover every Amsterdam schema, not only toy containers.
- **RLP canonicality** has 500k fuzz cases of evidence and no proof yet. The prefix-freeness proof strategy is standard, but it is unwritten in Lean.
- **D2r agreement** (deep nesting) is argued on the spec side. No fixture exercises it; it is tracked under DISC-001 (DECISIONS Q20), with probe `tx-deep-rlp-40000` as the reference-side reproducer. The claim that "no transaction schema nests more than about 4 levels" needs a check against every transaction type, including access lists, authorization lists and blob hashes. It also applies to the untyped `rlp.decode` sites (`incremental_mpt.py:936`, `witness_state.py:112,198`), which are protected only by the 2^10-byte node limit. That argument holds only if every such input comes from a bounded witness field. This is unverified for `witness_state.py:198`.
- **Thin O1 coverage.** The 9 fixtures do not test: `boolean` bytes other than 0 or 1, per-element `ByteList` limits (a 1025-byte witness node, a 65537-byte code), 257 headers, a wrong `public_keys` element length (65 bytes), an empty non-zero-scope list, or offsets ≥ 2^31. `#guard`s are proposed, but these cases lack fixtures.
- **SSZ encode partiality at 2^32** (S6) is stated but has no consumer theorem using the hypothesis. No `Envelope` field exists for it; by DECISIONS B6 one is added only when a named consumer theorem needs it (see `EthBase`).
- **The binding [S] proof** is sketched only. It needs an owner in `EthSecurity`, and the SHA-256 assumption for requests must be reconciled with the Keccak ROM (D5).
- **Schema fidelity.** Field order is checkable through `SszSchema.fieldNames` (F13): a prototype script outside this repository compared each adapter's names with REFERENCE-RECORDS. The core has no such check yet, and names alone do not check widths, limits or progressive versus plain types against `_infer`. The proposal for those is a `#guard` comparing `hashTreeRoot` of a sample value with a stored root generated from EELS; the generator script and stored roots do not exist yet.
- **Reference evidence:** the D1r fuzzing ran under 0.1.7 (byte-identical `rlp.py`); a rerun under the locked 0.1.6 would remove the version caveat.
- **Address derivation ownership.** Placing it here (not in `EthVmInstructions`) is a judgement call made in this spec, not an ARCHITECTURE decision.
- **Performance** of `encode` (two-pass) and cursor `decode` is unmeasured, as is the SSZ `decode` of a maximal witness (thousands of nodes).
- **The fixed-arity tuple laxity (D4r)** is deliberately not modelled. Any EELS change that introduces a fixed-arity RLP tuple target would silently diverge.
