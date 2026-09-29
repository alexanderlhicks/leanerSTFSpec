# `EthBase`: primitive words, integers, bytes and the envelope

*Status: informal specification, draft. Date: 2026-09-29. Pin: `tests-zkevm@v21.0.0` @e1a316a0. Architecture: `STFSpec/informal/ARCHITECTURE.md`.*
*Navigation: interface findings F2, F19 (DECISIONS §3) · gate: [REVIEW §3](../REVIEW.md) · decisions: D1, D2, D5, D14, D18, D21 · questions: B6/Q17, B14/Q15, Q16, Q18, F2, F19.*

Paths without a prefix are relative to `src/ethereum/` at the pin. `ethereum_types/…` paths refer to the installed `ethereum-types` 0.4.1 (the version locked in `uv.lock`; `reference.toml`), read from the scratch venv at `site-packages/ethereum_types/`.

## 1. Purpose

`EthBase` is layer L0 (ARCHITECTURE §2): the primitive value types every other library uses. These are the EVM word `U256` with its full EVM arithmetic API, bounded and unbounded integers (`Uint`, `U8`…`U64`), byte sequences (`Bytes`), fixed-width byte types (`Address`, `Hash32`, `Bytes32`, `Bloom`, …) with their lawful orderings, big/little-endian conversions, a few numeric helpers from `utils/`, the `HashConsts` record of keccak-derived constants (D5; values only, computed by `EthHash`), and the `Envelope` record of implementation limits. It contains no fork policy, no hashing and no codecs. Its main architectural job is to make replacement exercise 4 (ARCHITECTURE §1) pass: callers see `U256` only through stable observers and representation-independent laws.

## 2. Requirements

**R1. `U256` is a `structure`, never an `abbrev`** (ARCHITECTURE §1, §5.1; D1). Callers must use only the observers `toBitVec`/`toNat`/`toInt` and the operation laws of §7. The stored field is internal by convention; exercise 4 checks this.

**R2. Two arithmetic families, not one.** The pinned `ethereum_types` has two kinds of arithmetic on fixed-width integers, and a naive reading can mix them up:
- *Checked (Python operator) arithmetic.* `+`, `-`, `*`, `//`, `%`, `**`, `<<` on `U256`/`U64`/… construct a result of the same class and **raise `OverflowError` if it is out of range** (`ethereum_types/numeric.py:91–135`, `_in_range` at `:611`). `a - b` with `a < b` raises (`:103–111`). `//` and `%` by zero raise `ZeroDivisionError`. `U256(1) << U256(256)` raises `OverflowError`, which I checked on the installed library. Constructing `U256(n)` from an out-of-range `int`/`Uint` raises (`:44–48`).
- *Wrapping arithmetic.* `wrapping_add/sub/mul/pow` reduce mod 2^256 (`:614–667`), and `~x` is masked (`:670`).

The EVM opcodes use wrapping ops or explicit `Uint` intermediates (`forks/amsterdam/vm/instructions/arithmetic.py:28–367`, `bitwise.py:123–274`). **Everything else (balances, gas, fees, nonces, SSZ/RLP field construction) uses checked ops.** Their failure is *not* an EVM exceptional halt: the interpreter catches only `ExceptionalHalt`/`Revert` (`vm/interpreter.py:276,386,456,466`). So an `OverflowError` or `ZeroDivisionError` propagates to `verify_stateless_new_payload`'s catch-all (`stateless.py:303`) and makes the whole block invalid with the output `(root, false, chain_id, 0x1501)`. Each such site reachable from guest input is an enumerated CONTRACT O13 fault with a named constructor (the output is the same as O6/O7), unless a local handler consumes it first (for example `execution_engine/new_payload.py:60–68`, which makes it O6). `EthBase` must therefore expose **checked** operations returning `Option`/`Except` alongside the total EVM operations. It must never silently wrap or saturate where EELS raises.

**R3. `Uint` is unbounded** (`ethereum_types/numeric.py:517–540`): `_in_range` is `value ≥ 0`, so subtraction below zero raises `OverflowError` and addition never overflows. It is modelled by `Nat`, with `Nat.sub` truncation **forbidden** at call sites that mirror EELS `Uint` subtraction: use `Uint.sub? : Nat → Nat → Option Nat`.

**R4. Cross-type behaviour.** `U256(1) == Uint(1)` and `U256(1) == 1` are `True` (`__eq__` compares numbers, `:325–341`), but `U256(1) < Uint(2)` and `U256(1) + Uint(1)` raise `TypeError` (both checked on the installed library). The spec is typed, so the `TypeError` cases are unreachable in well-typed EELS paths. The cross-type equality means that an EELS test like `divisor == 0` is numeric equality.

**R5. EVM word semantics (normative definitions, EELS argument order: first popped operand first).**
- `add/sub/mul`: mod 2^256 (`arithmetic.py:28,55,82`).
- `div a b = 0` if `b = 0`, else `⌊a/b⌋` (`:109`). `mod a b = 0` if `b = 0`, else `a % b` (`:175`).
- `sdiv`: on the two's-complement values, `0` if the divisor is 0. `−2^255 / −1 = −2^255` is an explicit case (`:139–169`; `from_signed(2^255)` would otherwise raise). Otherwise it is truncated division (`sign(a·b)·(|a| div |b|)`, i.e. `Int.tdiv`).
- `smod`: `0` if the divisor is 0, else `sign(a)·(|a| mod |b|)` (`Int.tmod`) (`:205–229`).
- `addmod/mulmod a b n`: `0` if `n = 0`, else `(a+b) mod n` / `(a·b) mod n` over **unbounded** intermediates (`:235–289`: operands are converted to `Uint`).
- `exp a b = a^b mod 2^256` (`:297–326`, three-argument `pow` over `Uint`). The spec must use square-and-multiply mod 2^256, not the full power.
- `signextend k x`: `x` if `k > 31`, else sign-extend from byte `k` counted from the least-significant end (`:334–367`).
- `lt/gt/eq/iszero` return the word 0 or 1; `slt/sgt` compare `to_signed` values (`comparison.py:24–177`).
- `and/or/xor/not` bitwise (`bitwise.py:24–117`).
- `byte i x`: `0` if `i ≥ 32`, else byte `i` counted from the most-significant end (`:123–153`).
- `shl s v`: `0` if `s ≥ 256`, else `(v << s) mod 2^256`, computed over `Uint` (`:159–183`). `shr` works the same way with `>>` (`:189–213`).
- `sar s v`: `from_signed(to_signed v >> s)` if `s < 256`; otherwise `0` for non-negative `v` and `2^256−1` for negative `v` (`:219–245`).
- `clz x = 256 − bitLength x` (`:251–274`, EIP-7939, new since Osaka; easy to miss).

**R6. Signed conversions.** `to_signed` (`ethereum_types/numeric.py:675–686`) is two's complement at 256 bits. `from_signed` (`:594–608`) **raises** for values outside `[−2^255, 2^255)`: `from_signed(−2^255)` succeeds, `from_signed(2^255)` raises (checked). The spec provides a checked `ofInt?` and proves that every EVM use is in range.

**R7. Byte conversions.**
- `to_be_bytes()` is minimal big-endian, and `Uint(0).to_be_bytes() = b""` (`:477–484`). This is load-bearing for RLP integer encoding.
- `to_be_bytes32()` raises `OverflowError` for values ≥ 2^256 (`:424`); this is only reachable for `Uint`.
- `FixedUnsigned.from_be_bytes(buf)` rejects `len(buf) > byteWidth` **by length, not value**: 33 zero bytes raise `ValueError` for `U256` (`:566–577`; checked).
- `Uint.from_be_bytes` accepts any length (`:523`).
- `U32.from_le_bytes` and the other little-endian variants are analogous.

**R8. Fixed-width bytes.** `FixedBytes.__new__` raises `ValueError` unless the length is exact (`ethereum_types/bytes.py:29–37`).
- `Address = Bytes20` (`state.py:33`), `Hash32 = Bytes32` (`crypto/hash.py:19`), `Root = Hash32` (`state.py:34`), `Bloom = Bytes256` (`forks/amsterdam/fork_types.py:34`), `VersionedHash = Hash32` (`fork_types.py:32`).
- *Naive-reading trap:* these are `bytes` subclasses, so slicing or concatenating them yields plain `bytes`. Equality with a plain `bytes` of the same content is `True`. The spec must use explicit conversions and `Hash32 ≠ Bytes32` only as a type distinction (D2).

**R9. Helpers from `utils/`.**
- `ceil32 n` is the least multiple of 32 that is `≥ n` (`utils/numeric.py:43`).
- `get_sign` is signum (`:19`).
- `left_pad_zero_bytes v n` / `right_pad_zero_bytes v n` are `rjust`/`ljust` (`utils/byte.py:18,40`): **no truncation** if `len v > n`.
- `taylor_exponential f n d` (`utils/numeric.py:177`) is the loop exactly as written. It is used for the blob base fee (`vm/gas.py:987`). It raises `ZeroDivisionError` if `d = 0`, so it is total only under `d > 0`.
- `to_address_masked w` is the last 20 bytes of `w.to_be_bytes32()` (`forks/amsterdam/utils/address.py:24`).

**R10. Hex utilities** (`utils/hexadecimal.py`, `forks/amsterdam/utils/hexadecimal.py`) are used in scope only to build **constants** (for example `hex_to_address` in `fork.py`, `requests.py`, `vm/eoa_delegation.py`; `hex_to_bytes` in `merkle_patricia_trie.py:72`, `crypto/kzg.py:54`) and by fixture loaders. They are never applied to guest input. The spec may write the constants as literals, provided a `#guard` checks each literal against the hex string in the source. Python quirks we do **not** reproduce, since they are not reachable from guest input:
- `bytes.fromhex` accepts whitespace between bytes;
- `int(s, 16)` accepts `_`, whitespace and `+`;
- `hex_to_address` left-pads with `rjust(40,"0")`.

**R11. `Envelope`** is a record of implementation limits used as explicit hypotheses in consumer theorems. It must never narrow the accepted input domain of the reference guest (ARCHITECTURE §5.1; CONTRACT §7).

**R12. Totality.** Every public function is total. Partiality in EELS (raises) is made explicit in `Option`/`Except` result types.

## 3. EELS source map

| EELS item | Line | Spec declaration | Notes |
|---|---|---|---|
| `utils/numeric.py::get_sign` | 19 | `Int.sign` (reuse) / `STFSpec.Base.getSign` | used only by `sdiv`/`smod`, whose laws subsume it |
| `utils/numeric.py::ceil32` | 43 | `STFSpec.Base.ceil32 : Nat → Nat` | gas and memory sizing |
| `utils/numeric.py::is_prime` | 68 | `STFSpec.Base.isPrime : Nat → Bool` (internal) | **not reachable from the guest** (no in-scope caller); candidate for `EXCLUDED.md` |
| `utils/numeric.py::le_bytes_to_uint32_sequence` | 96 | `STFSpec.Base.leBytesToU32s` (internal) | only `ethash.py` uses it: unreachable; exclusion candidate |
| `utils/numeric.py::le_uint32_sequence_to_bytes` | 122 | `STFSpec.Base.leU32sToBytes` (internal) | as above |
| `utils/numeric.py::le_uint32_sequence_to_uint` | 155 | `STFSpec.Base.leU32sToNat` (internal) | as above |
| `utils/numeric.py::taylor_exponential` | 177 | `STFSpec.Base.taylorExponential : Nat → Nat → (d : Nat) → 0 < d → Nat` | blob base fee; termination proof needed |
| `utils/byte.py::left_pad_zero_bytes` | 18 | `Bytes.leftPadZero` | no truncation |
| `utils/byte.py::right_pad_zero_bytes` | 40 | `Bytes.rightPadZero` | memory reads |
| `utils/hexadecimal.py::*` | 20–206 | `STFSpec.Base.Hex.*` (internal, test/constant only) | `has_hex_prefix`, `remove_hex_prefix`, `hex_to_bytes{,8,32,256}`, `hex_to_hash`, `hex_to_uint`, `hex_to_u8/u64/u256` |
| `forks/amsterdam/utils/hexadecimal.py::hex_to_root` | 21 | `STFSpec.Base.Hex.toRoot` (internal) | constants only |
| `forks/amsterdam/utils/hexadecimal.py::hex_to_address` | 39 | `STFSpec.Base.Hex.toAddress` (internal) | constants only; `rjust` padding |
| `utils/__init__.py::has_field` | 9 | none (Python reflection) | no in-scope caller; exclusion candidate. Claimed so that it is visibly owned |
| `forks/amsterdam/utils/address.py::to_address_masked` | 24 | `Address.ofU256Masked : U256 → Address` | a pure conversion, so it is split from the rest of `address.py`; `compute_*` go to `EthCodec` (they need RLP and Keccak) |

| `forks/amsterdam/fork_types.py::Authorization` | 87 | `structure Authorization` | a plain record `{chainId : U256, address : Address, nonce : U64, yParity : U8, r s : U256}`. It must be visible to `EthVmCore` (`vm/__init__.py`, `vm/eoa_delegation.py`, `vm/gas.py`) and `EthBlock` (`transactions.py`, `fork.py`), and `EthBase` is their common base. `EthBlock`'s spec already expects it here. Its RLP codec is `EthBlock`'s |
| `forks/amsterdam/fork_types.py::StateGasPerByte` | 45 | `structure StateGasPerByte where rate : Nat` | an EIP-8037 rate type, deliberately not a `Uint`. Only the *type* lives here; the value (`vm/gas.py:56`, 1530) is an Amsterdam value in `EthFork` (record type in `EthVmCore`) |
| `forks/amsterdam/fork_types.py::StateGasPerByte.__mul__` | 58 | `StateGasPerByte.charge : StateGasPerByte → Nat → Nat` | `rate · numBytes`, as `StateGas`; unbounded, no failure |
| `forks/amsterdam/fork_types.py::StateGasPerByte.__rmul__` | 62 | same function (commuted operands) | Python operand-order plumbing only |

**Owned by EthStateCommit.** `encode_account` in `forks/amsterdam/fork_types.py` needs Account and RLP and is claimed by EthStateCommit; EthBase and EthCodec must not introduce duplicate implementations. ExecutionGas/StateGas are Nat aliases, and the fixed-width aliases remain here.

**External semantics.** `EthBase` specifies these `ethereum_types` items (inventory `external` entries):
- `ethereum_types.numeric.{Uint, U256, U64, U32, U16, U8, FixedUnsigned, Unsigned, ulen}`;
- `ethereum_types.bytes.{Bytes, Bytes0, Bytes8, Bytes20, Bytes32, Bytes48, Bytes64, Bytes96, Bytes256, FixedBytes}`;
- `ethereum_types.frozen.{slotted_freezable, modify}`.

Each is specified as follows:
- **Numeric types.** R2, R3, R6 and R7, with the checked and wrapping families kept separate. `ulen` is `ByteArray.size`/`List.length` as `Nat`.
- **`Bytes` and the fixed-width types.** R8.
- **`slotted_freezable`/`modify`.** Python immutability plumbing. Lean values are immutable, and `modify obj f` is functional record update. There is no semantic content, but consumers must not rely on mutation-after-freeze (none observed).

### Implemented U256 value slice

The following declarations are in `STFSpec/Base/U256.lean`, namespace
`STFSpec.Base.U256` (the structure is `STFSpec.Base.U256`). All rows are
**discharged for this slice**: total, pure and without state effects. The source is the
locked `ethereum-types` 0.4.1 at the EELS pin. The unsigned arithmetic slice below is also implemented; all other APIs remain
**unimplemented** and the module's draft status is unchanged. `toNat`/`toInt` and `ofNat?`/`ofInt?`
are the stable Lean observer/checked-result names for Python `__int__`/`to_signed`
and `U256(...)`/`from_signed`; `ofNat` is an additional wrapping model helper.

| Dependency/source at the pin | Lean declaration and public type | Domain and success observation | Ordered failures / consumer | Public laws | Regression evidence |
|---|---|---|---|---|---|
| `ethereum_types/numeric.py:690` (`U256`) | `structure U256` | All 256-bit words | None | `ext`, `toBitVec_inj`, `toNat_inj`, `toInt_inj` | `U256Client.lean`: observer injectivity |
| `ethereum_types/numeric.py:325` (`__eq__`) | `DecidableEq U256` | All word pairs; equality is numeric equality within the word type | None; Python cross-type equality is represented by numeric observers, not heterogeneous Lean equality | `toNat_inj`, `toInt_inj` | `U256.lean`: checked construction equals constants; `U256Client.lean`: injectivity |
| Lean model of `numeric.py:690` | `toBitVec : U256 → BitVec 256` | All words; stable abstraction | None | `toNat_eq`, `toInt_eq`, `toBitVec_inj` | `U256Client.lean`: model extensionality |
| `ethereum_types/numeric.py:321` (`__int__`) | `toNat : U256 → Nat` | All words; unsigned integer in `[0, 2^256)` | None | `toNat_lt`, `toNat_inj` | `U256.lean`: 0, 1, signed-boundary words, max |
| `ethereum_types/numeric.py:675` (`to_signed`) | `toInt : U256 → Int` | All words; unsigned value below `2^255`, otherwise unsigned value minus `2^256` | None | `toInt_eq_toNat_cond`, `le_toInt`, `toInt_lt`, `toInt_inj` | `U256.lean`: `2^255−1`, `2^255`, `2^255+1`, max; differential signed observations |
| Lean model constructor | `ofBitVec : BitVec 256 → U256` | All model values; bit-vector observation is the input | None | `toBitVec_ofBitVec`, `ofBitVec_toBitVec` | `U256Client.lean`: extensionality; constructor laws compiled universally |
| Lean wrapping model helper, not Python `U256(n)` | `ofNat : Nat → U256` | All natural inputs; value reduced modulo `2^256` | None | `toBitVec_ofNat`, `toNat_ofNat`, `toNat_ofNat_of_lt`, `ofNat_toNat` | `U256.lean`: `2^256`, `2^256+1`; differential checked Python construction after masking |
| `ethereum_types/numeric.py:44,611` (`U256(n)`) | `ofNat? : Nat → Option U256` | Succeeds iff `n < 2^256`; unsigned observation is `n` | Unsigned overflow becomes `none`; callers own named fault/first-handler projection (D14/B14), not this primitive | `ofNat?_eq_some_iff`, `ofNat?_eq_none_iff`, `ofNat?_toNat` | `U256.lean`: 0, 1, `2^255±1`, max, `2^256`; differential success/rejection |
| `ethereum_types/numeric.py:594` (`from_signed`) | `ofInt? : Int → Option U256` | Succeeds iff `−2^255 ≤ i < 2^255`; signed observation is `i`, unsigned observation encodes two's complement | Upper overflow first; after the source's nonnegative success branch, lower overflow; both become `none`. Lean tests the lower bound also on nonnegative inputs, where it holds. Callers own fault projection (D14/B14) | `ofInt?_eq_some_iff`, `ofInt?_eq_none_iff`, `ofInt?_toInt`, `toNat_ofInt?` | `U256.lean`: signed min/min−1/max/max+1, −1/0/1; universal inverse in `U256Client.lean`; differential success/rejection |
| `ethereum_types/numeric.py:44` on `bool`; EELS `forks/amsterdam/vm/instructions/comparison.py:43` | `ofBool : Bool → U256` | All Booleans; false ↦ 0, true ↦ 1 | None | `toNat_ofBool`, `toInt_ofBool`, `ofBool_eq_ofNat` | `U256.lean`: both Booleans; differential Boolean construction |
| `ethereum_types/numeric.py:44` on 0 | `zero : U256` | Unsigned and signed value 0 | None | `toNat_zero`, `toInt_zero` | `U256.lean`: zero |
| `ethereum_types/numeric.py:44` on 1 | `one : U256` | Unsigned and signed value 1 | None | `toNat_one`, `toInt_one` | `U256.lean`: one |
| `ethereum_types/numeric.py:711–712` (`MAX_VALUE`) | `max : U256` | Unsigned `2^256−1`, signed −1 | None | `toNat_max`, `toInt_max` | `U256.lean`: max; differential dependency constant |
| `ethereum_types/numeric.py:343–369` (numeric comparisons) | `Ord U256`; `Std.TransOrd U256`; `Std.LawfulEqOrd U256` | All pairs of words; compare unsigned numeric observations | None in the typed same-word domain; Python cross-type order errors are unreachable here | `compare_eq`, `compare_eq_eq_iff`, `compare_eq_lt_iff`, `compare_eq_gt_iff` | `U256.lean`: unsigned sign-boundary order, wrapped equality; `U256Client.lean`: laws only; differential numeric comparisons |

Regression paths in the table are under `STFSpec/Conformance/Base/`. The root
`STFSpec/Conformance.lean` imports both Lean suites. The host driver
`STFSpec/Conformance/Base/u256_differential.py` reads the actual pinned dependency in
the frozen EELS venv, checks its version and the checkout commit against `reference.toml`,
and generates public-API guards outside the repository. Its fixed seed is 256; the
72 unsigned cases, 73 signed cases and 75 comparison pairs include the listed boundaries.
Generated observations are bug-finding evidence only (CONTRIBUTING §1), never committed
normative values. Invoke the script with the EELS venv's Python and
`--eels <checkout> --output <scratch-file.lean>`; it runs Lean and reports the executed guards and rejection counts.
No EEST guest records are executed by this slice.

### Implemented unsigned arithmetic slice

`STFSpec/Base/U256Arithmetic.lean` adds the following operations in
`STFSpec.Base.U256`. All rows are **discharged for this value slice**, on all
word inputs, with no state effects. They implement only the numerical part of the
EELS handlers: stack admission/pop/push, gas charging, PC updates and frame error
priority remain owned by `EthVmInstructions` and are not claimed implemented here.
Checked failures return `none`; their named fault and first-handler projection belong
to each consumer under D14/B14. Same-type operands make Python `TypeError` cases
unreachable at this seam. Signed division/remainder and exponentiation remain
**unimplemented**, as do the remaining APIs outside the earlier value slice.

| Source at the pin (dependencies: `ethereum-types` 0.4.1) | Lean declaration and public type | Success/model observation | Ordered failures / consumer | Public laws | Regression evidence |
|---|---|---|---|---|---|
| EELS `forks/amsterdam/vm/instructions/arithmetic.py:28`; `ethereum_types/numeric.py:614` | `add : U256 → U256 → U256` | Sum modulo `2^256`; bit-vector addition | None at the value seam | `toBitVec_add`, `toNat_add` | `U256Arithmetic.lean`: max+1 wraps to zero; handler differential |
| EELS `forks/amsterdam/vm/instructions/arithmetic.py:55`; `ethereum_types/numeric.py:625` | `sub : U256 → U256 → U256` | First minus second modulo `2^256`; bit-vector subtraction; `(2^256−b.toNat+a.toNat) % 2^256` | None at the value seam | `toBitVec_sub`, `toNat_sub` | `U256Arithmetic.lean`: 0−1 wraps to max; 7−3 and 3−7; handler differential |
| EELS `forks/amsterdam/vm/instructions/arithmetic.py:82`; `ethereum_types/numeric.py:636` | `mul : U256 → U256 → U256` | Product modulo `2^256`; bit-vector multiplication | None at the value seam | `toBitVec_mul`, `toNat_mul` | `U256Arithmetic.lean`: max·max=1, `2^128·2^128=0`; handler differential |
| EELS `forks/amsterdam/vm/instructions/arithmetic.py:109`; `ethereum_types/numeric.py:158` | `div : U256 → U256 → U256` | Zero if divisor is zero; otherwise first unsigned value divided by second | EVM zero-divisor branch succeeds with zero; nonzero quotient fits, so checked dependency construction cannot overflow | `toNat_div`, `div_zero`, `div_mod_decomposition`, `div_mod_eq` | `U256Arithmetic.lean`: zero divisors, asymmetric operands, max/1; handler differential |
| EELS `forks/amsterdam/vm/instructions/arithmetic.py:175`; `ethereum_types/numeric.py:178` | `mod : U256 → U256 → U256` | Zero if divisor is zero; otherwise first unsigned value modulo second | EVM zero-divisor branch succeeds with zero; nonzero remainder is below divisor and fits | `toNat_mod`, `mod_zero`, `mod_lt`, `div_mod_decomposition`, `div_mod_eq` | `U256Arithmetic.lean`: max%0=0 (not Nat/BitVec remainder), asymmetric operands, decomposition; handler differential |
| EELS `forks/amsterdam/vm/instructions/arithmetic.py:235` | `addmod : U256 → U256 → U256 → U256` | Zero if modulus is zero; otherwise unbounded `(a.toNat+b.toNat) % n.toNat`, without intermediate wrapping | Zero branch before reduction; nonzero modulus proves remainder fits and constructor failure is unreachable | `toNat_addmod`, `addmod_lt` | `U256Arithmetic.lean`: addmod max 1 max=1, moduli 0/1; handler differential |
| EELS `forks/amsterdam/vm/instructions/arithmetic.py:266` | `mulmod : U256 → U256 → U256 → U256` | Zero if modulus is zero; otherwise unbounded `(a.toNat*b.toNat) % n.toNat`, without intermediate wrapping | Zero branch before reduction; nonzero modulus proves remainder fits and constructor failure is unreachable | `toNat_mulmod`, `mulmod_lt` | `U256Arithmetic.lean`: mulmod max max 12=9, moduli 0/1; handler differential |
| `ethereum_types/numeric.py:91,44,611` | `checkedAdd : U256 → U256 → Option U256` | Succeeds iff unreduced sum is below `2^256`, retaining that sum | OverflowError becomes `none`; consumer owns first handler/outcome | `checkedAdd_eq_some_iff`, `checkedAdd_eq_none_iff` | `U256Arithmetic.lean`: max+1 fails, max+0 and (max−1)+1 succeed; dependency differential |
| `ethereum_types/numeric.py:103,44,611` | `checkedSub : U256 → U256 → Option U256` | Succeeds iff second unsigned value is at most first, retaining the difference | Underflow (source OverflowError) becomes `none`; underflow guard precedes subtraction. Result constructor cannot overflow; consumer owns first handler/outcome | `checkedSub_eq_some_iff`, `checkedSub_eq_none_iff` | `U256Arithmetic.lean`: 0−1 fails, 0−0/max−max/max−0 succeed; dependency differential |
| `ethereum_types/numeric.py:131,44,611` | `checkedMul : U256 → U256 → Option U256` | Succeeds iff unreduced product is below `2^256`, retaining that product | OverflowError becomes `none`; consumer owns first handler/outcome | `checkedMul_eq_some_iff`, `checkedMul_eq_none_iff` | `U256Arithmetic.lean`: max·max and `2^128·2^128` fail; max·1/max·0 and `(2^128−1)(2^128+1)` succeed; dependency differential |
| `ethereum_types/numeric.py:158,44,611` | `checkedDiv : U256 → U256 → Option U256` | Succeeds iff divisor is nonzero, retaining unsigned quotient | ZeroDivisionError becomes `none`; quotient cannot overflow; consumer owns first handler/outcome | `checkedDiv_eq_some_iff`, `checkedDiv_eq_none_iff` | `U256Arithmetic.lean`: max/0 and 0/0 fail; 0/1 and max/1 succeed; dependency differential |
| `ethereum_types/numeric.py:178,44,611` | `checkedMod : U256 → U256 → Option U256` | Succeeds iff divisor is nonzero, retaining unsigned remainder | ZeroDivisionError becomes `none`; remainder cannot overflow; consumer owns first handler/outcome | `checkedMod_eq_some_iff`, `checkedMod_eq_none_iff` | `U256Arithmetic.lean`: max%0 and 0%0 fail; 0%1 and max%1 succeed; dependency differential |

The derived modular algebra is proved as named equalities, without adding arithmetic
instances to `U256`: `add_comm`, `add_assoc`, `add_zero`, `zero_add`, `mul_comm`,
`mul_assoc`, `mul_one`, `one_mul`, `mul_zero`, `zero_mul`, `mul_add`, `add_mul`,
`sub_eq_add_sub_zero`, `add_sub_zero`, `sub_self`, `add_sub_cancel`, `sub_add_cancel`.
Together these provide the addition/multiplication identities, associativity,
commutativity, distributivity and additive inverse (`sub zero a`) required by §7.
`div_mod_decomposition` uses an unbounded product/sum; `div_mod_eq` proves the word-level
reconstruction too. Signed arithmetic and shift laws remain separate.

Regression paths are under `STFSpec/Conformance/Base/`; `U256ArithmeticClient.lean`
contains fixed caller proofs using only public observers and operation laws, imported
by the Conformance root alongside the guards. The separate host driver
`u256_arithmetic_differential.py` takes `--eels <checkout> --output <scratch-file.lean>`
when run by that checkout's frozen venv Python. It verifies the pin/dependency version,
imports the actual seven pinned opcode handlers without modifying them, and invokes
them through a minimal frame adapter supplying stack, PC and a real `GasMeter` with
sufficient gas. The reference's actual pop/push, gas charge and default discarded trace
execute; gas/stack failures and full `Evm` construction are not compared. Checked cases
invoke the actual dependency operators. The fixed seed is 2562: 130 binary cases per
operation, including all pairs of eight boundaries and multiplication boundaries, and
196 ternary cases per modular operation. It generates and executes 1692 scratch guards;
no oracle output is committed and no EEST guest record is executed.

## 4. Tests

- **EEST fixture areas:**
  - `ported_static/vmArithmeticTest` (19), `vmBitwiseLogicOperation` (11), `stShift` (40);
  - `constantinople/eip145_bitwise_shift`, `osaka/eip7939_count_leading_zeros`;
  - `frontier/opcodes`, `ported_static/vmTests`, `stRandom`, `stRandom2`;
  - `cancun/eip7516_blobgasfee` and `cancun/eip4844_blobs` (for `taylor_exponential`).

  All run through the guest; the guest records are all in the `blockchain_tests` format.
- **EELS unit tests** (`tests/json_loader/` at the pin): none target `ethereum_types` or `utils/numeric.py` directly. `test_withdrawal_codec.py::test_decode_oversized_withdrawal_amount` exercises the U64 range check through RLP/SSZ decoding.
- **`core` `#guard` cases.**
  - Words:
    - `div x 0 = 0` and `mod x 0 = 0`;
    - `sdiv (−2^255) (−1) = −2^255`, `smod (−7) 2 = −1`, `sdiv 7 (−2) = −3` (truncation);
    - `addmod (2^256−1) 1 (2^256−1) = 1`, i.e. no wrap before the reduction; `mulmod max max 12`;
    - `exp 2 256 = 0`, `exp 0 0 = 1`, `exp 3 (2^256−1)` (performance);
    - `signextend 31 x = x`, `signextend 32 x = x`, `signextend 0 0x80 = max − 0x7f`;
    - `byte 31 x = x & 0xff`, `byte 32 x = 0`;
    - `shl 255 1 = 2^255`, `shl 256 1 = 0`, `sar 256 (−1) = max`, `sar 256 1 = 0`, `sar 255 (−1) = max`;
    - `clz 0 = 256`, `clz 1 = 255`, `clz max = 0`;
    - `slt (−1) 0 = 1`.
  - Checked arithmetic: `checkedAdd max 1 = none`, `checkedSub 0 1 = none`, `ofNat? 2^256 = none`, `ofInt? 2^255 = none`, `ofInt? (−2^255) = some 2^255`.
  - Bytes: `Uint.toBeBytes 0 = empty`, `U256.ofBeBytes? (33 zero bytes) = none`, `ceil32 0 = 0`, `ceil32 33 = 64`, `leftPadZero` of a 21-byte value to 20 returns it unchanged.
  - `taylorExponential 1 0 1 = 1`, plus the blob base fee values from EIP-4844's table.
  - Adversarial: `exp` with a 256-bit exponent completes in bounded time.
- **Property / differential tests.**
  - Every word op against a `Nat`/`Int` model on random and boundary inputs (0, 1, 2^255±1, 2^256−1), generated by `#eval`-driven tests in `EthConformance`.
  - A differential harness against `ethereum_types` in the scratch venv (bug-finding only; CONTRIBUTING §1).
  - Each constant written as a literal is checked against its EELS hex source.

## 5. Interface

Reference field order, widths and inherited records are catalogued in [REFERENCE-RECORDS](../REFERENCE-RECORDS.md), generated from the exact pin. Wire-schema owners must use those layouts and prove their codec instances. Runtime records may use the explicit abstraction below; omitted fields or `…` remain implementation blockers, not implicit freedom to choose semantics.

All items are public unless marked internal. The namespace is `STFSpec.Base`.

```lean
-- Words (D1(a) initial representation; field internal by convention)
structure U256 where
  private ofBitVecRaw :: val : BitVec 256          -- internal
namespace U256
  def toBitVec : U256 → BitVec 256                  -- stable observer
  def toNat    : U256 → Nat                         -- stable observer
  def toInt    : U256 → Int                         -- two's complement (to_signed)
  def ofBitVec : BitVec 256 → U256
  def ofNat    : Nat → U256                         -- wrapping (mod 2^256)
  def ofNat?   : Nat → Option U256                  -- checked: Python U256(n)
  def ofInt?   : Int → Option U256                  -- checked: from_signed
  def ofBool   : Bool → U256
  def zero one max : U256
  instance : DecidableEq U256; instance : Ord U256  -- unsigned order
  -- EVM operations (total); argument order = EELS pop order
  def add sub mul div sdiv mod smod exp : U256 → U256 → U256
  def addmod mulmod : U256 → U256 → U256 → U256
  def signextend (k x : U256) : U256
  def lt gt slt sgt eq : U256 → U256 → U256         -- 0/1 words
  def iszero not clz : U256 → U256
  def and or xor : U256 → U256 → U256
  def byte (i x : U256) : U256
  def shl shr sar (shift value : U256) : U256
  def ult ule slt' : U256 → U256 → Bool             -- Bool-valued comparisons
  -- Checked (Python-operator) arithmetic
  def checkedAdd checkedSub checkedMul : U256 → U256 → Option U256
  def checkedDiv checkedMod : U256 → U256 → Option U256   -- none on zero divisor
  -- Conversions
  def toBeBytes32 : U256 → Bytes32
  def ofBeBytes32 : Bytes32 → U256
  def ofBeBytes?  : ByteArray → Option U256          -- none iff size > 32
  def toBeBytes   : U256 → ByteArray                 -- minimal; 0 ↦ empty
  def toLeBytes32 : U256 → Bytes32
  def bitLength   : U256 → Nat
end U256

-- Bounded integers: same pattern, structure over BitVec n; checked + wrapping families
structure U64 where private val : UInt64            -- executable (unboxed); and U8/U16/U32 over UInt8/16/32
-- model: Nat < 2^64 via toNat; reference semantics via toBitVec : U64 → BitVec 64 (the abstraction)
-- U64.toNat, ofNat?, ofNat (wrapping), checkedAdd/Sub/Mul, wrappingAdd/Sub/Mul,
-- toBeBytes8, toLeBytes8, ofBeBytes?, ofLeBytes?, toBeBytes (minimal)

-- Unbounded
abbrev Uint := Nat                                   -- public model = Nat itself
def Uint.sub? : Nat → Nat → Option Nat               -- Python OverflowError on underflow
def Uint.toBeBytes : Nat → ByteArray                 -- minimal big-endian; 0 ↦ empty
def Uint.ofBeBytes Uint.ofLeBytes : ByteArray → Nat
def Uint.toBeBytes32? : Nat → Option Bytes32         -- none iff ≥ 2^256

-- Bytes
abbrev Bytes := ByteArray
def Bytes.toList : Bytes → List UInt8               -- stable observer (model)
def Bytes.leftPadZero Bytes.rightPadZero : Bytes → Nat → Bytes
def Bytes.extractPadded : Bytes → (start len : Nat) → Bytes  -- zero-extended read (internal helper for memory/calldata users)

-- Fixed width (D2: BitVec n initially); each a distinct structure
structure FixedBytes (n : Nat) where private val : BitVec (8*n)
structure Address where private val : BitVec 160
structure Hash32  where private val : BitVec 256
abbrev Bytes32 := FixedBytes 32;  abbrev Bytes8 := FixedBytes 8
abbrev Bytes48 := FixedBytes 48;  abbrev Bytes64 := FixedBytes 64
abbrev Bytes96 := FixedBytes 96;  abbrev Bloom := FixedBytes 256
abbrev Root := Hash32;  abbrev VersionedHash := Hash32;  abbrev Hash64 := FixedBytes 64
-- each: toBytes : _ → ByteArray, ofBytes? : ByteArray → Option _, toNat,
--       DecidableEq, a hand-written lawful `compare` (lexicographic = numeric big-endian)
def Hash32.toBytes32 : Hash32 → Bytes32; def Hash32.ofBytes32 : Bytes32 → Hash32
def Address.ofU256Masked : U256 → Address           -- to_address_masked
def Address.toU256 : Address → U256

-- Fork-typed records hosted here (see §3)
structure Authorization where
  chainId : U256; address : Address; nonce : U64; yParity : U8; r : U256; s : U256
structure StateGasPerByte where rate : Nat
def StateGasPerByte.charge (g : StateGasPerByte) (numBytes : Nat) : Nat := g.rate * numBytes

-- Numeric helpers
def ceil32 : Nat → Nat
def taylorExponential (factor numerator denominator : Nat) (h : 0 < denominator) : Nat
def isPrime : Nat → Bool                             -- internal, unreachable
def leBytesToU32s : ByteArray → Array U32            -- internal, unreachable
def leU32sToBytes : Array U32 → ByteArray            -- internal, unreachable
def leU32sToNat   : Array U32 → Nat                  -- internal, unreachable

-- Hex (internal: constants and conformance only)
namespace Hex
  def removePrefix : String → String
  def toBytes? : String → Option ByteArray
  def toBytesN? (n : Nat) : String → Option (FixedBytes n)   -- rjust-padded variants
  def toNat? : String → Option Nat
  def toAddress? toRoot? : String → Option _
end Hex

-- Keccak-derived constants (D5; DECISIONS §3, F2). Values only: EthBase does no hashing.
-- Queried once per block by `EthHash.HashConsts.query` and carried in the block state;
-- consumers take them from there, never from a literal.
structure HashConsts where
  emptyCodeHash  : Hash32   -- keccak256 b""                  (state.py:36)
  emptyTrieRoot  : Hash32   -- keccak256 (rlp b"") = keccak256 0x80 (merkle_patricia_trie.py:71)
  emptyOmmerHash : Hash32   -- keccak256 (rlp []) = keccak256 0xc0  (fork.py:116)
  transferTopic  : Hash32   -- keccak256 b"Transfer(address,address,uint256)" (vm/__init__.py:40, EIP-7708)
def HashConsts.literals : HashConsts   -- the `Id` values, as hex literals:
  -- c5d24601…5d85a470, 56e81f17…e363b421, 1dcc4de8…40d49347, ddf252ad…f523b3ef;
  -- `EthHash` checks `HashConsts.query (m := Id) = HashConsts.literals` (EthHash §7)

-- Orderings for map and set keys (F19); all are `compareOn toNat` (numeric big-endian)
instance : Std.TransOrd Address; instance : Std.TransOrd Hash32; instance : Std.TransOrd (FixedBytes n)
instance : Std.LawfulEqCmp (compare : Address → Address → Ordering)
instance : Ord (Address × Bytes32)          -- lexicographic (lexOrd): slot keys (EthState, EthCommit)
instance : Std.TransOrd (Address × Bytes32)

-- Envelope: hypotheses of named consumer theorems only (DECISIONS B6). Fields are added only
-- when a named consumer theorem needs them; none is fixed yet (see §10).
structure Envelope where
```

## 6. Data structures

| Type | Representation | Model / abstraction | Invariant | Persistence class | Complexity |
|---|---|---|---|---|---|
| `U256` | `structure` over `BitVec 256` (D1(a)) | `BitVec 256`, α = `toBitVec`; also `toNat` (< 2^256) and `toInt` | none beyond the type | immutable value: snapshot-safe | add/sub/logic O(1) words, but `BitVec` is `Nat`-backed (bignum boxed); mul O(1) bignum; `exp` O(log b) mulmods; `addmod`/`mulmod` use a 512-bit `Nat` intermediate. **Costs are measured, not proved** ([REVIEW §7](../REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks) replacement gate R4) |
| `U8`…`U64` | **executable:** `structure` over `UInt8`…`UInt64` (unboxed). *Reference:* `BitVec n` semantics | `Nat < 2^n`; `toNat`, `toBitVec` (executable → reference) | none beyond the width | immutable | O(1), unboxed |
| `Uint` | `Nat` | itself | none | immutable | GMP-backed |
| `Bytes` | `ByteArray` | `List UInt8` via `toList` | none | **linear-only when updated** (in-place only if unshared; ARCHITECTURE §5.0). Read-only payloads (code, calldata, witness nodes) may be shared from snapshots freely | `extract`/`append` O(n); `get` O(1) |
| `FixedBytes n`, `Address`, `Hash32` | `structure` over `BitVec (8n)` (D2) | `Vector UInt8 n` (byte list of length `n`), via `toBytes` | size fixed by type | immutable: snapshot-safe; used as `Std.TreeMap` keys | `compare` O(n); conversion to/from bytes O(n) |
| `Authorization`, `StateGasPerByte`, `HashConsts` | records | themselves | none (`HashConsts`: equals `HashConsts.literals` at `Id`, checked in `EthHash`) | immutable | O(1) |
| `Envelope` | record of `Nat` | itself | none | immutable | — |

**Representation note (D2).** `BitVec` gives cheap equality and numeric `compare`, but `toBytes`/`ofBytes?` cost a byte loop per conversion. `Vector UInt8 n` makes byte access cheap but comparison slower. The chosen representation must keep `compare` equal to the lexicographic order on big-endian bytes (EELS sorts addresses and slots as `bytes`, for example in the BAL). That equality is a law, not a coincidence of representation.

## 7. Contract and laws

**Commuting equations (α = `toBitVec`, or `toNat` where noted).** Each is [R]. Only these, never the definitions, are used downstream.
- `(add a b).toBitVec = a.toBitVec + b.toBitVec`; `sub`, `mul`, `and`, `or`, `xor`, `not` likewise with the `BitVec` operation.
- `(div a b).toNat = if b.toNat = 0 then 0 else a.toNat / b.toNat`; `mod` likewise with `%`.
- `(sdiv a b).toInt = if b.toInt = 0 then 0 else if a.toInt = −2^255 ∧ b.toInt = −1 then −2^255 else Int.tdiv a.toInt b.toInt`.
- `(smod a b).toInt = if b.toInt = 0 then 0 else Int.tmod a.toInt b.toInt`.
- `(addmod a b n).toNat = if n.toNat = 0 then 0 else (a.toNat + b.toNat) % n.toNat`; `mulmod` likewise with `*`.
- `(exp a b).toNat = a.toNat ^ b.toNat % 2^256`.
- `(signextend k x).toBitVec = if k.toNat > 31 then x.toBitVec else (x.toBitVec.setWidth (8*(k.toNat+1))).signExtend 256`.
- `(byte i x).toNat = if i.toNat ≥ 32 then 0 else x.toNat / 2^(8*(31 − i.toNat)) % 256`.
- `(shl s v).toBitVec = if s.toNat ≥ 256 then 0 else v.toBitVec <<< s.toNat`; `shr` with `>>>`.
- `(sar s v).toBitVec = v.toBitVec.sshiftRight s.toNat`. *Inferred:* `BitVec.sshiftRight` saturates to all sign bits for shifts ≥ 256, matching EELS's explicit branch. This must be proved against the EELS case split, not assumed.
- `(clz x).toNat = 256 − x.toNat.log2 − 1` for `x ≠ 0`, and `256` for `x = 0`.
- `(lt a b).toNat = if a.toNat < b.toNat then 1 else 0`; `slt` via `toInt`; `eq`, `iszero`, `gt`, `sgt` likewise.
- Checked: `checkedAdd a b = some c ↔ a.toNat + b.toNat < 2^256 ∧ c.toNat = a.toNat + b.toNat`; likewise for `checkedSub`, `checkedMul`, `ofNat?`, `ofInt?`, `checkedDiv`, `checkedMod`.

**Observer laws** [C]:
- `toBitVec` is injective (`U256.ext`), and `ofBitVec`/`toBitVec` are inverse;
- `toNat_lt : x.toNat < 2^256`;
- `toInt` is in `[−2^255, 2^255)`, and `ofInt? x.toInt = some x`;
- `ofBeBytes32 (toBeBytes32 x) = x`;
- `ofBeBytes? (toBeBytes x) = some x`, and `toBeBytes x` has no leading zero byte (feeds RLP canonicality);
- `Uint.ofBeBytes (Uint.toBeBytes n) = n`.

**Fixed bytes** [C]:
- `ofBytes? b = some x ↔ b.size = n ∧ x.toBytes = b`;
- `compare` is a lawful total order (`Std.TransCmp`, `Std.LawfulEqCmp`), and `compare x y = compare x.toBytes.toList y.toBytes.toList` (lexicographic).
- The pair order on `(Address × Bytes32)` is lexicographic in the component orders and is `Std.TransCmp` (F19); `Std.LawfulEqCmp` holds for `Address` (shown in a compiled prototype of the interfaces, via `Address.toNat_inj`).

**Derived laws** (on the model, proved once): `add`/`mul` form a commutative ring mod 2^256; `sub a b = add a (neg b)`; the `div`/`mod` decomposition `a = b·(div a b) + mod a b` for `b ≠ 0`; shift composition for small shifts; `ceil32 n % 32 = 0 ∧ n ≤ ceil32 n < n + 32`.

**Totality** [T]: `taylorExponential` terminates for a positive denominator by a finite prefix followed by bit-length descent (§7 argument below). Use a lexicographic measure: first the iterations remaining until `i + 1 ≥ max(1, ceil(2·numerator/denominator))`, then the bit length of the accumulated numerator. The latter decreases once the prefix is exhausted. The iterated-floor recurrence must be preserved; the unfloored factorial expression is only an upper bound, not the recurrence or a globally decreasing measure. Formalisation remains open (§10).

**Fast path** [F]: if D1(b) moves to limbs, only this component's definitions and law proofs change. Replacement exercise 4 checks that downstream opcode proofs are unchanged.

### Informal correctness argument

**Claim.** The public observers refine the pinned integer and byte operations, distinguishing EVM wrapping arithmetic from Python checked arithmetic; the numeric helpers terminate on their stated domains.

**Premises.** Widths are positive, checked conversions report overflow, byte order is explicit, and the Taylor denominator is positive. These are local premises; neither gas bounds nor hash assumptions are needed.

**Argument.** Interpret a word as its unsigned natural value. Modular arithmetic commutes with reduction modulo 2^256; a checked operation instead compares the unreduced result with the range and returns the corresponding error. Signed operations use the two's-complement interpretation before dividing or comparing, then reduce the result. Byte conversion is positional evaluation, so induction on the byte sequence proves the endian equations and fixed-width inverse laws. Padded reads split the requested window into its intersection with the input and its zero suffix; this also proves the zero-length case without converting an enormous offset to a host index. For Taylor, the reference recurrence is a_(i+1) = floor(a_i * numerator / (denominator * (i+1))). After i+1 reaches max(1, ceil(2*numerator/denominator)), each nonzero term at least halves. A finite prefix followed by a bit-length descent proves termination. Iterated flooring must be retained; a real-valued exponential is not an interchangeable definition.

**Open obligations.** Complete the enumeration of checked-operation failure sites and their errors, the actual Taylor measure and its practical cost analysis (DISC-002), and the Envelope domain. The recurrence argument proves mathematical termination, not a usable zkVM cycle bound.

See [COMPOSITION](../COMPOSITION.md) for how these premises are supplied and [REVIEW](../REVIEW.md) for implementation gates. This is a conditional informal argument, not a completed Lean proof.

## 8. Composition

- **Depends on:** none (Lean core only).
- **Used by:** directly `EthHash`, `EthField`, `EthState`; transitively every core library.
- **Seams provided.** The word API (observer laws) consumed by `EthVmInstructions`. Checked arithmetic, whose `none` results consumers must map to the enclosing EELS handler: typically block-invalid at `stateless.py:303`, never an EVM halt. Fixed-width key types with a lawful `compare`, consumed by `EthState` maps and the BAL builder. `Envelope` as the hypothesis type of refinement theorems (`EthConformance`, consumers). The `HashConsts` record type, filled by `EthHash.HashConsts.query` and read by `EthState`, `EthCommit`, `EthVmCore` and `EthBlock`.
- **Guarantees.** All operations are total and deterministic. No `@[extern]`/`@[implemented_by]`, and no `@[csimp]` (D21).
- **Relies on.** Nothing, except Lean core `BitVec`/`Nat` lemmas at v4.34.0 (P3).

## 9. Open decisions

- **D1** (U256 representation): this module is the whole of the decision. The initial choice is (a). The laws above are the D1 contract, and exercise 4 tests it.
- **D2** (address/hash representation): `BitVec n` provisional. Affects `compare` cost for `Std.TreeMap` keys and byte-conversion cost at codec boundaries.
- **D21** (accepted, 2026-09-28): no `@[csimp]` and no axiom-adding tactics (`native_decide`, `bv_decide`). A fast path is either a representation replacement proved against this module's contract (D25), or an executable definition with a legible reference beside it and an ordinary equality proof (`CONTRIBUTING.md` §4).
- **D18** (accepted): `U64` should be `UInt64`-backed (unboxed), which is performance-appropriate. A `BitVec`-backed `U64` would need a recorded legibility or proof-friendliness justification in `STFSpec/informal/DEBT.md` (the measurable limitation is boxing).
- **D14** (accepted): checked-arithmetic failures must map to explicit block-level error constructors; reachable unrowed sites are CONTRACT O13 members, each with a named constructor.
- **D5** (provisional, broad scope): the keccak-derived constants are the `HashConsts` record here, not literals used directly (DECISIONS §3, F2).
- Implicit Python exceptions as semantics: resolved by DECISIONS B14 (Q15); the sites were enumerated by the failure ledger (maintained outside this repository); see §10.
- `fork_types.py` placement: resolved, DECISIONS Q16 (done).
- `Envelope` contents: resolved, DECISIONS B6 (Q17).
- **Open: unreachable utilities** (DECISIONS Q18). `is_prime`, `le_*uint32*` and `has_field` are outside the guest call graph (by a static call-graph pass over the pinned EELS); exclude them in `STFSpec/informal/EXCLUDED.md` with that reason. This spec claims them until then.

## 10. Gaps

- **U256 value and unsigned arithmetic slices complete; remaining API unimplemented.** The structure, observers, constructors, constants, unsigned equality/order, add/sub/mul/div/mod/addmod/mulmod and checkedAdd/Sub/Mul/Div/Mod laws are discharged in §3. Signed division/remainder, exponentiation, comparisons/bitwise/shift operations, byte conversions, narrow/unbounded integer helpers and remaining records are unimplemented. `U256Client.lean` and `U256ArithmeticClient.lean` preserve baseline client scripts using only public observers/laws; full R4 alternative-representation and opcode-loop cost evidence remains open.
- **Review gate:** discharge the open obligations in §7’s informal correctness argument and the module’s rows in [REVIEW](../REVIEW.md) before claiming the corresponding refinement. Expand grouped source claims into exact per-operation signatures, ordered failures and effect equations; coverage ownership alone does not supply these.

- **Implicit-exception sites not all closed.** A static pass over the pinned EELS (X1) enumerates the EELS sites where a checked `U256`/`U64`/`Uint` operation or constructor can raise. Reachable, unrowed ones are O13 (CONTRACT §4): witnessed, the legacy-`v` `U64` chain-id overflow (`transactions.py:878`); argued reachable, balance overflow (`state_tracker.py:663,687`), the parent-header `U64` blob-field overflows (`vm/gas.py:931,944,945`) and the BLOBBASEFEE `U256` overflow (`vm/instructions/environment.py:607`). The EthBase-owned helper sites (`utils/numeric.py:61,65,204,208`, `forks/amsterdam/utils/address.py:39,60,63,93`, `utils/byte.py:37,59`) are still unresolved (neither shown reachable nor proved unreachable). Until a consumer's sites are closed, it can accidentally use wrapping or `Nat.sub` and diverge on untested inputs. This is the largest semantic risk in this module.
- **`sar` saturation law and the `signextend` bit-level law.** These are stated but unproved. The Lean core `BitVec` lemma coverage at v4.34.0 has not been checked; missing lemmas would have to be proved locally, since Mathlib is not allowed.
- **`taylor_exponential` termination.** The finite-prefix/halving strategy in §7 is not formalised. The EELS loop has no bound on iterations beyond arithmetic decay, and DISC-002 measured about 2.7·(excess/11684671) iterations, extrapolating to about 4×10¹² for an adversarial parent with `excess ≈ 2^64`. So the proof must also address feasibility, not only termination (DISC-002).
- **`exp` performance.** Square-and-multiply mod 2^256 over `BitVec` is not benchmarked. A naive `BitVec` power would be catastrophic.
- **D1/D2 benchmarks missing.** `BitVec`-backed `U256` costs (boxing, GMP) are unmeasured in an opcode loop ([REVIEW §7](../REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks) replacement gate R4); `U64` is `UInt64`-backed and needs no such benchmark.
- **Lexicographic `compare` = EELS `bytes` order.** This is stated but not yet tied to the specific EELS sort sites (BAL, storage keys). The consumers should cite this law.
- **`Envelope` has no fields yet.** By DECISIONS B6 each field must name the consumer theorem that needs it; none has been named.
- **Hex quirks.** Python `fromhex`/`int(…,16)` leniency is deliberately not reproduced. This is justified only because all in-scope uses are constants. If a future path parses hex from input, this becomes a semantic gap.
- **EEST coverage is thin for checked-arithmetic failures.** The fixture areas exercise EVM wrapping arithmetic well. They do not exercise, for example, `U256` overflow in fee computation or `Uint` underflow, which cannot be reached in valid blocks. Some are reachable from guest input (argued from the pinned source; see the implicit-exception bullet above), so they need probe or constructed tests rather than EEST coverage.
- **`to_signed` width rule.** The rule (`8·⌈bits/8⌉`, `numeric.py:679–680`) is irrelevant for the standard widths. I infer that no non-byte-aligned `FixedUnsigned` is used; this is not verified by a grep.
- **Differential coverage beyond the implemented slices.** The §3 drivers compare the value slice with pinned `ethereum-types`, unsigned EVM arithmetic with actual pinned handlers through a minimal frame adapter, and checked unsigned arithmetic with dependency operators. Signed arithmetic, exponentiation, comparisons/bitwise/shifts and byte conversion differential coverage remains unimplemented; the guest conformance runner remains absent.
