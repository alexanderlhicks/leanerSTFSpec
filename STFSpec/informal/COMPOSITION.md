# Conditional correctness of the complete guest

*Status: conditional proof plan. Date: 2026-10-30.*

Reviewed against `tests-zkevm@v21.0.0`, commit `e1a316a06fc3d3e0a5da36fdc78580811e9d8a36`, on 2026-09-28. This is the shared contract for the spec guidance documents. It states a proof plan and its unproved premises; it does **not** certify that the current draft, or a future implementation merely following it, is already complete or sound. [REVIEW](REVIEW.md) records the remaining gates.

## 1. Three distinct correctness statements

1. **Reference fidelity:** the guest produces the same bytes as the pinned Python guest on an agreed domain and reference environment, including validation failures. Host resource/capability differences require the unresolved D14/O12 policy; they cannot be silently classified as irrelevant.
2. **Semantic soundness:** a successful stateless execution agrees with a well-formed, code-authentic full state having the supplied parent root, or supplies a hash collision. This is conditional on data availability, the precise oracle model, and the relevant component refinements.
3. **Accepted-chain security:** that full state and its header context belong to the verifier's accepted chain. Chain ID, activation, parent anchoring and zkVM/compiled-guest correctness are external obligations. A guest success alone does not establish them.

Termination, reference fidelity and hash-based soundness are separate. Mathematical termination must hold without assuming collision resistance. Fixtures provide evidence for fidelity, not universal proofs of these statements.

## 2. Type ownership and adapters

The checked registry is [contracts.toml](contracts.toml). A consumer imports the owner's declaration through an allowed dependency; it must not redeclare a lookalike. Source ownership and type ownership differ: EthBlock claims Python `Log`, while EthVmCore owns Lean `Log` under D27 (accepted 2026-09-28). The interfaces below are Lean-like contracts. A compiled prototype of these interfaces covered one complete path through them, and its dispositions are in `STFSpec/informal/DECISIONS.md` §3.

| Contract | Owner | Required consumer behaviour |
|---|---|---|
| HashConsts | EthBase | Acquisition/threading follows F20; existing state/backend contexts retain the same record. |
| Nibbles | EthCommit | Consumers use public bounded digits, List abstraction, pure path laws and Q49 generation/clipped copies/lawful lexical map order; slices copy O(k). |
| Enc, Node, Ref | EthCommit | Preserve complete fields and recursive Array/Option children (EthCommit §3); semantic adoption remains conditional on B3/NEW-COMMIT-1/DISC-003, with remaining gates owned by EthCommit §10. |
| IncrementalMPT | EthCommit | Retain the complete supplied Bool and Ref; the Q55 decoder and local rootHash/mptRoot actions are supplied separately (EthCommit §3/§5/§7.0.9). Mutation, whole root/cache refinement and representation/admission obligations remain owned by §10 (B3). |
| InternalNode | EthCommit | Supply already interpreted byte/list fields and sixteen ordered children; use public assembly/model/query laws. |
| Trie, TrieValue, KeyBytes | EthCommit | Q53 supplies generic storage/safety, the byte-key contract, pure unsecured preparation and typed root composition; remaining concrete consumer contracts require lawful arbitrary-default equality, stored-value `PrepareSafe` distinct from `NoDefault`, injective byte keys with byte-lex order and caller-supplied coherent F20 empty root; initial preparation/root calls prove unsecured. |
| TrieError, Malformed | EthCommit | Keep Q52 path-list/leaf-value-list diagnostics in C14 order, raw compactEmpty distinct from later pathEmpty. Q59 supplies a bare selected-slot diagnostic and pure lookup equations; Q60 supplies collapseIndex, local reached mkBranch diagnostics and update/delete emission (EthCommit §3); frontend emission remains future; witness/guest adapters and reachable outcome projection remain separate, owned by CONTRACT O4/O13. |
| NodeDB, `NodeDB.Authentic` | EthCommit | Share the constructed raw table read-only. Concrete root-binding/agreement consumers require `Authentic keccak256`; Q55 decoder admission accepts arbitrary tables and caches actual occurrence answers. A generic oracle table alone supplies no concrete authenticity; equality of a decoded cache to a reference also needs eligible raw length. |
| Account, MathState, `PreState m`, BlockDiff | EthState | EthState §3/§7 owns supplied Account, raw MathState, raw BlockDiff, raw mathematical apply, raw PreState carrier and supplied-record ModelsLookups contracts. The carrier retains complete supplied functions without a Monad premise; equality adds no action-effect interpretation. Coarse WitnessItem/WitnessError and nominal StateError values retain supplied tags/payloads through construction/elimination; they add no diagnostic or outcome adapter. StateError operations and freezing remain open (EthState §5/R29/§10). Actual providers and context coherence, progress, code/root agreement and error refinement remain open. Raw diff callers preserve whole optional payloads and every metadata occurrence. Apply uses all four effect fields and ignores order metadata; it preserves untouched raw entries and requires no WF. Concrete source correspondence requires typed finite nonaliasing account/storage dictionaries with defaults None/zero and coherent F20 constants for code observations. Diff WF, reachable preservation, first-write history and F7 replay policy remain separate obligations. Callers use observers and ordered writes; they never inspect backend trie representation. |
| Models, CodeAuthentic, CodeChangesAuthentic | EthStateCommit | Structural WF, answer/root agreement and code authenticity are separate premises. Progress/availability is additional. |
| Stack | EthVmCore | Use the seven public bounded-stack APIs and ten ordinary laws owned by EthVmCore §3/§7; the Stack exchange row below covers `swap?`. Models are complete top-first word lists; storage/constructor/injectivity stay private. Arbitrary-error iff laws imply nonfull push/nonempty pop availability; success iff laws support both inverses with actual Stack equality. Indexed reads accept all Nat depths. Only typed Python lists of size≤1024 correspond; handler failure order, actual frame ownership and compiled allocation remain separate. |
| `decodeSingle`, `decodePair` | EthVmCore | Use the existing UInt8-to-Except APIs and eight discharged ordinary equations/error/bounds/injectivity laws owned by EthVmCore §3/§7. Preserve complete ordered pair payloads and the existing nullary invalidParameter. Valid-domain progress and alternative-error exclusion follow from those equations. Handler ordering, gas/PC effects, Stack operations, compiled costs and guest gates remain separate. |
| JumpdestMap | EthVmCore | Use the abstract immutable map, existing factory/contains operations and three supplied ordinary equations owned by EthVmCore §3/§5/§7. Empty/out-of-code absence, PUSH exclusion/resumption and true-hit byte identity are public-law consequences. Supply the intended complete code and establish actual frame code/map agreement; cache provenance, JUMP/JUMPI gas/error ordering and compiled costs/ownership remain separate. |
| `bufferRead` | EthVmCore | Use the existing Base Bytes/U256 types and the three supplied ordinary bridge/List/size laws owned by EthVmCore §3/§7; no Memory/gas/host-cap premise. Source correspondence retains typed-dependency/representable-width/allocation premises. |
| Memory | EthVmCore | DECISIONS Q62 owns the disposition; EthVmCore §5/§7 owns the supplied API and laws, with implementation status in §10. The local-premise handoff below records caller alignment/window and ordering duties; Q63 owns the separate memory-pricing policy contract. |
| GasCosts | EthVmCore | Use the exact raw 144-field constructor/projections and two ordinary ext/eta laws owned by EthVmCore §3/§5/§7. Raw aliases are independent; refund is signed, blob fields use existing Base.U64 and BLS arrays admit arbitrary lengths. Equal selected opcodeAdd cost and the same meter give equal complete chargeGas results. EthFork values/coherence, broader B8 classification, StateGasCosts, supported consumer domains and Memory pricing remain separate. |
| BlockGasCounters | EthVmCore | Use the raw constructor/projections and two ordinary ext/eta laws owned by EthVmCore §3/§7; retain complete independent execution, state and blob fields. Full BlockOutput belongs to EthBlock; actual block coherence, capacity arithmetic and checked failure precedence remain separate obligations. |
| StateGasCosts, VmLimits, VmConfig | EthVmCore | Use the exact raw data constructors/projections and six ordinary ext/eta laws owned by EthVmCore §3/§5/§7. StateGasCosts retains four Nat inputs; VmLimits retains three Nat fields; VmConfig retains the complete costs/stateCosts/limits records. Equal selected opcodeAdd prices and the same meter give equal complete chargeGas results even when unused stateCosts/limits differ. EthFork values, state amount observations/coherence, limit specialization and actual frame/target consistency remain separate; Q63 pricing is supplied separately through its ten ordinary laws; actual caller/coherence/resource obligations remain open. |
| MessageCallGas, `calculateMessageCallGas`, `initCodeCost` | EthVmCore | Q64 and EthVmCore §5/§7 own the supplied VmConfig-first signatures/default and six discharged ordinary laws. Retain the complete cost/subCall result; local transport needs only selected effective-stipend or init-price equality. Private public-law clients derive complete actual charge/error, affordability, rounding and explicitly financed local potential consequences. Bounded typed comparisons and their current/captured-default/host premises are owned by Core §3. Actual cfg/frame/target coherence, general source/default agreement, earlier CALL payments/state spill, child return and settlement remain caller-owned; no global WF or whole G2 result is supplied. |
| Stack exchange | EthVmCore | Q82 and EthVmCore §3/§5/§7 own the supplied all-Nat Option operation and exact two ordinary laws. Public-only private clients derive actual identity/commutation/involution and complete cell/size effects. SWAP1–16 uses (0,k), SWAPN (0,n), EXCHANGE (n,m); source gas/decode/bounds/mutation/PC order remains with handlers. Capacity and private Array preservation supply no frame ownership, compiled allocation or C1–C4 result. |
| GasMeter, ExceptionalHalt | EthVmCore | The supplied charge kernel (ten all-raw-meter laws) and commit/two rollback boundaries (eight laws on their local proof domains), plus refund/repay (seven all-raw-meter laws) and four local transfer operations (eight laws, forfeit only on pending-spill-zero) and signed refund addition/scalar maximum (four unconditional laws), plus transaction state-gas usage (one signed equation on its local baseline-to-grant proof), are owned by EthVmCore §3/§7. Consumers retain the complete six fields and use the public equations; no global WF, refund-sign or schedule premise is needed for the charges, refund/repay or ordinary restore; commit/entry restore/forfeit carry only their source assertion proofs. Nominal halt vocabulary supplies no producer/settlement implementation. |
| EvmGasAllocation, `allocateEvmGas` | EthVmCore | Q65 and EthVmCore §3/§5/§7 own the supplied VmConfig-first API, two local subtraction proofs, raw two-field result and four discharged ordinary laws. Nine private public-law client groups and finite complete controls are supplied; actual caller bridges remain open. Preserve floor/admission ordering; establish relevant admission/allocation cap consistency or the allocation cap proof independently. System transactions supply separate grants and bypass this helper. |
| TransactionGasSettlement, `settleTransactionGas` | EthVmCore | Q66 and EthVmCore §5/§7 own the supplied U256-refund API, three local gas proofs, raw complete four-field result and five discharged ordinary laws. Private public-law clients and complete finite controls are supplied in Core §3; actual callers remain open. Retain the signed-state clamp and pre-refund block dimensions, all source subtraction domains and the original checked refund-conversion boundary described below. |
| AddrSet, SlotSet, Frame | EthVmCore | Use the exact two Std.ExtTreeSet aliases and raw nine-field constructor/projections owned by EthVmCore §3/§5/§7. Base owns nominal Address and lexical address/slot ordering; Std owns set membership laws. Preserve all independent fields, complete provider values and supplied raw log shape. Raw construction/reconstruction/updates reduce without added admission or public helper laws. Actual creation, immutable context, source-Evm assembly, control/parent integration, F8 transport/emitter and all execution/resource/readiness claims remain open. |
| FrameCtx, `emitTransferLog` | EthVmCore | F8 supplies immutable systemAddress from RunnerEnv and an explicit helper address argument after Frame; child contexts inherit it. Local zero/complete nonzero log laws quantify arbitrary address/topic; source refinement instantiates the pinned Fork address and F20 topic. Context/emitter code remains open. |
| RunnerEnv | EthVmRunner | BlockConfig.runnerEnv forwards cfg.system.systemAddress beside the existing table and three-field VmConfig; createEvm copies it into FrameCtx. Intended construction/refinement establishes coherence, without a global raw-context admission predicate. Transport code remains open. |
| VmWorld, Log, LogRope | EthVmCore | VmWorld contains one TxState. TxObs and the ancestor cursor have one authoritative location. LogRope flattening defines visible order. |
| PrecompileResult, `PrecompileFn m`, `PrecompileTable m` | EthVmCore | EthPrecompiles creates implementations; EthFork installs pricing closures; EthVmRunner uses the same types and returned meter. |
| KZG raw versioned hash | EthPrecompiles | EthPrecompiles §3/§5/§7 supplies the canonical fixed global tag, raw ByteArray → Base.VersionedHash helper and complete ordinary byte-result law. PointEvaluation must reuse that owner; its proof/gas/table/frame implementation remains open. Q46/source-class/host domains remain explicit. |
| StepResult and requests/resume | EthVmInstructions | Handlers suspend, runner executes a child, resume observes a settled child. No handler imports the runner. |
| BudgetPolicy, `phiBudget`, `constBudget` | EthVmRunner | Supplied selectable mathematical vocabulary over the existing complete Core meter, owned by EthVmRunner §3/§5/§7. All raw fields and every Nat constant including zero are admitted. No installed default, runner integration or B11/G2–G7 guarantee is supplied. |
| ExecKind | EthVmRunner | Supplied nominal three-constructor entry carrier, owned by EthVmRunner §3/§5/§7 and exported by its facade. Private Conformance clients check exhaustive elimination and all ordered constructor inequalities. The `Exec` relation, its exact form and execution guarantees remain open. |
| InternalError, CheckedResult, `CheckedT` | EthVmRunner | Every caller propagates the internal channel without treating it as a validation error. |
| BlockConfig, BlockOutput, transaction/header records and errors | EthBlock | EthFork supplies values; EthStateless supplies payload/header adapters. BlockOutput is not defined in VmCore. |
| StatelessInput and StatelessValidationResult | EthStateless | The bounded output record/serializer/sentinel and ordinary complete layout, size and injectivity laws are supplied under EthStateless §3/§7; its §10 owns remaining input/guest/host-inverse obligations. EthConformance uses the same schemas; expected bytes are independent of a containing fixture's block-validity label. |

### Supplied local SSZ count-recovery handoff (Q87)

[EthCodec §5/§7](modules/EthCodec.md#7-contract-and-laws) owns the actual-value
predicate and complete ordinary constructor iff. Consumers compose immediate list
width and every actual-member obligation, or exact container arity and every ordered
paired-field obligation. Empty variable-child outer lists inspect no unused nested
values; direct zero-byte fixed products remain eligible. Leaves, limits and masks
add no support or typing certification. Q80 forward support remains independent.
The future raw inverse needs both actual Serializable and CountRecoverable proofs;
its theorem and decoder are unimplemented. Canonical successes still owe WT and
existential Serializable/reencoding, without a CountRecoverable conclusion. Actual
schema adapters, source invocation/large-scope/host premises, Rootable and guest O2
bridges remain separate; no readiness gate closes.

### Supplied generic SSZ schema forward handoff (Q81)

[EthCodec §5/§7](modules/EthCodec.md#5-interface) owns the five-field metadata
carrier and two direct forward wrappers with complete ordinary raw-call equations.
Consumers retain the actual dictionary `s`, actual `s.toValue a` and only the
requested operation's Serializable or Rootable proof. The forward equations need
no validity, descriptor WF, inverse or opposite-operation support premise.

Every actual instance owner still separately proves all three external §7
certifications: descriptor WF and both adapter directions. These are required
obligations, not generic class laws; no actual instances are supplied. Consumers
needing certification cite those actual proofs or state their hypotheses. Neither
metadata nor the three certifications alone establishes raw operation support.
Actual source schema/name/order/coercion/reflection correspondence and successful
decode→dataclass→fresh-view support stay with the concrete owner. No decoder guard
or execution-validity premise follows; O2 freedom and guest/resource/security/cost
and readiness claims remain separate. The existing private output consumer stays
unchanged.

### Supplied local SSZ root support (Q78)

EthCodec §5/§7 supplies `Ssz.Rootable` and its sole complete ordinary constructor
law. Consumers use actual child membership, exact equal-length/zip alignment,
declared sizes/limits, basic uint widths and the strict nested actual count
bounds in the appropriate units. Bool lists use one byte per basic Bool; fixed
vectors are composite elements. No typed packer is exported; Q79 supplies the raw
root result separately. Fixed vectors and containers acquire no count-mix-in bound.

Empty lists of unused malformed composite schemas can be Rootable without WF;
empty direct uint lists still inspect basic width. Private facade clients derive
Rootable→WT through public laws, independently by value and descriptor induction.
They explicitly refute a global Rootable→WF claim. Source construction visits
unused schemas, so class/name/reflection/order/coercion and the capacity-256
`more` premise remain local, along with backing/cache/hash/global/alias/host
coherence. Q79 supplies sparse false activity slots as depth 0 zero chunks in raw
contents, without adding a slot-builder API.

Actual decoded view→dataclass→fresh-view support remains separate from Q79’s
raw root-result law. Preserve every source-accepted byte input while investigating
the bridge; request rooting precedes semantic execution checks, including empty
transactions or headers and execution-invalid requests. No new decoder guard,
provider or schema field follows from this predicate alone. Source failure/resource
order, O2/O12/O13, security/binding, C1–C4 and readiness remain open with their owners.

### Supplied computational SSZ root handoff (Q79)

[EthCodec §5/§7](modules/EthCodec.md#7-contract-and-laws) owns the exact C-indexed
`Ssz.hashTreeRoot` and its sole complete ordinary constructor-result equation.
Callers retain named t/v/h and use the entire public equation. Its inline basic
bytes, ordered proof-independent child graph, capacities and sparse ranks are
stable mathematics; private workers are not consumer seams. Rootable's public
law supplies the actual child support/arity/count/classification premises. Local
projections, ordered certificates and physical bounds exist under C, and
actual-value induction determines all recursive results. An empty actual
composite list visits no unused malformed schema. Fixed vectors/containers gain
no count-mix bound; Bool lists use bytes and byte vectors remain composite list
elements. Progressive contents contain exactly the finite activity positions,
with depth 0 zero chunks at false bits and a separate full mask mix.

These raw roots are computed before inner semantic validation in the source.
Actual schema names/field order/classes/reflection/coercions, construction of
unused schemas and capacity 256 `more`, source backing/cache/hash/global/alias/
endian/host coherence and executed-path zero-table availability remain local.
The actual decoded view→dataclass→fresh-view bridge must preserve every tag,
ordered child, declared size and nested count. No decoder guard or execution/
nonempty-header/transaction premise is added. Finite original comparisons,
mathematical-only extensions and excluded no-result cases stay distinguished.
O2/O12/O13, request binding/external anchors, source resource/failure order,
C1–C4 and readiness are unchanged and remain separate obligations.

### Supplied SSZ zero-hash handoff (Q73)

[EthCodec §5/§7](modules/EthCodec.md#5-interface) owns the two supplied values and
two complete ordinary laws; §3/§4 owns the twelve private mathematical and six
independent facade client groups. Consumers derive branches, complete zero bytes,
ordered prefix/lookup/width and every successor's FIPS digest trace from those
laws and public Base/Hash contracts. Each SHA input has exactly 64 bytes, so the
local standard-domain premise is discharged without a depth premise.
The prefix includes 64 and excludes 65, while the recurrence remains defined at
65, 255, 256 and every Nat. Original source correspondence retains initialized
globals/aliases/hash behavior, nonnegative actual table indices below 256,
constructors/cache history and successful host execution. Mathematical root 256
claims no source table success. Source-only groups 0–3 remain UNRUN; no
source-runtime profile, merkleization, root admission, failure/outcome, compiled
sharing/resource, C1–C4 or guest/readiness obligation follows from the zero-hash
laws.

### Supplied progressive SSZ contents-tree handoff (Q75)

[EthCodec §5/§7](modules/EthCodec.md#7-contract-and-laws) supplies the optional-depth
`Ssz.merkleizeProgressive` and its complete ordinary public recurrence. Empty at
any Nat depth is the zero chunk. Each nonempty level uses a prefix of capacity 2^depth
and recurses on the suffix at depth + 2; local slicing discharges the ordinary
provider's physical capacity, so no caller premise is added. Starting at 0 takes
capacities 1/4/16/64. Ordinary calls may omit depth; first-class clients needing
Array→Bytes32 fix depth 0 explicitly, while `@Ssz.merkleizeProgressive` has the
underlying Array→Nat→Bytes32 type. Full ordered facade clients derive arbitrary-depth
recurrence/reference/finite-fold/reconstruction and local 64-byte FIPS consequences.
The contents tree alone does not bind counts. Q76 supplies the local length mix-in;
Q77 supplies the activity mix-in; source
node/backing/hash/global/cache/table-path/host correspondence, schema admission and
actual decoder/adapter-to-Rootable support remain consumer premises/open obligations.
No O2/O12/O13, error policy, resource, guest or readiness gate follows.

### Supplied SSZ length mix-in handoff (Q76)

[EthCodec §5/§7](modules/EthCodec.md#7-contract-and-laws) supplies exactly
`Ssz.mixInLength root len h` and its complete ordinary SHA equation. Natural List
lengths and Bytes sizes pass directly, with precisely their own `len < 2^256`
proof, including every nested consumer. No WF, WT or Rootable premise substitutes
for that local fact. Public Base byte laws expose all 32 count digits; the exact
64-byte message gives the FIPS bound 512 < 2^64 independently of count range.
Private facade clients derive full digest/byte consequences, equality/proof
transport and intended-count U256 observations using existing public laws.
`U256.ofNat` preserves a natural count only when its range is proved; it is not
an unrestricted admission bridge. Boundary/outside counts have no API argument,
not a chosen runtime rejection. Actual decoded count bounds, schema/adapters,
source order/class/backing/alias/cache/host agreement and root
binding and guest/O2/O12/O13/resource/readiness gates remain open with consumers.

### Supplied active-field mix-in handoff (Q77)

[EthCodec §5/§7](modules/EthCodec.md#5-interface) supplies the local-width helper
and sole complete ordinary equation. A caller supplies exactly `active.length ≤ 256`;
private arithmetic derives the numeric 256-bit fit. Public Base laws expand all 32
low-first mask digits after every supplied root byte; the fixed 64-byte message
supplies 512 < 2^64 for the full public Hash FIPS digest relation. Private facade
clients use all named root/active/h arguments and complete public laws.
Source correspondence additionally requires the actual source class, names,
nonempty/finaltrue/population/width admission, including `more` membership at
capacity, and ordered sparse activity positions. The supplied root must already
commit to the contents tree with inactive zero nodes. Mathematical mask packing
does not establish those premises or raw-list injectivity: trailingfalse padding
preserves the preimage. Actual guest masks are all true, with 19 and 5 entries respectively, without a
user-supplied-mask decoder contract. Source eager construction versus lazy/cache
hashing and backing/root/hash/global/alias/host coherence stay local. Q78 supplies
the local Rootable law. Actual decoder/adapter-to-Rootable support, enclosing
roots/binding, guest/O2/O12/O13 and resource/cost/readiness gates remain separate;
Q70/Q71 stay unchanged.

### Supplied raw SSZ pack handoff (Q72)

[EthCodec §5/§7](modules/EthCodec.md#5-interface) owns the supplied component helper
and its single complete ordered byte-observation law; §3/§4 owns source premises
and the six private property/client groups plus 15 whole-byte controls. Consumers
use that law and public Base byte/fixed-byte contracts. Flattened output recovers
the complete input prefix, but equal chunk arrays imply input equality only with
equal input lengths. If the first input is 32-byte aligned, concatenation preserves chunk
append. There is no root or length-binding seam.
Actual typed packing, schema/codec/root and adapter inverses, class/count/backing/
offset/cache premises, source-host/differential obligations and compiled costs
remain with their consumers; no guest/error/resource gate follows from raw chunks.

### Transaction-gas caller handoff (Q65, Q66)

[EthVmCore §5/§7](modules/EthVmCore.md#5-interface) owns the exact supplied
allocation API/four laws and supplied settlement API/five discharged laws; §3 owns
local allocation/settlement evidence and source correspondence, and §10 the
remaining actual caller obligations. Allocation reads only the
relevant execution cap. Equal relevant caps transport its local proof/result;
whole-config equality is unnecessary locally, while actual frame/target policy
coherence remains separate. Keep ordinary validation's floor checks and ordering,
and match the allocation cap to the admitted cap or establish its bound afresh.
A larger admission cap alone does not justify a smaller allocation cap. Do not
impose an ordinary allocation identity on the independent system grants.

Private local clients derive the positive-part state bound from explicit entry
partition, returned/baseline and final-potential hypotheses. Composing the public
allocation equation additionally gives settlement execution ≤ the same cap when
the caller supplies both floor bounds. These local premises are not a reachable
Runner invariant. Settlement callers establish all three local gas bounds, retain complete result
fields and supply a validated existing Base.U256 refund. Runner's prospective
`TransactionOutput.refundCounter : Nat` (EthVmRunner §5) remains unchanged.
For an actual successful output n, retain `n < 2^256` and reconstruct the exact
word using existing `U256.ofNat?_eq_some_iff`, `U256.ofNat?_toNat` and
`U256.toNat_lt`. A raw Nat observation does not itself prove that range; the
validated bridge and actual caller bounds remain unimplemented, with no public
adapter or new reachable rejection.

The private ordinary preparation-failure client in EthVmCore §3/§7 composes the
existing public laws with exactly the two allocation proofs, admitted F≤T and
partial-meter baseline≤R0/refund=0. Restore/post supplies pending-spill-zero;
forfeit then gives the complete final meter `(0,R0,R0,0,0,0)`, also from the
constructed entry meter. Allocation derives R0≤T; state usage and refund are zero,
with both unsigned bounds and existing U256 checked reconstruction. These facts
derive the remaining settlement proofs locally, giving complete result
`(max(T-R0,F), T-max(T-R0,F), max(T-R0,F), 0)` on both routes. Its six complete
numerical specializations assert no source reachability. Actual admission/cap/floor
transport, preparation assertion derivation, normal/child accounting and refund
bounds, system behavior, fees/providers/counters and G1/G2 remain open. There is
no new public API or actual Runner/cast implementation.

Signed meter refund conversion needs both unsigned bounds at its source phase.
Preparation restore/forfeit precedes cast `vm/interpreter.py:285`, before the
state-usage argument :291–293; normal TransactionEnd tracing :309–314 precedes
cast :318, before state usage :324–326. Preserve both points and the existing
proof/fault obligations rather than postponing conversion to block settlement
(`fork.py:1101–1110`). Base.ofInt? is the signed from_signed factory; unchecked
negative Int.toNat or wrapping ofNat also cannot replace unsigned construction.
Int.toNat on state usage has the distinct intended clamp semantics. The helper
proves no actual runner range, source-fault reachability, fee/provider effect,
transaction conservation, progress, resource or guest/readiness result.

### Supplied immutable buffer read

[EthVmCore §3/§7](modules/EthVmCore.md#3-eels-source-map) owns the supplied
`bufferRead` API, ordinary laws and conditional source correspondence. Consumers use
existing Base Bytes/U256 and the bridge/List/size laws. Public clients obtain empty
Bytes equality, unavailable/contained models and right-padding extension through
the existing Base law with its explicit window premise. No representation helper
or additional public law is exposed. Remaining resource/ordering/Memory obligations
are owned by EthVmCore §10 and REVIEW.

### Supplied Memory local-premise handoff (Q62)

[EthVmCore §5/§7](modules/EthVmCore.md#5-interface) owns the supplied exact API and ten
discharged ordinary laws. The implementation uses actual existing Base Bytes and
private packed aligned Memory storage; public clients unfold neither provider.
Initialize new frames with `Memory.empty`. For each expansion, establish
only `n % 32 = 0`; the operation appends exactly n zero bytes. For reads supply
`k = 0 ∨ s + k ≤ m.size`, and for writes supply
`v.size = 0 ∨ s + v.size ≤ m.size`. These local erased proofs do not require a
global frame invariant or a GasMeter premise. Size counts bytes, and alignment is
structural. No raw constructor or arbitrary-byte ingress is available to callers.

After a write, derive the read-window witness by rewriting the result size using
`Memory.size_write` and reusing the original write/read window proof. The
read-after-write and disjoint-read laws therefore introduce no additional semantic
premise or exported witness helper. Empty windows remain admitted at every Nat
offset; disjointness explicitly permits either window to be empty. Immutable read
values support later overlapping read-then-write copy clients without a new API.

The supplied Q63 pricing laws produce aligned increments and coverage; public-only
clients derive actual Memory expansion size and admitted windows/preservation. Actual
handlers must still connect their operands and write payload lengths to those windows. Preserve source charge-before-allocation,
return-buffer checks and static-check ordering. Source agreement covers only
intended aligned/admitted typed inputs and successful host premises; raw reads clip
and writes can grow outside that domain, without adding a guest rejection.
Remaining implementation, ownership, cost and readiness obligations are owned by
[EthVmCore §10](modules/EthVmCore.md#10-gaps) and REVIEW. Q63 owns the separate
memory-pricing policy contract; its local helpers and proofs are supplied under
EthVmCore §3/§5/§7.

Q63's supplied pricing helpers receive the caller's VmConfig. Compute ext without changing memory or charging gas; its discharged alignment law supplies the existing expansion proof, and its coverage law with the supplied Memory size/expand laws derives each listed empty-or-in-bounds window. Private public-only clients also derive complete same-size/permutation/duplicate/subsumed result invariance, seed-aware composition through actual Memory.expand, and admitted-read preservation. A write still requires the actual payload-size equality. Preserve actual source charge-before-allocation, return-buffer/static/init-code checks and CALL-family ordering. Local relevant-price congruence suffices for the arithmetic component when the target satisfies the same arithmetic/input interpretation; passing a config alone proves neither that fact nor coherence with the executing frame/other operations. No evm-asm or stateless-pancaketh runtime config shape is assumed or inspected. Actual caller/coherence, source-host, allocation/resource, L-MEM-BOUND and whole VM/guest obligations retain their owners.

### Supplied jump-destination handoff

[EthVmCore §3/§5/§7](modules/EthVmCore.md#3-eels-source-map) owns the supplied
abstract immutable map, two existing operations and three ordinary all-code/all-Nat
lookup equations. Call `validJumpDestinations` on the intended complete code and
use `contains` through those public equations. Private public-law consumers derive
head behavior, PUSH data exclusion/resumption/truncation, non-PUSH advancement,
true-hit bounds/byte identity and arbitrary out-of-code absence. Consumers neither
construct maps nor inspect bitmap storage. Semantic immutable sharing is distinct
from compiled allocation/sharing/ownership.

A frame must separately establish that its map belongs to its actual code. Future
code-hash caches require authenticity/coherence, and JUMP/JUMPI handlers must
establish their operand/gas/error order. Complete finite source/target controls
retain typed-dependency and successful host premises; they prove neither these
caller facts nor compiled costs, C1–C4 or whole VM/guest readiness.

### Internal first-write order premise

[EthState §3/§7.5](modules/EthState.md#3-eels-source-map) supplies the raw
persistent `WriteOrder` support; its component laws are owned by EthState §7.5. WF is
exact inverse/bound consistency; Agrees separately equates optional forward
presence with an arbitrary associated write map, including tombstones and zero.
Lawful key equality and both predicates enable later coupled ordered folds.
Full clear/restore/incorporation/extraction, caller reachability and account-read
history remain open, together with S1/S2 and composed C1/C4. Paired-root finite
tests do not establish the whole State invariant or select F7 clear traversal.

### Raw mathematical-state premise

[EthState §3/§7](modules/EthState.md#3-eels-source-map) supplies the Account value
provider and raw three-map MathState with total `account?`, `storageAt` and
`code? σ consts h`. Missing address/slot storage defaults to zero; optional account
absence differs from a present empty account. The caller's empty-code hash bypasses
raw code lookup; missing nonreserved model code remains `none`. Provider missing-code
errors (B2) remain unchanged. Source correspondence requires coherent F20 constants;
the model itself accepts arbitrary records and raw maps.

The [raw and structural laws](modules/EthState.md#raw-mathematical-state-observer-laws)
retain raw field/lookup extensionality and exactly three `WF` clauses: nonzero slots, nonempty inner maps and storage-domain
inclusion in accounts. Raw lookup extensionality keeps whole optional inner maps
and all raw code hashes. Fixed-constants observer equality cannot determine raw
code, even under `WF`; code authenticity/completeness are separate premises.
`wf_empty` proves only the empty raw triple's structural invariant. Raw mathematical
application is supplied by EthState §3/§7; mutation, providers, reachability,
diff/order/overlay preservation, S1/S2, commitments
and consumer/resource gates remain open. Complete finite native/reference-list
observations and retained sibling checks establish no composed cost bound.

### Supplied lookup context and bounded structural preservation (Q57–Q58)

[EthState R8/§3/§5](modules/EthState.md#3-eels-source-map) supplies
`ModelsLookups consts ps σ₀` as success-only agreement. Each tracker proof uses the fixed initial
BlockState record/provider carried by the participating contexts. Full binary
Models supplies lookup agreement at EthStateCommit's concrete `constsId`; using
it at the execution record requires F20 coherence. Arbitrary supplied-record lookup
agreement supplies no authentication, availability or root agreement; D5/X7 generic
coupling remains open.

[EthState §7.4](modules/EthState.md#74-invariants-exported-to-other-libraries) owns
Q58's supplied StructuralPremises and ordinary laws. Initial
MathState.WF plus deletion-to-clear and raw storage-change address-to-post-account
presence suffices for structural apply preservation, including empty patches and zero
writes with arbitrary metadata/code/account fields. This local implication supplies
neither full optional-map WF policy nor replay history, reachable extraction,
AccountWritesLookedUp or F7; those obligations remain with their existing producers.

### Typed-trie storage, preparation and root premise (Q53)

[EthCommit §3/§7.0.3](modules/EthCommit.md#3-eels-source-map) supplies generic
arbitrary-default storage and separate `NoDefault`/`PrepareSafe` laws. Its
`TrieValue` class specifies total encoding with nonemptiness under validity;
the generic lawful injective byte-key contract and pure preparation are supplied in
EthCommit §3. Typed root composition and the conditional existing-Bytes key adapter
below are supplied;
concrete consumer encoding and Python key/equality/alias bridges remain unimplemented.
Empty construction supplies both predicates for any
default; an all-value setter preserves safety from a safe input exactly when it deletes
by equality with that default or inserts a valid value. Preparation/root require safety
and `secured = false`, but no `NoDefault`; valid stored defaults are encoded directly.
Implemented preparation is pure with zero queries; the supplied typed root
calls C8 directly on that pure map
with the caller's existing F20 empty root. Local composition/empty equations need only
`Monad`; equality to a separate preparation-bind reference needs `LawfulMonad`.

EthBlock must supply valid concrete legacy records, nonempty typed envelope Bytes and
already-RLP withdrawal Bytes, with lawful byte keys and default `None` semantics. Its
dense arrays use the same EthCommit root operations (§5 of EthBlock), encoding each value once.
EthStateCommit supplies the total U256 encoder, all-value validity/nonempty laws and
wire injectivity (EthStateCommit §3), independently of supplied-default deletion.
Its exact integer equation and complete-wire source controls are owned there;
they do not supply a root or backend bridge.
It also supplies contextual Account encoding, unconditional nonempty and pair binding
under both complete assembled Q47 domains (EthStateCommit §3). That owner also
supplies the exact four-field equation and local original-source controls. The callback/root
integration remains open; no context-free Account instance follows from this class.
Source bridges additionally supply Python equality/dispatch agreement, valid
supported non-`None` values, complete schema/assembled-node `Encodable` (Q47), coherent
F20 constants and pinned host compatibility. Total invalid encodings imply no Python
success. Secure traversal, collisions, source history and generic coupling remain open;
approval alone supplies no concrete source bridge or consumer/root proof.

### Local account-leaf decoding seam

[EthStateCommit §3](modules/EthStateCommit.md#3-eels-source-map) supplies SC5
with caller-supplied F20 defaults: complete strict RLP, exact four-field shape,
then nonce → balance → root → code. The public contracts characterize all
accepted values and the sole coarse malformed-leaf rejection, raw empty input,
relevant-constants congruence and account SC10. The roundtrip takes **complete
assembled** `Rlp.Encodable`, exactly as account binding does under Q47; callers
must establish child and joined encoded-payload bounds. The shared conformance
`AccountDomain.empty_domain` helper discharges this premise for every supplied
emptyAccount and Hash32 root; the private `empty_account_roundtrip` client consumes it.
Explicit 32-byte hashes, including all-zero, are never replaced by defaults.
The private bounded balance fold equals its unsigned checked reference on every
finite input; nonce stays
unbounded. This local seam supplies no triggered backend lookup/root behavior,
secure traversal/callbacks, witness authentication, progress, collision/source-history,
generic coupling, global error adapter/O12, resources, C1–C4 or guest readiness.

### Local storage-leaf decoding seam

[EthStateCommit §3](modules/EthStateCommit.md#3-eels-source-map) supplies the pure
SC6 decoder and nonzero storage SC10 through public RLP/Base contracts.
Complete strict RLP parsing precedes list-to-zero or complete unsigned bytes;
private packed checked folding equals its full Nat reference on every finite Bytes.
The nominal witness-error carrier is owned by
[EthState §3/§5](modules/EthState.md#3-eels-source-map).
Only invalid RLP and parsed numeric overflow map locally to `.malformed .leaf`.
This supplies no global O4 adapter, granularity refinement,
authentication, lookup/progress, secure root/callback, Q55 action or generic
oracle coupling; those remain their owners' obligations. Local Q47 encodability
for SC10 follows the public U256 width bound; no stored-zero policy follows.

### Conditional existing Bytes key provider (Q54)

When a concrete Q53 consumer chooses existing Base `Bytes`,
[EthCommit §3/§7.0.3](modules/EthCommit.md#pure-unsecured-typed-preparation-q53)
owns the adapter and named exact-export law, relying on EthBase's Q54 provider.
RLP ordinal bytes retain byte order (zero `[128]` follows one `[1]`); EthBlock retains
concrete encoder, source equality/schema, safety and coherent F20 empty-root premises.
Public-import preparation/root clients retain those premises; the sequential reference
additionally requires `LawfulMonad`. Concrete consumer costs, host compatibility,
secured policy and generic coupling remain open with their existing owners.

### SHA-256 digest premise

[EthHash §3](modules/EthHash.md#3-eels-source-map) supplies the pure total
`sha256 : ByteArray → Bytes32` API and its padding, byte-order, ordered chaining
and full-digest model laws. Standard-domain correspondence retains Q46's caller
hypothesis. This supplies the digest operation for future SSZ/request consumers;
record encoding, request-root composition and collision assumptions remain their
owners' obligations.

### RIPEMD-160 digest premise

[EthHash §3](modules/EthHash.md#3-eels-source-map) supplies the total pure
`ripemd160 : ByteArray → FixedBytes 20` provider and all-input MD4 padding,
little-endian word/byte and ascending chaining laws into an inductive digest
model. Base packed generation, byte-list observations and checked fixed-byte
construction, together with the accepted compression bridge, supply its premises.
The future precompile consumer still owns gas-before-computation, the twelve-byte
zero prefix and host capability/resource policy (DISC-005/O12). Finite actual
pinned precompile observations do not discharge those Lean composition obligations.

### BLAKE2F parameter premise

`EthPrecompiles` establishes `data.size = 213` after its size check before calling
`Blake2b.getParameters`. The raw codec preserves every round count and flag;
its public byte laws and two inverse laws are owned by
[EthHash §3](modules/EthHash.md#3-eels-source-map). The precompile then owns gas
charging and flag rejection in R5 order before invoking compression.

BLAKE2b F's pure compression/byte premise is discharged for all UInt32 counts by
[EthHash §3](modules/EthHash.md#3-eels-source-map). Its precompile consumer must still
establish gas-before-compression and validate the raw flag after charging gas;
those effect/order obligations are not produced by the pure hash function.

### Keccak digest premise

The concrete fixed-rate Keccak provider supplies total byte-level model
correspondence and fixed widths ([EthHash §3](modules/EthHash.md#3-eels-source-map)).
Query dispatch, acquisition and oracle coupling have separate premises below.

The separate packed candidate supplies ordinary all-input equality with these
retained reference endpoints, including padding, block absorption and byte output
([EthHash §3](modules/EthHash.md#3-eels-source-map)); current defaults remain unchanged.
These laws do not supply the query instance, acquisition or oracle coupling, and
local native diagnostics do not supply target/resource composition.

### Pure trie path premise

[EthCommit §3/§7.0](modules/EthCommit.md#3-eels-source-map) supplies the bounded
`Nibbles` List abstraction, byte high/low split, canonical compact byte model,
lenient compact decoder and maximal common-prefix laws. The canonical encoder
inverse and injectivity bind path plus leaf flag. Accepted-wire reencoding is
normalization; unused high flags and even low padding need not survive.
The path type produces the digit-range premise. Raw empty compact input returns
`.malformed .compactEmpty` (Q48); the later empty decoded extension-path error
remains the node consumer's `.malformed .pathEmpty` obligation under existing O4.
Q49 supplies bounded packed generation, clipped prefix/suffix/window equations
and lawful lexicographic comparison with actual path equality, so ordered-map
insert/lookup/extensionality use public seams. Strict suffix decrease retains
`level < size` and positive advancement; equal bounded path prefixes follow
from maximal common-prefix laws. Q50 supplies the actual finite-map domain at zero, ending-key uniqueness and
representative-independent branch lookup, guarded child-domain preservation and
private strict sum descent for every numeric child (including empty children) and
positive shared extensions. Private longest shared-prefix selection supplies its
full-depth/shared-prefix premises, maximality, representative-independent length
and additional path, and strict sum descent for positive amounts (EthCommit §3). Full keys are retained; empty byte
values and prefix relationships remain allowed. Private bounded branch support
uses those partitions and ending lookup with supplied child construction followed
by C6 encoding in numeric order; its sequencing equations retain LawfulMonad
premises (EthCommit §3). It returns a branch without a parent query. Recursive C7 now consumes the supplied
child/domain witness and prefix domain/strict-descent laws, with public empty,
singleton, extension, ordered branch and optional-lookup extensionality equations.
Its private recursive selector equality permits different valid representatives at
every descendant; public clients use ordinary arbitrary-member equations without
a new selector API. C8 supplies the total local root wrapper and ordinary
reference/fused equality (§3). Canonicality and aggregate copy/comparison costs remain open.
Future node/trie consumers own those checks and witness/guest adapters. These
pure path/domain premises introduce no node/root or host-resource theorem; the local
decoder allocation exception is recorded in DEBT-COMPACT-DECODE.

### Decoder field diagnostic premise

[EthCommit §3/§7.0.4](modules/EthCommit.md#3-eels-source-map) supplies Q52's
nominal diagnostic declarations and public codec/compact seam clients. The complete
C14 decoder parses the whole RLP before shape dispatch, after any Q55 preparse
query, checks a two-item path field before
compact decoding, and checks a list-valued leaf value only after successful leaf
compact decoding. Extension path/child checks, original descendant-error
propagation and branch-list ending leniency are supplied in the complete dispatcher.
WitnessError/guest adapters remain unimplemented;
CONTRACT O4 owns the unchanged output projection.

### Nominal partial-node carrier support

[EthCommit §3](modules/EthCommit.md#3-eels-source-map) owns the nominal
Enc/Node/Ref and secured/root IncrementalMPT field contracts. Consumers preserve the
supplied flag and complete root. B3/NEW-COMMIT-1 requires the DISC-003 provenance
and failure/observation demonstration before semantic adoption; constructors and
structural clients do not establish it. Remaining admission, operation and cache
representation/refinement gates are owned by [EthCommit §10](modules/EthCommit.md#10-gaps).

### Pure completed-cache child-reference premise

[EthCommit §3/§7.0.7](modules/EthCommit.md#3-eels-source-map) owns the supplied pure
observer, five all-bare equations and private ordinary List/HP equality. Its conditional
source-value differential evidence requires the §3 cache/class/recursive assembly premises;
hashless-short reconstruction requires Enc.hash? = none. Inline output rebuilds current
fields, including canonical HP and the interpreted C16 ending, rather than original raw
provenance. Input Enc retains raw bytes; the stored-hash shortcut retains its supplied hash.
B3/DISC-003 adoption and dirty-cache/query/write/whole-operation obligations remain open.

### Supplied incremental-root premise

[EthCommit §3/§7.0.9](modules/EthCommit.md#3-eels-source-map) owns rootHash/mptRoot,
six plain-Monad equations, ordinary whole-action reference equality and conditional
source evidence. Consumers pass coherent F20 constants and preserve the relevant
accessed-cache/child embedding, complete assembly/class/Id/hash/finite-host premises.
Clean stored-hash roots bypass descendants; dirty caches and mutable source query
stages remain distinct. This supplies no whole root/map/action/adoption/readiness gate.

### Completed immediate-extension premise

[EthCommit §3/§7.0.8](modules/EthCommit.md#3-eels-source-map) owns the supplied
constructor, four plain-Monad cases, private reference equality and conditional
source-value domain. Consumers preserve one immediate splice and whole retained
children; final Encodable/cache/embedding/class/Id/hash/host premises remain explicit.
Source witness/child/own effects are distinct from Id node-image comparison; committed
recording-state/transformer controls supply separate generic-effect evidence. Whole
update/root scheduling, canonicality and guest/resource obligations remain open.

### Completed fresh-leaf premise

[EthCommit §3/§6/§7.0.6](modules/EthCommit.md#3-eels-source-map) owns the supplied
constructor, literal effects, private all-finite-input reference equality and successful
fresh-source domain. Consumers retain the complete assembled Encodable/class/Id/hash/host
premises; arbitrary caches and mutable failure states are outside that relation. Whole
update/root scheduling and its effect/lifetime/refinement obligations remain open under B15.

### Completed reached-branch premise (supplied local operation)

[EthCommit §3](modules/EthCommit.md#3-eels-source-map) supplies mkBranch on every
finite bare child array/value, with a private ordinary List/wire literal action
equality under plain Monad. Actual presence census and terminal dispatch precede
sole-survivor witnessing; stub/query failure precedes actual-index classification.
Fresh own completion is strict; supplied-hash and supplied-raw witness gates retain
their exact effects, and a queried cached-long hashless answer is not installed.
Short current reconstruction updates retained branch-survivor top Enc; immediate
leaf/ext splice discards only that top Enc. No public witness/cache helper or law
is added. Concrete source comparison uses the clean finite nonaliasing entry-image,
consulted source raw-presence/hash/current-field and child-embedding premises in §3;
retained terminal/multiple parent
completion additionally starts with raw = None/hash = None independently of dirty.
Immediate collapse and subsequent strict completion are separate comparison stages.
Mutable dirty/history/descendant observers and arbitrary generic source actions are
not simulated by the all-input nominal reference equality. Whole mutation and the
existing WF/map/root/witness/security/resource/readiness gates remain open.

### Bare mutation handoff (Q60; encoded setter supplied)

Q60 collapseIndex constructor/complete observer and strict reason 12 parser support
are supplied by EthCommit §3, together with local reached mkBranch emission.
Decoder and lookup never emit it. Update and exact update_branch_oob are supplied
by EthCommit §3/§7.0.10; delete and both approved root equations are also supplied there;
encoded mptSet and its emptyEncoding equation are supplied separately by EthCommit §3.
Normal/-O decoder, lookup, update, deletion and setter parser controls
preserve old tags/fields and full Nat identity.

[EthCommit C18/C19/C22–C25/C29/§7.0.10](modules/EthCommit.md#5-interface) owns
approved total update/delete/mptSet completion and the four local equation types.
The supplied direct update preserves matched/split extensions and actual branch
arity with private strict completions, original-child totality and full all-input
plain-Monad offset/List CPS equality. Its public root bounds law keeps the exact
index/arity and bare pure error. EthCommit §3 owns the complete controls, concrete
source stages/premises and remaining history obligations; no extra consumer helper
or public source/WF predicate is supplied.
The separate supplied deletion realization strictly completes every visited surviving
node, including no-op nodes, while retaining off-path caches. Its private source-control
classification propagates visited child completion through no-change parents and
merges one immediate leaf/ext before the dirty guard. Ordinary independent List-wire/
continuation/set and packed-offset CPS equality retains plain Monad; both public root
errors are bare pure. Concrete agreement retains clean same-origin returns only where
a reached parent actually inspects dirty, with separate consulted embedding, full
retained-cache, Encodable/class/host premises owned by EthCommit §3. It introduces no
public metadata or a broad WF/initial-clean requirement.

The encoded setter preserves literal provider-result bind/pure/Except.map syntax under
plain Monad, with private arbitrary-provider/List action equality and complete controls
owned by EthCommit §3. Focused validation and the bounded frontend catalog pass:
26 successful completed projections, eight source-only encoding/default boundaries
and 20 explicit diagnostics. The complete premises and history limits remain there.
Callers preserve actual key/value/secured/root fields and operation order: direct
empty update inserts, while frontend none/some empty deletes after secure key
acquisition. This action equality concerns only the nominal root/secured carrier;
source `_data`, default/witness records and mutable partial state are not equated.
No bare Account instance or contextual root callback is supplied.

C19/C24/C25 own the clean-entry private change/cache rule and exact reached-site
failures. Callers preserve actual positions and action order, including a sole stub
or underlying query failure before index classification. Bare diagnostics alone
supply no O4/O13 reachability or projection.

Source agreement needs compatible finite nonaliasing represented dirty/cache/current
fields, bounded paths, selected accesses and reached-collapse correspondence domains,
complete assembly Encodable, exact class/hash/Id and host premises. Canonical progress
additionally carries its real value/shape/availability premises. These are theorem
premises, not new runtime/public WF predicates. Consumers use public operation/model
laws; private worker/structural/reference proofs may change internally under B15/Q33.
An Id value equation does not license stateful/failing generic action reordering,
cache/witness/lifetime equivalence or arbitrary initially dirty source shape.
Remaining frontend diagnostics/law and catalog, mptSet, map-level mutation laws,
root/map/backend/security/witness, W1/S2/R2/O12/resources/costs and guest readiness
remain open.

### Pure lookup premise (Q59; supplied local operation)

[EthCommit C20/§§5/7](modules/EthCommit.md#5-interface) owns the supplied total pure
lookup and seven constructor equations on finite bare Ref/Nibbles inputs, with all Enc
fields unconstrained. Only the reached nonterminal selected-slot bound is checked;
terminal value/absence precedes bounds. Lookup takes no Node.WF/cache/admission premise.
Source value/stub correspondence needs valid selected accesses, the actual
Hash32-to-64-nibble/source-class bridge and host premises. The bare bounds diagnostic
supplies no guest reachability/handler/output claim (CONTRACT O4/O13).
The diagnostic, operation, seven equations, private structural proper-child and
all-bare offset/reference proofs, public-only clients and complete-value/first-error
controls are supplied there. Q59 supplies no decoder/WF/cache/
mutation/root/security agreement, generic coupling/action-result lifetime, whole W1/S2,
C1–C4/O12 or guest readiness premise.

### Complete decoder action premise (Q55; supplied local operation, partial W1)

[EthCommit C13–C14/§5/§7.6](modules/EthCommit.md#5-interface) owns the two generic
complete decoder operations and query-before-whole-RLP acquisition on newly entered
eligible raw occurrences, with private actual-key cycle/remaining-key and parsed
inline-subterm totality support, three public plain-Monad equations, and complete
finite Id/state/failure/source conformance. Consumer/error/lifetime and whole W1
composition remain open. Pure lookup (supplied separately under Q59), childRef (supplied separately), raw cache shape, lenient
admission,
ordered diagnostics and current-path cycle behavior retain their contracts.
Concrete agreement premises are `Id.run (decodeRoot consts.emptyTrieRoot db r) =
.ok t`, using the actual Id interpretation and coherent supplied F20 constants.
Cache/reference equality requires authenticity and raw length ≥32; long inline
and arbitrary alias-keyed DB entries retain actual complete-preimage answers.
Consumers prove exact parsed inline subterm/reencoding provenance, without
normalizing accepted raw HP. No decoder locally acquires constants.

EthStateWitness runs generic decode actions at B4/W2 triggers, distinguishing read
cache reuse from fresh root-computation decoding. Its current pure result thunk
is Id only; a thunk of an action does not cache an executed result. Generic
successful-result ownership/lifetime and first-failure/F6 refinement remain open.
Underlying monadic failure remains in its original channel; typed decoder errors
preserve earlier query effects and stop later traversal. The existing witness
error-adapter/CONTRACT projection is a separate implementation obligation.
Hash-relative security/value comparison requires a real interpretation bridge,
explicit relevant-query equations and lawful sequencing; stable Id values do not
prove arbitrary stateful/failing effects. Q55 supplies no whole W1/S2/R2 coupling
or production cost/resource gate, and selects no B15 completed-node memo.

### Internal-node encoding premise

[EthCommit §3/§7](modules/EthCommit.md#3-eels-source-map) supplies nonrecursive
complete assembly, all-input total RLP model equality and the exact inline/one
whole-query rule. Public laws retain arbitrary nested fields, sixteen ordered
children/value-last, all 32 answer bytes, original oracle failures and transformer
contexts. Standard/pinned correspondence requires `Encodable` of the complete
assembly, including HP width and joined payload; actual trie/schema callers own
that premise, Python Extended interpretation and host compatibility. Global oracle
coupling, cache/witness and whole-trie/resource gates remain open; the total local
C8 wrapper is supplied by the following seam.

### Mathematical-root domain and constants premise

`PatricializeDomain` is the public proof seam in EthCommit's `Root` owner;
its fields use actual `Nibbles.size`/`take` and finite-map membership. Recursive C7
constructs internal nodes on this domain; C8 supplies `mathRoot emptyRoot obj`. Q50's arbitrary-depth helper
requires the proof explicitly; no behavior outside that domain is selected.
Empty `mathRoot emptyRoot` locally returns `pure emptyRoot` without a new query
or local oracle failure. Caller-owned F20 acquisition must provide the coherent
constant. On nonempty maps the actual C7 action precedes exactly one final query
on the complete top assembly; descendants and their original errors remain ordered.
The private C6/root reference equals the fused action in every lawful oracle monad,
including all answer bytes and effects. This total local equality uses Q47, not
`Encodable` or collision assumptions; fixed32 answers have RLP width33.
Concrete Id/pinned-root correspondence needs compatible prepared-map/value
interpretation, constant coherence, complete assembled-node `Encodable` and
successful host behavior. Python empty root queries `80` once; local Q50 empty
execution queries zero times. These whole generic traces are not identified.
Q53 typed preparation/root composition is supplied above. Concrete encoding bridges, whole-source refinement and D5 generic coupling remain open.

### RLP encoding premise

[EthCodec §3/§7](modules/EthCodec.md#3-eels-source-map) supplies total packed
encoding and its exact byte-list model, computed/output widths and ordered child
payload concatenation. Standard/pinned correspondence retains `Encodable` (Q47),
which characterizes every recursive child and encoded list payload length.
Consumers can compose empty/nested byte/list models without unfolding the temporary
writer cache. The raw wire-law domains are owned by EthCodec §7; schema
instances and guest outcomes remain their owners' open obligations.

The encoding-only typed handoff is supplied by
[EthCodec §3/§5/§7](modules/EthCodec.md#implemented-typed-rlp-encoding-foundation):
`RlpEncode` has exactly the `toRlp` field, `encodeOf` composes it with raw encoding,
and Nat's adapter is exactly `ofNat` on every natural. Private facade clients
compose complete byte/size laws and conditional raw-wire image, including a
bounded caller's public-law domain discharge and a nominal instance dispatch
control. Standard/source correspondence retains Q47's `Encodable` and actual
source-class/host premises. No generic inverse or class proof field follows;
the separate typed decoding foundation supplies `RlpDecode`, `decodeTo`, Nat
decoding and its conditional roundtrip. Other instances remain open in EthCodec
§10. Q68 owns the diagnostic equation and source/consumer observation.

The ByteArray pair is also supplied by [EthCodec §3/§7](modules/EthCodec.md#implemented-bytearray-rlp-instances):
`RlpEncode.toRlp` is exactly `.bytes`, `RlpDecode.ofRlp` is exactly `toBytes`,
and `decodeTo_encodeOf_byteArray` retains `Encodable (.bytes b)` (Q47).
Private facade clients recover the exact successful leaf/domain and reencode
the complete original wire; bounded callers discharge their own size premise.
All bytes, including leading zeros, remain data. Lists reject only after raw
success; every raw diagnostic and the complete typed result survive under Q68.
Source admission is original builtin Bytes, with source/runtime and first-consuming
handler premises retained. Other instances, schemas, host-depth, guest and cost
gates remain open; this supplied handoff changes no decision or readiness status.

### Raw SSZ model premise

[EthCodec §3/§5/§7](modules/EthCodec.md#3-eels-source-map) supplies the raw
`SszType`/`SszValue`/`SszError` constructors and ordinary inductive elimination.
Consumers can retain complete natural/boolean/byte payloads, ordered recursive
children and independent masks. Construction proves no source-class/schema
admission, well-formedness, typing, codec inverse, rootability, error-producer or
guest outcome property. The raw handoff adds no acceptance restriction or
authored constructor-law family; structural sizing is supplied separately below.

Separately, [EthCodec §3/§5/§7](modules/EthCodec.md#7-contract-and-laws) supplies
Q67's structural classifier and single ordinary equation on every raw descriptor.
Private public-equation clients compose optional field sums, derive mask/list
independence and inspect complete slot tables. Consumers inspect the complete
`Option Nat`, retain `some 0` separately from `none`, and establish local admission,
positive-divisor, serialization and root-domain premises independently. Conditional
static source interpretation supplies no executable/formal Python correspondence,
actual schema or compiled resource theorem; the residual domain questions remain
open in EthCodec §10.

Q74 additionally supplies the physical-capacity `Ssz.merkleize` helper and its
complete ordered padded-fold equation, owned by EthCodec §5/§7. Each caller
supplies the actual chunk-count bound at the selected rounded depth; a declared
byte/item bound needs a packing/child-root bridge. Physical helper support is
weaker than declared admission: 31 and 32 bytes both fit one chunk at declared 31,
while 33 bytes do not fit declared 32's one-chunk capacity. The helper retains
plain zero-padding ambiguity and supplies no count mix-in or binding theorem.
Q79 supplies the proof-bounded raw recursive root and its complete equation on
Q78’s supplied local Rootable domain. Actual successful decoder/adapter-to-support
proofs and typed root/schema refinement remain open. Structurally supported
execution-invalid requests must still root before inner validation. No schema
class field, accepted-domain, O2/O12/O13, resource, security or readiness change
follows.

Separately, Q70 supplies `SszType.WellFormed` and the sole ordinary public
`wellFormed_iff` constructor law, owned by EthCodec §5/§7. Consumers use that
nameless structural equation: recursive children remain obligations at limit 0,
ordinary fields are nonempty, and progressive masks use final activity, length
and population rather than an all-one assumption. Source names/reflection/class
construction, including `more` at capacity 256, are supplied locally; the predicate
alone proves none of them. Q71 supplies payload typing separately below; count/backing/offset/scope,
cache and codec/root domains remain separate. Q87 supplies the local count-recovery
premise; its future inverse and decoder completion remain open. Some fixed-zero
schemas are WF, so division/recovery must establish positivity locally. Q67 stays
total on every malformed schema; logical controls assert no executable source,
codec, root, guest, resource or cost agreement.

Separately, Q71 supplies payload-only `SszValue.WellTyped` and the single
ordinary complete `wellTyped_iff`, owned by EthCodec §5/§7. Consumers use actual
member recursion and exact equal-length/zip field alignment. Masks do not change
payload typing, and empty actual lists visit no child values. WT⇒WF is false;
consumers needing WF state it separately. Source classes/names/coercions,
recursive uint256 constructor/backing counts and mix-ins, and offsets/scope/cache
remain local premises. Q87 count recovery is supplied separately; its inverse/decoder and actual
codec/root bridges remain open.
Private public-law clients compose these independent judgments and give fixed-zero
count-size counterexamples without a codec claim. This Prop slice supplies no
source execution or guest/resource/security/cost/readiness result.

### Derived address premise

[EthCodec §3/§7](modules/EthCodec.md#3-eels-source-map) supplies the exact CREATE
RLP preimage and CREATE2 two-query order/dependence, concrete Id formulas and
final twenty-byte suffix laws. Every Keccak uses `KeccakQuery`, retaining arbitrary
answers and ordered effects; lawful ExceptT error contracts preserve original
failures. Base's `Address.toBytes_ofNat_toNat` proves suffix conversion, including
leading zeros and no-op source padding.
`encodable_computeContractAddress_preimage` supplies Q47's CREATE `Encodable`
premise for every sender and nonce below 2^256, including U64 protocol nonces.
The total Nat API has no input cap. VM creation/state/gas/collision behavior,
oracle coupling, security assumptions and guest/resource gates remain their owners' obligations.

### RLP header premise

[EthCodec §3/§7](modules/EthCodec.md#3-eels-source-map) supplies the packed
`decodeItemLength` helper's suffix/window model correspondence, ordered header
diagnostics and positive unbounded declared extent. It inspects at most eight
length digits and does not validate payload availability or canonical item forms.
Future full parsers must bound the extent inside the parent list window before
payload reads, recurse only within that extent and require full consumption.
The full decoder's laws are owned by EthCodec §7. Schemas, host-depth and guest
outcomes remain open.

### Raw RLP decoder premise

[EthCodec §3/§7](modules/EthCodec.md#3-eels-source-map) supplies total packed raw
decoding, exact storage/list-model and byte-window equations and named ordered
singleton/short-form failure cases. Private cursor windows are bounded before
child descent or leaf copies. Shared parser semantics are audited separately
against authenticated locked source. Consumers use the raw inverse, accepted-image
and binding contracts owned by [EthCodec §7](modules/EthCodec.md#7-contract-and-laws)
with their explicit domains; they retain Q47's total extension without
outside-domain inverse or pinned-host claims. Schemas, host-depth/resources,
security and guest outcomes remain open.

### Typed RLP model premise

[EthCodec §3/§7](modules/EthCodec.md#3-eels-source-map) supplies raw-model typed
leaf accept sets and byte/field order preservation. The integer premise includes
both minimality directions and complete bounded range; union success requires
exactly one successful alternative. Consumers compose the raw wire laws from
EthCodec §7 and must implement child schemas/instances wherever the pinned caller
uses `decode_to`. Q68's supplied wrapper preserves raw errors and the entire
typed result after raw success. Erasure means mathematical source/consumer
observation in existing `Except Unit`, mapping all diagnostic errors to one
rejection channel while preserving complete successes; it is not replacement of
wrapper diagnostics or a new exported projection API.

The class, wrapper, Nat decoder and conditional Nat theorem are supplied.
Private facade clients establish whole typed forwarding and raw-first failure,
a generic inverse only with its caller-owned adapter-inverse and Encodable
premises, bounded local Nat discharge, and successful Nat exact reencoding.
The168 complete controls preserve arbitrary diagnostics and custom successes. Source correspondence retains intended target
admission, successful reflection/class metadata, local callback refinement and
host premises; the source typed catch retains causes and supplies no Python
exception-object/message equality. Raw host exceptions bypass that catch. Header
fallback O3 and transaction O6 retain their distinct first consuming handlers;
using the wrapper alone proves no schema-depth or D2r agreement. These leaf laws
discharge none of the handler, guest outcome, host-depth or complete schema
premises (D14, Q20, O12).

The supplied generic List seam is owned by [EthCodec §5/§7](modules/EthCodec.md#7-contract-and-laws).
Consumers lift agreement for their actual list members through the public model
law, recursively reusing that same law for nested lists. This model lifting
requires no wire domain. The public wire law additionally requires Encodable of
the complete assembled model: every child and the joined encoded payload bound.
Per-child sizes do not establish that aggregate bound. Neither left inverse gives
generic successful-decoding-to-reencoding without separate element model-recovery
premises. Ordered child models, list-shape-before-child typing, empty success and
the first complete error remain visible under Q68. Schema ownership and local
source admission/reflection/callback, first-handler and host duties remain as
above; pure error equations supply no callback execution or cost trace.

### Hash32 table-support premise

[EthBase §3](modules/EthBase.md#3-eels-source-map) supplies Q51's total
nonprotocol Hashable Hash32, its all-input executable/reference equality and
existing actual equality's lawful hash classes. Complete numeric/byte observers
preserve support hashing; public Std insertion/overwrite/different-key lookup
laws hold without a distinct-hash premise. This supplies only the table prerequisite
for EthCommit's NodeDB. Its actual construction and authentication premise are
provided below; generic oracle coupling, eager decoding, root agreement and
resource gates remain with their existing owners. Support/bucket collisions affect costs, not key equality
or cryptographic authenticity; map expected costs retain ARCHITECTURE §5.0's
measurement/distribution premises.

### Raw node database premise

[EthCommit §3](modules/EthCommit.md#3-eels-source-map) supplies C12's actual
NodeDB/map, ordered monad-parametric construction, List reference/model equality
and full last-write lookup. `authentic_build_id` produces the separate concrete
`Authentic keccak256` premise required by future decoder/cache/agreement consumers
(EthCommit §7.4/§7.6, EthStateWitness and EthSecurity). Empty/raw malformed inputs
are uninterpreted; arbitrary oracle answers and errors forward in input order.
Transformer and failure equations require explicit LawfulMonad where stated.
Reconstructed keys and actual Std lookups use only public Base/map laws.
Generic concrete-authentication coupling remains D5/X7; no decoder, root,
witness agreement, host-resource or C1–C4/R4 completion follows from this slice.

### Hash constants and oracle premises

Constants acquisition and coherence follow F20 (EthStateless R5, EthBlock §2.7,
EthConformance R4); a `consts` parameter alone does not establish coherence, and
generic interpretation coupling remains open (D5, X7).
The query interface additionally supplies definitionally concrete Id dispatch,
forwarding ExceptT/StateT instances and ordered four-query `HashConsts.query`
acquisition, with public run equations and arbitrary-answer/error observations
(EthHash §3). Concrete equality to Base literals is evaluated through guards and
authenticated pinned globals; it is not an equality theorem. Production F20 entry
seams, consumer coherence and generic oracle coupling remain open.

### Checked error channels

`CheckedResult ε α := Except InternalError (Except ε α)` has exactly three interpretations:

- `.ok (.ok a)`: successful computation;
- `.ok (.error e)`: a validation/backend fault, projected according to its guest phase;
- `.error i`: spec-internal failure, retained by the checked guest.

Every hashing interface is parametric in `{m} [Monad m] [KeccakQuery m]`, and execution specialises to `m := Id` (D5). The monadic form is `CheckedT ε m := ExceptT ε (ExceptT InternalError m)`, whose `.run.run` gives `m (CheckedResult ε α)`. The adapter `runVmChecked : VmM m (Except InternalError α) → VmWorld m → m (CheckedResult VmFault (α × VmWorld m))` converts without swapping meanings. For an action run on world `w`:

```text
action w = .error vf                    => .ok (.error vf)
action w = .ok (.error i, w')           => .error i
action w = .ok (.ok a, w')              => .ok (.ok (a, w'))
```

`BlockError.ofStateError` maps witness faults to `.witness` and other state faults to `.state`. `BlockError.ofVmFault` delegates `.state e` to that adapter and maps other VM faults to `.vmFault`. Transaction decode errors are indexed at the block/payload caller. On the complete guest path they cannot reach `executeBlock`: `is_valid_versioned_hashes` consumes every deterministic decode failure first, giving O6. They stay live for a standalone `executeBlock`. Public-key count and wrong-key errors remain distinct, with the transaction index retained for the latter. EVM exceptional halt/revert are FrameError data inside a completed run; they use settlement, not these global-error adapters. An unchecked system call ignores a settled FrameError, not a provider fault or InternalError.

Guest classification preserves the outer/inner Python handler boundary: decode/schema failure gives O1; root computation failure gives O2 (to be proved unreachable on decoded values: DECISIONS §3, O2); after a root exists, inner validation faults, including the enumerated O13 faults, produce `(root,false,chainId,0x1501)`. An InternalError remains checked; only the public total projection uses the documented sentinel fallback. Proving that fallback unreachable requires the fuel theorem **and** a proof that arbitrary accepted input constructs valid contexts. X1 still needs an exhaustive classification of the reachable exception sites before this projection is complete.

### Configuration and crypto adapters

Construct `vmConfig := {costs, stateCosts, limits}` once. FrameCtx and RunnerEnv receive that same config; child contexts inherit it. `BlockConfig.runnerEnv` derives it from `gas`, `stateGas` and `limits`, alongside `precompiles`. F8 separately forwards `cfg.system.systemAddress` into RunnerEnv; successful createEvm copies it into immutable FrameCtx, and CALL/CREATE child constructors inherit it. processCall and SELFDESTRUCT use `ctx.systemAddress` and the existing `world.tx.block.consts.transferTopic` argument. Intended Fork→Block→Runner assembly/source-refinement proves these equations and supplies the pinned address/topic; local helper, Step/Exec and independent gas/fuel laws acquire no global raw admission or address-literal premise. Whole-record/model equalities retain the field. These address/context/emitter/transport/value implementations remain open; F20 acquisition/lifetime, log discard/settlement, generic D5 coupling, G2–G7, S2 and resources stay separate. Each precompile closure captures its pricing from that config. Successful `PrecompileResult.ok m' out` satisfies:

```text
m'.gasLeft ≤ m.gasLeft
{m' with gasLeft := m.gasLeft} = m
```

Install `m'` directly, with no second charge. The table's address set equals its lookup domain and supplies transaction warm addresses. Amsterdam's depth remains 0 through 1024 inclusive; making other limit fields configurable does not establish support for arbitrary depth policies.

secp256k1 recovery returns Bytes64, the unprefixed x/y bytes. Hash those bytes for an address; a 65-byte public-key hint includes prefix 0x04 and must be checked against recovery/signature semantics. Boolean parity recovery completeness is restricted to the documented `x=r<n` domain. `mapToCurveG1/G2` stop before cofactor clearing; EVM mapping wrappers clear exactly once. These are semantic adapters, not representational conveniences.

For payload conversion, `Array PublicKey` erases each subtype to its ByteArray for EthBlock while retaining the 65-byte/prefix/verification checks. `AnyHeader` is the existing ParentHeader sum, not a second header representation. [REFERENCE-RECORDS](REFERENCE-RECORDS.md) fixes source field order, widths and inheritance for all wire/schema adapters. Dense transaction/receipt/withdrawal arrays in BlockOutput model index-keyed unsecured tries: root construction uses `rlp i` keys and the reference typed/legacy value encoding; receipt traversal for requests follows recorded receipt_keys, appended in transaction order, rather than sorting RLP keys (fork.py:1124; requests.py:291).

### Natural-reference residue arithmetic premise

[EthField §3/§5/§7](modules/EthField.md#supplied-basic-natural-reference-arithmetic)
supplies canonical `PrimeFieldRef` construction and basic add/sub/neg/mul/isZero with
ordinary observer equations and four directly delegating operator instances. Generic
private facade clients compose those laws for range, both zero-recognition directions,
signed subtraction/negation and cancellation, for every p>1 and arbitrary unread
metadata. Consumers use observers and public laws. The eight exact natural moduli are
separately supplied by EthField §3, without instances, aliases, square-root metadata or
backend parameters. Composite residue arithmetic and literal modulus values supply no
field structure or primality fact. The separate natural-reference power leaf supplies
`pow`, `toNat_pow` and direct natural-exponent notation for all canonical bases and Nat
exponents, including composite/nonunit cases and zero-to-zero. Private facade clients
derive range, zero/one, square/product/exponent-add/iterated-power laws using public
observations alone, with arbitrary unread metadata. The positive-modulus private worker
chooses no public powMod-zero completion. The separate canonical-sign leaf supplies
sgn0/sgn0_eq; private facade clients derive true/false, zero/one, reducing-constructor
parity and metadata irrelevance through equal natural observations, for every p>1. The
separate checked-reference decoder supplies ByteArray `ofBytesBE?` and its complete
success iff via public Base byte/unbounded-natural providers. Private facade clients
derive none iff, original-value/range, empty/all-zero, leading-zero/positional equality
and Option-Nat metadata irrelevance. Generic decoding has no width cap. Actual source
correspondence requires typed 32-byte assertion-active KZG, or exactly 64-byte BLS
inputs; optimized KZG agrees only on admitted values. Consumer length checks, original
exceptions and outcome mapping remain separate. This reference premise supplies no Fp2,
sqrt or negation-sign law. Runtime Montgomery aliases/D6, sqrt/encoding,
executable/tower inverse, public powMod, concrete fields/towers/Mathlib bridges and
actual curve/precompile composition remain open; this reference seam supplies no
production performance or guest-readiness result.

The separate Q86 inverse leaf supplies the complete public finite signed
`EuclideanCoefficient` graph and canonical `Inv0Model`/`toNat_inv0_iff` contract. Every
existing p>1 element, including composite nonunits, has exactly one canonical result;
metadata is arbitrary and unread. Public-only clients derive range, zero, raw-input
reduction and metadata observer congruence. The product law alone takes local gcd-one;
concrete prime/nonzero-to-gcd bridges stay with future consumers. Replacements prove
output graph membership under canonical input observation, without unfolding the private
Euclidean worker. No raw-Nat operation, Inv/Div instance, division, field structure or
actual curve/precompile composition is supplied.

## 3. Inductive state invariant

Let `Reachable` mean a trace starting from valid block/transaction construction and using the specified admission, step, call, settlement, BAL and incorporation operations. This trace predicate must be defined; it is stronger than arbitrary calls to public raw helpers.

The induction invariant has the following parts:

1. Structural MathState/overlay invariants, including no orphan storage and the specified absent-account defaults.
2. Every changed account has been looked up in the immutable provider context before its first write. This populates the reference witness storage-root cache. At concrete Id/stable interpretation, the witness prototype repeats the same immutable lookup at root computation rather than storing call history; the reachable trace proves that extra lookup succeeds and agrees. For generic Q55 actions, value agreement alone does not prove equal query effects/first failure or result-cache lifetime. A raw setAccount/destroyAccount does not establish this fact.
3. TxRevertible contains writes, clears, transient values and write-order metadata; TxObs stays outside snapshots. Rollback selects the saved revertible roots and retains observations/created-account tracking and the authoritative ancestor cursor.
4. Account order, storage-address order and per-address slot order enumerate each current live write once. A clear resets the affected storage ordering, makes pending writes into reads, and hides lower overlays. Incorporation performs clears before ordered writes.
5. BAL updates observe the unmerged transaction and block views, then merge. First-index pre-values, nonce maximum and balance/code last-value behaviour follow the source builder.
6. Code hashes newly installed by callers authenticate their bytes. This is CodeChangesAuthentic, not a structural law of EthState, which cannot import hashing.

The induction begins with tracker construction over an arbitrary WF prestate σ₀, under
`ModelsLookups consts ps σ₀` at its fixed supplied record/provider (Q57) and the
required F20 context-coherence premises. Q58's structural implication is a separate
raw conditional theorem; it does not construct this reachable trace. Construction and
preservation of the complete reachable invariant remain obligations. Each future
operation's observer equation must preserve it; the caller establishes the operation's
preconditions. Snapshot/restore proves part 3 directly. Ordered fold induction proves
parts 1 and 4 at incorporation and diff extraction.
Parts 2 and 6 require proofs across Block, Instructions and Runner, rather than an assertion in
State alone. WriteOrder uses persistent position indexes so erase/reinsert and snapshots do not
rely on repeatedly filtering a list.

Witness updates must use the recorded order. EELS's branch collapse can need unavailable siblings, so exchanging delete and insert can exchange failure with success. Even a successful no-op delete can change an accepted noncanonical node's root. Canonical finite-map root laws therefore cannot be applied unconditionally to raw witnesses. The storage-root-only rewrite phase's set-order independence remains an explicit obligation.

## 4. Composing VM execution and termination

The supplied pure Log/LogRope handoff is owned by
[EthVmCore §3/§5/§7](modules/EthVmCore.md#3-eels-source-map): complete raw Log fields,
public rope constructors, two operations and six ordinary laws. Consumers use
`toList_append` for singleton emission and successful-child chronology; failed-child
selection retains the parent observation. Private public-only clients establish this
algebra, including inner success followed by outer discard and empty error-output
selection while stored logs remain unchanged. These are model statements, not a
settled-child or frame implementation. Actual gas/static/stack/HashConsts ordering,
settlement, state and top-level output/receipt integration remain caller obligations.
Raw shapes remain observable. EthVmCore §4 scopes the 102 native C3 measurements and
sharing/cleanup limits; no whole execution or resource gate follows.

The dependency order is Core → Instructions → Runner; precompile implementations reach Runner through the table, and the runner alone executes children. For each opcode, the local proof matches the ordered Python guards, effects and failure priority. The request boundary captures everything needed to resume; the child theorem supplies its settled meter, output, logs, state and error. FrameResult.toChildOutcome copies those fields with its non-top ChildSettled proof; runFrame alone is not a settled child result. How the runner produces that proof is open (DECISIONS F11): either a decidable check raising `InternalError.invariant`, proved dead together with the fuel guarantees, or a settled subtype returned by the runner. Resume equations complete the corresponding Python call/create operation.

Define Exec from these same step/resume/settlement operations. Induction on checked execution proves soundness. Induction on a finite Exec derivation chooses sufficient fuel and proves completeness; the same derivation proves monotonicity for larger fuel **with semantic gas fixed**. Gas-dependent code makes a general gas-monotonicity claim false.

The local charge kernel is supplied under [EthVmCore §3/§7](modules/EthVmCore.md#3-eels-source-map).
Execution charging consumes its amount of Φ; state charging preserves Φ and cannot
increase execution gas. The ordinary positive-charge client uses an explicit `1 ≤ a`
premise. Zero charging is neutral. These all-raw-meter laws neither choose a schedule
nor establish any whole-iteration or child-return inequality. Commit and both rollback
boundaries additionally preserve Φ under the local proof domains owned by EthVmCore
§3/§7. Ordinary rollback returns only pending spill and retains committed spill; entry
rollback returns both pools. Public-law clients compose these with charging and derive
ordinary rollback idempotence without a global invariant. Refund credit and spill repayment
also preserve Φ through their seven all-raw-meter laws. Public-only clients retain B/q/C,
derive the min branches and repayment identity, and compose the actual charge/refund/repay
operations. Exact charge/refund inversion uses a local initial pending-spill-zero premise;
a concrete counterexample excludes unconditional inversion. Repayment exhausts at least
one pool universally, with no input proof or new failure. Local transfer laws additionally
account for saved value-first grants: withholding decreases Φ by the returned execution
grant and retains E/64; draining preserves Φ; restoring adds only the supplied execution
amount to Φ. Forfeit uses only pending spill zero and retains arbitrary committed spill.
Public clients derive complete saved-amount withhold/drain/restore inversion, idempotence
and zero identity. Actual rollback post laws supply the local forfeit premise, without
a full settlement proof. Signed refund addition independently preserves Φ and all five
Nat fields for arbitrary Int k. Public-law clients derive zero/composition/inverse and
exact ordinary rollback/reset order; resetting after addition discards q+k, while adding
after reset retains k. The scalar maximum laws admit every Nat and prove complementary
granted/retained shares. Neither helper proves caller refund sign, storage history or
message-call affordability/stipend facts. These facts establish no real CREATE round trip (collision
occurs before drain), stipend bound or continuing-iteration decrease. Caller premise reachability,
remaining meter operations, full L-SETTLE/F11, settlement and frame/runner composition
remain obligations. The signed `txStateGasUsed` observer and its single ordinary equation
are additionally supplied under EthVmCore §3/§7. Callers establish only the local
baseline-to-grant proof; arbitrary other raw fields and negative usage remain admitted.
Private public-law clients derive E/q/baseline insensitivity, independent spill additions,
grant growth and reservoir decrease. No caller reachability or transaction-conservation
claim follows.

For computable sufficiency use Φ = gasLeft + stateGasSpilled + stateGasCommittedSpill. Local meter algebra establishes neutral redistribution and decreases for execution charges. Strengthen runner induction with child-final Φ ≤ child-entry Φ. The whole parent iteration, including forwarding, EIP-150, stipend, failed preflight, child settlement and returned gas, must decrease Φ whenever execution continues. Then entry Φ continuing iterations plus one terminal iteration gives `phiBudget`. This is the candidate proof, not a proved bound. Numeric schedule checks do not establish the whole-round-trip inequality.

Structural totality separately uses remaining depth, helper stage and fuel. The checked result of every child/top-level call retains InternalError. Only after proving the four guarantees and context invariants may the guest theorem conclude O11 is unreachable. Host recursion depth, memory allocation and zkVM cycles require measurement of the compiled implementation; mathematical fuel sufficiency does not discharge those operational obligations.

## 5. Backend-parametric block simulation

`Models` relates successful answers/roots to σ and includes structural WF and CodeAuthentic. It does not promise those operations succeed: an always-error provider otherwise satisfies implications vacuously. The full side needs progress on the execution trace, including CodeComplete. The witness side may fail on unavailable nodes or code.

Full Models retains the concrete Id record of EthStateCommit §5/§7.3 (Q57).
Both execution contexts must be coherent with that record before its lookup conjunct
can supply `ModelsLookups` at their BlockState.consts; factory parameters alone do
not establish this. The universal full-WF diff root clause and authentication/collision/
progress premises are unchanged; Q58's structural-only theorem cannot replace them.

Witness agreement also requires authenticated witness node/code databases, coherent oracle-derived constants and the specified decode thunk (EthStateWitness.WitnessBackend.WF). Guest construction must establish those premises.

For a **successful witness trace**, compare it with a progressive full provider representing σ. At each query, successful-answer agreement gives the same value, or the collision extractor reports unequal preimages with equal hash. Deterministic step/validation laws then choose the same branch and preserve the observation/state invariant. Induct through child frames, transaction settlement and block incorporation. The ordered final diff is the same; the backend root law gives the mathematical post-state root or a collision. This is directional simulation of successful witness execution, not equality of success/failure for any pair of Models providers.

The extractor must cover node encodings, address/slot preimages, dirty updated paths and code preimages from both providers. Structural WF alone does not authenticate σ.code; a state root binds code hashes, not bytes in a separate store. The secure-key collision case also needs a specified fold order for full roots.

This simulation establishes the conditional block-level theorem once all induction cases are proved. It does not establish that every honest witness succeeds. Witness completeness requires a separate construction/availability theorem, including eager off-path decoding obligations.

## 6. Composing bytes, validation and commitments

Codec type induction plus per-record instance inverses turns accepted bytes into the same guest value as the reference. Rootability/offset domains must be shown for actual accepted inputs; do not add a new bound merely to make the proof work. Compute the request commitment before inner validation, as in Python. Header decoding and contiguity checks then construct the context. Payload guards, block admission and execution follow their ordered contracts. Section 5 supplies semantic agreement on successful execution, and the complete error projection supplies reference failure outputs.

Final encoding is fixed: 32-byte request root, boolean byte, eight-byte little-endian chain ID, two-byte little-endian schema ID, in that order (CONTRACT §3); the input prefix's schema ID is big-endian. The zero sentinel sets every field to zero. Case analysis over the phases proves the 43-byte output equation, conditional on domain/host agreement and the completed X1 classification.

Header-chain binding additionally needs an external accepted tip. Request binding uses the exact guest schema and a separate SHA-256 collision statement. Keccak trie/code/header binding must use one resolved oracle scope: arbitrary-oracle hashes cannot be combined silently with literal concrete empty roots/code hashes or concretely produced new code hashes. D5 resolves this: the constants are `HashConsts`, queried through the same oracle. The ROM experiment must count adversary, guest, full-state and extractor queries. The coupling of `Models` at generic `m` remains open (X7). F20 specifies the acquisition/threading design; production composition must still establish coherent constants across the witness, payload checks and block, including their availability before block-header validation.

## 7. Proof dependency diagram and discharge table

```mermaid
flowchart TD
  B[Base observer and checked arithmetic laws] --> C[Codec and concrete hash laws]
  B --> F[Field and curve bridges]
  F --> P[Pairing and precompile correspondence]
  B --> S[State lifetimes and reachable trace invariants]
  C --> T[Trie and state commitment agreement]
  S --> T
  S --> V[Core and opcode refinement]
  C --> V
  V --> R[Runner and four fuel guarantees]
  P --> R
  R --> E[Block trace simulation and error projection]
  T --> E
  E --> G[Guest phase and 43-byte output equation]
  C --> G
  G --> SEC[Conditional stateless to stateful security]
  A[External chain anchor and oracle assumptions] --> SEC
```

This is a proof dependency graph, not the core import graph; in particular State does not import commitments. All nodes are obligations until their module laws and arguments are discharged.

| Premise | Producer | Consumer | Current discharge |
|---|---|---|---|
| Integer/byte/model equations | Base | all layers | partial discharge: implemented primitive model laws in [EthBase §3](modules/EthBase.md#3-eels-source-map); remaining premises in EthBase §10 |
| Canonical codecs and actual schema domains | Codec + record owners | Guest, Commit, Block | schemas/layout catalogued; inverses/domain proof open |
| Valid curve/pairing and exact adapters | Field/Curve/Pairing + bridges | Precompiles/Runner/Block | conditional arguments; concrete proofs open |
| Reachability, ordered diff and rollback | State + Block/Instructions/Runner | Witness/BAL/block simulation | API revised; caller induction open |
| Canonical vs accepted witness agreement | Commit/StateCommit/Witness | Security | counterexamples reproduced; extractors/commutation open |
| Whole-iteration progress and context WF | Core/Instructions/Runner/Fork | checked guest | candidate bound; fuel-adequacy investigation required ([REVIEW §7](REVIEW.md#7-acceptance-criteria-proof-gates-composition-cases-replacement-and-cost-checks) G2–G7) |
| Exact outcome projection | each semantic owner; Conformance coordinates X1 | Stateless | shared channels aligned; exhaustive site classification open |
| Backend progress/authenticity | Full + fixture/pre-state construction | block simulation | premises explicit; implementation/proof open |
| Anchors and oracle coupling | consumer + Security | security conclusion | external anchor specified; D5 coupling open |

An implementation is ready for a claimed end-to-end theorem only when every required premise has a producer and a discharged proof. Markdown argument sections and mechanical document checks are necessary scaffolding; they cannot guarantee the truth of an unproved premise.

### Local security RLP reference support

`ToVCVio` (security package only; owning [guidance](modules/ToVCVio.md) §§5/7) consumes existing core canonical RLP, exact hash-byte and `InternalNode` contracts. Its child threshold uses the complete encoded list; empty absence, inline lists and digest bytes remain distinct. Its explicit `QueryMorphism` preserves pure/bind and the chosen full query action for this kernel. The actual core adapter uses the installed `KeccakQuery` on both sides, recursive complete Encodable and list shape, and `LawfulMonad`; an unrelated callback additionally needs full action equality at that exact preimage. Equal digest values alone do not couple failure/state. Same-h raw-pair extraction performs no additional query and has conditional soundness, not whole-map binding. Executable certificate/derivation construction and actual reference/effect realization, map uniqueness, witness provenance, X7 generic provider/model coupling, an installed VCV-io QueryHom adapter and budgets remain open. No arbitrary direct-style transport follows from a generic capability type.

The same local guidance supplies a faithful nonrecursive Patricia shell, complete assembled/preimage injection and a separate finite resolved canonical shape. `LocallyAdmissible` reference widths/counts do not resolve hidden child kind. Safe pure prepared images have nonempty encoded values under the public lawful key/value/safety premises, without an unsecured premise; this gives no concrete encoder injectivity or frontend policy. Total C7 empty-terminal ambiguity is retained. Executable recursive derivation construction and actual C7/effect realization, canonical map uniqueness/binding and witness agreement remain open. A later empty/nonempty collision extractor additionally needs actual empty-root coherence.

The local `PatriciaStructure` seam (ToVCVio §§5/7) supplies exact finite prefix removal, mutually structural resolved tree/optional-root lookup, packed join with ordinary List model equality, and one-step outer prefix compression. Lookup preservation is unconditional; shape preservation requires the actual `Canonical` predicate. Full byte observation follows the joined-prefix law. Empty core values, lenient witness behavior and witness data/default/acquisition effects remain under their existing owners. The local `PatriciaSupport` laws supply complete supported keys for actual canonical finite trees and two distinct complete keys for canonical branches, including repeated identical children and equal values. They retain child canonicality and terminal-inclusive occupancy and provide no runtime witness selector. The `PatriciaExtensionality` seam (ToVCVio §§5/7) supplies canonical resolved-tree observational extensionality: both actual canonicality premises and all-finite full optional values/bytes remain explicit. The local `PatriciaRealization` seam (ToVCVio §§5/7) supplies ordinary Prop existence of a canonical optional resolved root for every actual finite map satisfying `NonemptyValues`, including the empty map, with exact full optional bytes at every finite key. All construction support remains private. No runtime map canonicalizer, normalization, public resolved-map uniqueness corollary, executable C7/C6 reference/effect realization, C8 hashing/source agreement or binding claim follows.

The local `PatriciaReference` seam (ToVCVio §§5/7) adds mutually structural Prop node/optional-child interpretation under one fixed deterministic hash proof model. Five constructors preserve complete paths/nonempty values, extension segments, terminal presence and every original numeric slot. Every present child carries the complete assembled `FitsRlp` certificate and uses the existing actual `asListNode`/`refWithHash`; the three conditional laws give reference admissibility, occupied=optional presence, and `Canonical` plus node derivation implies local shell admissibility. All count/vector adapters stay private. Top Fits remains separate from bare node derivation; the logical domain seam below characterizes inhabitation exactly; equal values/repeated children/zero digest answers are permitted. Actual C7 map/maximal-prefix/partition/value-encoding equality, per-child interleaving/action/failure correspondence, unconditional C8 top hashing, supplied empty-root coherence, witness provenance and X7/security/budgets/cost/readiness remain open.

The local `PatriciaRlpDomain` seam (ToVCVio §§5/7; Q56) supplies total
noncomputable logical payload/node/reference widths and noncircular complete C and
strict-descendant D. Three ordinary conditional width laws retain exact public
assembly/HP/threshold premises; three equivalences characterize D with bare Node,
C with Node plus whole Fits, and C with present Ref for every fixed pure h. Every
original numeric child occurrence, full value and terminal tag is preserved;
canonicality/injectivity are not added. Payload bounds do not impose a complete
encoded-width cap. This is logical support only: executable width extraction,
general HP flag simplification, runtime witness construction and actual map/C7/C6/
effect/C8/empty-root/F20/D5/witness/security/budget/cost agreement remain separate.
