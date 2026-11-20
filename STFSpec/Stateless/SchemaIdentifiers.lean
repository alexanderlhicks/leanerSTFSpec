/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Fork.Amsterdam.SchemaIdentifiers
import STFSpec.Stateless.ProtocolFork
import Init.Data.Vector.Basic
import Init.Omega

/-!
# Stateless input schema identifier aliases

Library `EthStateless`. A nominal selector from the Fork-owned raw tag and transparent
aliases of the remaining selected data. The finite transport is private and bounded.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3–7.
-/

namespace STFSpec.Stateless

-- Explicit source-tag order, independent of compiler constructor ordinals.
private def supportedForks : Vector ProtocolFork 21 :=
  ⟨#[.frontier, .homestead, .daoFork, .tangerineWhistle, .spuriousDragon, .byzantium,
    .stPetersburg, .istanbul, .muirGlacier, .berlin, .london, .arrowGlacier, .grayGlacier,
    .paris, .shanghai, .cancun, .prague, .osaka, .bpo1, .bpo2, .amsterdam], rfl⟩

private def pick (index : UInt8) (h : 1 ≤ index.toNat ∧ index.toNat ≤ 21) : ProtocolFork :=
  supportedForks[index.toNat - 1]'(by omega)

private theorem pick_toIndex (index : UInt8) (h : 1 ≤ index.toNat ∧ index.toNat ≤ 21) :
    (pick index h).toIndex = index := by
  have supported :
      index.toNat = 1 ∨ index.toNat = 2 ∨ index.toNat = 3 ∨ index.toNat = 4 ∨
      index.toNat = 5 ∨ index.toNat = 6 ∨ index.toNat = 7 ∨ index.toNat = 8 ∨
      index.toNat = 9 ∨ index.toNat = 10 ∨ index.toNat = 11 ∨ index.toNat = 12 ∨
      index.toNat = 13 ∨ index.toNat = 14 ∨ index.toNat = 15 ∨ index.toNat = 16 ∨
      index.toNat = 17 ∨ index.toNat = 18 ∨ index.toNat = 19 ∨ index.toNat = 20 ∨
      index.toNat = 21 := by omega
  rcases supported with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn |
    hn | hn | hn | hn | hn | hn | hn | hn | hn
  all_goals
    apply UInt8.toNat_inj.mp
    simp [pick, supportedForks, hn, ProtocolFork.toIndex]

private theorem pick_proof_irrelevance (index : UInt8)
    (h₁ h₂ : 1 ≤ index.toNat ∧ index.toNat ≤ 21) : pick index h₁ = pick index h₂ := rfl

-- A configured unsupported tag cannot discharge this local proof.
private theorem selected_bound :
    1 ≤ Fork.Amsterdam.STATELESS_INPUT_SCHEMA_FORK_INDEX.toNat ∧
    Fork.Amsterdam.STATELESS_INPUT_SCHEMA_FORK_INDEX.toNat ≤ 21 := by decide

/-- Nominal selected fork, transported from the Fork-owned raw tag; EELS
`src/ethereum/forks/amsterdam/stateless.py:129` at the pin. -/
def schemaForkIndex : ProtocolFork :=
  pick Fork.Amsterdam.STATELESS_INPUT_SCHEMA_FORK_INDEX selected_bound

/-- Alias of the owned revision; EELS
`src/ethereum/forks/amsterdam/stateless.py:130` at the pin. -/
abbrev schemaRevision : UInt8 := Fork.Amsterdam.STATELESS_INPUT_SCHEMA_REVISION

/-- Alias of the owned ID; EELS
`src/ethereum/forks/amsterdam/stateless.py:131–133` at the pin. -/
abbrev schemaId : UInt16 := Fork.Amsterdam.STATELESS_INPUT_SCHEMA_ID

/-- Alias of the owned prefix width; EELS
`src/ethereum/forks/amsterdam/stateless.py:134` at the pin. -/
abbrev schemaIdSize : Nat := Fork.Amsterdam.STATELESS_INPUT_SCHEMA_ID_SIZE

/-- Alias of the complete owned big-endian prefix; EELS
`src/ethereum/forks/amsterdam/stateless.py:135–138` at the pin. -/
abbrev schemaIdBytes : ByteArray := Fork.Amsterdam.STATELESS_INPUT_SCHEMA_ID_BYTES

private theorem selected_coherence :
    schemaForkIndex.toIndex = Fork.Amsterdam.STATELESS_INPUT_SCHEMA_FORK_INDEX :=
  pick_toIndex _ _

private theorem id_coherence : schemaId =
    (schemaForkIndex.toIndex.toUInt16 <<< 8) ||| schemaRevision.toUInt16 := by
  rw [selected_coherence]
  rfl

private theorem bytes_coherence :
    schemaIdBytes = ⟨#[schemaForkIndex.toIndex, schemaRevision]⟩ := by
  rw [selected_coherence]
  decide

private theorem bytes_size : schemaIdBytes.size = schemaIdSize := rfl

end STFSpec.Stateless
