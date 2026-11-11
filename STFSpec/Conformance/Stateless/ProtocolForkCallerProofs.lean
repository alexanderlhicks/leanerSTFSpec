/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Stateless

/-!
# Protocol fork facade clients

Library `EthConformance`. Private complete type, dependent elimination, branch,
mapping and injectivity clients for historical metadata.
Spec guidance: `STFSpec/informal/modules/EthStateless.md` §§3/4/5/7.
-/

namespace STFSpec.Conformance.Stateless.ProtocolForkCallerProofs

open STFSpec.Stateless

universe u

private def frontierConstructor : ProtocolFork := ProtocolFork.frontier
private def homesteadConstructor : ProtocolFork := ProtocolFork.homestead
private def daoForkConstructor : ProtocolFork := ProtocolFork.daoFork
private def tangerineWhistleConstructor : ProtocolFork := ProtocolFork.tangerineWhistle
private def spuriousDragonConstructor : ProtocolFork := ProtocolFork.spuriousDragon
private def byzantiumConstructor : ProtocolFork := ProtocolFork.byzantium
private def stPetersburgConstructor : ProtocolFork := ProtocolFork.stPetersburg
private def istanbulConstructor : ProtocolFork := ProtocolFork.istanbul
private def muirGlacierConstructor : ProtocolFork := ProtocolFork.muirGlacier
private def berlinConstructor : ProtocolFork := ProtocolFork.berlin
private def londonConstructor : ProtocolFork := ProtocolFork.london
private def arrowGlacierConstructor : ProtocolFork := ProtocolFork.arrowGlacier
private def grayGlacierConstructor : ProtocolFork := ProtocolFork.grayGlacier
private def parisConstructor : ProtocolFork := ProtocolFork.paris
private def shanghaiConstructor : ProtocolFork := ProtocolFork.shanghai
private def cancunConstructor : ProtocolFork := ProtocolFork.cancun
private def pragueConstructor : ProtocolFork := ProtocolFork.prague
private def osakaConstructor : ProtocolFork := ProtocolFork.osaka
private def bpo1Constructor : ProtocolFork := ProtocolFork.bpo1
private def bpo2Constructor : ProtocolFork := ProtocolFork.bpo2
private def amsterdamConstructor : ProtocolFork := ProtocolFork.amsterdam

private def observerType : ProtocolFork → UInt8 := ProtocolFork.toIndex

private theorem frontier_index : ProtocolFork.frontier.toIndex = 0x01 := rfl
private theorem homestead_index : ProtocolFork.homestead.toIndex = 0x02 := rfl
private theorem dao_fork_index : ProtocolFork.daoFork.toIndex = 0x03 := rfl
private theorem tangerine_whistle_index : ProtocolFork.tangerineWhistle.toIndex = 0x04 := rfl
private theorem spurious_dragon_index : ProtocolFork.spuriousDragon.toIndex = 0x05 := rfl
private theorem byzantium_index : ProtocolFork.byzantium.toIndex = 0x06 := rfl
private theorem st_petersburg_index : ProtocolFork.stPetersburg.toIndex = 0x07 := rfl
private theorem istanbul_index : ProtocolFork.istanbul.toIndex = 0x08 := rfl
private theorem muir_glacier_index : ProtocolFork.muirGlacier.toIndex = 0x09 := rfl
private theorem berlin_index : ProtocolFork.berlin.toIndex = 0x0a := rfl
private theorem london_index : ProtocolFork.london.toIndex = 0x0b := rfl
private theorem arrow_glacier_index : ProtocolFork.arrowGlacier.toIndex = 0x0c := rfl
private theorem gray_glacier_index : ProtocolFork.grayGlacier.toIndex = 0x0d := rfl
private theorem paris_index : ProtocolFork.paris.toIndex = 0x0e := rfl
private theorem shanghai_index : ProtocolFork.shanghai.toIndex = 0x0f := rfl
private theorem cancun_index : ProtocolFork.cancun.toIndex = 0x10 := rfl
private theorem prague_index : ProtocolFork.prague.toIndex = 0x11 := rfl
private theorem osaka_index : ProtocolFork.osaka.toIndex = 0x12 := rfl
private theorem bpo1_index : ProtocolFork.bpo1.toIndex = 0x13 := rfl
private theorem bpo2_index : ProtocolFork.bpo2.toIndex = 0x14 := rfl
private theorem amsterdam_index : ProtocolFork.amsterdam.toIndex = 0x15 := rfl

private def eliminate {P : ProtocolFork → Sort u}
    (frontier : P .frontier)
    (homestead : P .homestead)
    (daoFork : P .daoFork)
    (tangerineWhistle : P .tangerineWhistle)
    (spuriousDragon : P .spuriousDragon)
    (byzantium : P .byzantium)
    (stPetersburg : P .stPetersburg)
    (istanbul : P .istanbul)
    (muirGlacier : P .muirGlacier)
    (berlin : P .berlin)
    (london : P .london)
    (arrowGlacier : P .arrowGlacier)
    (grayGlacier : P .grayGlacier)
    (paris : P .paris)
    (shanghai : P .shanghai)
    (cancun : P .cancun)
    (prague : P .prague)
    (osaka : P .osaka)
    (bpo1 : P .bpo1)
    (bpo2 : P .bpo2)
    (amsterdam : P .amsterdam)
    (fork : ProtocolFork) : P fork :=
  match fork with
  | .frontier => frontier
  | .homestead => homestead
  | .daoFork => daoFork
  | .tangerineWhistle => tangerineWhistle
  | .spuriousDragon => spuriousDragon
  | .byzantium => byzantium
  | .stPetersburg => stPetersburg
  | .istanbul => istanbul
  | .muirGlacier => muirGlacier
  | .berlin => berlin
  | .london => london
  | .arrowGlacier => arrowGlacier
  | .grayGlacier => grayGlacier
  | .paris => paris
  | .shanghai => shanghai
  | .cancun => cancun
  | .prague => prague
  | .osaka => osaka
  | .bpo1 => bpo1
  | .bpo2 => bpo2
  | .amsterdam => amsterdam

section

variable {P : ProtocolFork → Sort u}
    (frontier : P .frontier)
    (homestead : P .homestead)
    (daoFork : P .daoFork)
    (tangerineWhistle : P .tangerineWhistle)
    (spuriousDragon : P .spuriousDragon)
    (byzantium : P .byzantium)
    (stPetersburg : P .stPetersburg)
    (istanbul : P .istanbul)
    (muirGlacier : P .muirGlacier)
    (berlin : P .berlin)
    (london : P .london)
    (arrowGlacier : P .arrowGlacier)
    (grayGlacier : P .grayGlacier)
    (paris : P .paris)
    (shanghai : P .shanghai)
    (cancun : P .cancun)
    (prague : P .prague)
    (osaka : P .osaka)
    (bpo1 : P .bpo1)
    (bpo2 : P .bpo2)
    (amsterdam : P .amsterdam)

private theorem eliminate_frontier_branch :
    eliminate
      frontier homestead daoFork tangerineWhistle
      spuriousDragon byzantium stPetersburg istanbul
      muirGlacier berlin london arrowGlacier
      grayGlacier paris shanghai cancun
      prague osaka bpo1 bpo2
      amsterdam
      .frontier = frontier := rfl

private theorem eliminate_homestead_branch :
    eliminate
      frontier homestead daoFork tangerineWhistle
      spuriousDragon byzantium stPetersburg istanbul
      muirGlacier berlin london arrowGlacier
      grayGlacier paris shanghai cancun
      prague osaka bpo1 bpo2
      amsterdam
      .homestead = homestead := rfl

private theorem eliminate_dao_fork_branch :
    eliminate
      frontier homestead daoFork tangerineWhistle
      spuriousDragon byzantium stPetersburg istanbul
      muirGlacier berlin london arrowGlacier
      grayGlacier paris shanghai cancun
      prague osaka bpo1 bpo2
      amsterdam
      .daoFork = daoFork := rfl

private theorem eliminate_tangerine_whistle_branch :
    eliminate
      frontier homestead daoFork tangerineWhistle
      spuriousDragon byzantium stPetersburg istanbul
      muirGlacier berlin london arrowGlacier
      grayGlacier paris shanghai cancun
      prague osaka bpo1 bpo2
      amsterdam
      .tangerineWhistle = tangerineWhistle := rfl

private theorem eliminate_spurious_dragon_branch :
    eliminate
      frontier homestead daoFork tangerineWhistle
      spuriousDragon byzantium stPetersburg istanbul
      muirGlacier berlin london arrowGlacier
      grayGlacier paris shanghai cancun
      prague osaka bpo1 bpo2
      amsterdam
      .spuriousDragon = spuriousDragon := rfl

private theorem eliminate_byzantium_branch :
    eliminate
      frontier homestead daoFork tangerineWhistle
      spuriousDragon byzantium stPetersburg istanbul
      muirGlacier berlin london arrowGlacier
      grayGlacier paris shanghai cancun
      prague osaka bpo1 bpo2
      amsterdam
      .byzantium = byzantium := rfl

private theorem eliminate_st_petersburg_branch :
    eliminate
      frontier homestead daoFork tangerineWhistle
      spuriousDragon byzantium stPetersburg istanbul
      muirGlacier berlin london arrowGlacier
      grayGlacier paris shanghai cancun
      prague osaka bpo1 bpo2
      amsterdam
      .stPetersburg = stPetersburg := rfl

private theorem eliminate_istanbul_branch :
    eliminate
      frontier homestead daoFork tangerineWhistle
      spuriousDragon byzantium stPetersburg istanbul
      muirGlacier berlin london arrowGlacier
      grayGlacier paris shanghai cancun
      prague osaka bpo1 bpo2
      amsterdam
      .istanbul = istanbul := rfl

private theorem eliminate_muir_glacier_branch :
    eliminate
      frontier homestead daoFork tangerineWhistle
      spuriousDragon byzantium stPetersburg istanbul
      muirGlacier berlin london arrowGlacier
      grayGlacier paris shanghai cancun
      prague osaka bpo1 bpo2
      amsterdam
      .muirGlacier = muirGlacier := rfl

private theorem eliminate_berlin_branch :
    eliminate
      frontier homestead daoFork tangerineWhistle
      spuriousDragon byzantium stPetersburg istanbul
      muirGlacier berlin london arrowGlacier
      grayGlacier paris shanghai cancun
      prague osaka bpo1 bpo2
      amsterdam
      .berlin = berlin := rfl

private theorem eliminate_london_branch :
    eliminate
      frontier homestead daoFork tangerineWhistle
      spuriousDragon byzantium stPetersburg istanbul
      muirGlacier berlin london arrowGlacier
      grayGlacier paris shanghai cancun
      prague osaka bpo1 bpo2
      amsterdam
      .london = london := rfl

private theorem eliminate_arrow_glacier_branch :
    eliminate
      frontier homestead daoFork tangerineWhistle
      spuriousDragon byzantium stPetersburg istanbul
      muirGlacier berlin london arrowGlacier
      grayGlacier paris shanghai cancun
      prague osaka bpo1 bpo2
      amsterdam
      .arrowGlacier = arrowGlacier := rfl

private theorem eliminate_gray_glacier_branch :
    eliminate
      frontier homestead daoFork tangerineWhistle
      spuriousDragon byzantium stPetersburg istanbul
      muirGlacier berlin london arrowGlacier
      grayGlacier paris shanghai cancun
      prague osaka bpo1 bpo2
      amsterdam
      .grayGlacier = grayGlacier := rfl

private theorem eliminate_paris_branch :
    eliminate
      frontier homestead daoFork tangerineWhistle
      spuriousDragon byzantium stPetersburg istanbul
      muirGlacier berlin london arrowGlacier
      grayGlacier paris shanghai cancun
      prague osaka bpo1 bpo2
      amsterdam
      .paris = paris := rfl

private theorem eliminate_shanghai_branch :
    eliminate
      frontier homestead daoFork tangerineWhistle
      spuriousDragon byzantium stPetersburg istanbul
      muirGlacier berlin london arrowGlacier
      grayGlacier paris shanghai cancun
      prague osaka bpo1 bpo2
      amsterdam
      .shanghai = shanghai := rfl

private theorem eliminate_cancun_branch :
    eliminate
      frontier homestead daoFork tangerineWhistle
      spuriousDragon byzantium stPetersburg istanbul
      muirGlacier berlin london arrowGlacier
      grayGlacier paris shanghai cancun
      prague osaka bpo1 bpo2
      amsterdam
      .cancun = cancun := rfl

private theorem eliminate_prague_branch :
    eliminate
      frontier homestead daoFork tangerineWhistle
      spuriousDragon byzantium stPetersburg istanbul
      muirGlacier berlin london arrowGlacier
      grayGlacier paris shanghai cancun
      prague osaka bpo1 bpo2
      amsterdam
      .prague = prague := rfl

private theorem eliminate_osaka_branch :
    eliminate
      frontier homestead daoFork tangerineWhistle
      spuriousDragon byzantium stPetersburg istanbul
      muirGlacier berlin london arrowGlacier
      grayGlacier paris shanghai cancun
      prague osaka bpo1 bpo2
      amsterdam
      .osaka = osaka := rfl

private theorem eliminate_bpo1_branch :
    eliminate
      frontier homestead daoFork tangerineWhistle
      spuriousDragon byzantium stPetersburg istanbul
      muirGlacier berlin london arrowGlacier
      grayGlacier paris shanghai cancun
      prague osaka bpo1 bpo2
      amsterdam
      .bpo1 = bpo1 := rfl

private theorem eliminate_bpo2_branch :
    eliminate
      frontier homestead daoFork tangerineWhistle
      spuriousDragon byzantium stPetersburg istanbul
      muirGlacier berlin london arrowGlacier
      grayGlacier paris shanghai cancun
      prague osaka bpo1 bpo2
      amsterdam
      .bpo2 = bpo2 := rfl

private theorem eliminate_amsterdam_branch :
    eliminate
      frontier homestead daoFork tangerineWhistle
      spuriousDragon byzantium stPetersburg istanbul
      muirGlacier berlin london arrowGlacier
      grayGlacier paris shanghai cancun
      prague osaka bpo1 bpo2
      amsterdam
      .amsterdam = amsterdam := rfl

end

private theorem complete_mapping (fork : ProtocolFork) :
    fork.toIndex = match fork with
      | .frontier => (0x01 : UInt8)
      | .homestead => 0x02
      | .daoFork => 0x03
      | .tangerineWhistle => 0x04
      | .spuriousDragon => 0x05
      | .byzantium => 0x06
      | .stPetersburg => 0x07
      | .istanbul => 0x08
      | .muirGlacier => 0x09
      | .berlin => 0x0a
      | .london => 0x0b
      | .arrowGlacier => 0x0c
      | .grayGlacier => 0x0d
      | .paris => 0x0e
      | .shanghai => 0x0f
      | .cancun => 0x10
      | .prague => 0x11
      | .osaka => 0x12
      | .bpo1 => 0x13
      | .bpo2 => 0x14
      | .amsterdam => 0x15 := by
  cases fork <;> rfl

private theorem tag_injective (a b : ProtocolFork) (h : a.toIndex = b.toIndex) :
    a = b := by
  cases a <;> cases b <;> simp_all [ProtocolFork.toIndex]

end STFSpec.Conformance.Stateless.ProtocolForkCallerProofs
