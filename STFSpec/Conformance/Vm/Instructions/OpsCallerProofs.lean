/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Instructions

/-!
# Opcode facade clients and complete literal byte controls

Library `EthConformance`. Every expected byte/member pair and hole is bound to
pinned EELS `src/ethereum/forks/amsterdam/vm/instructions/__init__.py:32–220`.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Instructions.OpsCallerProofs
open STFSpec.Vm.Instructions

private def encoder : Ops → UInt8 := Ops.toByte
private def decoder : UInt8 → Option Ops := Ops.ofByte?

private theorem opcode_roundtrip (o : Ops) : decoder (encoder o) = some o :=
  Ops.ofByte_toByte o

private theorem byte_roundtrip (b : UInt8) (o : Ops) (h : decoder b = some o) :
    encoder o = b := Ops.toByte_ofByte b o h

-- Consumer consequences use only the two public laws.
private theorem encoder_injective (o p : Ops) (h : encoder o = encoder p) : o = p := by
  have hd := congrArg decoder h
  rw [opcode_roundtrip, opcode_roundtrip] at hd
  exact Option.some.inj hd

private theorem absent_byte (b : UInt8) (h : decoder b = none) (o : Ops) :
    encoder o ≠ b := by
  intro he
  have hd := opcode_roundtrip o
  rw [he, h] at hd
  cases hd

-- Exhaustive constructor coverage plus 153 independently literal encoder pairs.
private theorem encoder_pairs (o : Ops) :
    encoder o = match o with
      | .add => 0x01
      | .mul => 0x02
      | .sub => 0x03
      | .div => 0x04
      | .sdiv => 0x05
      | .mod => 0x06
      | .smod => 0x07
      | .addmod => 0x08
      | .mulmod => 0x09
      | .exp => 0x0A
      | .signextend => 0x0B
      | .lt => 0x10
      | .gt => 0x11
      | .slt => 0x12
      | .sgt => 0x13
      | .eq => 0x14
      | .iszero => 0x15
      | .and => 0x16
      | .or => 0x17
      | .xor => 0x18
      | .not => 0x19
      | .byte => 0x1A
      | .shl => 0x1B
      | .shr => 0x1C
      | .sar => 0x1D
      | .clz => 0x1E
      | .keccak => 0x20
      | .address => 0x30
      | .balance => 0x31
      | .origin => 0x32
      | .caller => 0x33
      | .callvalue => 0x34
      | .calldataload => 0x35
      | .calldatasize => 0x36
      | .calldatacopy => 0x37
      | .codesize => 0x38
      | .codecopy => 0x39
      | .gasprice => 0x3A
      | .extcodesize => 0x3B
      | .extcodecopy => 0x3C
      | .returndatasize => 0x3D
      | .returndatacopy => 0x3E
      | .extcodehash => 0x3F
      | .blockhash => 0x40
      | .coinbase => 0x41
      | .timestamp => 0x42
      | .number => 0x43
      | .prevrandao => 0x44
      | .gaslimit => 0x45
      | .chainid => 0x46
      | .selfbalance => 0x47
      | .basefee => 0x48
      | .blobhash => 0x49
      | .blobbasefee => 0x4A
      | .slotnum => 0x4B
      | .stop => 0x00
      | .jump => 0x56
      | .jumpi => 0x57
      | .pc => 0x58
      | .gas => 0x5A
      | .jumpdest => 0x5B
      | .sload => 0x54
      | .sstore => 0x55
      | .tload => 0x5C
      | .tstore => 0x5D
      | .pop => 0x50
      | .push0 => 0x5F
      | .push1 => 0x60
      | .push2 => 0x61
      | .push3 => 0x62
      | .push4 => 0x63
      | .push5 => 0x64
      | .push6 => 0x65
      | .push7 => 0x66
      | .push8 => 0x67
      | .push9 => 0x68
      | .push10 => 0x69
      | .push11 => 0x6A
      | .push12 => 0x6B
      | .push13 => 0x6C
      | .push14 => 0x6D
      | .push15 => 0x6E
      | .push16 => 0x6F
      | .push17 => 0x70
      | .push18 => 0x71
      | .push19 => 0x72
      | .push20 => 0x73
      | .push21 => 0x74
      | .push22 => 0x75
      | .push23 => 0x76
      | .push24 => 0x77
      | .push25 => 0x78
      | .push26 => 0x79
      | .push27 => 0x7A
      | .push28 => 0x7B
      | .push29 => 0x7C
      | .push30 => 0x7D
      | .push31 => 0x7E
      | .push32 => 0x7F
      | .dup1 => 0x80
      | .dup2 => 0x81
      | .dup3 => 0x82
      | .dup4 => 0x83
      | .dup5 => 0x84
      | .dup6 => 0x85
      | .dup7 => 0x86
      | .dup8 => 0x87
      | .dup9 => 0x88
      | .dup10 => 0x89
      | .dup11 => 0x8A
      | .dup12 => 0x8B
      | .dup13 => 0x8C
      | .dup14 => 0x8D
      | .dup15 => 0x8E
      | .dup16 => 0x8F
      | .swap1 => 0x90
      | .swap2 => 0x91
      | .swap3 => 0x92
      | .swap4 => 0x93
      | .swap5 => 0x94
      | .swap6 => 0x95
      | .swap7 => 0x96
      | .swap8 => 0x97
      | .swap9 => 0x98
      | .swap10 => 0x99
      | .swap11 => 0x9A
      | .swap12 => 0x9B
      | .swap13 => 0x9C
      | .swap14 => 0x9D
      | .swap15 => 0x9E
      | .swap16 => 0x9F
      | .dupn => 0xE6
      | .swapn => 0xE7
      | .exchange => 0xE8
      | .mload => 0x51
      | .mstore => 0x52
      | .mstore8 => 0x53
      | .msize => 0x59
      | .mcopy => 0x5E
      | .log0 => 0xA0
      | .log1 => 0xA1
      | .log2 => 0xA2
      | .log3 => 0xA3
      | .log4 => 0xA4
      | .create => 0xF0
      | .call => 0xF1
      | .callcode => 0xF2
      | .return_ => 0xF3
      | .delegatecall => 0xF4
      | .create2 => 0xF5
      | .staticcall => 0xFA
      | .revert => 0xFD
      | .selfdestruct => 0xFF
  := by
  cases o <;> rfl

private theorem decode_00 : decoder (0x00 : UInt8) = some .stop := rfl
private theorem decode_01 : decoder (0x01 : UInt8) = some .add := rfl
private theorem decode_02 : decoder (0x02 : UInt8) = some .mul := rfl
private theorem decode_03 : decoder (0x03 : UInt8) = some .sub := rfl
private theorem decode_04 : decoder (0x04 : UInt8) = some .div := rfl
private theorem decode_05 : decoder (0x05 : UInt8) = some .sdiv := rfl
private theorem decode_06 : decoder (0x06 : UInt8) = some .mod := rfl
private theorem decode_07 : decoder (0x07 : UInt8) = some .smod := rfl
private theorem decode_08 : decoder (0x08 : UInt8) = some .addmod := rfl
private theorem decode_09 : decoder (0x09 : UInt8) = some .mulmod := rfl
private theorem decode_0a : decoder (0x0A : UInt8) = some .exp := rfl
private theorem decode_0b : decoder (0x0B : UInt8) = some .signextend := rfl
private theorem decode_0c : decoder (0x0C : UInt8) = none := rfl
private theorem decode_0d : decoder (0x0D : UInt8) = none := rfl
private theorem decode_0e : decoder (0x0E : UInt8) = none := rfl
private theorem decode_0f : decoder (0x0F : UInt8) = none := rfl
private theorem decode_10 : decoder (0x10 : UInt8) = some .lt := rfl
private theorem decode_11 : decoder (0x11 : UInt8) = some .gt := rfl
private theorem decode_12 : decoder (0x12 : UInt8) = some .slt := rfl
private theorem decode_13 : decoder (0x13 : UInt8) = some .sgt := rfl
private theorem decode_14 : decoder (0x14 : UInt8) = some .eq := rfl
private theorem decode_15 : decoder (0x15 : UInt8) = some .iszero := rfl
private theorem decode_16 : decoder (0x16 : UInt8) = some .and := rfl
private theorem decode_17 : decoder (0x17 : UInt8) = some .or := rfl
private theorem decode_18 : decoder (0x18 : UInt8) = some .xor := rfl
private theorem decode_19 : decoder (0x19 : UInt8) = some .not := rfl
private theorem decode_1a : decoder (0x1A : UInt8) = some .byte := rfl
private theorem decode_1b : decoder (0x1B : UInt8) = some .shl := rfl
private theorem decode_1c : decoder (0x1C : UInt8) = some .shr := rfl
private theorem decode_1d : decoder (0x1D : UInt8) = some .sar := rfl
private theorem decode_1e : decoder (0x1E : UInt8) = some .clz := rfl
private theorem decode_1f : decoder (0x1F : UInt8) = none := rfl
private theorem decode_20 : decoder (0x20 : UInt8) = some .keccak := rfl
private theorem decode_21 : decoder (0x21 : UInt8) = none := rfl
private theorem decode_22 : decoder (0x22 : UInt8) = none := rfl
private theorem decode_23 : decoder (0x23 : UInt8) = none := rfl
private theorem decode_24 : decoder (0x24 : UInt8) = none := rfl
private theorem decode_25 : decoder (0x25 : UInt8) = none := rfl
private theorem decode_26 : decoder (0x26 : UInt8) = none := rfl
private theorem decode_27 : decoder (0x27 : UInt8) = none := rfl
private theorem decode_28 : decoder (0x28 : UInt8) = none := rfl
private theorem decode_29 : decoder (0x29 : UInt8) = none := rfl
private theorem decode_2a : decoder (0x2A : UInt8) = none := rfl
private theorem decode_2b : decoder (0x2B : UInt8) = none := rfl
private theorem decode_2c : decoder (0x2C : UInt8) = none := rfl
private theorem decode_2d : decoder (0x2D : UInt8) = none := rfl
private theorem decode_2e : decoder (0x2E : UInt8) = none := rfl
private theorem decode_2f : decoder (0x2F : UInt8) = none := rfl
private theorem decode_30 : decoder (0x30 : UInt8) = some .address := rfl
private theorem decode_31 : decoder (0x31 : UInt8) = some .balance := rfl
private theorem decode_32 : decoder (0x32 : UInt8) = some .origin := rfl
private theorem decode_33 : decoder (0x33 : UInt8) = some .caller := rfl
private theorem decode_34 : decoder (0x34 : UInt8) = some .callvalue := rfl
private theorem decode_35 : decoder (0x35 : UInt8) = some .calldataload := rfl
private theorem decode_36 : decoder (0x36 : UInt8) = some .calldatasize := rfl
private theorem decode_37 : decoder (0x37 : UInt8) = some .calldatacopy := rfl
private theorem decode_38 : decoder (0x38 : UInt8) = some .codesize := rfl
private theorem decode_39 : decoder (0x39 : UInt8) = some .codecopy := rfl
private theorem decode_3a : decoder (0x3A : UInt8) = some .gasprice := rfl
private theorem decode_3b : decoder (0x3B : UInt8) = some .extcodesize := rfl
private theorem decode_3c : decoder (0x3C : UInt8) = some .extcodecopy := rfl
private theorem decode_3d : decoder (0x3D : UInt8) = some .returndatasize := rfl
private theorem decode_3e : decoder (0x3E : UInt8) = some .returndatacopy := rfl
private theorem decode_3f : decoder (0x3F : UInt8) = some .extcodehash := rfl
private theorem decode_40 : decoder (0x40 : UInt8) = some .blockhash := rfl
private theorem decode_41 : decoder (0x41 : UInt8) = some .coinbase := rfl
private theorem decode_42 : decoder (0x42 : UInt8) = some .timestamp := rfl
private theorem decode_43 : decoder (0x43 : UInt8) = some .number := rfl
private theorem decode_44 : decoder (0x44 : UInt8) = some .prevrandao := rfl
private theorem decode_45 : decoder (0x45 : UInt8) = some .gaslimit := rfl
private theorem decode_46 : decoder (0x46 : UInt8) = some .chainid := rfl
private theorem decode_47 : decoder (0x47 : UInt8) = some .selfbalance := rfl
private theorem decode_48 : decoder (0x48 : UInt8) = some .basefee := rfl
private theorem decode_49 : decoder (0x49 : UInt8) = some .blobhash := rfl
private theorem decode_4a : decoder (0x4A : UInt8) = some .blobbasefee := rfl
private theorem decode_4b : decoder (0x4B : UInt8) = some .slotnum := rfl
private theorem decode_4c : decoder (0x4C : UInt8) = none := rfl
private theorem decode_4d : decoder (0x4D : UInt8) = none := rfl
private theorem decode_4e : decoder (0x4E : UInt8) = none := rfl
private theorem decode_4f : decoder (0x4F : UInt8) = none := rfl
private theorem decode_50 : decoder (0x50 : UInt8) = some .pop := rfl
private theorem decode_51 : decoder (0x51 : UInt8) = some .mload := rfl
private theorem decode_52 : decoder (0x52 : UInt8) = some .mstore := rfl
private theorem decode_53 : decoder (0x53 : UInt8) = some .mstore8 := rfl
private theorem decode_54 : decoder (0x54 : UInt8) = some .sload := rfl
private theorem decode_55 : decoder (0x55 : UInt8) = some .sstore := rfl
private theorem decode_56 : decoder (0x56 : UInt8) = some .jump := rfl
private theorem decode_57 : decoder (0x57 : UInt8) = some .jumpi := rfl
private theorem decode_58 : decoder (0x58 : UInt8) = some .pc := rfl
private theorem decode_59 : decoder (0x59 : UInt8) = some .msize := rfl
private theorem decode_5a : decoder (0x5A : UInt8) = some .gas := rfl
private theorem decode_5b : decoder (0x5B : UInt8) = some .jumpdest := rfl
private theorem decode_5c : decoder (0x5C : UInt8) = some .tload := rfl
private theorem decode_5d : decoder (0x5D : UInt8) = some .tstore := rfl
private theorem decode_5e : decoder (0x5E : UInt8) = some .mcopy := rfl
private theorem decode_5f : decoder (0x5F : UInt8) = some .push0 := rfl
private theorem decode_60 : decoder (0x60 : UInt8) = some .push1 := rfl
private theorem decode_61 : decoder (0x61 : UInt8) = some .push2 := rfl
private theorem decode_62 : decoder (0x62 : UInt8) = some .push3 := rfl
private theorem decode_63 : decoder (0x63 : UInt8) = some .push4 := rfl
private theorem decode_64 : decoder (0x64 : UInt8) = some .push5 := rfl
private theorem decode_65 : decoder (0x65 : UInt8) = some .push6 := rfl
private theorem decode_66 : decoder (0x66 : UInt8) = some .push7 := rfl
private theorem decode_67 : decoder (0x67 : UInt8) = some .push8 := rfl
private theorem decode_68 : decoder (0x68 : UInt8) = some .push9 := rfl
private theorem decode_69 : decoder (0x69 : UInt8) = some .push10 := rfl
private theorem decode_6a : decoder (0x6A : UInt8) = some .push11 := rfl
private theorem decode_6b : decoder (0x6B : UInt8) = some .push12 := rfl
private theorem decode_6c : decoder (0x6C : UInt8) = some .push13 := rfl
private theorem decode_6d : decoder (0x6D : UInt8) = some .push14 := rfl
private theorem decode_6e : decoder (0x6E : UInt8) = some .push15 := rfl
private theorem decode_6f : decoder (0x6F : UInt8) = some .push16 := rfl
private theorem decode_70 : decoder (0x70 : UInt8) = some .push17 := rfl
private theorem decode_71 : decoder (0x71 : UInt8) = some .push18 := rfl
private theorem decode_72 : decoder (0x72 : UInt8) = some .push19 := rfl
private theorem decode_73 : decoder (0x73 : UInt8) = some .push20 := rfl
private theorem decode_74 : decoder (0x74 : UInt8) = some .push21 := rfl
private theorem decode_75 : decoder (0x75 : UInt8) = some .push22 := rfl
private theorem decode_76 : decoder (0x76 : UInt8) = some .push23 := rfl
private theorem decode_77 : decoder (0x77 : UInt8) = some .push24 := rfl
private theorem decode_78 : decoder (0x78 : UInt8) = some .push25 := rfl
private theorem decode_79 : decoder (0x79 : UInt8) = some .push26 := rfl
private theorem decode_7a : decoder (0x7A : UInt8) = some .push27 := rfl
private theorem decode_7b : decoder (0x7B : UInt8) = some .push28 := rfl
private theorem decode_7c : decoder (0x7C : UInt8) = some .push29 := rfl
private theorem decode_7d : decoder (0x7D : UInt8) = some .push30 := rfl
private theorem decode_7e : decoder (0x7E : UInt8) = some .push31 := rfl
private theorem decode_7f : decoder (0x7F : UInt8) = some .push32 := rfl
private theorem decode_80 : decoder (0x80 : UInt8) = some .dup1 := rfl
private theorem decode_81 : decoder (0x81 : UInt8) = some .dup2 := rfl
private theorem decode_82 : decoder (0x82 : UInt8) = some .dup3 := rfl
private theorem decode_83 : decoder (0x83 : UInt8) = some .dup4 := rfl
private theorem decode_84 : decoder (0x84 : UInt8) = some .dup5 := rfl
private theorem decode_85 : decoder (0x85 : UInt8) = some .dup6 := rfl
private theorem decode_86 : decoder (0x86 : UInt8) = some .dup7 := rfl
private theorem decode_87 : decoder (0x87 : UInt8) = some .dup8 := rfl
private theorem decode_88 : decoder (0x88 : UInt8) = some .dup9 := rfl
private theorem decode_89 : decoder (0x89 : UInt8) = some .dup10 := rfl
private theorem decode_8a : decoder (0x8A : UInt8) = some .dup11 := rfl
private theorem decode_8b : decoder (0x8B : UInt8) = some .dup12 := rfl
private theorem decode_8c : decoder (0x8C : UInt8) = some .dup13 := rfl
private theorem decode_8d : decoder (0x8D : UInt8) = some .dup14 := rfl
private theorem decode_8e : decoder (0x8E : UInt8) = some .dup15 := rfl
private theorem decode_8f : decoder (0x8F : UInt8) = some .dup16 := rfl
private theorem decode_90 : decoder (0x90 : UInt8) = some .swap1 := rfl
private theorem decode_91 : decoder (0x91 : UInt8) = some .swap2 := rfl
private theorem decode_92 : decoder (0x92 : UInt8) = some .swap3 := rfl
private theorem decode_93 : decoder (0x93 : UInt8) = some .swap4 := rfl
private theorem decode_94 : decoder (0x94 : UInt8) = some .swap5 := rfl
private theorem decode_95 : decoder (0x95 : UInt8) = some .swap6 := rfl
private theorem decode_96 : decoder (0x96 : UInt8) = some .swap7 := rfl
private theorem decode_97 : decoder (0x97 : UInt8) = some .swap8 := rfl
private theorem decode_98 : decoder (0x98 : UInt8) = some .swap9 := rfl
private theorem decode_99 : decoder (0x99 : UInt8) = some .swap10 := rfl
private theorem decode_9a : decoder (0x9A : UInt8) = some .swap11 := rfl
private theorem decode_9b : decoder (0x9B : UInt8) = some .swap12 := rfl
private theorem decode_9c : decoder (0x9C : UInt8) = some .swap13 := rfl
private theorem decode_9d : decoder (0x9D : UInt8) = some .swap14 := rfl
private theorem decode_9e : decoder (0x9E : UInt8) = some .swap15 := rfl
private theorem decode_9f : decoder (0x9F : UInt8) = some .swap16 := rfl
private theorem decode_a0 : decoder (0xA0 : UInt8) = some .log0 := rfl
private theorem decode_a1 : decoder (0xA1 : UInt8) = some .log1 := rfl
private theorem decode_a2 : decoder (0xA2 : UInt8) = some .log2 := rfl
private theorem decode_a3 : decoder (0xA3 : UInt8) = some .log3 := rfl
private theorem decode_a4 : decoder (0xA4 : UInt8) = some .log4 := rfl
private theorem decode_a5 : decoder (0xA5 : UInt8) = none := rfl
private theorem decode_a6 : decoder (0xA6 : UInt8) = none := rfl
private theorem decode_a7 : decoder (0xA7 : UInt8) = none := rfl
private theorem decode_a8 : decoder (0xA8 : UInt8) = none := rfl
private theorem decode_a9 : decoder (0xA9 : UInt8) = none := rfl
private theorem decode_aa : decoder (0xAA : UInt8) = none := rfl
private theorem decode_ab : decoder (0xAB : UInt8) = none := rfl
private theorem decode_ac : decoder (0xAC : UInt8) = none := rfl
private theorem decode_ad : decoder (0xAD : UInt8) = none := rfl
private theorem decode_ae : decoder (0xAE : UInt8) = none := rfl
private theorem decode_af : decoder (0xAF : UInt8) = none := rfl
private theorem decode_b0 : decoder (0xB0 : UInt8) = none := rfl
private theorem decode_b1 : decoder (0xB1 : UInt8) = none := rfl
private theorem decode_b2 : decoder (0xB2 : UInt8) = none := rfl
private theorem decode_b3 : decoder (0xB3 : UInt8) = none := rfl
private theorem decode_b4 : decoder (0xB4 : UInt8) = none := rfl
private theorem decode_b5 : decoder (0xB5 : UInt8) = none := rfl
private theorem decode_b6 : decoder (0xB6 : UInt8) = none := rfl
private theorem decode_b7 : decoder (0xB7 : UInt8) = none := rfl
private theorem decode_b8 : decoder (0xB8 : UInt8) = none := rfl
private theorem decode_b9 : decoder (0xB9 : UInt8) = none := rfl
private theorem decode_ba : decoder (0xBA : UInt8) = none := rfl
private theorem decode_bb : decoder (0xBB : UInt8) = none := rfl
private theorem decode_bc : decoder (0xBC : UInt8) = none := rfl
private theorem decode_bd : decoder (0xBD : UInt8) = none := rfl
private theorem decode_be : decoder (0xBE : UInt8) = none := rfl
private theorem decode_bf : decoder (0xBF : UInt8) = none := rfl
private theorem decode_c0 : decoder (0xC0 : UInt8) = none := rfl
private theorem decode_c1 : decoder (0xC1 : UInt8) = none := rfl
private theorem decode_c2 : decoder (0xC2 : UInt8) = none := rfl
private theorem decode_c3 : decoder (0xC3 : UInt8) = none := rfl
private theorem decode_c4 : decoder (0xC4 : UInt8) = none := rfl
private theorem decode_c5 : decoder (0xC5 : UInt8) = none := rfl
private theorem decode_c6 : decoder (0xC6 : UInt8) = none := rfl
private theorem decode_c7 : decoder (0xC7 : UInt8) = none := rfl
private theorem decode_c8 : decoder (0xC8 : UInt8) = none := rfl
private theorem decode_c9 : decoder (0xC9 : UInt8) = none := rfl
private theorem decode_ca : decoder (0xCA : UInt8) = none := rfl
private theorem decode_cb : decoder (0xCB : UInt8) = none := rfl
private theorem decode_cc : decoder (0xCC : UInt8) = none := rfl
private theorem decode_cd : decoder (0xCD : UInt8) = none := rfl
private theorem decode_ce : decoder (0xCE : UInt8) = none := rfl
private theorem decode_cf : decoder (0xCF : UInt8) = none := rfl
private theorem decode_d0 : decoder (0xD0 : UInt8) = none := rfl
private theorem decode_d1 : decoder (0xD1 : UInt8) = none := rfl
private theorem decode_d2 : decoder (0xD2 : UInt8) = none := rfl
private theorem decode_d3 : decoder (0xD3 : UInt8) = none := rfl
private theorem decode_d4 : decoder (0xD4 : UInt8) = none := rfl
private theorem decode_d5 : decoder (0xD5 : UInt8) = none := rfl
private theorem decode_d6 : decoder (0xD6 : UInt8) = none := rfl
private theorem decode_d7 : decoder (0xD7 : UInt8) = none := rfl
private theorem decode_d8 : decoder (0xD8 : UInt8) = none := rfl
private theorem decode_d9 : decoder (0xD9 : UInt8) = none := rfl
private theorem decode_da : decoder (0xDA : UInt8) = none := rfl
private theorem decode_db : decoder (0xDB : UInt8) = none := rfl
private theorem decode_dc : decoder (0xDC : UInt8) = none := rfl
private theorem decode_dd : decoder (0xDD : UInt8) = none := rfl
private theorem decode_de : decoder (0xDE : UInt8) = none := rfl
private theorem decode_df : decoder (0xDF : UInt8) = none := rfl
private theorem decode_e0 : decoder (0xE0 : UInt8) = none := rfl
private theorem decode_e1 : decoder (0xE1 : UInt8) = none := rfl
private theorem decode_e2 : decoder (0xE2 : UInt8) = none := rfl
private theorem decode_e3 : decoder (0xE3 : UInt8) = none := rfl
private theorem decode_e4 : decoder (0xE4 : UInt8) = none := rfl
private theorem decode_e5 : decoder (0xE5 : UInt8) = none := rfl
private theorem decode_e6 : decoder (0xE6 : UInt8) = some .dupn := rfl
private theorem decode_e7 : decoder (0xE7 : UInt8) = some .swapn := rfl
private theorem decode_e8 : decoder (0xE8 : UInt8) = some .exchange := rfl
private theorem decode_e9 : decoder (0xE9 : UInt8) = none := rfl
private theorem decode_ea : decoder (0xEA : UInt8) = none := rfl
private theorem decode_eb : decoder (0xEB : UInt8) = none := rfl
private theorem decode_ec : decoder (0xEC : UInt8) = none := rfl
private theorem decode_ed : decoder (0xED : UInt8) = none := rfl
private theorem decode_ee : decoder (0xEE : UInt8) = none := rfl
private theorem decode_ef : decoder (0xEF : UInt8) = none := rfl
private theorem decode_f0 : decoder (0xF0 : UInt8) = some .create := rfl
private theorem decode_f1 : decoder (0xF1 : UInt8) = some .call := rfl
private theorem decode_f2 : decoder (0xF2 : UInt8) = some .callcode := rfl
private theorem decode_f3 : decoder (0xF3 : UInt8) = some .return_ := rfl
private theorem decode_f4 : decoder (0xF4 : UInt8) = some .delegatecall := rfl
private theorem decode_f5 : decoder (0xF5 : UInt8) = some .create2 := rfl
private theorem decode_f6 : decoder (0xF6 : UInt8) = none := rfl
private theorem decode_f7 : decoder (0xF7 : UInt8) = none := rfl
private theorem decode_f8 : decoder (0xF8 : UInt8) = none := rfl
private theorem decode_f9 : decoder (0xF9 : UInt8) = none := rfl
private theorem decode_fa : decoder (0xFA : UInt8) = some .staticcall := rfl
private theorem decode_fb : decoder (0xFB : UInt8) = none := rfl
private theorem decode_fc : decoder (0xFC : UInt8) = none := rfl
private theorem decode_fd : decoder (0xFD : UInt8) = some .revert := rfl
private theorem decode_fe : decoder (0xFE : UInt8) = none := rfl
private theorem decode_ff : decoder (0xFF : UInt8) = some .selfdestruct := rfl

end STFSpec.Conformance.Vm.Instructions.OpsCallerProofs
