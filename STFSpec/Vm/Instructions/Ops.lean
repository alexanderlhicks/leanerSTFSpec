/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

/-!
# Amsterdam opcode bytes

Library `EthVmInstructions`. The finite opcode vocabulary and total byte conversions
follow pinned EELS `src/ethereum/forks/amsterdam/vm/instructions/__init__.py:32–220`.
Spec guidance: `STFSpec/informal/modules/EthVmInstructions.md` §§2.3/3/5/7.
-/

namespace STFSpec.Vm.Instructions

/-- The 153 pinned EELS `Ops` members, at
`src/ethereum/forks/amsterdam/vm/instructions/__init__.py:32–220`.
Constructors use lowercase source names; `RETURN` uses `return_`. -/
inductive Ops where
  | add
  | mul
  | sub
  | div
  | sdiv
  | mod
  | smod
  | addmod
  | mulmod
  | exp
  | signextend
  | lt
  | gt
  | slt
  | sgt
  | eq
  | iszero
  | and
  | or
  | xor
  | not
  | byte
  | shl
  | shr
  | sar
  | clz
  | keccak
  | address
  | balance
  | origin
  | caller
  | callvalue
  | calldataload
  | calldatasize
  | calldatacopy
  | codesize
  | codecopy
  | gasprice
  | extcodesize
  | extcodecopy
  | returndatasize
  | returndatacopy
  | extcodehash
  | blockhash
  | coinbase
  | timestamp
  | number
  | prevrandao
  | gaslimit
  | chainid
  | selfbalance
  | basefee
  | blobhash
  | blobbasefee
  | slotnum
  | stop
  | jump
  | jumpi
  | pc
  | gas
  | jumpdest
  | sload
  | sstore
  | tload
  | tstore
  | pop
  | push0
  | push1
  | push2
  | push3
  | push4
  | push5
  | push6
  | push7
  | push8
  | push9
  | push10
  | push11
  | push12
  | push13
  | push14
  | push15
  | push16
  | push17
  | push18
  | push19
  | push20
  | push21
  | push22
  | push23
  | push24
  | push25
  | push26
  | push27
  | push28
  | push29
  | push30
  | push31
  | push32
  | dup1
  | dup2
  | dup3
  | dup4
  | dup5
  | dup6
  | dup7
  | dup8
  | dup9
  | dup10
  | dup11
  | dup12
  | dup13
  | dup14
  | dup15
  | dup16
  | swap1
  | swap2
  | swap3
  | swap4
  | swap5
  | swap6
  | swap7
  | swap8
  | swap9
  | swap10
  | swap11
  | swap12
  | swap13
  | swap14
  | swap15
  | swap16
  | dupn
  | swapn
  | exchange
  | mload
  | mstore
  | mstore8
  | msize
  | mcopy
  | log0
  | log1
  | log2
  | log3
  | log4
  | create
  | call
  | callcode
  | return_
  | delegatecall
  | create2
  | staticcall
  | revert
  | selfdestruct

namespace Ops

/-- The byte assigned to an opcode by pinned EELS
`src/ethereum/forks/amsterdam/vm/instructions/__init__.py:32–220`. -/
def toByte : Ops → UInt8
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

/-- Decode every byte, returning `none` at the 103 bytes absent from pinned EELS
`src/ethereum/forks/amsterdam/vm/instructions/__init__.py:32–220`. -/
def ofByte? (b : UInt8) : Option Ops :=
  match b.toNat with
  | 0x01 => some .add
  | 0x02 => some .mul
  | 0x03 => some .sub
  | 0x04 => some .div
  | 0x05 => some .sdiv
  | 0x06 => some .mod
  | 0x07 => some .smod
  | 0x08 => some .addmod
  | 0x09 => some .mulmod
  | 0x0A => some .exp
  | 0x0B => some .signextend
  | 0x10 => some .lt
  | 0x11 => some .gt
  | 0x12 => some .slt
  | 0x13 => some .sgt
  | 0x14 => some .eq
  | 0x15 => some .iszero
  | 0x16 => some .and
  | 0x17 => some .or
  | 0x18 => some .xor
  | 0x19 => some .not
  | 0x1A => some .byte
  | 0x1B => some .shl
  | 0x1C => some .shr
  | 0x1D => some .sar
  | 0x1E => some .clz
  | 0x20 => some .keccak
  | 0x30 => some .address
  | 0x31 => some .balance
  | 0x32 => some .origin
  | 0x33 => some .caller
  | 0x34 => some .callvalue
  | 0x35 => some .calldataload
  | 0x36 => some .calldatasize
  | 0x37 => some .calldatacopy
  | 0x38 => some .codesize
  | 0x39 => some .codecopy
  | 0x3A => some .gasprice
  | 0x3B => some .extcodesize
  | 0x3C => some .extcodecopy
  | 0x3D => some .returndatasize
  | 0x3E => some .returndatacopy
  | 0x3F => some .extcodehash
  | 0x40 => some .blockhash
  | 0x41 => some .coinbase
  | 0x42 => some .timestamp
  | 0x43 => some .number
  | 0x44 => some .prevrandao
  | 0x45 => some .gaslimit
  | 0x46 => some .chainid
  | 0x47 => some .selfbalance
  | 0x48 => some .basefee
  | 0x49 => some .blobhash
  | 0x4A => some .blobbasefee
  | 0x4B => some .slotnum
  | 0x00 => some .stop
  | 0x56 => some .jump
  | 0x57 => some .jumpi
  | 0x58 => some .pc
  | 0x5A => some .gas
  | 0x5B => some .jumpdest
  | 0x54 => some .sload
  | 0x55 => some .sstore
  | 0x5C => some .tload
  | 0x5D => some .tstore
  | 0x50 => some .pop
  | 0x5F => some .push0
  | 0x60 => some .push1
  | 0x61 => some .push2
  | 0x62 => some .push3
  | 0x63 => some .push4
  | 0x64 => some .push5
  | 0x65 => some .push6
  | 0x66 => some .push7
  | 0x67 => some .push8
  | 0x68 => some .push9
  | 0x69 => some .push10
  | 0x6A => some .push11
  | 0x6B => some .push12
  | 0x6C => some .push13
  | 0x6D => some .push14
  | 0x6E => some .push15
  | 0x6F => some .push16
  | 0x70 => some .push17
  | 0x71 => some .push18
  | 0x72 => some .push19
  | 0x73 => some .push20
  | 0x74 => some .push21
  | 0x75 => some .push22
  | 0x76 => some .push23
  | 0x77 => some .push24
  | 0x78 => some .push25
  | 0x79 => some .push26
  | 0x7A => some .push27
  | 0x7B => some .push28
  | 0x7C => some .push29
  | 0x7D => some .push30
  | 0x7E => some .push31
  | 0x7F => some .push32
  | 0x80 => some .dup1
  | 0x81 => some .dup2
  | 0x82 => some .dup3
  | 0x83 => some .dup4
  | 0x84 => some .dup5
  | 0x85 => some .dup6
  | 0x86 => some .dup7
  | 0x87 => some .dup8
  | 0x88 => some .dup9
  | 0x89 => some .dup10
  | 0x8A => some .dup11
  | 0x8B => some .dup12
  | 0x8C => some .dup13
  | 0x8D => some .dup14
  | 0x8E => some .dup15
  | 0x8F => some .dup16
  | 0x90 => some .swap1
  | 0x91 => some .swap2
  | 0x92 => some .swap3
  | 0x93 => some .swap4
  | 0x94 => some .swap5
  | 0x95 => some .swap6
  | 0x96 => some .swap7
  | 0x97 => some .swap8
  | 0x98 => some .swap9
  | 0x99 => some .swap10
  | 0x9A => some .swap11
  | 0x9B => some .swap12
  | 0x9C => some .swap13
  | 0x9D => some .swap14
  | 0x9E => some .swap15
  | 0x9F => some .swap16
  | 0xE6 => some .dupn
  | 0xE7 => some .swapn
  | 0xE8 => some .exchange
  | 0x51 => some .mload
  | 0x52 => some .mstore
  | 0x53 => some .mstore8
  | 0x59 => some .msize
  | 0x5E => some .mcopy
  | 0xA0 => some .log0
  | 0xA1 => some .log1
  | 0xA2 => some .log2
  | 0xA3 => some .log3
  | 0xA4 => some .log4
  | 0xF0 => some .create
  | 0xF1 => some .call
  | 0xF2 => some .callcode
  | 0xF3 => some .return_
  | 0xF4 => some .delegatecall
  | 0xF5 => some .create2
  | 0xFA => some .staticcall
  | 0xFD => some .revert
  | 0xFF => some .selfdestruct
  | _ => none

/-- Decoding an opcode's assigned byte returns that opcode. -/
theorem ofByte_toByte (o : Ops) : ofByte? (toByte o) = some o := by
  cases o <;> rfl

/-- Successful decoding preserves the complete input byte. -/
theorem toByte_ofByte (b : UInt8) (o : Ops) (h : ofByte? b = some o) :
    toByte o = b := by
  unfold ofByte? at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals
    subst o
    apply UInt8.toNat_inj.mp
    symm
    assumption

end Ops
end STFSpec.Vm.Instructions
