#!/usr/bin/env python3
"""Complete frozen memory-pricing observations and strict public CLI.

Default frame comparison checks the committed literal catalog. Optional source
frames and their binding digest are supplied by the caller; this comparator does
not produce or authenticate that external evidence. See EthVmCore §3 for scope.
"""

import argparse
import copy
import json
import re
import sys
import textwrap
from pathlib import Path

CATALOG = {
    "status": "manually reasoned literal expectations only; no execution/model results",
    "date": "2026-10-17",
    "eels_pin": "e1a316a06fc3d3e0a5da36fdc78580811e9d8a36",
    "count": 39,
    "pinnedSourceRows": 24,
    "genericLeanOnlyRows": 12,
    "rawSourceOnlyRows": 3,
    "numericEncoding": "decimal strings or full sixteen-limb big-endian u32be hex array; "
    "no truncation",
    "memoryModels": {
        "E": {"size": 0, "hex": ""},
        "Z32": {
            "size": 32,
            "hex": "0000000000000000000000000000000000000000000000000000000000000000",
        },
        "Z64": {
            "size": 64,
            "hex": "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        },
        "A32": {
            "size": 32,
            "hex": "008000ff00000000000000000000000000000000000000000000000000000000",
        },
        "RAW1": {"size": 1, "hex": "80"},
    },
    "cases": [
        {
            "id": "C01",
            "domain": "pinned-source",
            "helper": "calculate_memory_gas_cost",
            "memoryPerWord": "3",
            "size": "0",
            "expectedCost": "0",
        },
        {
            "id": "C02",
            "domain": "pinned-source",
            "helper": "calculate_memory_gas_cost",
            "memoryPerWord": "3",
            "size": "1",
            "expectedCost": "3",
        },
        {
            "id": "C03",
            "domain": "pinned-source",
            "helper": "calculate_memory_gas_cost",
            "memoryPerWord": "3",
            "size": "31",
            "expectedCost": "3",
        },
        {
            "id": "C04",
            "domain": "pinned-source",
            "helper": "calculate_memory_gas_cost",
            "memoryPerWord": "3",
            "size": "32",
            "expectedCost": "3",
        },
        {
            "id": "C05",
            "domain": "pinned-source",
            "helper": "calculate_memory_gas_cost",
            "memoryPerWord": "3",
            "size": "33",
            "expectedCost": "6",
        },
        {
            "id": "C06",
            "domain": "pinned-source",
            "helper": "calculate_memory_gas_cost",
            "memoryPerWord": "3",
            "size": "64",
            "expectedCost": "6",
        },
        {
            "id": "C07",
            "domain": "pinned-source",
            "helper": "calculate_memory_gas_cost",
            "memoryPerWord": "3",
            "size": "704",
            "expectedCost": "66",
        },
        {
            "id": "C08",
            "domain": "pinned-source",
            "helper": "calculate_memory_gas_cost",
            "memoryPerWord": "3",
            "size": "705",
            "expectedCost": "70",
        },
        {
            "id": "C09",
            "domain": "generic-Lean-only",
            "helper": "calculate_memory_gas_cost",
            "memoryPerWord": "0",
            "size": "32",
            "expectedCost": "0",
        },
        {
            "id": "C10",
            "domain": "generic-Lean-only",
            "helper": "calculate_memory_gas_cost",
            "memoryPerWord": "0",
            "size": "704",
            "expectedCost": "0",
        },
        {
            "id": "C11",
            "domain": "generic-Lean-only",
            "helper": "calculate_memory_gas_cost",
            "memoryPerWord": "0",
            "size": "705",
            "expectedCost": "1",
        },
        {
            "id": "C12",
            "domain": "generic-Lean-only",
            "helper": "calculate_memory_gas_cost",
            "memoryPerWord": "7",
            "size": "64",
            "expectedCost": "14",
        },
        {
            "id": "P01",
            "domain": "pinned-source",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "0",
            "memory": "E",
            "extensions": [],
            "expected": {"cost": "0", "expandBy": "0"},
            "expectedMemoryAfter": "E",
        },
        {
            "id": "P02",
            "domain": "pinned-source",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "0",
            "memory": "E",
            "extensions": [
                [
                    "115792089237316195423570985008687907853269984665640564039457584007913129639935",
                    "0",
                ]
            ],
            "expected": {"cost": "0", "expandBy": "0"},
            "expectedMemoryAfter": "E",
        },
        {
            "id": "P03",
            "domain": "pinned-source",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "0",
            "memory": "Z32",
            "extensions": [
                [
                    "115792089237316195423570985008687907853269984665640564039457584007913129639935",
                    "0",
                ]
            ],
            "expected": {"cost": "0", "expandBy": "0"},
            "expectedMemoryAfter": "Z32",
        },
        {
            "id": "P04",
            "domain": "pinned-source",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "0",
            "memory": "E",
            "extensions": [["0", "1"]],
            "expected": {"cost": "3", "expandBy": "32"},
            "expectedMemoryAfter": "E",
        },
        {
            "id": "P05",
            "domain": "pinned-source",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "0",
            "memory": "E",
            "extensions": [["31", "1"]],
            "expected": {"cost": "3", "expandBy": "32"},
            "expectedMemoryAfter": "E",
        },
        {
            "id": "P06",
            "domain": "pinned-source",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "0",
            "memory": "E",
            "extensions": [["31", "2"]],
            "expected": {"cost": "6", "expandBy": "64"},
            "expectedMemoryAfter": "E",
        },
        {
            "id": "P07",
            "domain": "pinned-source",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "0",
            "memory": "Z32",
            "extensions": [["31", "1"]],
            "expected": {"cost": "0", "expandBy": "0"},
            "expectedMemoryAfter": "Z32",
        },
        {
            "id": "P08",
            "domain": "pinned-source",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "0",
            "memory": "Z32",
            "extensions": [["31", "2"]],
            "expected": {"cost": "3", "expandBy": "32"},
            "expectedMemoryAfter": "Z32",
        },
        {
            "id": "P09",
            "domain": "pinned-source",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "0",
            "memory": "Z64",
            "extensions": [["32", "33"]],
            "expected": {"cost": "3", "expandBy": "32"},
            "expectedMemoryAfter": "Z64",
        },
        {
            "id": "P10",
            "domain": "pinned-source",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "0",
            "memory": "E",
            "extensions": [["0", "32"], ["0", "64"]],
            "expected": {"cost": "6", "expandBy": "64"},
            "expectedMemoryAfter": "E",
        },
        {
            "id": "P11",
            "domain": "pinned-source",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "0",
            "memory": "E",
            "extensions": [["0", "64"], ["0", "32"]],
            "expected": {"cost": "6", "expandBy": "64"},
            "expectedMemoryAfter": "E",
        },
        {
            "id": "P12",
            "domain": "pinned-source",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "0",
            "memory": "E",
            "extensions": [
                ["0", "64"],
                ["0", "64"],
                ["1", "1"],
                [
                    "115792089237316195423570985008687907853269984665640564039457584007913129639935",
                    "0",
                ],
            ],
            "expected": {"cost": "6", "expandBy": "64"},
            "expectedMemoryAfter": "E",
        },
        {
            "id": "P13",
            "domain": "pinned-source",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "0",
            "memory": "A32",
            "extensions": [["0", "32"], ["7", "1"]],
            "expected": {"cost": "0", "expandBy": "0"},
            "expectedMemoryAfter": "A32",
        },
        {
            "id": "P14",
            "domain": "pinned-source",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "0",
            "memory": "E",
            "extensions": [["0", "704"], ["704", "1"]],
            "expected": {"cost": "70", "expandBy": "736"},
            "expectedMemoryAfter": "E",
        },
        {
            "id": "P15",
            "domain": "pinned-source",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "0",
            "memory": "E",
            "extensions": [
                [
                    "115792089237316195423570985008687907853269984665640564039457584007913129639935",
                    "1",
                ]
            ],
            "expected": {
                "cost": {
                    "u32be": [
                        "00002000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "18000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                    ]
                },
                "expandBy": {
                    "u32be": [
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000001",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                    ]
                },
            },
            "expectedMemoryAfter": "E",
        },
        {
            "id": "P16",
            "domain": "pinned-source",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "0",
            "memory": "E",
            "extensions": [
                [
                    "115792089237316195423570985008687907853269984665640564039457584007913129639935",
                    "115792089237316195423570985008687907853269984665640564039457584007913129639935",
                ]
            ],
            "expected": {
                "cost": {
                    "u32be": [
                        "00008000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "30000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                    ]
                },
                "expandBy": {
                    "u32be": [
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000002",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                        "00000000",
                    ]
                },
            },
            "expectedMemoryAfter": "E",
        },
        {
            "id": "G01",
            "domain": "generic-Lean-only",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "7",
            "memory": "E",
            "extensions": [],
            "expected": {"cost": "7", "expandBy": "0"},
            "expectedMemoryAfter": "E",
        },
        {
            "id": "G02",
            "domain": "generic-Lean-only",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "7",
            "memory": "E",
            "extensions": [["0", "32"]],
            "expected": {"cost": "10", "expandBy": "32"},
            "expectedMemoryAfter": "E",
        },
        {
            "id": "G03",
            "domain": "generic-Lean-only",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "7",
            "memory": "E",
            "extensions": [["0", "32"], ["0", "64"]],
            "expected": {"cost": "13", "expandBy": "64"},
            "expectedMemoryAfter": "E",
        },
        {
            "id": "G04",
            "domain": "generic-Lean-only",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "7",
            "memory": "Z32",
            "extensions": [["0", "64"]],
            "expected": {"cost": "10", "expandBy": "32"},
            "expectedMemoryAfter": "Z32",
        },
        {
            "id": "G05",
            "domain": "generic-Lean-only",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "0",
            "zeroSeed": "0",
            "memory": "E",
            "extensions": [["0", "32"]],
            "expected": {"cost": "0", "expandBy": "32"},
            "expectedMemoryAfter": "E",
        },
        {
            "id": "G06",
            "domain": "generic-Lean-only",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "0",
            "zeroSeed": "0",
            "memory": "E",
            "extensions": [["0", "705"]],
            "expected": {"cost": "1", "expandBy": "736"},
            "expectedMemoryAfter": "E",
        },
        {
            "id": "G07",
            "domain": "generic-Lean-only",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "7",
            "zeroSeed": "0",
            "memory": "E",
            "extensions": [["0", "64"]],
            "expected": {"cost": "14", "expandBy": "64"},
            "expectedMemoryAfter": "E",
        },
        {
            "id": "G08",
            "domain": "generic-Lean-only",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "0",
            "zeroSeed": "7",
            "memory": "E",
            "extensions": [["0", "32"]],
            "expected": {"cost": "7", "expandBy": "32"},
            "expectedMemoryAfter": "E",
        },
        {
            "id": "R01",
            "domain": "raw-source-only-separate-release",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "0",
            "memory": "RAW1",
            "extensions": [],
            "expected": {"cost": "0", "expandBy": "0"},
            "expectedMemoryAfter": "RAW1",
        },
        {
            "id": "R02",
            "domain": "raw-source-only-separate-release",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "0",
            "memory": "RAW1",
            "extensions": [["0", "32"]],
            "expected": {"cost": "0", "expandBy": "0"},
            "expectedMemoryAfter": "RAW1",
        },
        {
            "id": "R03",
            "domain": "raw-source-only-separate-release",
            "helper": "calculate_gas_extend_memory",
            "memoryPerWord": "3",
            "zeroSeed": "0",
            "memory": "RAW1",
            "extensions": [["32", "1"]],
            "expected": {"cost": "3", "expandBy": "32"},
            "expectedMemoryAfter": "RAW1",
        },
    ],
}
EXTRA = {
    "status": "manually reasoned frozen additional target-only predictions; no "
    "model/source/target execution",
    "date": "2026-10-18",
    "memoryModels": {
        "Z736": {
            "size": 736,
            "hex": "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        }
    },
    "cases": [
        {
            "id": "E01",
            "domain": "generic-Lean-only",
            "helper": "calculate_memory_gas_cost",
            "configProfile": "rawA",
            "memoryPerWord": "0",
            "zeroSeed": "0",
            "size": "736",
            "expectedCost": "1",
        },
        {
            "id": "E02",
            "domain": "generic-Lean-only",
            "helper": "calculate_memory_gas_cost",
            "configProfile": "rawA",
            "memoryPerWord": "0",
            "zeroSeed": "0",
            "size": "768",
            "expectedCost": "1",
        },
        {
            "id": "E03",
            "domain": "generic-Lean-only",
            "helper": "calculate_gas_extend_memory",
            "configProfile": "rawA",
            "memoryPerWord": "0",
            "zeroSeed": "0",
            "memory": "Z736",
            "extensions": [["0", "768"]],
            "expected": {"cost": "0", "expandBy": "32"},
            "expectedMemoryAfter": "Z736",
        },
        {
            "id": "E04",
            "domain": "generic-Lean-only",
            "helper": "calculate_gas_extend_memory",
            "configProfile": "rawA",
            "memoryPerWord": "0",
            "zeroSeed": "7",
            "memory": "Z736",
            "extensions": [["0", "768"]],
            "expected": {"cost": "7", "expandBy": "32"},
            "expectedMemoryAfter": "Z736",
        },
        {
            "id": "E05",
            "domain": "generic-Lean-only",
            "helper": "calculate_memory_gas_cost",
            "configProfile": "rawB",
            "memoryPerWord": "3",
            "zeroSeed": "99",
            "size": "64",
            "expectedCost": "6",
        },
        {
            "id": "E06",
            "domain": "generic-Lean-only",
            "helper": "calculate_gas_extend_memory",
            "configProfile": "rawB",
            "memoryPerWord": "3",
            "zeroSeed": "7",
            "memory": "E",
            "extensions": [["0", "32"], ["0", "64"]],
            "expected": {"cost": "13", "expandBy": "64"},
            "expectedMemoryAfter": "E",
        },
    ],
    "manualReasoning": {
        "E01": "23 words; 529/512 gives1; linear coefficient0",
        "E02": "24 words; 576/512 gives1; linear coefficient0",
        "E03": "old23 words cost1, new24 words cost1, positive aligned difference32, seed0",
        "E04": "same ordered difference0, seed7 included once",
        "E05": "two words times3 gives6, quadratic0; zero99 and every "
        "unrelated field immaterial",
        "E06": "cost3 at32 then6 at64; sum of deltas6 plus seed7 gives13; "
        "extent64; identical G03 arguments/selected fields with "
        "every unrelated field profile changed",
    },
}
PROFILES = {
    "status": "frozen literal raw target fixtures; not EthFork/default/supported policy; "
    "no execution",
    "perRowOverrides": ["costs.memoryPerWord", "costs.zero"],
    "scalarSeedDefault": "0",
    "extensionSeed": "row.zeroSeed",
    "fieldTypes": {
        "base": "Nat",
        "veryLow": "Nat",
        "low": "Nat",
        "mid": "Nat",
        "high": "Nat",
        "warmAccess": "Nat",
        "coldAccountAccess": "Nat",
        "coldStorageAccess": "Nat",
        "storageWrite": "Nat",
        "callStipend": "Nat",
        "accountWrite": "Nat",
        "callValue": "Nat",
        "codeInitPerWord": "Nat",
        "createAccess": "Nat",
        "zero": "Nat",
        "memoryPerWord": "Nat",
        "fastStep": "Nat",
        "refundStorageClear": "Int",
        "precompileEcrecover": "Nat",
        "precompileP256Verify": "Nat",
        "precompileSha256Base": "Nat",
        "precompileSha256PerWord": "Nat",
        "precompileRipemd160Base": "Nat",
        "precompileRipemd160PerWord": "Nat",
        "precompileIdentityBase": "Nat",
        "precompileIdentityPerWord": "Nat",
        "precompileBlake2FPerRound": "Nat",
        "precompilePointEvaluation": "Nat",
        "precompileBlsG1Add": "Nat",
        "precompileBlsG1Mul": "Nat",
        "precompileBlsG1Map": "Nat",
        "precompileBlsG2Add": "Nat",
        "precompileBlsG2Mul": "Nat",
        "precompileBlsG2Map": "Nat",
        "precompileEcAdd": "Nat",
        "precompileEcMul": "Nat",
        "precompileEcPairingBase": "Nat",
        "precompileEcPairingPerPoint": "Nat",
        "perBlob": "U64",
        "blobScheduleTarget": "U64",
        "blobTargetGasPerBlock": "U64",
        "blobBaseCost": "Nat",
        "blobScheduleMax": "U64",
        "blobMinGasPrice": "Nat",
        "blobBaseFeeUpdateFraction": "Nat",
        "blockAccessListItem": "Nat",
        "txBase": "Nat",
        "txValueCost": "Nat",
        "txDataTokenStandard": "Nat",
        "txDataTokenFloor": "Nat",
        "txAccessListAddress": "Nat",
        "txAccessListStorageKey": "Nat",
        "txMaxGasLimit": "Nat",
        "txMaxTotalGasLimit": "Nat",
        "authTupleBytes": "Nat",
        "executionPerAuthBaseCost": "Nat",
        "limitAdjustmentFactor": "Nat",
        "limitMinimum": "Nat",
        "opcodeAdd": "Nat",
        "opcodeSub": "Nat",
        "opcodeMul": "Nat",
        "opcodeDiv": "Nat",
        "opcodeSdiv": "Nat",
        "opcodeMod": "Nat",
        "opcodeSmod": "Nat",
        "opcodeAddmod": "Nat",
        "opcodeMulmod": "Nat",
        "opcodeSignextend": "Nat",
        "opcodeLt": "Nat",
        "opcodeGt": "Nat",
        "opcodeSlt": "Nat",
        "opcodeSgt": "Nat",
        "opcodeEq": "Nat",
        "opcodeIsZero": "Nat",
        "opcodeAnd": "Nat",
        "opcodeOr": "Nat",
        "opcodeXor": "Nat",
        "opcodeNot": "Nat",
        "opcodeByte": "Nat",
        "opcodeShl": "Nat",
        "opcodeShr": "Nat",
        "opcodeSar": "Nat",
        "opcodeClz": "Nat",
        "opcodeJump": "Nat",
        "opcodeJumpi": "Nat",
        "opcodeJumpDest": "Nat",
        "opcodeCallDataLoad": "Nat",
        "opcodeBlockHash": "Nat",
        "opcodeCoinbase": "Nat",
        "opcodePop": "Nat",
        "opcodeMsize": "Nat",
        "opcodePc": "Nat",
        "opcodeGas": "Nat",
        "opcodeAddress": "Nat",
        "opcodeOrigin": "Nat",
        "opcodeCaller": "Nat",
        "opcodeCallValue": "Nat",
        "opcodeCallDataSize": "Nat",
        "opcodeCodeSize": "Nat",
        "opcodeGasPrice": "Nat",
        "opcodeTimestamp": "Nat",
        "opcodeNumber": "Nat",
        "opcodeGasLimit": "Nat",
        "opcodePrevRandao": "Nat",
        "opcodeReturnDataSize": "Nat",
        "opcodeChainId": "Nat",
        "opcodeSelfBalance": "Nat",
        "opcodeBaseFee": "Nat",
        "opcodeBlobBaseFee": "Nat",
        "opcodeSlotNum": "Nat",
        "opcodeBlobHash": "Nat",
        "opcodePush": "Nat",
        "opcodePush0": "Nat",
        "opcodeDup": "Nat",
        "opcodeSwap": "Nat",
        "opcodeDupn": "Nat",
        "opcodeSwapn": "Nat",
        "opcodeExchange": "Nat",
        "opcodeTload": "Nat",
        "opcodeTstore": "Nat",
        "opcodeReturnDataCopyBase": "Nat",
        "opcodeReturnDataCopyPerWord": "Nat",
        "opcodeCallDataCopyBase": "Nat",
        "opcodeCodeCopyBase": "Nat",
        "opcodeMcopyBase": "Nat",
        "opcodeMloadBase": "Nat",
        "opcodeMstoreBase": "Nat",
        "opcodeMstore8Base": "Nat",
        "opcodeCopyPerWord": "Nat",
        "opcodeExpBase": "Nat",
        "opcodeExpPerByte": "Nat",
        "opcodeKeccak256Base": "Nat",
        "opcodeKeccak256PerWord": "Nat",
        "opcodeLogBase": "Nat",
        "opcodeLogDataPerByte": "Nat",
        "opcodeLogTopic": "Nat",
        "opcodeSelfDestructBase": "Nat",
        "blsPairingBase": "Nat",
        "blsPairingPerPair": "Nat",
        "blsG1KDiscount": "Array Nat",
        "blsG2KDiscount": "Array Nat",
        "blsG1MaxDiscount": "Nat",
        "blsG2MaxDiscount": "Nat",
        "blsMultiplier": "Nat",
    },
    "profiles": {
        "rawA": {
            "costs": {
                "base": "0",
                "veryLow": "0",
                "low": "0",
                "mid": "0",
                "high": "0",
                "warmAccess": "0",
                "coldAccountAccess": "0",
                "coldStorageAccess": "0",
                "storageWrite": "0",
                "callStipend": "0",
                "accountWrite": "0",
                "callValue": "0",
                "codeInitPerWord": "0",
                "createAccess": "0",
                "zero": "0",
                "memoryPerWord": "0",
                "fastStep": "0",
                "refundStorageClear": "0",
                "precompileEcrecover": "0",
                "precompileP256Verify": "0",
                "precompileSha256Base": "0",
                "precompileSha256PerWord": "0",
                "precompileRipemd160Base": "0",
                "precompileRipemd160PerWord": "0",
                "precompileIdentityBase": "0",
                "precompileIdentityPerWord": "0",
                "precompileBlake2FPerRound": "0",
                "precompilePointEvaluation": "0",
                "precompileBlsG1Add": "0",
                "precompileBlsG1Mul": "0",
                "precompileBlsG1Map": "0",
                "precompileBlsG2Add": "0",
                "precompileBlsG2Mul": "0",
                "precompileBlsG2Map": "0",
                "precompileEcAdd": "0",
                "precompileEcMul": "0",
                "precompileEcPairingBase": "0",
                "precompileEcPairingPerPoint": "0",
                "perBlob": "0",
                "blobScheduleTarget": "0",
                "blobTargetGasPerBlock": "0",
                "blobBaseCost": "0",
                "blobScheduleMax": "0",
                "blobMinGasPrice": "0",
                "blobBaseFeeUpdateFraction": "0",
                "blockAccessListItem": "0",
                "txBase": "0",
                "txValueCost": "0",
                "txDataTokenStandard": "0",
                "txDataTokenFloor": "0",
                "txAccessListAddress": "0",
                "txAccessListStorageKey": "0",
                "txMaxGasLimit": "0",
                "txMaxTotalGasLimit": "0",
                "authTupleBytes": "0",
                "executionPerAuthBaseCost": "0",
                "limitAdjustmentFactor": "0",
                "limitMinimum": "0",
                "opcodeAdd": "0",
                "opcodeSub": "0",
                "opcodeMul": "0",
                "opcodeDiv": "0",
                "opcodeSdiv": "0",
                "opcodeMod": "0",
                "opcodeSmod": "0",
                "opcodeAddmod": "0",
                "opcodeMulmod": "0",
                "opcodeSignextend": "0",
                "opcodeLt": "0",
                "opcodeGt": "0",
                "opcodeSlt": "0",
                "opcodeSgt": "0",
                "opcodeEq": "0",
                "opcodeIsZero": "0",
                "opcodeAnd": "0",
                "opcodeOr": "0",
                "opcodeXor": "0",
                "opcodeNot": "0",
                "opcodeByte": "0",
                "opcodeShl": "0",
                "opcodeShr": "0",
                "opcodeSar": "0",
                "opcodeClz": "0",
                "opcodeJump": "0",
                "opcodeJumpi": "0",
                "opcodeJumpDest": "0",
                "opcodeCallDataLoad": "0",
                "opcodeBlockHash": "0",
                "opcodeCoinbase": "0",
                "opcodePop": "0",
                "opcodeMsize": "0",
                "opcodePc": "0",
                "opcodeGas": "0",
                "opcodeAddress": "0",
                "opcodeOrigin": "0",
                "opcodeCaller": "0",
                "opcodeCallValue": "0",
                "opcodeCallDataSize": "0",
                "opcodeCodeSize": "0",
                "opcodeGasPrice": "0",
                "opcodeTimestamp": "0",
                "opcodeNumber": "0",
                "opcodeGasLimit": "0",
                "opcodePrevRandao": "0",
                "opcodeReturnDataSize": "0",
                "opcodeChainId": "0",
                "opcodeSelfBalance": "0",
                "opcodeBaseFee": "0",
                "opcodeBlobBaseFee": "0",
                "opcodeSlotNum": "0",
                "opcodeBlobHash": "0",
                "opcodePush": "0",
                "opcodePush0": "0",
                "opcodeDup": "0",
                "opcodeSwap": "0",
                "opcodeDupn": "0",
                "opcodeSwapn": "0",
                "opcodeExchange": "0",
                "opcodeTload": "0",
                "opcodeTstore": "0",
                "opcodeReturnDataCopyBase": "0",
                "opcodeReturnDataCopyPerWord": "0",
                "opcodeCallDataCopyBase": "0",
                "opcodeCodeCopyBase": "0",
                "opcodeMcopyBase": "0",
                "opcodeMloadBase": "0",
                "opcodeMstoreBase": "0",
                "opcodeMstore8Base": "0",
                "opcodeCopyPerWord": "0",
                "opcodeExpBase": "0",
                "opcodeExpPerByte": "0",
                "opcodeKeccak256Base": "0",
                "opcodeKeccak256PerWord": "0",
                "opcodeLogBase": "0",
                "opcodeLogDataPerByte": "0",
                "opcodeLogTopic": "0",
                "opcodeSelfDestructBase": "0",
                "blsPairingBase": "0",
                "blsPairingPerPair": "0",
                "blsG1KDiscount": [],
                "blsG2KDiscount": [],
                "blsG1MaxDiscount": "0",
                "blsG2MaxDiscount": "0",
                "blsMultiplier": "0",
            },
            "stateCosts": {
                "costPerStateByte": "0",
                "bytesPerNewAccount": "0",
                "bytesPerStorageSet": "0",
                "bytesPerAuthBase": "0",
            },
            "limits": {"stackDepthLimit": "0", "maxCodeSize": "0", "maxInitCodeSize": "0"},
        },
        "rawB": {
            "costs": {
                "base": "1",
                "veryLow": "1",
                "low": "1",
                "mid": "1",
                "high": "1",
                "warmAccess": "1",
                "coldAccountAccess": "1",
                "coldStorageAccess": "1",
                "storageWrite": "1",
                "callStipend": "1",
                "accountWrite": "1",
                "callValue": "1",
                "codeInitPerWord": "1",
                "createAccess": "1",
                "zero": "1",
                "memoryPerWord": "1",
                "fastStep": "1",
                "refundStorageClear": "-7",
                "precompileEcrecover": "1",
                "precompileP256Verify": "1",
                "precompileSha256Base": "1",
                "precompileSha256PerWord": "1",
                "precompileRipemd160Base": "1",
                "precompileRipemd160PerWord": "1",
                "precompileIdentityBase": "1",
                "precompileIdentityPerWord": "1",
                "precompileBlake2FPerRound": "1",
                "precompilePointEvaluation": "1",
                "precompileBlsG1Add": "1",
                "precompileBlsG1Mul": "1",
                "precompileBlsG1Map": "1",
                "precompileBlsG2Add": "1",
                "precompileBlsG2Mul": "1",
                "precompileBlsG2Map": "1",
                "precompileEcAdd": "1",
                "precompileEcMul": "1",
                "precompileEcPairingBase": "1",
                "precompileEcPairingPerPoint": "1",
                "perBlob": "1",
                "blobScheduleTarget": "1",
                "blobTargetGasPerBlock": "1",
                "blobBaseCost": "1",
                "blobScheduleMax": "1",
                "blobMinGasPrice": "1",
                "blobBaseFeeUpdateFraction": "1",
                "blockAccessListItem": "1",
                "txBase": "1",
                "txValueCost": "1",
                "txDataTokenStandard": "1",
                "txDataTokenFloor": "1",
                "txAccessListAddress": "1",
                "txAccessListStorageKey": "1",
                "txMaxGasLimit": "1",
                "txMaxTotalGasLimit": "1",
                "authTupleBytes": "1",
                "executionPerAuthBaseCost": "1",
                "limitAdjustmentFactor": "1",
                "limitMinimum": "1",
                "opcodeAdd": "1",
                "opcodeSub": "1",
                "opcodeMul": "1",
                "opcodeDiv": "1",
                "opcodeSdiv": "1",
                "opcodeMod": "1",
                "opcodeSmod": "1",
                "opcodeAddmod": "1",
                "opcodeMulmod": "1",
                "opcodeSignextend": "1",
                "opcodeLt": "1",
                "opcodeGt": "1",
                "opcodeSlt": "1",
                "opcodeSgt": "1",
                "opcodeEq": "1",
                "opcodeIsZero": "1",
                "opcodeAnd": "1",
                "opcodeOr": "1",
                "opcodeXor": "1",
                "opcodeNot": "1",
                "opcodeByte": "1",
                "opcodeShl": "1",
                "opcodeShr": "1",
                "opcodeSar": "1",
                "opcodeClz": "1",
                "opcodeJump": "1",
                "opcodeJumpi": "1",
                "opcodeJumpDest": "1",
                "opcodeCallDataLoad": "1",
                "opcodeBlockHash": "1",
                "opcodeCoinbase": "1",
                "opcodePop": "1",
                "opcodeMsize": "1",
                "opcodePc": "1",
                "opcodeGas": "1",
                "opcodeAddress": "1",
                "opcodeOrigin": "1",
                "opcodeCaller": "1",
                "opcodeCallValue": "1",
                "opcodeCallDataSize": "1",
                "opcodeCodeSize": "1",
                "opcodeGasPrice": "1",
                "opcodeTimestamp": "1",
                "opcodeNumber": "1",
                "opcodeGasLimit": "1",
                "opcodePrevRandao": "1",
                "opcodeReturnDataSize": "1",
                "opcodeChainId": "1",
                "opcodeSelfBalance": "1",
                "opcodeBaseFee": "1",
                "opcodeBlobBaseFee": "1",
                "opcodeSlotNum": "1",
                "opcodeBlobHash": "1",
                "opcodePush": "1",
                "opcodePush0": "1",
                "opcodeDup": "1",
                "opcodeSwap": "1",
                "opcodeDupn": "1",
                "opcodeSwapn": "1",
                "opcodeExchange": "1",
                "opcodeTload": "1",
                "opcodeTstore": "1",
                "opcodeReturnDataCopyBase": "1",
                "opcodeReturnDataCopyPerWord": "1",
                "opcodeCallDataCopyBase": "1",
                "opcodeCodeCopyBase": "1",
                "opcodeMcopyBase": "1",
                "opcodeMloadBase": "1",
                "opcodeMstoreBase": "1",
                "opcodeMstore8Base": "1",
                "opcodeCopyPerWord": "1",
                "opcodeExpBase": "1",
                "opcodeExpPerByte": "1",
                "opcodeKeccak256Base": "1",
                "opcodeKeccak256PerWord": "1",
                "opcodeLogBase": "1",
                "opcodeLogDataPerByte": "1",
                "opcodeLogTopic": "1",
                "opcodeSelfDestructBase": "1",
                "blsPairingBase": "1",
                "blsPairingPerPair": "1",
                "blsG1KDiscount": ["1", "0", "2"],
                "blsG2KDiscount": ["1", "0", "2"],
                "blsG1MaxDiscount": "1",
                "blsG2MaxDiscount": "1",
                "blsMultiplier": "1",
            },
            "stateCosts": {
                "costPerStateByte": "2",
                "bytesPerNewAccount": "3",
                "bytesPerStorageSet": "4",
                "bytesPerAuthBase": "5",
            },
            "limits": {"stackDepthLimit": "7", "maxCodeSize": "8", "maxInitCodeSize": "9"},
        },
    },
}

SCHEMA = "memory-pricing-v1"
UINT = "ethereum_types.numeric.Uint"
UWORD = "ethereum_types.numeric.U256"
EXTEND = "ethereum.forks.amsterdam.vm.gas.ExtendMemory"
ROWS = [
    r for r in CATALOG["cases"] if r["domain"] != "raw-source-only-separate-release"
] + EXTRA["cases"]
MODELS = dict(CATALOG["memoryModels"], **EXTRA["memoryModels"])


def literal(value):
    """Decode frozen full numbers only; never evaluate a pricing formula."""
    if isinstance(value, str) and re.fullmatch(r"0|[1-9][0-9]*", value):
        return int(value)
    if type(value) is dict and set(value) == {"u32be"}:
        limbs = value["u32be"]
        if (
            type(limbs) is list
            and len(limbs) == 16
            and all(type(x) is str and re.fullmatch("[0-9a-f]{8}", x) for x in limbs)
        ):
            return int("".join(limbs), 16)
    raise ValueError("invalid complete frozen integer")


def config(row):
    out = copy.deepcopy(PROFILES["profiles"][row.get("configProfile", "rawA")])
    out["costs"]["memoryPerWord"] = row["memoryPerWord"]
    out["costs"]["zero"] = row.get("zeroSeed", "0")

    def convert(v):
        if type(v) is dict:
            return {k: convert(x) for k, x in v.items()}
        if type(v) is list:
            return [convert(x) for x in v]
        return int(v)

    return convert(out)


def scalar(row):
    return row["helper"] == "calculate_memory_gas_cost"


def args_for(row, target=True):
    out = (
        {"n": int(row["size"])}
        if scalar(row)
        else {
            "memory": copy.deepcopy(MODELS[row["memory"]]),
            "windows": [[int(s), int(k)] for s, k in row["extensions"]],
        }
    )
    if target:
        out = {"config": config(row), **out}
    return out


def result_for(row):
    return (
        {"cost": literal(row["expectedCost"])}
        if scalar(row)
        else {k: literal(v) for k, v in row["expected"].items()}
    )


def target_types(row):
    return (
        {"config": "VmConfig", "n": "Nat", "result": {"cost": "Nat"}}
        if scalar(row)
        else {
            "config": "VmConfig",
            "memory": "Memory",
            "windows": "List(U256,U256)",
            "result": {"cost": "Nat", "expandBy": "Nat"},
        }
    )


def expected_target(backend):
    return [
        {
            "schema": SCHEMA,
            "id": r["id"],
            "domain": r["domain"],
            "backend": backend,
            "operation": "scalar" if scalar(r) else "extension",
            "input": args_for(r),
            "output": {"result": result_for(r), "after": args_for(r)},
            "types": target_types(r),
        }
        for r in ROWS
    ]


def class_args(row):
    if scalar(row):
        return {"n": UINT}
    return {
        "memory": "builtins.bytearray",
        "windows": "builtins.list",
        "pairs": [
            {"pair": "builtins.tuple", "start": UWORD, "size": UWORD} for _ in row["extensions"]
        ],
    }


def expected_source(digest):
    out = []
    for r in ROWS:
        if r["domain"] != "pinned-source":
            continue
        classes = {
            "input": class_args(r),
            "result": {
                "container": UINT if scalar(r) else EXTEND,
                "fields": {k: UINT for k in result_for(r)},
            },
            "after": class_args(r),
            "bindingDigest": digest,
        }
        out.append(
            {
                "schema": SCHEMA,
                "id": r["id"],
                "domain": "pinned-source",
                "operation": "scalar" if scalar(r) else "extension",
                "policy": {
                    "zero": {"value": 0, "class": UINT},
                    "memoryPerWord": {"value": 3, "class": UINT},
                },
                "input": args_for(r, False),
                "output": {"result": result_for(r), "after": args_for(r, False)},
                "classes": classes,
            }
        )
    return out


def unique(pairs):
    out = {}
    for k, v in pairs:
        if k in out:
            raise ValueError("duplicate key: " + k)
        out[k] = v
    return out


def invalid_constant(value):
    raise ValueError("non-finite number: " + value)


def same(actual, expected, path="frame"):
    """Exact recursive schema, types and complete values; bool is not an int."""
    if type(actual) is not type(expected):
        raise ValueError(path + ": incorrect type")
    if type(expected) is dict:
        if set(actual) != set(expected):
            raise ValueError(path + ": incorrect keys")
        for k, v in expected.items():
            same(actual[k], v, path + "." + k)
    elif type(expected) is list:
        if len(actual) != len(expected):
            raise ValueError(path + ": incorrect length")
        for i, (a, b) in enumerate(zip(actual, expected)):
            same(a, b, path + f"[{i}]")
    elif actual != expected:
        raise ValueError(path + ": incorrect value")


def parse(data, expected):
    """Consistent LF/CRLF, final terminator, no normalization before validation."""
    if type(data) is not bytes or not data:
        raise ValueError("empty/nonbyte stream")
    sep = b"\r\n" if b"\r" in data else b"\n"
    lines = data.split(sep)
    if lines[-1] != b"" or any(
        not line or b"\r" in line or b"\n" in line for line in lines[:-1]
    ):
        raise ValueError("inconsistent/incomplete framing")
    if len(lines) - 1 != len(expected):
        raise ValueError("incorrect record count")
    rows = [
        json.loads(
            line.decode("utf8"), object_pairs_hook=unique, parse_constant=invalid_constant
        )
        for line in lines[:-1]
    ]
    same(rows, expected)
    return rows


def encode(rows, newline=b"\n"):
    return newline.join(json.dumps(r, separators=(",", ":")).encode() for r in rows) + newline


def self_test():
    accepted = rejected = 0
    targets = expected_target("interpreted")
    sources = expected_source("a" * 64)
    for rows in [targets, expected_target("native"), sources]:
        for newline in [b"\n", b"\r\n"]:
            parse(encode(rows, newline), rows)
            accepted += 1

    def reject(data, expected=targets):
        nonlocal rejected
        try:
            parse(data, expected)
        except (ValueError, UnicodeError, TypeError):
            rejected += 1
            return
        raise ValueError("adversary accepted")

    # Recursively exercise every nested key and every literal leaf, not selected summaries.
    def paths(v, prefix=()):
        if type(v) is dict:
            for k, x in v.items():
                yield from paths(x, prefix + (k,))
        elif type(v) is list:
            for i, x in enumerate(v):
                yield from paths(x, prefix + (i,))
        else:
            yield prefix, v

    for expected in [targets, sources]:
        for full_row in expected:
            sample = [full_row]
            idx = 0
            row = full_row
            for path, value in paths(row):
                a = copy.deepcopy(sample)
                node = a[idx]
                for key in path[:-1]:
                    node = node[key]
                for bad in (
                    [True, 1.0, -1, str(value), value + 1]
                    if type(value) is int
                    else ["changed", 0, None]
                ):
                    if type(bad) is type(value) and bad == value:
                        continue
                    node[path[-1]] = bad
                    reject(encode(a), sample)

            # missing/extra/duplicate keys at every nested dictionary
            def objects(v, prefix=()):
                if type(v) is dict:
                    yield prefix, v
                    for k, x in v.items():
                        yield from objects(x, prefix + (k,))
                elif type(v) is list:
                    for i, x in enumerate(v):
                        yield from objects(x, prefix + (i,))

            for path, obj in objects(row):
                for key in obj:
                    a = copy.deepcopy(sample)
                    node = a[idx]
                    for part in path:
                        node = node[part]
                    del node[key]
                    reject(encode(a), sample)
                a = copy.deepcopy(sample)
                node = a[idx]
                for part in path:
                    node = node[part]
                node["unexpected"] = 0
                reject(encode(a), sample)
                # Duplicate an exact dictionary's first key in the real JSON text.
                if obj:
                    raw = json.dumps(obj, separators=(",", ":"))
                    key = next(iter(obj))
                    dup = (
                        "{"
                        + json.dumps(key)
                        + ":"
                        + json.dumps(obj[key], separators=(",", ":"))
                        + ","
                        + raw[1:]
                    )
                    frames = [json.dumps(x, separators=(",", ":")) for x in sample]
                    frames[idx] = frames[idx].replace(raw, dup, 1)
                    reject(("\n".join(frames) + "\n").encode(), sample)
        for bad in [
            encode(expected[:-1]),
            encode(expected + [expected[0]]),
            encode(list(reversed(expected))),
            encode(expected)[:-1],
            b"\n" + encode(expected),
            encode(expected) + b"{}\n",
            encode(expected).replace(b"\n", b"\r"),
            encode(expected).replace(b"\n", b"\r\n", 1),
        ]:
            reject(bad, expected)
    changed = copy.deepcopy(targets)
    row = next(x for x in changed if x["id"] == "P13")
    hx = row["input"]["memory"]["hex"]
    row["input"]["memory"]["hex"] = hx[:30] + ("01" if hx[30:32] != "01" else "02") + hx[32:]
    reject(encode(changed))
    for field in ["cost", "expandBy"]:
        changed = copy.deepcopy(targets)
        row = next(x for x in changed if x["id"] == "P15")
        row["output"]["result"][field] += 1
        reject(encode(changed))
    for rowid in ["P10", "P01"]:
        changed = copy.deepcopy(targets)
        row = next(x for x in changed if x["id"] == rowid)
        row["input"]["windows"].append([0, 0])
        reject(encode(changed))
    for bad in [b"NaN", b"Infinity", b"-Infinity"]:
        reject(encode(targets).replace(b'"n":0', b'"n":' + bad, 1))
    for malformed in [
        {"u32be": ["00000000"] * 15},
        {"u32be": ["00000000"] * 17},
        {"u32be": ["0000000G"] * 16},
        {"u32be": ["0"] * 16},
        "01",
        True,
        1.0,
    ]:
        try:
            literal(malformed)
        except ValueError:
            rejected += 1
        else:
            raise ValueError("noncanonical literal accepted")
    print(
        json.dumps(
            {"accepted": accepted, "rejected": rejected, "targetRows": 42, "sourceRows": 24}
        )
    )


def lean_cfg(name, profile):
    costs = []
    for field, value in profile["costs"].items():
        ty = PROFILES["fieldTypes"][field]
        text = (
            ("#[" + ", ".join(value) + "]")
            if ty == "Array Nat"
            else ("(" + value + ")")
            if ty == "Int"
            else "U64.ofNat " + value
            if ty == "U64"
            else value
        )
        costs.append(f"    {field} := {text}")
    return (
        f"private def {name} : VmConfig := {{\n  costs := {{\n"
        + "\n".join(costs)
        + "\n  }\n  stateCosts := { "
        + ", ".join(k + " := " + v for k, v in profile["stateCosts"].items())
        + " }\n  limits := { "
        + ", ".join(k + " := " + v for k, v in profile["limits"].items())
        + " }\n}\n"
    )


def lean_words(row):
    return (
        "[" + ", ".join(f"(U256.ofNat {s}, U256.ofNat {k})" for s, k in row["extensions"]) + "]"
    )


def lean_memory(row):
    name = row["memory"]
    size = MODELS[name]["size"]
    base = "Memory.empty" if size == 0 else f"(Memory.empty.expand {size} (by decide))"
    if name == "A32":
        return f"({base}.write 0 (Bytes.ofList [0,128,0,255" + ",0" * 28 + "]) (by decide))"
    return base


def cfg_expr(row):
    name = row.get("configProfile", "rawA")
    return (
        "{ "
        + name
        + " with costs := { "
        + name
        + ".costs with memoryPerWord := "
        + row["memoryPerWord"]
        + ", zero := "
        + row.get("zeroSeed", "0")
        + " } }"
    )


def definitions():
    return "\n".join(lean_cfg(k, v) for k, v in PROFILES["profiles"].items())


def guard_layout(text):
    """Lay out the generated raw-profile state-cost record fields."""
    lines = []
    for line in text.splitlines():
        if line.startswith("  stateCosts := { "):
            fields = line.removeprefix("  stateCosts := { ").removesuffix(" }")
            lines.append(
                "  stateCosts := {\n"
                + ",\n".join("    " + field for field in fields.split(", "))
                + "\n  }"
            )
        else:
            lines.append(line)
    return "\n".join(lines) + "\n"


def emit_guards():
    text = """/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Vm.Core
/-! Complete frozen memory-pricing guards; no returned extent is allocated.
Library `EthConformance`. Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/7. -/
namespace STFSpec.Conformance.Vm.Core.MemoryGasGuards
open STFSpec.Vm.Core STFSpec.Base
""" + definitions()
    for row in ROWS:
        text += "\n-- " + row["id"] + " " + row["domain"] + "\n#guard\n"
        cfg = cfg_expr(row)
        result = result_for(row)
        if scalar(row):
            text += (
                "  calculateMemoryGasCost\n    ("
                + cfg
                + ")\n    "
                + row["size"]
                + " == "
                + str(result["cost"])
                + "\n"
            )
        else:
            memory = lean_memory(row).replace(",", ",\n    ")
            windows = lean_words(row).replace(", ", ",\n      ")
            model = ", ".join(str(b) for b in bytes.fromhex(MODELS[row["memory"]]["hex"]))
            chunks = textwrap.wrap(
                model, width=86, break_long_words=False, break_on_hyphens=False
            )
            text += "  let m := " + memory + ";\n"
            text += "  let r := calculateGasExtendMemory\n    (" + cfg + ")\n"
            text += "    m " + windows + ";\n"
            text += "  r.cost == " + str(result["cost"]) + " &&\n"
            text += "    r.expandBy == " + str(result["expandBy"]) + " &&\n"
            text += "    m.toBytes == [" + "\n      ".join(chunks) + "]\n"
    return guard_layout(text + "\nend STFSpec.Conformance.Vm.Core.MemoryGasGuards\n")


def emit_lean():
    text = """import Lean
import STFSpec.Vm.Core
open STFSpec.Vm.Core STFSpec.Base Lean
""" + definitions()
    cost_fields = []
    for name, ty in PROFILES["fieldTypes"].items():
        cost_fields.append(
            '("' + name + '", toJson c.costs.' + name + (".toNat" if ty == "U64" else "") + ")"
        )
    state_fields = [
        '("' + n + '", toJson c.stateCosts.' + n + ")"
        for n in PROFILES["profiles"]["rawA"]["stateCosts"]
    ]
    limit_fields = [
        '("' + n + '", toJson c.limits.' + n + ")"
        for n in PROFILES["profiles"]["rawA"]["limits"]
    ]
    text += (
        '\nprivate def observeConfig (c : VmConfig) : Json := Json.mkObj [\n  ("costs", Json.mkObj ['
        + ",\n    ".join(cost_fields)
        + ']),\n  ("stateCosts", Json.mkObj ['
        + ", ".join(state_fields)
        + ']),\n  ("limits", Json.mkObj ['
        + ", ".join(limit_fields)
        + "])]\n"
    )
    text += """
private def hexBytes (xs : List UInt8) : String := String.ofList (xs.flatMap fun b =>
  let hi := b.toNat / 16
  let lo := b.toNat % 16
  [Char.ofNat (if hi < 10 then hi + 48 else hi + 87),
   Char.ofNat (if lo < 10 then lo + 48 else lo + 87)])
private def observeMemory (m : Memory) : Json :=
  Json.mkObj [("size", toJson m.size), ("hex", toJson (hexBytes m.toBytes))]
private def scalarFrame (id domain backend : String) (cfg : VmConfig) (n : Nat) : Json :=
  let before := Json.mkObj [("config", observeConfig cfg), ("n", toJson n)]
  let r := calculateMemoryGasCost cfg n
  let after := Json.mkObj [("config", observeConfig cfg), ("n", toJson n)]
  Json.mkObj [("schema", toJson "memory-pricing-v1"), ("id", toJson id),
    ("domain", toJson domain), ("backend", toJson backend), ("operation", toJson "scalar"),
    ("input", before), ("output", Json.mkObj [("result", Json.mkObj [("cost", toJson r)]), ("after", after)]),
    ("types", Json.mkObj [("config", toJson "VmConfig"), ("n", toJson "Nat"),
      ("result", Json.mkObj [("cost", toJson "Nat")])])]
private def extensionFrame (id domain backend : String) (cfg : VmConfig) (m : Memory)
    (ws : List (U256 × U256)) : Json :=
  let before := Json.mkObj [("config", observeConfig cfg), ("memory", observeMemory m),
    ("windows", toJson (ws.map fun w => [w.1.toNat, w.2.toNat]))]
  let r := calculateGasExtendMemory cfg m ws
  let after := Json.mkObj [("config", observeConfig cfg), ("memory", observeMemory m),
    ("windows", toJson (ws.map fun w => [w.1.toNat, w.2.toNat]))]
  Json.mkObj [("schema", toJson "memory-pricing-v1"), ("id", toJson id),
    ("domain", toJson domain), ("backend", toJson backend), ("operation", toJson "extension"),
    ("input", before), ("output", Json.mkObj [("result", Json.mkObj [("cost", toJson r.cost),
      ("expandBy", toJson r.expandBy)]), ("after", after)]),
    ("types", Json.mkObj [("config", toJson "VmConfig"), ("memory", toJson "Memory"),
      ("windows", toJson "List(U256,U256)"),
      ("result", Json.mkObj [("cost", toJson "Nat"), ("expandBy", toJson "Nat")])])]

def main (args : List String) : IO Unit := do
  let backend := args.headD "interpreted"
"""
    for row in ROWS:
        call = "scalarFrame" if scalar(row) else "extensionFrame"
        arg = row["size"] if scalar(row) else f"({lean_memory(row)}) {lean_words(row)}"
        text += f'  IO.println (({call} "{row["id"]}" "{row["domain"]}" backend ({cfg_expr(row)}) {arg}).compress)\n'
    return text


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    group = ap.add_mutually_exclusive_group(required=True)
    group.add_argument("--self-test", action="store_true")
    group.add_argument("--emit-lean", action="store_true")
    group.add_argument("--emit-guards", action="store_true")
    group.add_argument("--frames", type=Path)
    ap.add_argument("--backend", choices=["interpreted", "native"], default="interpreted")
    ap.add_argument("--source-frames", type=Path)
    ap.add_argument("--source-binding-digest")
    args = ap.parse_args()
    if args.self_test:
        self_test()
        return
    if args.emit_lean:
        print(emit_lean(), end="")
        return
    if args.emit_guards:
        print(emit_guards(), end="")
        return
    actual = parse(args.frames.read_bytes(), expected_target(args.backend))
    source_count = 0
    if args.source_frames:
        if not args.source_binding_digest or not re.fullmatch(
            "[0-9a-f]{64}", args.source_binding_digest
        ):
            raise ValueError("frozen preflight catalog binding digest required")
        src = parse(
            args.source_frames.read_bytes(), expected_source(args.source_binding_digest)
        )
        target = {r["id"]: r for r in actual}
        for row in src:
            same(row["output"]["result"], target[row["id"]]["output"]["result"])
            same(
                row["input"],
                {k: v for k, v in target[row["id"]]["input"].items() if k != "config"},
            )
        source_count = len(src)
    print(
        json.dumps(
            {
                "targetRowsCompared": len(actual),
                "backend": args.backend,
                "sourceRowsCompared": source_count,
            }
        )
    )


if __name__ == "__main__":
    try:
        main()
    except (ValueError, TypeError, UnicodeError, OSError, json.JSONDecodeError) as exc:
        print(str(exc), file=sys.stderr)
        sys.exit(1)
