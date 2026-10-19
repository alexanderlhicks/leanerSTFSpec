#!/usr/bin/env python3
"""Complete call/init observations with strict literal and source-frame comparison.

This reader consumes caller-supplied complete target/source frames and a previously
authenticated binding-catalog digest. It neither produces nor authenticates the
source baseline. See EthVmCore §3 for the dated external evidence and limitations.
No runtime pricing model generates the frozen expectations.
"""

import argparse
import copy
import json
import re
import sys
from pathlib import Path

CATALOG = {
    "schema": "call-init-target-inputs-v1",
    "status": "literal input materialization only; no helper/model execution",
    "pin": "e1a316a06fc3d3e0a5da36fdc78580811e9d8a36",
    "count": 32,
    "cases": [
        {
            "id": "C01",
            "operation": "call",
            "input": {
                "value": 0,
                "gas": 0,
                "gasLeft": 0,
                "memoryCost": 0,
                "extraGas": 0,
                "stipend": {"mode": "omitted"},
            },
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "C02",
            "operation": "call",
            "input": {
                "value": 1,
                "gas": 0,
                "gasLeft": 0,
                "memoryCost": 0,
                "extraGas": 0,
                "stipend": {"mode": "omitted"},
            },
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "C03",
            "operation": "call",
            "input": {
                "value": 1,
                "gas": 100,
                "gasLeft": 63,
                "memoryCost": 0,
                "extraGas": 0,
                "stipend": {"mode": "omitted"},
            },
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "C04",
            "operation": "call",
            "input": {
                "value": 1,
                "gas": 100,
                "gasLeft": 64,
                "memoryCost": 0,
                "extraGas": 0,
                "stipend": {"mode": "omitted"},
            },
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "C05",
            "operation": "call",
            "input": {
                "value": 1,
                "gas": 100,
                "gasLeft": 65,
                "memoryCost": 0,
                "extraGas": 0,
                "stipend": {"mode": "omitted"},
            },
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "C06",
            "operation": "call",
            "input": {
                "value": 0,
                "gas": 5,
                "gasLeft": 100,
                "memoryCost": 0,
                "extraGas": 0,
                "stipend": {"mode": "explicit", "value": 7},
            },
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "C07",
            "operation": "call",
            "input": {
                "value": 1,
                "gas": 5,
                "gasLeft": 100,
                "memoryCost": 0,
                "extraGas": 0,
                "stipend": {"mode": "explicit", "value": 7},
            },
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "C08",
            "operation": "call",
            "input": {
                "value": (
                    115792089237316195423570985008687907853269984665640564039457584007913129639935
                ),
                "gas": 5,
                "gasLeft": 100,
                "memoryCost": 0,
                "extraGas": 0,
                "stipend": {"mode": "explicit", "value": 0},
            },
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "C09",
            "operation": "call",
            "input": {
                "value": 1,
                "gas": 10,
                "gasLeft": 9,
                "memoryCost": 4,
                "extraGas": 6,
                "stipend": {"mode": "omitted"},
            },
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "C10",
            "operation": "call",
            "input": {
                "value": 1,
                "gas": 10,
                "gasLeft": 10,
                "memoryCost": 4,
                "extraGas": 6,
                "stipend": {"mode": "omitted"},
            },
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "C11",
            "operation": "call",
            "input": {
                "value": 0,
                "gas": 100,
                "gasLeft": 74,
                "memoryCost": 4,
                "extraGas": 6,
                "stipend": {"mode": "omitted"},
            },
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "C12",
            "operation": "call",
            "input": {
                "value": 1,
                "gas": 100,
                "gasLeft": 75,
                "memoryCost": 4,
                "extraGas": 6,
                "stipend": {"mode": "explicit", "value": 7},
            },
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "C13",
            "operation": "call",
            "input": {
                "value": 0,
                "gas": 0,
                "gasLeft": 4,
                "memoryCost": 5,
                "extraGas": 0,
                "stipend": {"mode": "omitted"},
            },
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "C14",
            "operation": "call",
            "input": {
                "value": 0,
                "gas": 100,
                "gasLeft": 63,
                "memoryCost": 64,
                "extraGas": 0,
                "stipend": {"mode": "omitted"},
            },
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "C15",
            "operation": "call",
            "input": {
                "value": 0,
                "gas": 100,
                "gasLeft": 64,
                "memoryCost": 64,
                "extraGas": 0,
                "stipend": {"mode": "omitted"},
            },
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "C16",
            "operation": "call",
            "input": {
                "value": 1,
                "gas": 18446744073709551616,
                "gasLeft": 18446744073709551616,
                "memoryCost": 0,
                "extraGas": 0,
                "stipend": {"mode": "omitted"},
            },
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "I01",
            "operation": "init",
            "input": {"n": 0},
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "I02",
            "operation": "init",
            "input": {"n": 1},
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "I03",
            "operation": "init",
            "input": {"n": 31},
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "I04",
            "operation": "init",
            "input": {"n": 32},
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "I05",
            "operation": "init",
            "input": {"n": 33},
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "I06",
            "operation": "init",
            "input": {"n": 63},
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "I07",
            "operation": "init",
            "input": {"n": 64},
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "I08",
            "operation": "init",
            "input": {"n": 65},
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "I09",
            "operation": "init",
            "input": {"n": 18446744073709551617},
            "domain": "pinned-source",
            "configProfile": "pinned",
        },
        {
            "id": "G01",
            "domain": "generic-Lean-only",
            "operation": "call",
            "configProfile": "generic",
            "input": {
                "value": 0,
                "gas": 0,
                "gasLeft": 0,
                "memoryCost": 0,
                "extraGas": 0,
                "stipend": {"mode": "omitted"},
            },
        },
        {
            "id": "G02",
            "domain": "generic-Lean-only",
            "operation": "call",
            "configProfile": "generic",
            "input": {
                "value": 1,
                "gas": 0,
                "gasLeft": 0,
                "memoryCost": 0,
                "extraGas": 0,
                "stipend": {"mode": "omitted"},
            },
        },
        {
            "id": "G03",
            "domain": "generic-Lean-only",
            "operation": "call",
            "configProfile": "generic",
            "input": {
                "value": 0,
                "gas": 10,
                "gasLeft": 64,
                "memoryCost": 0,
                "extraGas": 0,
                "stipend": {"mode": "explicit", "value": 0},
            },
        },
        {
            "id": "G04",
            "domain": "generic-Lean-only",
            "operation": "call",
            "configProfile": "generic",
            "input": {
                "value": 1,
                "gas": 10,
                "gasLeft": 64,
                "memoryCost": 0,
                "extraGas": 0,
                "stipend": {"mode": "explicit", "value": 0},
            },
        },
        {
            "id": "G05",
            "domain": "generic-Lean-only",
            "operation": "init",
            "configProfile": "zeroWord",
            "input": {"n": 33},
        },
        {
            "id": "G06",
            "domain": "generic-Lean-only",
            "operation": "init",
            "configProfile": "generic",
            "input": {"n": 1},
        },
        {
            "id": "G07",
            "domain": "generic-Lean-only",
            "operation": "init",
            "configProfile": "generic",
            "input": {"n": 33},
        },
    ],
}
EXPECTED = {
    "schema": "call-init-target-expected-v1",
    "status": "unchanged hand literals from WI241/242, not observations/computed outputs",
    "results": [
        {"id": "C01", "result": {"cost": 0, "subCall": 0}},
        {"id": "C02", "result": {"cost": 0, "subCall": 2300}},
        {"id": "C03", "result": {"cost": 63, "subCall": 2363}},
        {"id": "C04", "result": {"cost": 63, "subCall": 2363}},
        {"id": "C05", "result": {"cost": 64, "subCall": 2364}},
        {"id": "C06", "result": {"cost": 5, "subCall": 5}},
        {"id": "C07", "result": {"cost": 5, "subCall": 12}},
        {"id": "C08", "result": {"cost": 5, "subCall": 5}},
        {"id": "C09", "result": {"cost": 16, "subCall": 2310}},
        {"id": "C10", "result": {"cost": 6, "subCall": 2300}},
        {"id": "C11", "result": {"cost": 69, "subCall": 63}},
        {"id": "C12", "result": {"cost": 70, "subCall": 71}},
        {"id": "C13", "result": {"cost": 0, "subCall": 0}},
        {"id": "C14", "result": {"cost": 100, "subCall": 100}},
        {"id": "C15", "result": {"cost": 0, "subCall": 0}},
        {
            "id": "C16",
            "result": {"cost": 18158513697557839872, "subCall": 18158513697557842172},
        },
        {"id": "I01", "result": {"cost": 0}},
        {"id": "I02", "result": {"cost": 2}},
        {"id": "I03", "result": {"cost": 2}},
        {"id": "I04", "result": {"cost": 2}},
        {"id": "I05", "result": {"cost": 4}},
        {"id": "I06", "result": {"cost": 4}},
        {"id": "I07", "result": {"cost": 4}},
        {"id": "I08", "result": {"cost": 6}},
        {"id": "I09", "result": {"cost": 1152921504606846978}},
        {"id": "G01", "result": {"cost": 0, "subCall": 7}},
        {"id": "G02", "result": {"cost": 0, "subCall": 19}},
        {"id": "G03", "result": {"cost": 10, "subCall": 17}},
        {"id": "G04", "result": {"cost": 10, "subCall": 10}},
        {"id": "G05", "result": {"cost": 0}},
        {"id": "G06", "result": {"cost": 5}},
        {"id": "G07", "result": {"cost": 10}},
    ],
}
PROFILES = {
    "schema": "call-init-private-raw-fixtures-v1",
    "status": "complete literal test records; only three relevant pinned prices, no "
    "coherent Amsterdam config/default/factory claim",
    "costFieldTypes": {
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
        "perBlob": "STFSpec.Base.U64",
        "blobScheduleTarget": "STFSpec.Base.U64",
        "blobTargetGasPerBlock": "STFSpec.Base.U64",
        "blobBaseCost": "Nat",
        "blobScheduleMax": "STFSpec.Base.U64",
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
        "pinned": {
            "costs": {
                "base": 0,
                "veryLow": 0,
                "low": 0,
                "mid": 0,
                "high": 0,
                "warmAccess": 0,
                "coldAccountAccess": 0,
                "coldStorageAccess": 0,
                "storageWrite": 0,
                "callStipend": 2300,
                "accountWrite": 0,
                "callValue": 0,
                "codeInitPerWord": 2,
                "createAccess": 0,
                "zero": 0,
                "memoryPerWord": 0,
                "fastStep": 0,
                "refundStorageClear": -11,
                "precompileEcrecover": 0,
                "precompileP256Verify": 0,
                "precompileSha256Base": 0,
                "precompileSha256PerWord": 0,
                "precompileRipemd160Base": 0,
                "precompileRipemd160PerWord": 0,
                "precompileIdentityBase": 0,
                "precompileIdentityPerWord": 0,
                "precompileBlake2FPerRound": 0,
                "precompilePointEvaluation": 0,
                "precompileBlsG1Add": 0,
                "precompileBlsG1Mul": 0,
                "precompileBlsG1Map": 0,
                "precompileBlsG2Add": 0,
                "precompileBlsG2Mul": 0,
                "precompileBlsG2Map": 0,
                "precompileEcAdd": 0,
                "precompileEcMul": 0,
                "precompileEcPairingBase": 0,
                "precompileEcPairingPerPoint": 0,
                "perBlob": 0,
                "blobScheduleTarget": 0,
                "blobTargetGasPerBlock": 0,
                "blobBaseCost": 0,
                "blobScheduleMax": 0,
                "blobMinGasPrice": 0,
                "blobBaseFeeUpdateFraction": 0,
                "blockAccessListItem": 0,
                "txBase": 0,
                "txValueCost": 0,
                "txDataTokenStandard": 0,
                "txDataTokenFloor": 0,
                "txAccessListAddress": 0,
                "txAccessListStorageKey": 0,
                "txMaxGasLimit": 0,
                "txMaxTotalGasLimit": 0,
                "authTupleBytes": 0,
                "executionPerAuthBaseCost": 0,
                "limitAdjustmentFactor": 0,
                "limitMinimum": 0,
                "opcodeAdd": 0,
                "opcodeSub": 0,
                "opcodeMul": 0,
                "opcodeDiv": 0,
                "opcodeSdiv": 0,
                "opcodeMod": 0,
                "opcodeSmod": 0,
                "opcodeAddmod": 0,
                "opcodeMulmod": 0,
                "opcodeSignextend": 0,
                "opcodeLt": 0,
                "opcodeGt": 0,
                "opcodeSlt": 0,
                "opcodeSgt": 0,
                "opcodeEq": 0,
                "opcodeIsZero": 0,
                "opcodeAnd": 0,
                "opcodeOr": 0,
                "opcodeXor": 0,
                "opcodeNot": 0,
                "opcodeByte": 0,
                "opcodeShl": 0,
                "opcodeShr": 0,
                "opcodeSar": 0,
                "opcodeClz": 0,
                "opcodeJump": 0,
                "opcodeJumpi": 0,
                "opcodeJumpDest": 0,
                "opcodeCallDataLoad": 0,
                "opcodeBlockHash": 0,
                "opcodeCoinbase": 0,
                "opcodePop": 0,
                "opcodeMsize": 0,
                "opcodePc": 0,
                "opcodeGas": 0,
                "opcodeAddress": 0,
                "opcodeOrigin": 0,
                "opcodeCaller": 0,
                "opcodeCallValue": 0,
                "opcodeCallDataSize": 0,
                "opcodeCodeSize": 0,
                "opcodeGasPrice": 0,
                "opcodeTimestamp": 0,
                "opcodeNumber": 0,
                "opcodeGasLimit": 0,
                "opcodePrevRandao": 0,
                "opcodeReturnDataSize": 0,
                "opcodeChainId": 0,
                "opcodeSelfBalance": 0,
                "opcodeBaseFee": 0,
                "opcodeBlobBaseFee": 0,
                "opcodeSlotNum": 0,
                "opcodeBlobHash": 0,
                "opcodePush": 0,
                "opcodePush0": 0,
                "opcodeDup": 0,
                "opcodeSwap": 0,
                "opcodeDupn": 0,
                "opcodeSwapn": 0,
                "opcodeExchange": 0,
                "opcodeTload": 0,
                "opcodeTstore": 0,
                "opcodeReturnDataCopyBase": 0,
                "opcodeReturnDataCopyPerWord": 0,
                "opcodeCallDataCopyBase": 0,
                "opcodeCodeCopyBase": 0,
                "opcodeMcopyBase": 0,
                "opcodeMloadBase": 0,
                "opcodeMstoreBase": 0,
                "opcodeMstore8Base": 0,
                "opcodeCopyPerWord": 0,
                "opcodeExpBase": 0,
                "opcodeExpPerByte": 0,
                "opcodeKeccak256Base": 0,
                "opcodeKeccak256PerWord": 0,
                "opcodeLogBase": 0,
                "opcodeLogDataPerByte": 0,
                "opcodeLogTopic": 0,
                "opcodeSelfDestructBase": 0,
                "blsPairingBase": 0,
                "blsPairingPerPair": 0,
                "blsG1KDiscount": [],
                "blsG2KDiscount": [],
                "blsG1MaxDiscount": 0,
                "blsG2MaxDiscount": 0,
                "blsMultiplier": 0,
            },
            "stateCosts": {
                "costPerStateByte": 2,
                "bytesPerNewAccount": 3,
                "bytesPerStorageSet": 4,
                "bytesPerAuthBase": 5,
            },
            "limits": {"stackDepthLimit": 7, "maxCodeSize": 8, "maxInitCodeSize": 9},
        },
        "generic": {
            "costs": {
                "base": 1,
                "veryLow": 1,
                "low": 1,
                "mid": 1,
                "high": 1,
                "warmAccess": 1,
                "coldAccountAccess": 1,
                "coldStorageAccess": 1,
                "storageWrite": 1,
                "callStipend": 19,
                "accountWrite": 1,
                "callValue": 1,
                "codeInitPerWord": 5,
                "createAccess": 1,
                "zero": 7,
                "memoryPerWord": 1,
                "fastStep": 1,
                "refundStorageClear": -11,
                "precompileEcrecover": 1,
                "precompileP256Verify": 1,
                "precompileSha256Base": 1,
                "precompileSha256PerWord": 1,
                "precompileRipemd160Base": 1,
                "precompileRipemd160PerWord": 1,
                "precompileIdentityBase": 1,
                "precompileIdentityPerWord": 1,
                "precompileBlake2FPerRound": 1,
                "precompilePointEvaluation": 1,
                "precompileBlsG1Add": 1,
                "precompileBlsG1Mul": 1,
                "precompileBlsG1Map": 1,
                "precompileBlsG2Add": 1,
                "precompileBlsG2Mul": 1,
                "precompileBlsG2Map": 1,
                "precompileEcAdd": 1,
                "precompileEcMul": 1,
                "precompileEcPairingBase": 1,
                "precompileEcPairingPerPoint": 1,
                "perBlob": 1,
                "blobScheduleTarget": 1,
                "blobTargetGasPerBlock": 1,
                "blobBaseCost": 1,
                "blobScheduleMax": 1,
                "blobMinGasPrice": 1,
                "blobBaseFeeUpdateFraction": 1,
                "blockAccessListItem": 1,
                "txBase": 1,
                "txValueCost": 1,
                "txDataTokenStandard": 1,
                "txDataTokenFloor": 1,
                "txAccessListAddress": 1,
                "txAccessListStorageKey": 1,
                "txMaxGasLimit": 1,
                "txMaxTotalGasLimit": 1,
                "authTupleBytes": 1,
                "executionPerAuthBaseCost": 1,
                "limitAdjustmentFactor": 1,
                "limitMinimum": 1,
                "opcodeAdd": 1,
                "opcodeSub": 1,
                "opcodeMul": 1,
                "opcodeDiv": 1,
                "opcodeSdiv": 1,
                "opcodeMod": 1,
                "opcodeSmod": 1,
                "opcodeAddmod": 1,
                "opcodeMulmod": 1,
                "opcodeSignextend": 1,
                "opcodeLt": 1,
                "opcodeGt": 1,
                "opcodeSlt": 1,
                "opcodeSgt": 1,
                "opcodeEq": 1,
                "opcodeIsZero": 1,
                "opcodeAnd": 1,
                "opcodeOr": 1,
                "opcodeXor": 1,
                "opcodeNot": 1,
                "opcodeByte": 1,
                "opcodeShl": 1,
                "opcodeShr": 1,
                "opcodeSar": 1,
                "opcodeClz": 1,
                "opcodeJump": 1,
                "opcodeJumpi": 1,
                "opcodeJumpDest": 1,
                "opcodeCallDataLoad": 1,
                "opcodeBlockHash": 1,
                "opcodeCoinbase": 1,
                "opcodePop": 1,
                "opcodeMsize": 1,
                "opcodePc": 1,
                "opcodeGas": 1,
                "opcodeAddress": 1,
                "opcodeOrigin": 1,
                "opcodeCaller": 1,
                "opcodeCallValue": 1,
                "opcodeCallDataSize": 1,
                "opcodeCodeSize": 1,
                "opcodeGasPrice": 1,
                "opcodeTimestamp": 1,
                "opcodeNumber": 1,
                "opcodeGasLimit": 1,
                "opcodePrevRandao": 1,
                "opcodeReturnDataSize": 1,
                "opcodeChainId": 1,
                "opcodeSelfBalance": 1,
                "opcodeBaseFee": 1,
                "opcodeBlobBaseFee": 1,
                "opcodeSlotNum": 1,
                "opcodeBlobHash": 1,
                "opcodePush": 1,
                "opcodePush0": 1,
                "opcodeDup": 1,
                "opcodeSwap": 1,
                "opcodeDupn": 1,
                "opcodeSwapn": 1,
                "opcodeExchange": 1,
                "opcodeTload": 1,
                "opcodeTstore": 1,
                "opcodeReturnDataCopyBase": 1,
                "opcodeReturnDataCopyPerWord": 1,
                "opcodeCallDataCopyBase": 1,
                "opcodeCodeCopyBase": 1,
                "opcodeMcopyBase": 1,
                "opcodeMloadBase": 1,
                "opcodeMstoreBase": 1,
                "opcodeMstore8Base": 1,
                "opcodeCopyPerWord": 1,
                "opcodeExpBase": 1,
                "opcodeExpPerByte": 1,
                "opcodeKeccak256Base": 1,
                "opcodeKeccak256PerWord": 1,
                "opcodeLogBase": 1,
                "opcodeLogDataPerByte": 1,
                "opcodeLogTopic": 1,
                "opcodeSelfDestructBase": 1,
                "blsPairingBase": 1,
                "blsPairingPerPair": 1,
                "blsG1KDiscount": [1, 0, 2],
                "blsG2KDiscount": [1, 0, 2],
                "blsG1MaxDiscount": 1,
                "blsG2MaxDiscount": 1,
                "blsMultiplier": 1,
            },
            "stateCosts": {
                "costPerStateByte": 2,
                "bytesPerNewAccount": 3,
                "bytesPerStorageSet": 4,
                "bytesPerAuthBase": 5,
            },
            "limits": {"stackDepthLimit": 7, "maxCodeSize": 8, "maxInitCodeSize": 9},
        },
        "zeroWord": {
            "costs": {
                "base": 1,
                "veryLow": 1,
                "low": 1,
                "mid": 1,
                "high": 1,
                "warmAccess": 1,
                "coldAccountAccess": 1,
                "coldStorageAccess": 1,
                "storageWrite": 1,
                "callStipend": 19,
                "accountWrite": 1,
                "callValue": 1,
                "codeInitPerWord": 0,
                "createAccess": 1,
                "zero": 7,
                "memoryPerWord": 1,
                "fastStep": 1,
                "refundStorageClear": -11,
                "precompileEcrecover": 1,
                "precompileP256Verify": 1,
                "precompileSha256Base": 1,
                "precompileSha256PerWord": 1,
                "precompileRipemd160Base": 1,
                "precompileRipemd160PerWord": 1,
                "precompileIdentityBase": 1,
                "precompileIdentityPerWord": 1,
                "precompileBlake2FPerRound": 1,
                "precompilePointEvaluation": 1,
                "precompileBlsG1Add": 1,
                "precompileBlsG1Mul": 1,
                "precompileBlsG1Map": 1,
                "precompileBlsG2Add": 1,
                "precompileBlsG2Mul": 1,
                "precompileBlsG2Map": 1,
                "precompileEcAdd": 1,
                "precompileEcMul": 1,
                "precompileEcPairingBase": 1,
                "precompileEcPairingPerPoint": 1,
                "perBlob": 1,
                "blobScheduleTarget": 1,
                "blobTargetGasPerBlock": 1,
                "blobBaseCost": 1,
                "blobScheduleMax": 1,
                "blobMinGasPrice": 1,
                "blobBaseFeeUpdateFraction": 1,
                "blockAccessListItem": 1,
                "txBase": 1,
                "txValueCost": 1,
                "txDataTokenStandard": 1,
                "txDataTokenFloor": 1,
                "txAccessListAddress": 1,
                "txAccessListStorageKey": 1,
                "txMaxGasLimit": 1,
                "txMaxTotalGasLimit": 1,
                "authTupleBytes": 1,
                "executionPerAuthBaseCost": 1,
                "limitAdjustmentFactor": 1,
                "limitMinimum": 1,
                "opcodeAdd": 1,
                "opcodeSub": 1,
                "opcodeMul": 1,
                "opcodeDiv": 1,
                "opcodeSdiv": 1,
                "opcodeMod": 1,
                "opcodeSmod": 1,
                "opcodeAddmod": 1,
                "opcodeMulmod": 1,
                "opcodeSignextend": 1,
                "opcodeLt": 1,
                "opcodeGt": 1,
                "opcodeSlt": 1,
                "opcodeSgt": 1,
                "opcodeEq": 1,
                "opcodeIsZero": 1,
                "opcodeAnd": 1,
                "opcodeOr": 1,
                "opcodeXor": 1,
                "opcodeNot": 1,
                "opcodeByte": 1,
                "opcodeShl": 1,
                "opcodeShr": 1,
                "opcodeSar": 1,
                "opcodeClz": 1,
                "opcodeJump": 1,
                "opcodeJumpi": 1,
                "opcodeJumpDest": 1,
                "opcodeCallDataLoad": 1,
                "opcodeBlockHash": 1,
                "opcodeCoinbase": 1,
                "opcodePop": 1,
                "opcodeMsize": 1,
                "opcodePc": 1,
                "opcodeGas": 1,
                "opcodeAddress": 1,
                "opcodeOrigin": 1,
                "opcodeCaller": 1,
                "opcodeCallValue": 1,
                "opcodeCallDataSize": 1,
                "opcodeCodeSize": 1,
                "opcodeGasPrice": 1,
                "opcodeTimestamp": 1,
                "opcodeNumber": 1,
                "opcodeGasLimit": 1,
                "opcodePrevRandao": 1,
                "opcodeReturnDataSize": 1,
                "opcodeChainId": 1,
                "opcodeSelfBalance": 1,
                "opcodeBaseFee": 1,
                "opcodeBlobBaseFee": 1,
                "opcodeSlotNum": 1,
                "opcodeBlobHash": 1,
                "opcodePush": 1,
                "opcodePush0": 1,
                "opcodeDup": 1,
                "opcodeSwap": 1,
                "opcodeDupn": 1,
                "opcodeSwapn": 1,
                "opcodeExchange": 1,
                "opcodeTload": 1,
                "opcodeTstore": 1,
                "opcodeReturnDataCopyBase": 1,
                "opcodeReturnDataCopyPerWord": 1,
                "opcodeCallDataCopyBase": 1,
                "opcodeCodeCopyBase": 1,
                "opcodeMcopyBase": 1,
                "opcodeMloadBase": 1,
                "opcodeMstoreBase": 1,
                "opcodeMstore8Base": 1,
                "opcodeCopyPerWord": 1,
                "opcodeExpBase": 1,
                "opcodeExpPerByte": 1,
                "opcodeKeccak256Base": 1,
                "opcodeKeccak256PerWord": 1,
                "opcodeLogBase": 1,
                "opcodeLogDataPerByte": 1,
                "opcodeLogTopic": 1,
                "opcodeSelfDestructBase": 1,
                "blsPairingBase": 1,
                "blsPairingPerPair": 1,
                "blsG1KDiscount": [1, 0, 2],
                "blsG2KDiscount": [1, 0, 2],
                "blsG1MaxDiscount": 1,
                "blsG2MaxDiscount": 1,
                "blsMultiplier": 1,
            },
            "stateCosts": {
                "costPerStateByte": 2,
                "bytesPerNewAccount": 3,
                "bytesPerStorageSet": 4,
                "bytesPerAuthBase": 5,
            },
            "limits": {"stackDepthLimit": 7, "maxCodeSize": 8, "maxInitCodeSize": 9},
        },
    },
}
WITNESSES = {
    "status": "unchanged hand planned charge witnesses; actual chargeGas UNRUN",
    "initOtherCharge": 0,
    "witnesses": [
        {
            "id": "C09",
            "name": "whole-shortage",
            "meter": {
                "gasLeft": 9,
                "stateGasLeft": 17,
                "stateGasBaseline": 3,
                "refundCounter": -9,
                "stateGasSpilled": 5,
                "stateGasCommittedSpill": 7,
            },
            "amount": 20,
            "result": {"kind": "error", "error": "outOfGas"},
        },
        {
            "id": "C10",
            "name": "whole-equality",
            "meter": {
                "gasLeft": 10,
                "stateGasLeft": 17,
                "stateGasBaseline": 3,
                "refundCounter": -9,
                "stateGasSpilled": 5,
                "stateGasCommittedSpill": 7,
            },
            "amount": 10,
            "result": {
                "kind": "ok",
                "meter": {
                    "gasLeft": 0,
                    "stateGasLeft": 17,
                    "stateGasBaseline": 3,
                    "refundCounter": -9,
                    "stateGasSpilled": 5,
                    "stateGasCommittedSpill": 7,
                },
            },
        },
        {
            "id": "C13",
            "name": "memory-only-shortage",
            "meter": {
                "gasLeft": 4,
                "stateGasLeft": 17,
                "stateGasBaseline": 3,
                "refundCounter": -9,
                "stateGasSpilled": 5,
                "stateGasCommittedSpill": 7,
            },
            "amount": 5,
            "result": {"kind": "error", "error": "outOfGas"},
        },
        {
            "id": "I05",
            "name": "init-equality",
            "meter": {
                "gasLeft": 4,
                "stateGasLeft": 17,
                "stateGasBaseline": 3,
                "refundCounter": -9,
                "stateGasSpilled": 5,
                "stateGasCommittedSpill": 7,
            },
            "amount": 4,
            "result": {
                "kind": "ok",
                "meter": {
                    "gasLeft": 0,
                    "stateGasLeft": 17,
                    "stateGasBaseline": 3,
                    "refundCounter": -9,
                    "stateGasSpilled": 5,
                    "stateGasCommittedSpill": 7,
                },
            },
        },
        {
            "id": "I05",
            "name": "init-shortage",
            "meter": {
                "gasLeft": 3,
                "stateGasLeft": 17,
                "stateGasBaseline": 3,
                "refundCounter": -9,
                "stateGasSpilled": 5,
                "stateGasCommittedSpill": 7,
            },
            "amount": 4,
            "result": {"kind": "error", "error": "outOfGas"},
        },
        {
            "id": "G05",
            "name": "zero-price-identity",
            "meter": {
                "gasLeft": 0,
                "stateGasLeft": 17,
                "stateGasBaseline": 3,
                "refundCounter": -9,
                "stateGasSpilled": 5,
                "stateGasCommittedSpill": 7,
            },
            "amount": 0,
            "result": {
                "kind": "ok",
                "meter": {
                    "gasLeft": 0,
                    "stateGasLeft": 17,
                    "stateGasBaseline": 3,
                    "refundCounter": -9,
                    "stateGasSpilled": 5,
                    "stateGasCommittedSpill": 7,
                },
            },
        },
    ],
}

BINDING = "80a2e38c1fdbdcb7b489eb87c9e6778edfa6beca291873133745408bf27e314e"
UINT = "ethereum_types.numeric.Uint"
UWORD = "ethereum_types.numeric.U256"
RESULTS = {r["id"]: r["result"] for r in EXPECTED["results"]}


def target_types(row):
    args = (
        {"n": "Nat"}
        if row["operation"] == "init"
        else {
            "value": "U256",
            "gas": "Nat",
            "gasLeft": "Nat",
            "memoryCost": "Nat",
            "extraGas": "Nat",
            "stipend": {"mode": row["input"]["stipend"]["mode"], "selected": "Nat"},
        }
    )
    result = (
        {"container": "Nat", "fields": {"cost": "Nat"}}
        if row["operation"] == "init"
        else {"container": "MessageCallGas", "fields": {"cost": "Nat", "subCall": "Nat"}}
    )
    return {"config": "VmConfig", "input": args, "result": result}


def expected_target(backend):
    frames = []
    for row in CATALOG["cases"]:
        args = {
            "config": copy.deepcopy(PROFILES["profiles"][row["configProfile"]]),
            **copy.deepcopy(row["input"]),
        }
        witnesses = [
            {k: copy.deepcopy(v) for k, v in w.items() if k != "id"}
            for w in WITNESSES["witnesses"]
            if w["id"] == row["id"]
        ]
        frames.append(
            {
                "schema": "call-init-target-v1",
                "id": row["id"],
                "domain": row["domain"],
                "backend": backend,
                "operation": row["operation"],
                "input": args,
                "output": {
                    "result": copy.deepcopy(RESULTS[row["id"]]),
                    "after": copy.deepcopy(args),
                },
                "types": target_types(row),
                "charge": witnesses,
            }
        )
    return frames


def expected_source(digest):
    frames = []
    policy = {
        k: {"value": v, "class": UINT}
        for k, v in {
            "zero": 0,
            "callStipend": 2300,
            "capturedDefault": 2300,
            "codeInitPerWord": 2,
        }.items()
    }
    for row in CATALOG["cases"]:
        if row["domain"] != "pinned-source":
            continue
        call = row["operation"] == "call"
        classes = (
            {"n": UINT}
            if not call
            else {
                "value": UWORD,
                "gas": UINT,
                "gasLeft": UINT,
                "memoryCost": UINT,
                "extraGas": UINT,
                "stipend": {"mode": row["input"]["stipend"]["mode"], "selectedClass": UINT},
            }
        )
        result = {
            "container": "ethereum.forks.amsterdam.vm.gas.MessageCallGas" if call else UINT,
            "fields": {"cost": UINT, "subCall": UINT} if call else {"cost": UINT},
        }
        frames.append(
            {
                "schema": "call-init-source-v1",
                "id": row["id"],
                "domain": "pinned-source",
                "operation": row["operation"],
                "policy": copy.deepcopy(policy),
                "input": copy.deepcopy(row["input"]),
                "output": {
                    "result": copy.deepcopy(RESULTS[row["id"]]),
                    "after": copy.deepcopy(row["input"]),
                },
                "classes": {
                    "input": classes,
                    "result": result,
                    "after": copy.deepcopy(classes),
                    "bindingDigest": digest,
                },
            }
        )
    return frames


def unique(pairs):
    out = {}
    for k, v in pairs:
        if k in out:
            raise ValueError("duplicate key: " + k)
        out[k] = v
    return out


def invalid_constant(value):
    raise ValueError("nonfinite number: " + value)


def same(actual, expected, path="frame"):
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
    # Explicit framing adapter: source capture remains exact original LF bytes.
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


def couple(targets, sources):
    selected = [r for r in targets if r["domain"] == "pinned-source"]
    if len(selected) != 25 or len(sources) != 25:
        raise ValueError("incorrect coupling domain")
    for target, source in zip(selected, sources):
        same(target["id"], source["id"])
        same(target["operation"], source["operation"])
        args = {k: v for k, v in target["input"].items() if k != "config"}
        after = {k: v for k, v in target["output"]["after"].items() if k != "config"}
        same(args, source["input"])
        same(after, source["output"]["after"])
        same(target["output"]["result"], source["output"]["result"])
        costs = target["input"]["config"]["costs"]
        policy = source["policy"]
        for field in ["zero", "callStipend", "codeInitPerWord"]:
            same(costs[field], policy[field]["value"])
        if target["operation"] == "call" and args["stipend"]["mode"] == "omitted":
            same(costs["callStipend"], policy["capturedDefault"]["value"])


def encode(rows, newline=b"\n"):
    return newline.join(json.dumps(r, separators=(",", ":")).encode() for r in rows) + newline


def self_test():
    target = expected_target("interpreted")
    source = expected_source(BINDING)
    accepted = rejected = 0
    for rows in [target, expected_target("native"), source]:
        for newline in [b"\n", b"\r\n"]:
            parse(encode(rows, newline), rows)
            accepted += 1
    couple(target, source)

    def reject(data, expected):
        nonlocal rejected
        try:
            parse(data, expected)
        except (ValueError, TypeError, UnicodeError):
            rejected += 1
            return
        raise ValueError("parser adversary accepted")

    def mutate(rows, index, path, value):
        bad = copy.deepcopy(rows)
        obj = bad[index]
        for key in path[:-1]:
            obj = obj[key]
        obj[path[-1]] = value
        reject(encode(bad), rows)

    for bad in [True, 1.0, -1, "0"]:
        mutate(target, 0, ["input", "gas"], bad)
        mutate(source, 0, ["input", "gas"], bad)
        mutate(target, 0, ["input", "value"], bad)
    for index, path, bad in [
        (7, ["input", "value"], 1),
        (15, ["output", "result", "cost"], 18158513697557839873),
        (24, ["output", "result", "cost"], 1152921504606846979),
        (8, ["output", "result"], {"cost": 2310, "subCall": 16}),
        (0, ["output", "after", "config", "costs", "zero"], 1),
        (0, ["input", "config", "stateCosts", "bytesPerNewAccount"], 0),
        (0, ["input", "config", "costs", "perBlob"], True),
        (0, ["input", "config", "costs", "refundStorageClear"], -11.0),
        (0, ["input", "stipend"], {"mode": "explicit", "value": 2300}),
        (6, ["input", "stipend", "value"], 8),
        (9, ["charge", 0, "result", "meter", "refundCounter"], 0),
        (9, ["charge", 0, "result", "meter", "stateGasSpilled"], 0),
        (
            8,
            ["charge", 0, "result"],
            {"kind": "ok", "meter": WITNESSES["witnesses"][0]["meter"]},
        ),
        (0, ["types", "input", "gas"], "Uint"),
    ]:
        mutate(target, index, path, bad)
    for path, bad in [
        (["classes", "bindingDigest"], "0" * 64),
        (["classes", "input", "gas"], "builtins.int"),
        (["policy", "capturedDefault", "value"], 19),
        (["policy", "callStipend", "value"], 19),
        (["output", "after", "gas"], 1),
    ]:
        mutate(source, 0, path, bad)
    for rows in [target, source]:
        for data in [
            encode(rows[:-1]),
            encode(rows + [rows[0]]),
            encode(list(reversed(rows))),
            encode(rows)[:-1],
            b"\n" + encode(rows),
            encode(rows) + b"{}\n",
            encode(rows).replace(b"\n", b"\r"),
            encode(rows).replace(b"\n", b"\r\n", 1),
            b"noise\n" + encode(rows),
            b"\xff" + encode(rows),
            encode(rows).replace(b'"gas":0', b'"gas":NaN', 1),
            encode(rows).replace(b'"gas":0', b'"gas":Infinity', 1),
            encode(rows).replace(b'"gas":0', b'"gas":0,"gas":0', 1),
        ]:
            reject(data, rows)
        for key in ["input", "output", "schema"]:
            bad = copy.deepcopy(rows)
            del bad[0][key]
            reject(encode(bad), rows)
        bad = copy.deepcopy(rows)
        bad[0]["output"]["extra"] = 0
        reject(encode(bad), rows)
        bad = copy.deepcopy(rows)
        del bad[0]["output"]["after"]["gas"]
        reject(encode(bad), rows)
    print(
        f"PASS parser self-test accepted={accepted} rejected={rejected}; "
        "synthetic hand frames only"
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--target", type=Path)
    parser.add_argument("--backend", choices=["interpreted", "native"])
    parser.add_argument("--source", type=Path)
    parser.add_argument("--binding-digest")
    args = parser.parse_args()
    try:
        if args.self_test:
            if any(
                x is not None
                for x in [args.target, args.backend, args.source, args.binding_digest]
            ):
                parser.error("--self-test is separate from file comparison")
            self_test()
            return 0
        if any(
            x is None for x in [args.target, args.backend, args.source, args.binding_digest]
        ):
            parser.error(
                "target, backend, source and externally authenticated binding digest are required"
            )
        if args.binding_digest != BINDING:
            raise ValueError("wrong externally authenticated source binding")
        targets = parse(args.target.read_bytes(), expected_target(args.backend))
        sources = parse(args.source.read_bytes(), expected_source(args.binding_digest))
        couple(targets, sources)
        print(f"PASS call-init target32/source25 backend={args.backend}")
        return 0
    except (ValueError, TypeError, UnicodeError, OSError) as exc:
        print("call/init comparison failed: " + str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
