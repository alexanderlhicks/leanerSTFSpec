#!/usr/bin/env python3
"""Complete settlement observations. Target/parser modes never import EELS.

Finite framing limits constrain evidence processing, not the Lean input domain.
"""

import argparse
import copy
import json
from pathlib import Path
import re
import sys

SCHEMA = "transaction-gas-settlement-v1"
CANDIDATE = "q66-three-bounds-u256"
CATALOG = "85e4141895312e8b634aeef4b421da9300826bbdf5c2898ec9fd0992b3e38711"
INPUT_FIELDS = (
    "txGas",
    "calldataFloor",
    "gasLeft",
    "stateGasLeft",
    "refundUnsigned",
    "stateSigned",
)
RESULT_FIELDS = ("gasUsed", "gasLeft", "executionGasUsed", "stateGasUsed")
TARGET = [
    {
        "id": "S01",
        "kind": "helper",
        "input": {
            "txGas": "0",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "0",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "0",
            "gasLeft": "0",
            "executionGasUsed": "0",
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S02",
        "kind": "helper",
        "input": {
            "txGas": "1",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "1",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "1",
            "gasLeft": "0",
            "executionGasUsed": "1",
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S03",
        "kind": "helper",
        "input": {
            "txGas": "4",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "after": {
            "txGas": "4",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "4",
            "gasLeft": "0",
            "executionGasUsed": "4",
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S04",
        "kind": "helper",
        "input": {
            "txGas": "5",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "1",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "5",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "1",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "4",
            "gasLeft": "1",
            "executionGasUsed": "5",
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S05",
        "kind": "helper",
        "input": {
            "txGas": "6",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "1",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "6",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "1",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "5",
            "gasLeft": "1",
            "executionGasUsed": "6",
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S06",
        "kind": "helper",
        "input": {
            "txGas": "9",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "after": {
            "txGas": "9",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "8",
            "gasLeft": "1",
            "executionGasUsed": "9",
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S07",
        "kind": "helper",
        "input": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "10",
            "gasLeft": "0",
            "executionGasUsed": "10",
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S08",
        "kind": "helper",
        "input": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "1",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "1",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "9",
            "gasLeft": "1",
            "executionGasUsed": "10",
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S09",
        "kind": "helper",
        "input": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "8",
            "gasLeft": "2",
            "executionGasUsed": "10",
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S10",
        "kind": "helper",
        "input": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "3",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "3",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "8",
            "gasLeft": "2",
            "executionGasUsed": "10",
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S11",
        "kind": "helper",
        "input": {
            "txGas": "11",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "after": {
            "txGas": "11",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "9",
            "gasLeft": "2",
            "executionGasUsed": "11",
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S12",
        "kind": "helper",
        "input": {
            "txGas": "14",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "after": {
            "txGas": "14",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "12",
            "gasLeft": "2",
            "executionGasUsed": "14",
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S13",
        "kind": "helper",
        "input": {
            "txGas": "15",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "after": {
            "txGas": "15",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "12",
            "gasLeft": "3",
            "executionGasUsed": "15",
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S14",
        "kind": "helper",
        "input": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "result": {
            "gasUsed": "56",
            "gasLeft": "44",
            "executionGasUsed": "40",
            "stateGasUsed": "30",
        },
    },
    {
        "id": "S15",
        "kind": "helper",
        "input": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "13",
            "stateSigned": "30",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "13",
            "stateSigned": "30",
        },
        "result": {
            "gasUsed": "57",
            "gasLeft": "43",
            "executionGasUsed": "40",
            "stateGasUsed": "30",
        },
    },
    {
        "id": "S16",
        "kind": "helper",
        "input": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "15",
            "stateSigned": "30",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "15",
            "stateSigned": "30",
        },
        "result": {
            "gasUsed": "56",
            "gasLeft": "44",
            "executionGasUsed": "40",
            "stateGasUsed": "30",
        },
    },
    {
        "id": "S17",
        "kind": "helper",
        "input": {
            "txGas": "100",
            "calldataFloor": "55",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "55",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "result": {
            "gasUsed": "56",
            "gasLeft": "44",
            "executionGasUsed": "55",
            "stateGasUsed": "30",
        },
    },
    {
        "id": "S18",
        "kind": "helper",
        "input": {
            "txGas": "100",
            "calldataFloor": "56",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "56",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "result": {
            "gasUsed": "56",
            "gasLeft": "44",
            "executionGasUsed": "56",
            "stateGasUsed": "30",
        },
    },
    {
        "id": "S19",
        "kind": "helper",
        "input": {
            "txGas": "100",
            "calldataFloor": "57",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "57",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "result": {
            "gasUsed": "57",
            "gasLeft": "43",
            "executionGasUsed": "57",
            "stateGasUsed": "30",
        },
    },
    {
        "id": "S20",
        "kind": "helper",
        "input": {
            "txGas": "10",
            "calldataFloor": "10",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "1",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "10",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "1",
        },
        "result": {
            "gasUsed": "10",
            "gasLeft": "0",
            "executionGasUsed": "10",
            "stateGasUsed": "1",
        },
    },
    {
        "id": "S21",
        "kind": "helper",
        "input": {
            "txGas": "10",
            "calldataFloor": "10",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "10",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "10",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "10",
        },
        "result": {
            "gasUsed": "10",
            "gasLeft": "0",
            "executionGasUsed": "10",
            "stateGasUsed": "10",
        },
    },
    {
        "id": "S22",
        "kind": "helper",
        "input": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "10",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "10",
        },
        "result": {
            "gasUsed": "8",
            "gasLeft": "2",
            "executionGasUsed": "0",
            "stateGasUsed": "10",
        },
    },
    {
        "id": "S23",
        "kind": "helper",
        "input": {
            "txGas": "10",
            "calldataFloor": "1",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "10",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "1",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "10",
        },
        "result": {
            "gasUsed": "8",
            "gasLeft": "2",
            "executionGasUsed": "1",
            "stateGasUsed": "10",
        },
    },
    {
        "id": "S24",
        "kind": "helper",
        "input": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "-1",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "-1",
        },
        "result": {
            "gasUsed": "8",
            "gasLeft": "2",
            "executionGasUsed": "10",
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S25",
        "kind": "helper",
        "input": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": (
                "-115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": (
                "-115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
        },
        "result": {
            "gasUsed": "8",
            "gasLeft": "2",
            "executionGasUsed": "10",
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S26",
        "kind": "helper",
        "input": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "40",
            "stateGasLeft": "60",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "-1",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "40",
            "stateGasLeft": "60",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "-1",
        },
        "result": {
            "gasUsed": "0",
            "gasLeft": "100",
            "executionGasUsed": "0",
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S27",
        "kind": "helper",
        "input": {
            "txGas": "100",
            "calldataFloor": "20",
            "gasLeft": "40",
            "stateGasLeft": "60",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "20",
            "gasLeft": "40",
            "stateGasLeft": "60",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "20",
            "gasLeft": "80",
            "executionGasUsed": "20",
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S28",
        "kind": "helper",
        "input": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "100",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "100",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "0",
            "gasLeft": "100",
            "executionGasUsed": "0",
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S29",
        "kind": "helper",
        "input": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "100",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "100",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "0",
            "gasLeft": "100",
            "executionGasUsed": "0",
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S30",
        "kind": "helper",
        "input": {
            "txGas": "100",
            "calldataFloor": "100",
            "gasLeft": "40",
            "stateGasLeft": "60",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "100",
            "gasLeft": "40",
            "stateGasLeft": "60",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "100",
            "gasLeft": "0",
            "executionGasUsed": "100",
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S31",
        "kind": "helper",
        "input": {
            "txGas": "64",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "12",
            "stateSigned": "63",
        },
        "after": {
            "txGas": "64",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "12",
            "stateSigned": "63",
        },
        "result": {
            "gasUsed": "52",
            "gasLeft": "12",
            "executionGasUsed": "1",
            "stateGasUsed": "63",
        },
    },
    {
        "id": "S32",
        "kind": "helper",
        "input": {
            "txGas": "64",
            "calldataFloor": "1",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "12",
            "stateSigned": "63",
        },
        "after": {
            "txGas": "64",
            "calldataFloor": "1",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "12",
            "stateSigned": "63",
        },
        "result": {
            "gasUsed": "52",
            "gasLeft": "12",
            "executionGasUsed": "1",
            "stateGasUsed": "63",
        },
    },
    {
        "id": "S33",
        "kind": "helper",
        "input": {
            "txGas": "64",
            "calldataFloor": "2",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "12",
            "stateSigned": "63",
        },
        "after": {
            "txGas": "64",
            "calldataFloor": "2",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "12",
            "stateSigned": "63",
        },
        "result": {
            "gasUsed": "52",
            "gasLeft": "12",
            "executionGasUsed": "2",
            "stateGasUsed": "63",
        },
    },
    {
        "id": "S34",
        "kind": "helper",
        "input": {
            "txGas": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "after": {
            "txGas": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "gasLeft": "0",
            "executionGasUsed": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S35",
        "kind": "helper",
        "input": {
            "txGas": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639937"
            ),
            "calldataFloor": "0",
            "gasLeft": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "1",
        },
        "after": {
            "txGas": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639937"
            ),
            "calldataFloor": "0",
            "gasLeft": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "1",
        },
        "result": {
            "gasUsed": "1",
            "gasLeft": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "executionGasUsed": "0",
            "stateGasUsed": "1",
        },
    },
    {
        "id": "S36",
        "kind": "helper",
        "input": {
            "txGas": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "calldataFloor": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
        },
        "after": {
            "txGas": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "calldataFloor": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
        },
        "result": {
            "gasUsed": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "gasLeft": "0",
            "executionGasUsed": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "stateGasUsed": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
        },
    },
    {
        "id": "S37",
        "kind": "helper",
        "input": {
            "txGas": "18446744073709551626",
            "calldataFloor": "0",
            "gasLeft": "18446744073709551616",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "5",
        },
        "after": {
            "txGas": "18446744073709551626",
            "calldataFloor": "0",
            "gasLeft": "18446744073709551616",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "5",
        },
        "result": {
            "gasUsed": "8",
            "gasLeft": "18446744073709551618",
            "executionGasUsed": "5",
            "stateGasUsed": "5",
        },
    },
    {
        "id": "S38",
        "kind": "helper",
        "input": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "57896044618658097711785492504343953926634992332820282019728792003956564819968"
            ),
            "stateSigned": "0",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "57896044618658097711785492504343953926634992332820282019728792003956564819968"
            ),
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "8",
            "gasLeft": "2",
            "executionGasUsed": "10",
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S39",
        "kind": "helper",
        "input": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "8",
            "gasLeft": "2",
            "executionGasUsed": "10",
            "stateGasUsed": "0",
        },
    },
    {
        "id": "S40",
        "kind": "helper",
        "input": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "20",
            "stateGasLeft": "10",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "20",
            "stateGasLeft": "10",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "result": {
            "gasUsed": "56",
            "gasLeft": "44",
            "executionGasUsed": "40",
            "stateGasUsed": "30",
        },
    },
    {
        "id": "S41",
        "kind": "helper",
        "input": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "40",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "40",
        },
        "result": {
            "gasUsed": "56",
            "gasLeft": "44",
            "executionGasUsed": "30",
            "stateGasUsed": "40",
        },
    },
    {
        "id": "S42",
        "kind": "helper",
        "input": {
            "txGas": "100",
            "calldataFloor": "40",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "40",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "result": {
            "gasUsed": "56",
            "gasLeft": "44",
            "executionGasUsed": "40",
            "stateGasUsed": "30",
        },
    },
    {
        "id": "S43",
        "kind": "helper",
        "input": {
            "txGas": "100",
            "calldataFloor": "39",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "39",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "result": {
            "gasUsed": "56",
            "gasLeft": "44",
            "executionGasUsed": "40",
            "stateGasUsed": "30",
        },
    },
    {
        "id": "S44",
        "kind": "helper",
        "input": {
            "txGas": "100",
            "calldataFloor": "41",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "41",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "result": {
            "gasUsed": "56",
            "gasLeft": "44",
            "executionGasUsed": "41",
            "stateGasUsed": "30",
        },
    },
    {
        "id": "R01",
        "kind": "raw",
        "input": {"gasUsed": "0", "gasLeft": "0", "executionGasUsed": "0", "stateGasUsed": "0"},
        "after": {"gasUsed": "0", "gasLeft": "0", "executionGasUsed": "0", "stateGasUsed": "0"},
        "result": {
            "gasUsed": "0",
            "gasLeft": "0",
            "executionGasUsed": "0",
            "stateGasUsed": "0",
        },
        "reconstructed": {
            "gasUsed": "0",
            "gasLeft": "0",
            "executionGasUsed": "0",
            "stateGasUsed": "0",
        },
        "equal": True,
    },
    {
        "id": "R02",
        "kind": "raw",
        "input": {"gasUsed": "1", "gasLeft": "2", "executionGasUsed": "3", "stateGasUsed": "4"},
        "after": {"gasUsed": "1", "gasLeft": "2", "executionGasUsed": "3", "stateGasUsed": "4"},
        "result": {
            "gasUsed": "1",
            "gasLeft": "2",
            "executionGasUsed": "3",
            "stateGasUsed": "4",
        },
        "reconstructed": {
            "gasUsed": "1",
            "gasLeft": "2",
            "executionGasUsed": "3",
            "stateGasUsed": "4",
        },
        "equal": True,
    },
    {
        "id": "R03",
        "kind": "raw",
        "input": {"gasUsed": "4", "gasLeft": "3", "executionGasUsed": "2", "stateGasUsed": "1"},
        "after": {"gasUsed": "4", "gasLeft": "3", "executionGasUsed": "2", "stateGasUsed": "1"},
        "result": {
            "gasUsed": "4",
            "gasLeft": "3",
            "executionGasUsed": "2",
            "stateGasUsed": "1",
        },
        "reconstructed": {
            "gasUsed": "4",
            "gasLeft": "3",
            "executionGasUsed": "2",
            "stateGasUsed": "1",
        },
        "equal": True,
    },
    {
        "id": "R04",
        "kind": "raw",
        "input": {"gasUsed": "0", "gasLeft": "1", "executionGasUsed": "0", "stateGasUsed": "2"},
        "after": {"gasUsed": "0", "gasLeft": "1", "executionGasUsed": "0", "stateGasUsed": "2"},
        "result": {
            "gasUsed": "0",
            "gasLeft": "1",
            "executionGasUsed": "0",
            "stateGasUsed": "2",
        },
        "reconstructed": {
            "gasUsed": "0",
            "gasLeft": "1",
            "executionGasUsed": "0",
            "stateGasUsed": "2",
        },
        "equal": True,
    },
    {
        "id": "R05",
        "kind": "raw",
        "input": {
            "gasUsed": "18446744073709551616",
            "gasLeft": "0",
            "executionGasUsed": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "stateGasUsed": "1",
        },
        "after": {
            "gasUsed": "18446744073709551616",
            "gasLeft": "0",
            "executionGasUsed": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "stateGasUsed": "1",
        },
        "result": {
            "gasUsed": "18446744073709551616",
            "gasLeft": "0",
            "executionGasUsed": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "stateGasUsed": "1",
        },
        "reconstructed": {
            "gasUsed": "18446744073709551616",
            "gasLeft": "0",
            "executionGasUsed": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "stateGasUsed": "1",
        },
        "equal": True,
    },
    {
        "id": "R06",
        "kind": "raw",
        "input": {
            "gasUsed": "1",
            "gasLeft": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639937"
            ),
            "executionGasUsed": "0",
            "stateGasUsed": "18446744073709551616",
        },
        "after": {
            "gasUsed": "1",
            "gasLeft": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639937"
            ),
            "executionGasUsed": "0",
            "stateGasUsed": "18446744073709551616",
        },
        "result": {
            "gasUsed": "1",
            "gasLeft": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639937"
            ),
            "executionGasUsed": "0",
            "stateGasUsed": "18446744073709551616",
        },
        "reconstructed": {
            "gasUsed": "1",
            "gasLeft": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639937"
            ),
            "executionGasUsed": "0",
            "stateGasUsed": "18446744073709551616",
        },
        "equal": True,
    },
]
SOURCE = [
    {
        "id": "S01",
        "kind": "source-success",
        "input": {
            "txGas": "0",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "0",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "0",
            "gasLeft": "0",
            "executionGasUsed": "0",
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S02",
        "kind": "source-success",
        "input": {
            "txGas": "1",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "1",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "1",
            "gasLeft": "0",
            "executionGasUsed": "1",
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S03",
        "kind": "source-success",
        "input": {
            "txGas": "4",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "after": {
            "txGas": "4",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "4",
            "gasLeft": "0",
            "executionGasUsed": "4",
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S04",
        "kind": "source-success",
        "input": {
            "txGas": "5",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "1",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "5",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "1",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "4",
            "gasLeft": "1",
            "executionGasUsed": "5",
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S05",
        "kind": "source-success",
        "input": {
            "txGas": "6",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "1",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "6",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "1",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "5",
            "gasLeft": "1",
            "executionGasUsed": "6",
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S06",
        "kind": "source-success",
        "input": {
            "txGas": "9",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "after": {
            "txGas": "9",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "8",
            "gasLeft": "1",
            "executionGasUsed": "9",
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S07",
        "kind": "source-success",
        "input": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "10",
            "gasLeft": "0",
            "executionGasUsed": "10",
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S08",
        "kind": "source-success",
        "input": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "1",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "1",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "9",
            "gasLeft": "1",
            "executionGasUsed": "10",
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S09",
        "kind": "source-success",
        "input": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "8",
            "gasLeft": "2",
            "executionGasUsed": "10",
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S10",
        "kind": "source-success",
        "input": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "3",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "3",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "8",
            "gasLeft": "2",
            "executionGasUsed": "10",
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S11",
        "kind": "source-success",
        "input": {
            "txGas": "11",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "after": {
            "txGas": "11",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "9",
            "gasLeft": "2",
            "executionGasUsed": "11",
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S12",
        "kind": "source-success",
        "input": {
            "txGas": "14",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "after": {
            "txGas": "14",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "12",
            "gasLeft": "2",
            "executionGasUsed": "14",
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S13",
        "kind": "source-success",
        "input": {
            "txGas": "15",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "after": {
            "txGas": "15",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "12",
            "gasLeft": "3",
            "executionGasUsed": "15",
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S14",
        "kind": "source-success",
        "input": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "result": {
            "gasUsed": "56",
            "gasLeft": "44",
            "executionGasUsed": "40",
            "stateGasUsed": "30",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S15",
        "kind": "source-success",
        "input": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "13",
            "stateSigned": "30",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "13",
            "stateSigned": "30",
        },
        "result": {
            "gasUsed": "57",
            "gasLeft": "43",
            "executionGasUsed": "40",
            "stateGasUsed": "30",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S16",
        "kind": "source-success",
        "input": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "15",
            "stateSigned": "30",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "15",
            "stateSigned": "30",
        },
        "result": {
            "gasUsed": "56",
            "gasLeft": "44",
            "executionGasUsed": "40",
            "stateGasUsed": "30",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S17",
        "kind": "source-success",
        "input": {
            "txGas": "100",
            "calldataFloor": "55",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "55",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "result": {
            "gasUsed": "56",
            "gasLeft": "44",
            "executionGasUsed": "55",
            "stateGasUsed": "30",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S18",
        "kind": "source-success",
        "input": {
            "txGas": "100",
            "calldataFloor": "56",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "56",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "result": {
            "gasUsed": "56",
            "gasLeft": "44",
            "executionGasUsed": "56",
            "stateGasUsed": "30",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S19",
        "kind": "source-success",
        "input": {
            "txGas": "100",
            "calldataFloor": "57",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "57",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "result": {
            "gasUsed": "57",
            "gasLeft": "43",
            "executionGasUsed": "57",
            "stateGasUsed": "30",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S20",
        "kind": "source-success",
        "input": {
            "txGas": "10",
            "calldataFloor": "10",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "1",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "10",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "1",
        },
        "result": {
            "gasUsed": "10",
            "gasLeft": "0",
            "executionGasUsed": "10",
            "stateGasUsed": "1",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S21",
        "kind": "source-success",
        "input": {
            "txGas": "10",
            "calldataFloor": "10",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "10",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "10",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "10",
        },
        "result": {
            "gasUsed": "10",
            "gasLeft": "0",
            "executionGasUsed": "10",
            "stateGasUsed": "10",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S22",
        "kind": "source-success",
        "input": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "10",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "10",
        },
        "result": {
            "gasUsed": "8",
            "gasLeft": "2",
            "executionGasUsed": "0",
            "stateGasUsed": "10",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S23",
        "kind": "source-success",
        "input": {
            "txGas": "10",
            "calldataFloor": "1",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "10",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "1",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "10",
        },
        "result": {
            "gasUsed": "8",
            "gasLeft": "2",
            "executionGasUsed": "1",
            "stateGasUsed": "10",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S24",
        "kind": "source-success",
        "input": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "-1",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "-1",
        },
        "result": {
            "gasUsed": "8",
            "gasLeft": "2",
            "executionGasUsed": "10",
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S25",
        "kind": "source-success",
        "input": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": (
                "-115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": (
                "-115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
        },
        "result": {
            "gasUsed": "8",
            "gasLeft": "2",
            "executionGasUsed": "10",
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S26",
        "kind": "source-success",
        "input": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "40",
            "stateGasLeft": "60",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "-1",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "40",
            "stateGasLeft": "60",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "-1",
        },
        "result": {
            "gasUsed": "0",
            "gasLeft": "100",
            "executionGasUsed": "0",
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S27",
        "kind": "source-success",
        "input": {
            "txGas": "100",
            "calldataFloor": "20",
            "gasLeft": "40",
            "stateGasLeft": "60",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "20",
            "gasLeft": "40",
            "stateGasLeft": "60",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "20",
            "gasLeft": "80",
            "executionGasUsed": "20",
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S28",
        "kind": "source-success",
        "input": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "100",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "100",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "0",
            "gasLeft": "100",
            "executionGasUsed": "0",
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S29",
        "kind": "source-success",
        "input": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "100",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "100",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "0",
            "gasLeft": "100",
            "executionGasUsed": "0",
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S30",
        "kind": "source-success",
        "input": {
            "txGas": "100",
            "calldataFloor": "100",
            "gasLeft": "40",
            "stateGasLeft": "60",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "100",
            "gasLeft": "40",
            "stateGasLeft": "60",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "100",
            "gasLeft": "0",
            "executionGasUsed": "100",
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S31",
        "kind": "source-success",
        "input": {
            "txGas": "64",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "12",
            "stateSigned": "63",
        },
        "after": {
            "txGas": "64",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "12",
            "stateSigned": "63",
        },
        "result": {
            "gasUsed": "52",
            "gasLeft": "12",
            "executionGasUsed": "1",
            "stateGasUsed": "63",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S32",
        "kind": "source-success",
        "input": {
            "txGas": "64",
            "calldataFloor": "1",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "12",
            "stateSigned": "63",
        },
        "after": {
            "txGas": "64",
            "calldataFloor": "1",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "12",
            "stateSigned": "63",
        },
        "result": {
            "gasUsed": "52",
            "gasLeft": "12",
            "executionGasUsed": "1",
            "stateGasUsed": "63",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S33",
        "kind": "source-success",
        "input": {
            "txGas": "64",
            "calldataFloor": "2",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "12",
            "stateSigned": "63",
        },
        "after": {
            "txGas": "64",
            "calldataFloor": "2",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "12",
            "stateSigned": "63",
        },
        "result": {
            "gasUsed": "52",
            "gasLeft": "12",
            "executionGasUsed": "2",
            "stateGasUsed": "63",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S34",
        "kind": "source-success",
        "input": {
            "txGas": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "after": {
            "txGas": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "gasLeft": "0",
            "executionGasUsed": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S35",
        "kind": "source-success",
        "input": {
            "txGas": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639937"
            ),
            "calldataFloor": "0",
            "gasLeft": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "1",
        },
        "after": {
            "txGas": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639937"
            ),
            "calldataFloor": "0",
            "gasLeft": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "1",
        },
        "result": {
            "gasUsed": "1",
            "gasLeft": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "executionGasUsed": "0",
            "stateGasUsed": "1",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S36",
        "kind": "source-success",
        "input": {
            "txGas": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "calldataFloor": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
        },
        "after": {
            "txGas": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "calldataFloor": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
        },
        "result": {
            "gasUsed": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "gasLeft": "0",
            "executionGasUsed": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            "stateGasUsed": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S37",
        "kind": "source-success",
        "input": {
            "txGas": "18446744073709551626",
            "calldataFloor": "0",
            "gasLeft": "18446744073709551616",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "5",
        },
        "after": {
            "txGas": "18446744073709551626",
            "calldataFloor": "0",
            "gasLeft": "18446744073709551616",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "5",
        },
        "result": {
            "gasUsed": "8",
            "gasLeft": "18446744073709551618",
            "executionGasUsed": "5",
            "stateGasUsed": "5",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S38",
        "kind": "source-success",
        "input": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "57896044618658097711785492504343953926634992332820282019728792003956564819968"
            ),
            "stateSigned": "0",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "57896044618658097711785492504343953926634992332820282019728792003956564819968"
            ),
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "8",
            "gasLeft": "2",
            "executionGasUsed": "10",
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S39",
        "kind": "source-success",
        "input": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": (
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            ),
            "stateSigned": "0",
        },
        "result": {
            "gasUsed": "8",
            "gasLeft": "2",
            "executionGasUsed": "10",
            "stateGasUsed": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S40",
        "kind": "source-success",
        "input": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "20",
            "stateGasLeft": "10",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "20",
            "stateGasLeft": "10",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "result": {
            "gasUsed": "56",
            "gasLeft": "44",
            "executionGasUsed": "40",
            "stateGasUsed": "30",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S41",
        "kind": "source-success",
        "input": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "40",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "0",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "40",
        },
        "result": {
            "gasUsed": "56",
            "gasLeft": "44",
            "executionGasUsed": "30",
            "stateGasUsed": "40",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S42",
        "kind": "source-success",
        "input": {
            "txGas": "100",
            "calldataFloor": "40",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "40",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "result": {
            "gasUsed": "56",
            "gasLeft": "44",
            "executionGasUsed": "40",
            "stateGasUsed": "30",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S43",
        "kind": "source-success",
        "input": {
            "txGas": "100",
            "calldataFloor": "39",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "39",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "result": {
            "gasUsed": "56",
            "gasLeft": "44",
            "executionGasUsed": "40",
            "stateGasUsed": "30",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "S44",
        "kind": "source-success",
        "input": {
            "txGas": "100",
            "calldataFloor": "41",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "after": {
            "txGas": "100",
            "calldataFloor": "41",
            "gasLeft": "10",
            "stateGasLeft": "20",
            "refundUnsigned": "14",
            "stateSigned": "30",
        },
        "result": {
            "gasUsed": "56",
            "gasLeft": "44",
            "executionGasUsed": "41",
            "stateGasUsed": "30",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ],
            "resultClass": "ethereum.forks.amsterdam.vm.gas.TransactionGasSettlement",
            "resultTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
            ],
        },
    },
    {
        "id": "F01",
        "kind": "source-error",
        "input": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "11",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "11",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ]
        },
        "error": {"class": "builtins.OverflowError", "message": "", "args": []},
        "traceback": [
            {"file": "/fixture/gas.py", "line": 1226, "name": "settle_transaction_gas"},
            {"file": "/fixture/numeric.py", "line": 109, "name": "__sub__"},
        ],
    },
    {
        "id": "F02",
        "kind": "source-error",
        "input": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "5",
            "stateGasLeft": "6",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "5",
            "stateGasLeft": "6",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ]
        },
        "error": {"class": "builtins.OverflowError", "message": "", "args": []},
        "traceback": [
            {"file": "/fixture/gas.py", "line": 1226, "name": "settle_transaction_gas"},
            {"file": "/fixture/numeric.py", "line": 109, "name": "__sub__"},
        ],
    },
    {
        "id": "F03",
        "kind": "source-error",
        "input": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "11",
            "stateGasLeft": "1",
            "refundUnsigned": "0",
            "stateSigned": "11",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "11",
            "stateGasLeft": "1",
            "refundUnsigned": "0",
            "stateSigned": "11",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ]
        },
        "error": {"class": "builtins.OverflowError", "message": "", "args": []},
        "traceback": [
            {"file": "/fixture/gas.py", "line": 1226, "name": "settle_transaction_gas"},
            {"file": "/fixture/numeric.py", "line": 109, "name": "__sub__"},
        ],
    },
    {
        "id": "F04",
        "kind": "source-error",
        "input": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "11",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "0",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "11",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ]
        },
        "error": {"class": "builtins.OverflowError", "message": "", "args": []},
        "traceback": [
            {"file": "/fixture/gas.py", "line": 1234, "name": "settle_transaction_gas"},
            {"file": "/fixture/numeric.py", "line": 109, "name": "__sub__"},
        ],
    },
    {
        "id": "F05",
        "kind": "source-error",
        "input": {
            "txGas": "10",
            "calldataFloor": "10",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "11",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "10",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "11",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ]
        },
        "error": {"class": "builtins.OverflowError", "message": "", "args": []},
        "traceback": [
            {"file": "/fixture/gas.py", "line": 1234, "name": "settle_transaction_gas"},
            {"file": "/fixture/numeric.py", "line": 109, "name": "__sub__"},
        ],
    },
    {
        "id": "F06",
        "kind": "source-error",
        "input": {
            "txGas": "10",
            "calldataFloor": "11",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "11",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "11",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "11",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ]
        },
        "error": {"class": "builtins.OverflowError", "message": "", "args": []},
        "traceback": [
            {"file": "/fixture/gas.py", "line": 1234, "name": "settle_transaction_gas"},
            {"file": "/fixture/numeric.py", "line": 109, "name": "__sub__"},
        ],
    },
    {
        "id": "F07",
        "kind": "source-error",
        "input": {
            "txGas": "10",
            "calldataFloor": "11",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "11",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "0",
            "stateSigned": "0",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ]
        },
        "error": {"class": "builtins.OverflowError", "message": "", "args": []},
        "traceback": [
            {"file": "/fixture/gas.py", "line": 1240, "name": "settle_transaction_gas"},
            {"file": "/fixture/numeric.py", "line": 109, "name": "__sub__"},
        ],
    },
    {
        "id": "F08",
        "kind": "source-error",
        "input": {
            "txGas": "10",
            "calldataFloor": "11",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "-1",
        },
        "after": {
            "txGas": "10",
            "calldataFloor": "11",
            "gasLeft": "0",
            "stateGasLeft": "0",
            "refundUnsigned": "2",
            "stateSigned": "-1",
        },
        "types": {
            "inputTypes": [
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.Uint",
                "ethereum_types.numeric.U256",
                "builtins.int",
            ]
        },
        "error": {"class": "builtins.OverflowError", "message": "", "args": []},
        "traceback": [
            {"file": "/fixture/gas.py", "line": 1240, "name": "settle_transaction_gas"},
            {"file": "/fixture/numeric.py", "line": 109, "name": "__sub__"},
        ],
    },
]


class AdmissionError(ValueError):
    pass


def require(condition, reason):
    if not condition:
        raise AdmissionError(reason)


def keys(value, fields):
    require(type(value) is dict and set(value) == set(fields), "object fields")


def decimal(value, signed=False):
    pattern = r"0|-?[1-9][0-9]*" if signed else r"0|[1-9][0-9]*"
    require(
        type(value) is str
        and len(value) <= 1024
        and re.fullmatch(pattern, value, re.ASCII) is not None,
        "canonical decimal",
    )
    return int(value)


def inputs(value):
    keys(value, INPUT_FIELDS)
    values = [decimal(value[f], f == "stateSigned") for f in INPUT_FIELDS]
    require(0 <= values[4] < 2**256, "unsigned refund range")
    return values


def admit_input(value):
    t, f, e, r, refund, state = inputs(value)
    require(e + r <= t and max(0, state) <= t - e - r and f <= t, "outside three local bounds")


def result(value):
    keys(value, RESULT_FIELDS)
    for field in RESULT_FIELDS:
        decimal(value[field])


def unique_pairs(pairs):
    value = {}
    for key, item in pairs:
        require(key not in value, "duplicate JSON key")
        value[key] = item
    return value


def invalid_constant(value):
    raise AdmissionError("nonfinite JSON: " + value)


def encode_frame(records, mode):
    frames = [
        {
            "schema": SCHEMA,
            "candidate": CANDIDATE,
            "catalog": CATALOG,
            "mode": mode,
            "count": len(records),
        },
        *records,
        {"end": True, "count": len(records), "catalog": CATALOG},
    ]
    return (
        "\n".join(json.dumps(row, separators=(",", ":"), allow_nan=False) for row in frames)
        + "\n"
    ).encode("ascii")


def parse_frame(data, mode):
    require(type(data) is bytes and len(data) <= 1048576, "frame size/type")
    require(mode in ("target", "source"), "mode")
    lines = data.split(b"\n")
    if lines and lines[-1] == b"":
        lines.pop()
    require(all(line and len(line) <= 32768 for line in lines), "empty/long line")
    try:
        frames = [
            json.loads(line, object_pairs_hook=unique_pairs, parse_constant=invalid_constant)
            for line in lines
        ]
    except (ValueError, UnicodeDecodeError, RecursionError) as error:
        raise AdmissionError("invalid JSON: " + str(error)) from error
    expected = TARGET if mode == "target" else SOURCE
    require(len(frames) == len(expected) + 2, "frame count/EOF")
    header, footer = frames[0], frames[-1]
    keys(header, ("schema", "candidate", "catalog", "mode", "count"))
    require(
        type(header["count"]) is int
        and header
        == {
            "schema": SCHEMA,
            "candidate": CANDIDATE,
            "catalog": CATALOG,
            "mode": mode,
            "count": len(expected),
        },
        "header",
    )
    keys(footer, ("end", "count", "catalog"))
    require(
        type(footer["end"]) is bool
        and type(footer["count"]) is int
        and footer == {"end": True, "count": len(expected), "catalog": CATALOG},
        "footer",
    )
    for actual, frozen in zip(frames[1:-1], expected, strict=True):
        keys(actual, frozen)
        require(
            type(actual["id"]) is str
            and actual["id"] == frozen["id"]
            and actual["kind"] == frozen["kind"],
            "case order/kind",
        )
        if actual["kind"] == "raw":
            for field in ("input", "after", "result", "reconstructed"):
                result(actual[field])
            require(type(actual["equal"]) is bool, "raw equality type")
        else:
            inputs(actual["input"])
            inputs(actual["after"])
            if actual["kind"] != "source-error":
                admit_input(actual["input"])
                result(actual["result"])
        if mode == "source":
            require(actual["types"] == frozen["types"], "source class metadata")
        if actual["kind"] == "source-error":
            keys(actual["error"], ("class", "message", "args"))
            require(actual["error"] == frozen["error"], "source exception")
            trace = actual["traceback"]
            require(type(trace) is list and len(trace) >= 2, "traceback")
            # Preserve controller frames too, then require the original gas/numeric tail.
            for row in trace:
                keys(row, ("file", "line", "name"))
                require(
                    type(row["file"]) is str
                    and type(row["line"]) is int
                    and type(row["name"]) is str,
                    "traceback fields",
                )
            for row, required in zip(trace[-2:], frozen["traceback"], strict=True):
                require(
                    Path(row["file"]).name == Path(required["file"]).name
                    and row["line"] == required["line"]
                    and row["name"] == required["name"],
                    "original traceback site",
                )
            actual = dict(actual, traceback=frozen["traceback"])
        require(actual == frozen, "complete literal mismatch: " + actual["id"])
    return frames[1:-1]


def admit_source_inputs(values, Uint, U256):
    require(type(values) is tuple and len(values) == 6, "source input arity")
    for index, value in enumerate(values):
        expected = Uint if index < 4 else U256 if index == 4 else int
        require(type(value) is expected, "actual source input class")
        if index < 5:
            raw = value._number
            require(
                type(raw) is int and raw >= 0 and (index != 4 or raw < 2**256),
                "numeric primitive storage",
            )


def run_original(eels, evidence, profile, target_path):
    """One closed 52-entry schedule. All original imports are lazy here.

    CPython/native NewTypes/generated dataclass/runtime primitives remain explicit
    interpreter premises. Structural whole-file code matching is not a universal
    environment certificate or a requirement of marshal-byte canonicality.
    """
    import base64
    import csv
    import dataclasses
    import hashlib
    import importlib
    import importlib.metadata
    import inspect
    import io
    import marshal
    import platform
    import sysconfig
    import traceback
    import types

    require(
        profile
        in (
            "WI306-SETTLEMENT-author-01",
            "WI306-SETTLEMENT-root-01",
            "WI306-SETTLEMENT-review-a-01",
            "WI306-SETTLEMENT-review-b-01",
        ),
        "unreleased source profile",
    )
    target = parse_frame(target_path.read_bytes(), "target")
    require(
        not any(
            name == "ethereum" or name.startswith(("ethereum.", "ethereum_types"))
            for name in sys.modules
        ),
        "original already imported",
    )
    eels = eels.resolve(strict=True)
    evidence = evidence.resolve()
    evidence.mkdir(parents=True, exist_ok=False)
    journal = (evidence / "events.jsonl").open("x", encoding="ascii")

    def write(event):
        journal.write(json.dumps(event, separators=(",", ":"), allow_nan=False) + "\n")
        journal.flush()

    def file_info(path):
        logical = Path(path).absolute()
        physical = logical.resolve(strict=True)
        digest_object = hashlib.sha256()
        with physical.open("rb") as stream:
            for chunk in iter(lambda: stream.read(1048576), b""):
                digest_object.update(chunk)
        digest = digest_object.hexdigest()
        retained = evidence / "inputs" / (digest + ".bin")
        retained.parent.mkdir(exist_ok=True)
        if not retained.exists():
            with physical.open("rb") as source, retained.open("xb") as destination:
                for chunk in iter(lambda: source.read(1048576), b""):
                    destination.write(chunk)
        check = hashlib.sha256()
        with retained.open("rb") as stream:
            for chunk in iter(lambda: stream.read(1048576), b""):
                check.update(chunk)
        require(
            check.hexdigest() == digest and retained.stat().st_size == physical.stat().st_size,
            "retained bytes changed",
        )
        return {
            "path": str(logical),
            "realpath": str(physical),
            "retained": str(retained),
            "sha256": digest,
            "bytes": physical.stat().st_size,
            "mode": oct(physical.stat().st_mode & 0o777),
        }

    require(
        platform.python_implementation() == "CPython"
        and platform.python_version() == "3.13.7"
        and sys.flags.isolated == 1
        and sys.flags.dont_write_bytecode == 1
        and sys.flags.optimize == 0,
        "source CPython/options",
    )
    interpreter = Path(sys.executable).resolve(strict=True)
    require(
        interpreter
        == Path(
            "/home/alh/.local/share/uv/python/cpython-3.13.7-linux-x86_64-gnu/bin/python3.13"
        ),
        "source interpreter identity",
    )
    expected_files = {
        "src/ethereum/forks/amsterdam/vm/gas.py": (
            "91d7240e67b18b1f4406e17c11c1e9a8cf2e83b93e0dd0eb5071a23ba2a2ccc0"
        ),
        "src/ethereum/forks/amsterdam/fork_types.py": (
            "3e0013e251867df02aca7b746b77403b36b41d73f7c4158bed09964838c935ca"
        ),
        ".venv/lib/python3.13/site-packages/ethereum_types/numeric.py": (
            "47d040d4de043e46d19c2fd9f74b318396b6c83ab01fe346f98a3c477e58db46"
        ),
    }
    before_files = [file_info(eels / path) for path in expected_files]
    for relative, item in zip(expected_files, before_files, strict=True):
        require(item["sha256"] == expected_files[relative], "pinned source body: " + relative)
    controller = file_info(__file__)
    native_target = file_info(target_path)
    repo = Path(__file__).resolve().parents[4]
    artifact_paths = [
        repo / p
        for p in (
            "STFSpec/Vm/Core/TransactionGasSettlement.lean",
            "STFSpec/Conformance/Vm/Core/TransactionGasSettlementCallerProofs.lean",
            "STFSpec/Conformance/Vm/Core/TransactionGasSettlementGuards.lean",
            "scripts/TransactionGasSettlementNativeTests.lean",
            "scripts/test_transaction_gas_settlement_output_parser.py",
            "STFSpec/Vm/Core.lean",
            "STFSpec/Conformance.lean",
            "lakefile.toml",
            "reference.toml",
            ".lake/build/bin/transaction-gas-settlement-native-tests",
            ".lake/build/bin/transaction-gas-settlement-native-tests.rsp",
            ".lake/build/bin/transaction-gas-settlement-native-tests.trace",
        )
    ]
    for module in (
        "STFSpec/Vm/Core/TransactionGasSettlement",
        "STFSpec/Conformance/Vm/Core/TransactionGasSettlementCallerProofs",
        "STFSpec/Conformance/Vm/Core/TransactionGasSettlementGuards",
        "TransactionGasSettlementNativeTests",
    ):
        artifact_paths += [
            repo / (".lake/build/lib/lean/" + module + suffix)
            for suffix in (".olean", ".ilean", ".trace")
        ]
        artifact_paths += [
            repo / (".lake/build/ir/" + module + suffix) for suffix in (".c", ".setup.json")
        ]
    for module in (
        "STFSpec/Vm/Core/TransactionGasSettlement",
        "STFSpec/Conformance/Vm/Core/TransactionGasSettlementGuards",
        "TransactionGasSettlementNativeTests",
    ):
        artifact_paths.append(repo / (".lake/build/ir/" + module + ".c.o.export"))
    toolchain = Path("/home/alh/.elan/toolchains/leanprover--lean4---v4.34.0")
    artifact_paths += [
        toolchain / path
        for path in ("bin/lean", "bin/lake", "bin/clang", "lib/lean/libleanshared.so")
    ]
    artifacts = [
        file_info(path) for path in artifact_paths
    ]  # Missing required files fail before entry.
    sys.path.insert(0, str(eels / "src"))
    gas = importlib.import_module("ethereum.forks.amsterdam.vm.gas")
    numeric = importlib.import_module("ethereum_types.numeric")
    fork_types = importlib.import_module("ethereum.forks.amsterdam.fork_types")
    Uint, U256 = numeric.Uint, numeric.U256
    original, record_class = gas.settle_transaction_gas, gas.TransactionGasSettlement
    source_fields = ("gas_used", "gas_left", "execution_gas_used", "state_gas_used")
    require(
        Path(gas.__file__).resolve() == eels / "src/ethereum/forks/amsterdam/vm/gas.py"
        and Path(numeric.__file__).resolve()
        == eels / ".venv/lib/python3.13/site-packages/ethereum_types/numeric.py",
        "actual loaded physical modules",
    )
    require(
        original.__code__.co_firstlineno == 1178
        and original.__code__.co_filename == gas.__file__
        and tuple(inspect.signature(original).parameters)
        == (
            "tx_gas",
            "calldata_floor",
            "gas_left",
            "state_gas_left",
            "refund_counter",
            "state_gas_used",
        ),
        "whole original callable",
    )
    require(
        tuple(field.name for field in dataclasses.fields(record_class)) == source_fields,
        "complete result constructor order",
    )

    # Match ordinary Python methods structurally with a whole-module compilation.
    compiled = {}

    def collect_code(code):
        compiled[(code.co_filename, code.co_qualname, code.co_firstlineno)] = code
        for constant in code.co_consts:
            if type(constant) is types.CodeType:
                collect_code(constant)

    for path in expected_files:
        physical = eels / path
        collect_code(
            compile(physical.read_bytes(), str(physical), "exec", dont_inherit=True, optimize=0)
        )
    require(bool(compiled), "missing whole-file compiled snapshot")
    ordinary = [("settle_transaction_gas", original)]
    for cls in (Uint, U256):
        for name in (
            "__init__",
            "__sub__",
            "__floordiv__",
            "__lt__",
            "__le__",
            "__gt__",
            "__ge__",
            "__eq__",
            "__int__",
            "_in_range",
        ):
            ordinary.append((cls.__name__ + "." + name, getattr(cls, name)))
    matched = []
    for name, function in ordinary:
        require(
            function.__globals__ is (gas.__dict__ if function is original else numeric.__dict__)
            and function.__defaults__ is None
            and function.__kwdefaults__ is None
            and function.__closure__ is None,
            "ordinary selected method globals/defaults/closure",
        )
        code = function.__code__
        key = (code.co_filename, code.co_qualname, code.co_firstlineno)
        require(
            key in compiled and code == compiled[key],
            "whole-file structural code mismatch: " + name,
        )
        matched.append(
            {
                "name": name,
                "structuralCodeEqual": True,
                "loadedMarshalSha256": hashlib.sha256(marshal.dumps(code)).hexdigest(),
                "compiledMarshalSha256": hashlib.sha256(
                    marshal.dumps(compiled[key])
                ).hexdigest(),
            }
        )

    def callable_info(value):
        # Bound classmethod wrappers are transient: retain their stable components.
        function = getattr(value, "__func__", value)
        receiver = getattr(value, "__self__", None)
        item = {
            "functionId": id(function),
            "receiverId": None if receiver is None else id(receiver),
            "runtimeClass": type(function).__module__ + "." + type(function).__qualname__,
            "globalsId": id(getattr(function, "__globals__", None)),
            "defaultsId": id(getattr(function, "__defaults__", None)),
            "kwdefaultsId": id(getattr(function, "__kwdefaults__", None)),
            "closureId": id(getattr(function, "__closure__", None)),
        }
        code = getattr(function, "__code__", None)
        if code is not None:
            data = marshal.dumps(code)
            destination = evidence / "code" / (hashlib.sha256(data).hexdigest() + ".marshal")
            destination.parent.mkdir(exist_ok=True)
            if not destination.exists():
                destination.write_bytes(data)
            item.update(
                codeId=id(code),
                filename=code.co_filename,
                firstLine=code.co_firstlineno,
                qualname=code.co_qualname,
                marshalSha256=hashlib.sha256(data).hexdigest(),
                bytecodeSha256=hashlib.sha256(code.co_code).hexdigest(),
            )
        else:
            item["interpretation"] = "native/runtime callable; no ordinary Python code object"
        return item

    def context():
        require(
            gas.settle_transaction_gas is original
            and gas.TransactionGasSettlement is record_class
            and original.__globals__ is gas.__dict__
            and original.__defaults__ is None
            and original.__kwdefaults__ is None
            and original.__closure__ is None
            and gas.Uint is Uint
            and gas.U256 is U256
            and gas.dataclass is dataclasses.dataclass
            and gas.ExecutionGas is fork_types.ExecutionGas
            and gas.StateGas is fork_types.StateGas
            and gas.ExecutionGas.__supertype__ is Uint
            and gas.StateGas.__supertype__ is Uint,
            "source binding/default/global/class changed",
        )
        require(
            type(U256.MAX_VALUE) is U256
            and type(U256.MAX_VALUE._number) is int
            and U256.MAX_VALUE._number == 2**256 - 1,
            "U256 maximum binding",
        )
        builtin_map = original.__builtins__
        require(
            builtin_map["min"] is min
            and builtin_map["max"] is max
            and builtin_map["int"] is int,
            "source builtin bindings",
        )
        return {
            "helper": callable_info(original),
            "globalsId": id(original.__globals__),
            "builtinsId": id(builtin_map),
            "builtins": {n: callable_info(builtin_map[n]) for n in ("min", "max", "int")},
            "UintId": id(Uint),
            "U256Id": id(U256),
            "resultClassId": id(record_class),
            "UnsignedId": id(numeric.Unsigned),
            "dataclassBinding": callable_info(gas.dataclass),
            "numericMroIds": {
                cls.__name__: [id(base) for base in cls.__mro__] for cls in (Uint, U256)
            },
            "maxValueId": id(U256.MAX_VALUE),
            "maxValueClassId": id(type(U256.MAX_VALUE)),
            "maxValuePrimitiveTypeId": id(type(U256.MAX_VALUE._number)),
            "maxValue": str(U256.MAX_VALUE._number),
            "numericBuiltins": {
                n: callable_info(numeric.__builtins__[n]) for n in ("int", "isinstance", "type")
            },
            "resultFields": [
                {
                    "id": id(field),
                    "name": field.name,
                    "typeId": id(field.type),
                    "defaultId": id(field.default),
                    "defaultFactoryId": id(field.default_factory),
                    "init": field.init,
                    "kwOnly": field.kw_only,
                }
                for field in dataclasses.fields(record_class)
            ],
            "recordMethods": {
                n: callable_info(getattr(record_class, n))
                for n in ("__init__", "__repr__", "__eq__")
            },
            "ExecutionGas": callable_info(gas.ExecutionGas),
            "StateGas": callable_info(gas.StateGas),
            "NewTypeCall": callable_info(type(gas.ExecutionGas).__call__),
            "numericMethods": {
                cls.__name__: {
                    n: callable_info(getattr(cls, n))
                    for n in (
                        "__init__",
                        "__sub__",
                        "__floordiv__",
                        "__lt__",
                        "__le__",
                        "__gt__",
                        "__ge__",
                        "__eq__",
                        "__int__",
                        "_in_range",
                    )
                }
                for cls in (Uint, U256)
            },
        }

    def input_info(values):
        admit_source_inputs(values, Uint, U256)
        observations = []
        for index, value in enumerate(values):
            expected = Uint if index < 4 else U256 if index == 4 else int
            raw = value._number if index < 5 else value
            observations.append(
                {
                    "classId": id(type(value)),
                    "class": expected.__module__ + "." + expected.__qualname__,
                    "objectId": id(value),
                    "numberClass": "builtins.int",
                    "value": str(raw),
                }
            )
        return observations

    # Exactly 52 sets: 208 Uint, 52 U256, 52 ExecutionGas, 52 StateGas input setup calls.
    # NewType identity checks use the already constructed outputs, with no probe calls.
    prepared = []
    for row in SOURCE:
        t, f, e, r, refund, state = inputs(row["input"])
        execution, reservoir = Uint(e), Uint(r)
        typed_execution, typed_reservoir = gas.ExecutionGas(execution), gas.StateGas(reservoir)
        require(
            typed_execution is execution and typed_reservoir is reservoir, "NewType identity"
        )
        values = (Uint(t), Uint(f), typed_execution, typed_reservoir, U256(refund), state)
        prepared.append((row, values, input_info(values)))
    before = context()
    distribution = importlib.metadata.distribution("ethereum-types")
    require(distribution.version == "0.4.1", "numeric distribution version")
    installed = []
    record_text = distribution.read_text("RECORD")
    require(type(record_text) is str, "missing installed RECORD")
    for relative, digest, length in csv.reader(io.StringIO(record_text)):
        item = file_info(distribution.locate_file(relative))
        if digest:
            algorithm, expected = digest.split("=", 1)
            require(
                algorithm == "sha256"
                and str(item["bytes"]) == length
                and base64.urlsafe_b64encode(bytes.fromhex(item["sha256"]))
                .rstrip(b"=")
                .decode()
                == expected,
                "installed RECORD body mismatch",
            )
        installed.append(item)
    loaded = []
    for name, module in sorted(sys.modules.items()):
        path = getattr(module, "__file__", None)
        if path and Path(path).is_file():
            loaded.append(
                {
                    "module": name,
                    "moduleId": id(module),
                    "loaderId": id(getattr(module, "__loader__", None)),
                    "origin": getattr(getattr(module, "__spec__", None), "origin", None),
                    "loaderClass": type(getattr(module, "__loader__", None)).__module__
                    + "."
                    + type(getattr(module, "__loader__", None)).__qualname__,
                    **file_info(path),
                }
            )
    runtime_library = Path(sysconfig.get_config_var("LIBDIR")) / sysconfig.get_config_var(
        "LDLIBRARY"
    )
    write(
        {
            "event": "preflight",
            "selectedCalls": 0,
            "profile": profile,
            "seed": 30601,
            "rngUsed": False,
            "sourcePin": "e1a316a06fc3d3e0a5da36fdc78580811e9d8a36",
            "interpreter": file_info(interpreter),
            "runtimeLibrary": file_info(runtime_library),
            "runtime": sys.version,
            "runtimeFlags": {
                "isolated": sys.flags.isolated,
                "optimize": sys.flags.optimize,
                "dontWriteBytecode": sys.flags.dont_write_bytecode,
            },
            "sysPath": sys.path,
            "venv": file_info(eels / ".venv/pyvenv.cfg"),
            "lock": file_info(eels / "uv.lock"),
            "installedRecord": file_info(Path(distribution._path) / "RECORD"),
            "installedFiles": installed,
            "loadedModules": loaded,
            "sourceFiles": before_files,
            "controller": controller,
            "nativeTarget": native_target,
            "nativeCompilerAndInputs": artifacts,
            "wholeFileStructuralMatches": matched,
            "context": before,
            "setupCalls": {
                "Uint": 208,
                "U256": 52,
                "ExecutionGas": 52,
                "StateGas": 52,
                "settlementHelper": 0,
                "settlementRecord": 0,
                "extraNumericProbes": 0,
            },
            "prepared": [{"id": row["id"], "inputs": obs} for row, _, obs in prepared],
        }
    )
    records = []
    for index, (frozen, values, observations) in enumerate(prepared):
        require(
            context() == before and input_info(values) == observations, "before-entry changed"
        )
        write(
            {
                "event": "planned-before-entry",
                "index": index,
                "id": frozen["id"],
                "inputs": observations,
                "context": before,
            }
        )
        try:
            returned = original(
                *values
            )  # Sole original helper entry, exactly once per selected row.
        except Exception as error:
            require(
                frozen["kind"] == "source-error"
                and type(error) is OverflowError
                and type(error.args) is tuple
                and len(error.args) == 0,
                "unexpected source exception",
            )
            trace = [
                {"file": f.filename, "line": f.lineno, "name": f.name}
                for f in traceback.extract_tb(error.__traceback__)
            ]
            frame = {
                "id": frozen["id"],
                "kind": "source-error",
                "input": dict(zip(INPUT_FIELDS, [v["value"] for v in observations])),
                "after": dict(zip(INPUT_FIELDS, [v["value"] for v in input_info(values)])),
                "types": {"inputTypes": [v["class"] for v in observations]},
                "error": {
                    "class": type(error).__module__ + "." + type(error).__qualname__,
                    "message": str(error),
                    "args": list(error.args),
                },
                "traceback": trace,
            }
            result_observations = {
                "exceptionClassId": id(type(error)),
                "traceback": trace,
                "error": frame["error"],
            }
        else:
            require(
                frozen["kind"] == "source-success" and type(returned) is record_class,
                "actual result class",
            )
            fields = []
            for name in source_fields:
                value = getattr(returned, name)
                require(
                    type(value) is Uint and type(value._number) is int and value._number >= 0,
                    "actual result field class/storage",
                )
                fields.append(
                    {
                        "name": name,
                        "classId": id(type(value)),
                        "objectId": id(value),
                        "class": "ethereum_types.numeric.Uint",
                        "numberClass": "builtins.int",
                        "value": str(value._number),
                    }
                )
            frame = {
                "id": frozen["id"],
                "kind": "source-success",
                "input": dict(zip(INPUT_FIELDS, [v["value"] for v in observations])),
                "after": dict(zip(INPUT_FIELDS, [v["value"] for v in input_info(values)])),
                "types": {
                    "inputTypes": [v["class"] for v in observations],
                    "resultClass": type(returned).__module__
                    + "."
                    + type(returned).__qualname__,
                    "resultTypes": [v["class"] for v in fields],
                },
                "result": dict(zip(RESULT_FIELDS, [v["value"] for v in fields])),
            }
            require(
                frame["result"] == target[index]["result"], "all-four source/native comparison"
            )
            result_observations = {"resultClassId": id(type(returned)), "fields": fields}
        require(
            context() == before and input_info(values) == observations,
            "post-entry context/input changed",
        )
        records.append(frame)
        write(
            {
                "event": "observed",
                "index": index,
                "id": frozen["id"],
                "inputBefore": observations,
                "inputAfter": input_info(values),
                "result": result_observations,
                "contextAfter": context(),
            }
        )
    data = encode_frame(records, "source")
    parse_frame(data, "source")
    require(
        [file_info(eels / path) for path in expected_files] == before_files
        and file_info(__file__) == controller
        and file_info(target_path) == native_target,
        "post-run immutable input bodies/modes",
    )
    require(
        [file_info(path) for path in artifact_paths] == artifacts,
        "post-run compiler/native/input artifact bodies/modes",
    )
    for item in loaded:
        require(
            id(sys.modules[item["module"]]) == item["moduleId"]
            and id(getattr(sys.modules[item["module"]], "__loader__", None)) == item["loaderId"]
            and file_info(item["path"])
            == {
                key: item[key]
                for key in ("path", "realpath", "retained", "sha256", "bytes", "mode")
            },
            "post-run loaded module/artifact changed",
        )
    write(
        {
            "event": "finished",
            "selectedCalls": 52,
            "comparedSuccesses": 44,
            "sourceOnlyArithmeticExceptions": 8,
            "extraProbes": 0,
            "rawRecordCalls": 0,
            "contextUnchanged": context() == before,
        }
    )
    journal.close()
    sys.stdout.buffer.write(data)
    sys.stdout.buffer.flush()
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--check-target", type=Path)
    modes.add_argument("--check-source", type=Path)
    modes.add_argument("--source-eels", type=Path)
    parser.add_argument("--source-evidence", type=Path)
    parser.add_argument("--profile")
    parser.add_argument("--target-native", type=Path)
    args = parser.parse_args(argv)
    if args.source_eels:
        if not args.source_evidence or not args.profile or not args.target_native:
            parser.error("source requires --source-evidence, --profile and --target-native")
    elif args.source_evidence or args.profile or args.target_native:
        parser.error("source options require --source-eels")
    try:
        if args.source_eels:
            return run_original(
                args.source_eels, args.source_evidence, args.profile, args.target_native
            )
        mode = "target" if args.check_target else "source"
        with (args.check_target or args.check_source).open("rb") as stream:
            records = parse_frame(stream.read(1048577), mode)
        require(
            not any(
                name == "ethereum" or name.startswith(("ethereum.", "ethereum_types"))
                for name in sys.modules
            ),
            "unexpected original import",
        )
        print(
            f"PASS settlement {mode}: {len(records)} complete groups; original imports/calls 0"
        )
        return 0
    except (AdmissionError, OSError) as error:
        print("FAIL settlement: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
