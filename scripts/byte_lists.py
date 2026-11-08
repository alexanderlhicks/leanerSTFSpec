# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Shared byte-list field parser for the native observation drivers.

A one-line JSON list of integers in 0–255 is returned directly. Every other input,
including multi-line strings, goes through `ast.literal_eval`, so the callers'
validators see the same values and errors as with `ast.literal_eval` alone.
"""

import ast
import json


def parse_byte_list(raw):
    if type(raw) is not str or "\n" in raw or "\r" in raw:
        return ast.literal_eval(raw)
    try:
        value = json.loads(raw)
    except (ValueError, TypeError, RecursionError, MemoryError):
        pass
    else:
        if type(value) is list and all(type(byte) is int and 0 <= byte < 256 for byte in value):
            return value
    return ast.literal_eval(raw)
