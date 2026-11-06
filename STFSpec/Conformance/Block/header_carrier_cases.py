#!/usr/bin/env -S uv run --no-project --python 3.12 python
"""Independent raw header catalogue; no Lean or EELS implementation imports.

The inputs and identity/projection expectations were frozen before source and
Lean observation. The source comparison is finite raw-constructor evidence.
Run --write-input PATH before the native or interpreted producer.
"""

from pathlib import Path


FIELDS = [
    ("parentHash", "Hash32", 32),
    ("ommersHash", "Hash32", 32),
    ("coinbase", "Address", 20),
    ("stateRoot", "Root", 32),
    ("transactionsRoot", "Root", 32),
    ("receiptRoot", "Root", 32),
    ("bloom", "Bloom", 256),
    ("difficulty", "Nat", None),
    ("number", "Nat", None),
    ("gasLimit", "Nat", None),
    ("gasUsed", "Nat", None),
    ("timestamp", "U256", None),
    ("extraData", "Bytes", None),
    ("prevRandao", "Bytes32", 32),
    ("nonce", "Bytes8", 8),
    ("baseFeePerGas", "Nat", None),
    ("withdrawalsRoot", "Root", 32),
    ("blobGasUsed", "U64", None),
    ("excessBlobGas", "U64", None),
    ("parentBeaconBlockRoot", "Root", 32),
    ("requestsHash", "Hash32", 32),
    ("blockAccessListHash", "Hash32", 32),
    ("slotNumber", "U64", None),
]
ACCESSORS = [
    "gasLimit", "gasUsed", "baseFeePerGas", "timestamp", "number", "stateRoot",
    "excessBlobGas", "blobGasUsed", "parentHash",
]


def marker(position, width):
    return bytes((37 * position + 17 * j + 1) % 256 for j in range(width)).hex()


def profile(kind):
    values = []
    for position, (_, nominal, width) in enumerate(FIELDS):
        if width is not None:
            value = marker(position, width)
            if kind == "zero":
                value = "00" * width
            elif kind == "maximum":
                value = "ff" * width
            elif kind == "leading-zero":
                value = "00" + value[2:]
        elif nominal == "Bytes":
            value = "00010200ff"
            if kind == "zero":
                value = ""
            elif kind == "maximum":
                value = "ff" * 33
            elif kind == "leading-zero":
                value = "0000000100"
        else:
            value = 101 + position * 19
            if kind == "zero":
                value = 0
            elif kind == "maximum":
                value = (1 << (64 if nominal == "U64" else 256)) - 1
            elif kind == "unbounded" and nominal == "Nat":
                value = (1 << (4096 + position)) + position
        values.append(value)
    return values


def catalogue():
    rows = []
    groups = [("Header", "amsterdam", 23), ("PrevHeader", "bpo5", 21),
              ("ParentHeader", "amsterdam", 23), ("ParentHeader", "bpo5", 21)]
    for family, variant, count in groups:
        prefix = family + "/" + variant + "/"

        def add(label, values):
            rows.append({"caseId": prefix + label, "family": family,
                         "variant": variant, "values": values[:count]})

        for kind in ["zero", "maximum", "marker", "leading-zero", "unbounded"]:
            add(kind, profile(kind))
        # Duplicate full values retain independent row identities and positions.
        add("marker-duplicate-a", profile("marker"))
        add("marker-duplicate-b", profile("marker"))
        for position, (_, nominal, width) in enumerate(FIELDS[:count]):
            base = profile("marker")
            if width is not None:
                # Each byte of each field changes alone against the marker record.
                for byte_index in range(width):
                    value = bytearray.fromhex(base[position])
                    value[byte_index] ^= 0x80
                    changed = list(base)
                    changed[position] = value.hex()
                    add("field-%02d-byte-%03d" % (position, byte_index), changed)
                alternatives = ["00" * width, "ff" * width,
                                "00" * (width - 1) + "01"]
            elif nominal == "Bytes":
                alternatives = [bytes((j * 29) % 256 for j in range(length)).hex()
                                for length in [0, 1, 31, 32, 33, 257, 1025]]
                alternatives += ["00", "0000", "00000100", "ff00ff"]
            elif nominal == "Nat":
                alternatives = [0, 1, (1 << 64) - 1, 1 << 64,
                                (1 << 256) - 1, 1 << 256, (1 << 4096) + position]
            else:
                bits = 64 if nominal == "U64" else 256
                alternatives = [0, 1, 255, 256, (1 << (bits - 1)), (1 << bits) - 1]
            for index, alternative in enumerate(alternatives):
                changed = list(base)
                changed[position] = alternative
                add("field-%02d-value-%02d" % (position, index), changed)
    return rows


def input_bytes():
    return "".join("\t".join([row["caseId"], row["family"], row["variant"]]
                            + [str(value) for value in row["values"]]) + "\n"
                   for row in catalogue()).encode("ascii")


def expected_rows():
    for case in catalogue():
        fields = [{"position": index, "name": name, "type": nominal, "value": value}
                  for index, ((name, nominal, _), value) in
                  enumerate(zip(FIELDS, case["values"]))]
        named = {field["name"]: field for field in fields}
        accessors = [{key: named[name][key] for key in ("name", "type", "value")}
                     for name in ACCESSORS] if case["family"] == "ParentHeader" else []
        yield {"caseId": case["caseId"], "family": case["family"],
               "variant": case["variant"], "fields": fields, "commonAccessors": accessors}


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-input", required=True, type=Path)
    args = parser.parse_args()
    args.write_input.write_bytes(input_bytes())
    print("PASS: wrote", len(catalogue()), "input-only raw header rows")
