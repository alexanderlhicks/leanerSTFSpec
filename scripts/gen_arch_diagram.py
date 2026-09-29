#!/usr/bin/env python3
# Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
"""Generate the README architecture diagram from scripts/boundaries.toml.

The core graph is the transitive reduction of boundaries.toml; proof edges come from
contracts.toml and the fixture label from reference.toml. External packages,
consumers and the conformance oracle are added below. `--check` fails if README.md is stale.
"""
import pathlib, sys, tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
BEGIN, END = "<!-- BEGIN GENERATED ARCHITECTURE (scripts/gen_arch_diagram.py) -->", "<!-- END GENERATED ARCHITECTURE -->"

LABELS = {
    "EthStateless": "runStatelessGuest : bytes → bytes<br/>header chain · witness codecs",
    "EthFork": "Amsterdam composition<br/>parameters · fork modules · precompile table",
    "EthBlock": "executeBlock · transactions · receipts<br/>withdrawals · requests · block access lists",
    "EthVmRunner": "recursive call execution<br/>resume operations · termination",
    "EthVmInstructions": "one handler per opcode → StepResult<br/>(next frame · halt · child request)",
    "EthPrecompiles": "precompiled contracts",
    "EthVmCore": "Evm frame · stack · memory<br/>gas meter · gas parameters",
    "EthState": "state semantics: PreState + ModelsLookups<br/>overlays · lifetimes · laws",
    "EthStateCommit": "account / storage encodings<br/>state-root law · code-hash agreement",
    "EthStateFull": "full-state backend",
    "EthStateWitness": "witness-state backend",
    "EthCommit": "Merkle-Patricia trie<br/>partial trie · incremental root",
    "EthCodec": "RLP · SSZ · hash_tree_root",
    "EthHash": "keccak256 · SHA-256<br/>RIPEMD-160 · BLAKE2",
    "EthPairing": "pairings · KZG",
    "EthCurve": "secp256k1 · P-256 · BN254 · BLS12-381",
    "EthField": "prime fields · Fp2/Fp6/Fp12",
    "EthBase": "U256 · bytes · addresses · hashes",
    "EthConformance": "EEST runners · #guard suites",
}

def reduce(deps):
    closure = {}
    def close(l):
        if l not in closure:
            closure[l] = set()
            for d in deps[l]:
                closure[l] |= {d} | close(d)
        return closure[l]
    for l in deps: close(l)
    return {l: sorted(d for d in ds if not any(d in closure[o] for o in ds if o != d))
            for l, ds in deps.items()}

def diagram():
    libs = tomllib.loads((ROOT / "scripts/boundaries.toml").read_text())["libs"]
    proofs = tomllib.loads((ROOT / "STFSpec/informal/contracts.toml").read_text())["proof_imports"]
    tag = tomllib.loads((ROOT / "reference.toml").read_text())["release"]["tag"]
    red = reduce({n: s["deps"] for n, s in libs.items()})
    L = ["```mermaid", "flowchart TB",
         '  subgraph consumers["Verified implementations (refine the spec)"]', "    direction LR",
         '    evmasm["evm-asm<br/>hand-written RV64IM"]', '    pancake["stateless-pancaketh<br/>Pancake → RISC-V"]', "  end",
         '  subgraph core["Core package: Mathlib-free executable spec (edges enforced in CI)"]', "    direction TB"]
    for n in libs:
        if n != "EthConformance":
            L.append(f'    {n}["<b>{n}</b><br/>{LABELS.get(n, "")}"]')
    L.append("  end")
    L += [f'  EthConformance["<b>EthConformance</b><br/>{LABELS["EthConformance"]}"]',
          '  subgraph mathlibpkg["STFSpecMathlib: Mathlib bridge package"]', "    direction LR",
          '    FieldM["EthFieldMathlib<br/>PrimeField ≃+* ZMod p"]', '    CurveM["EthCurveMathlib<br/>group law"]',
          '    PairingM["EthPairingMathlib<br/>bilinearity · KZG"]', "  end",
          '  subgraph secpkg["STFSpecSecurity: security package"]',
          '    Security["<b>EthSecurity</b><br/>witness binding · stateless ⇒ stateful<br/>random-oracle bounds"]', "  end",
          '  Mathlib["Mathlib"]', '  VCV["VCV-io (planned)"]', '  CompPoly["CompPoly<br/>Montgomery Defs (D6 source candidate)"]',
          '  CryptoSpecs["ethereum/cryptography-specs<br/>BLS12-381 · KZG reference"]',
          f'  Oracle[("EEST zkevm fixtures · {tag}<br/>statelessInputBytes → statelessOutputBytes")]',
          "  evmasm -. refines .-> EthStateless", "  pancake -. refines .-> EthStateless"]
    for n, ds in red.items():
        for d in ds:
            L.append(f"  {n} --> {d}")
    nodes = {"EthFieldMathlib": "FieldM", "EthCurveMathlib": "CurveM",
             "EthPairingMathlib": "PairingM", "EthSecurity": "Security"}
    for name, deps in proofs.items():
        for dep in deps:
            L.append(f"  {nodes.get(name, name)} --> {nodes.get(dep, dep)}")
    L += ['  EthField -. "source candidate (D6)" .-> CompPoly', '  EthPairing -. "reference (D15)" .-> CryptoSpecs',
          '  Security -. "planned (P4)" .-> VCV', "  mathlibpkg --> Mathlib", "  secpkg --> Mathlib",
          '  EthConformance -- "golden rule: must pass" --> Oracle',
          "  classDef coreC fill:#e8f5e9,stroke:#2e7d32,color:#1b1b1b",
          "  classDef bridgeC fill:#e3f2fd,stroke:#1565c0,color:#1b1b1b",
          "  classDef secC fill:#f3e5f5,stroke:#6a1b9a,color:#1b1b1b",
          "  classDef extC fill:#fafafa,stroke:#757575,color:#1b1b1b",
          "  classDef oracleC fill:#fff3e0,stroke:#e65100,color:#1b1b1b",
          "  class " + ",".join(n for n in libs if n != "EthConformance") + " coreC",
          "  class FieldM,CurveM,PairingM bridgeC", "  class Security secC",
          "  class Mathlib,VCV,CompPoly,CryptoSpecs,evmasm,pancake,EthConformance extC", "  class Oracle oracleC", "```"]
    return "\n".join(L)

def main():
    readme = ROOT / "README.md"
    text = readme.read_text()
    if BEGIN not in text or END not in text:
        print("README.md lacks the generated-architecture markers"); return 1
    head, rest = text.split(BEGIN, 1); _, tail = rest.split(END, 1)
    new = head + BEGIN + "\n" + diagram() + "\n" + END + tail
    if "--check" in sys.argv:
        if new != text:
            print("README.md architecture diagram is stale: run scripts/gen_arch_diagram.py"); return 1
        print("README diagram up to date"); return 0
    readme.write_text(new); print("README diagram regenerated"); return 0

if __name__ == "__main__":
    sys.exit(main())
