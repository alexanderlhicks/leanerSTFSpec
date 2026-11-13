/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.State
import Lean.Data.Json

/-!
# Complete raw transaction-view observations

Native and interpreted producers execute public block and transaction views on the
same 118 input-only recipes. The independent frozen mathematical results are read
by `transaction_view_model.py`; no standalone Python source view exists.
Spec guidance: `STFSpec/informal/modules/EthState.md` §§3/4/7.1/7.2.
-/

open STFSpec.State STFSpec.Base Lean

private def digest (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def array (xs : List Json) : Json := .arr xs.toArray
private def number (n : Nat) : Json := toJson n
private def pair (a b : Json) : Json := array [a, b]
private def parseList (j : Json) : Except String (List Json) := do
  return (← j.getArr?).toList
private def parsePair (j : Json) : Except String (Json × Json) := do
  match ← parseList j with
  | [a, b] => return (a, b)
  | _ => throw "expected two fields"
private def parseMap {K V : Type} [Ord K] [Std.TransOrd K]
    (key : Json → Except String K) (value : Json → Except String V) (j : Json) :
    Except String (Std.ExtTreeMap K V) := do
  (← parseList j).foldlM (fun out entry ↦ do
    let (k, v) ← parsePair entry
    return out.insert (← key k) (← value v)) ∅
private def address (j : Json) : Except String Address := do
  return Address.ofNat (← j.getNat?)
private def slot (j : Json) : Except String Bytes32 := do
  return FixedBytes.ofNat (← j.getNat?)
private def hash (j : Json) : Except String Hash32 := do
  return digest (← j.getNat?)
private def word (j : Json) : Except String U256 := do
  return U256.ofNat (← j.getNat?)
private def account (j : Json) : Except String Account := do
  match ← parseList j with
  | [n, b, h] => return ⟨← n.getNat?, ← word b, ← hash h⟩
  | _ => throw "expected account triple"
private def optionalAccount (j : Json) : Except String (Option Account) :=
  match j with
  | .null => pure none
  | _ => return some (← account j)
private def code (j : Json) : Except String ByteArray := do
  let ns ← (← parseList j).mapM Json.getNat?
  return ByteArray.mk (ns.map UInt8.ofNat).toArray
private def storage (j : Json) := parseMap address (parseMap slot word) j
private def initial (j : Json) : Except String MathState := do
  return ⟨← parseMap address account (← j.getObjVal? "accounts"),
    ← storage (← j.getObjVal? "storage"), ← parseMap hash code (← j.getObjVal? "code")⟩

-- Every family is deliberately malformed. Traversal must use existing entries, not next.
private def order {K : Type} [Ord K] [Std.TransOrd K] (key : Nat → K)
    (variant salt : Nat) : WriteOrder K :=
  ⟨2 ^ 410 + variant + salt,
    (∅ : Std.ExtTreeMap K Nat).insert (key (700 + variant)) (2 ^ 411 + salt),
    (∅ : Std.ExtTreeMap Nat K).insert (3 + variant) (key (800 + salt))
      |>.insert (2 ^ 412 + variant) (key (800 + salt))
      |>.insert (19 + variant) (key (900 + salt))⟩
private def slotOrders (variant salt : Nat) : Std.ExtTreeMap Address (WriteOrder Bytes32) :=
  let out := (∅ : Std.ExtTreeMap Address (WriteOrder Bytes32)).insert
    (Address.ofNat (600 + variant)) (order FixedBytes.ofNat variant salt)
  if variant % 2 = 0 then out.insert (Address.ofNat 0) WriteOrder.empty
  else out.insert (Address.ofNat 1) (order FixedBytes.ofNat (variant + 1) (salt + 1))
private def revertible (j : Json) (variant salt : Nat) : Except String TxRevertible := do
  let clears ← (← parseList (← j.getObjVal? "clears")).mapM address
  return ⟨← parseMap address optionalAccount (← j.getObjVal? "accounts"),
    order Address.ofNat variant salt, ← storage (← j.getObjVal? "storage"),
    order Address.ofNat (variant + 1) (salt + 1), slotOrders variant salt,
    ← parseMap hash code (← j.getObjVal? "code"),
    clears.foldl (fun out a ↦ out.insert a) ∅,
    (∅ : Std.ExtTreeMap (Address × Bytes32) U256).insert
      (Address.ofNat (1000 + variant), FixedBytes.ofNat salt) U256.zero
      |>.insert (Address.ofNat (1001 + variant), FixedBytes.ofNat (salt + 1))
        (U256.ofNat (variant + salt + 1))⟩
private def constants (v : Nat) : HashConsts :=
  ⟨digest (17 + v), digest (2000 + v), digest (3000 + v), digest (4000 + v)⟩
private def provider (v : Nat) : PreState Id :=
  ⟨fun _ ↦ .error (.missing (.node (digest (5000 + v)))),
    fun _ _ ↦ .error (.malformed (.code (digest (6000 + v)))),
    fun _ ↦ .error (.unresolved (digest (7000 + v))),
    fun _ ↦ .error (.missing .leaf)⟩
private def block (r : TxRevertible) (v : Nat) : BlockState Id :=
  ⟨provider v, constants v, r.accountWrites, r.accountOrder, r.storageWrites,
    r.storageAddressOrder, r.storageSlotOrder, r.codeWrites, r.storageClears,
    (∅ : Std.HashSet Address).insert (Address.ofNat (8000 + v)),
    (∅ : Std.HashSet (Address × Bytes32)).insert
      (Address.ofNat (9000 + v), FixedBytes.ofNat (10000 + v)),
    (∅ : Std.HashSet Hash32).insert (digest (11000 + v)), some (2 ^ 420 + v)⟩
private def observations (v : Nat) : TxObs :=
  ⟨(∅ : Std.HashSet Address).insert (Address.ofNat (12000 + v)),
    (∅ : Std.HashSet (Address × Bytes32)).insert
      (Address.ofNat (13000 + v), FixedBytes.ofNat (14000 + v)),
    (∅ : Std.HashSet Hash32).insert (digest (15000 + v)),
    (∅ : Std.HashSet Address).insert (Address.ofNat (16000 + v))⟩
private def observeAccount (a : Account) : Json :=
  array [number a.nonce, number a.balance.toNat, number a.codeHash.toBytes32.toNat]
private def observe (σ : MathState) : Json := Json.mkObj [
  ("accounts", array (σ.accounts.toList.map (fun (a, x) ↦
    pair (number a.toNat) (observeAccount x)))),
  ("storage", array (σ.storage.toList.map (fun (a, slots) ↦
    pair (number a.toNat) (array (slots.toList.map (fun (k, v) ↦
      pair (number k.toNat) (number v.toNat))))))),
  ("code", array (σ.code.toList.map (fun (h, bytes) ↦
    pair (number h.toBytes32.toNat) (array (bytes.toList.map (fun b ↦ number b.toNat))))))]
private def execute (j : Json) : Except String Json := do
  let id ← (← j.getObjVal? "case").getNat?
  let v ← (← j.getObjVal? "ignoredVariant").getNat?
  let σ ← initial (← j.getObjVal? "initial")
  let b := block (← revertible (← j.getObjVal? "block") v 31) v
  let t : TxState Id := ⟨b, ← revertible (← j.getObjVal? "transaction") v 73,
    observations v⟩
  return Json.mkObj [("schema", toJson "transaction-view-v1"), ("case", number id),
    ("blockView", observe (b.view σ)), ("view", observe (t.view σ))]

/-- Print every complete public block and transaction mathematical view. -/
def main (args : List String) : IO Unit := do
  let path := args.headD "STFSpec/Conformance/State/transaction_view_inputs.json"
  let rows ← IO.ofExcept (parseList (← IO.ofExcept (Json.parse (← IO.FS.readFile path))))
  for row in rows do
    IO.println (← IO.ofExcept (execute row)).compress
