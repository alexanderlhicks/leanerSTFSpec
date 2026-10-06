/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit

/-!
# Complete account wire controls
Library `EthConformance`. Independent List framing preserves four full fields.
The emitter supplies whole values to both actual original source encoders.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` SC1/§4.
-/
namespace STFSpec.Conformance.StateCommit.AccountEncodingGuards
open STFSpec.Base STFSpec.Codec STFSpec.State STFSpec.StateCommit

private def lengthHeader (short long : Nat) (len : Nat) : List UInt8 :=
  if len < 56 then [UInt8.ofNat (short + len)] else
    UInt8.ofNat (long + (Uint.toBeBytesReference len).size) ::
      (Uint.toBeBytesReference len).toList
private def stringWire (xs : List UInt8) : List UInt8 :=
  if xs.length = 1 ∧ (xs.headD 128).toNat < 128 then xs else
    lengthHeader 128 183 xs.length ++ xs
private def reference (acc : Account) (root : Hash32) : List UInt8 :=
  let payload := stringWire (Uint.toBeBytesReference acc.nonce).toList ++
    stringWire (Uint.toBeBytesReference acc.balance.toNat).toList ++
    stringWire root.toBytes.toList ++ stringWire acc.codeHash.toBytes.toList
  lengthHeader 192 247 payload.length ++ payload
private def hash (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def pattern : Nat :=
  Uint.ofBeBytes (Bytes.ofList ((List.range 32).map fun i ↦ UInt8.ofNat (i * 7 + 3)))
private def nonces : List Nat :=
  [0, 1, 127, 128, 255, 256, 2 ^ 256 + 12345, 2 ^ 8192 + 17] ++
    ([32, 33, 55, 56, 255, 256] : List Nat).flatMap
    fun w ↦ [256 ^ (w - 1),256 ^ w - 1,256 ^ w]
private def balances : List Nat :=
  [0,1,127,128,255,256,2 ^ 256-1] ++ (List.range 32).flatMap fun i ↦
    let v := 256 ^ (i + 1)
    [v - 1] ++ if v < 2 ^ 256 then [v,v + 1] else []
private def cases : List (Nat × Nat × Nat × Nat) :=
  nonces.map (fun n ↦ (n,2 ^ 256-1,1,pattern)) ++
    balances.map (fun b ↦ (128,b,pattern,1)) ++
    (List.range 64).map (fun i ↦
      (2 ^ (i * 5) + i, (2 ^ (i % 256) + i * 1234567890123456789)%2 ^ 256,
        (pattern + i)%2 ^ 256, (2 ^ (i * 3) + 255 - i)%2 ^ 256)) ++
    [(0,0,0,0),(0,0,1,2),(0,0,2,1),(0,0,2 ^ 256-1,0)]
private def check (item : Nat × Nat × Nat × Nat) : Bool :=
  let (n, b, r, h) := item
  let acc := Account.mk n (U256.ofNat b) (hash h)
  decide (b < 2 ^ 256) && (encodeAccount acc (hash r)).data.toList == reference acc (hash r)

#guard cases.all check
#guard (Uint.toBeBytes (2 ^ 256+12345)).size == 33
#guard (encodeAccount (Account.mk 0 U256.zero (hash 1)) (hash 2)).data.toList !=
  (encodeAccount (Account.mk 0 U256.zero (hash 2)) (hash 1)).data.toList

private def emit : IO Unit := do
  for (item, i) in cases.zipIdx do
    let (n, b, r, h) := item
    let root := hash r
    let acc := Account.mk n (U256.ofNat b) (hash h)
    let raw := encodeAccount acc root
    let fields := s!"\{\"case\":{i},\"nonce\":{n},\"balance\":{b},"
    let roots := s!"\"storage_root\":{root.toBytes.toList.map UInt8.toNat},"
    let code := s!"\"code_hash\":{acc.codeHash.toBytes.toList.map UInt8.toNat},"
    IO.println s!"{fields}{roots}{code}\"encoded\":{raw.data.toList.map UInt8.toNat}}"
end STFSpec.Conformance.StateCommit.AccountEncodingGuards
