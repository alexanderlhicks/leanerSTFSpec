/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.StateCommit

/-!
# Complete contextual account-wire guards

Library `EthConformance`. Expected bytes use an independent unsigned division model
and explicit RLP headers, with exact expansions at the reachable wirePrefix thresholds.
No decoder, callback, hashing or assembled-root coverage is claimed.
Spec guidance: `STFSpec/informal/modules/EthStateCommit.md` §§3–4.
-/

open STFSpec.Base STFSpec.State STFSpec.StateCommit

private def unsignedBytes (n : Nat) : List UInt8 :=
  if n = 0 then [] else unsignedBytes (n / 256) ++ [UInt8.ofNat (n % 256)]
termination_by n

private def wirePrefix (short long : Nat) (n : Nat) : List UInt8 :=
  if n < 56 then [UInt8.ofNat (short + n)] else
    let digits := unsignedBytes n
    UInt8.ofNat (long + digits.length) :: digits

private def stringWire (bs : List UInt8) : List UInt8 :=
  match bs with
  | [b] => if b.toNat < 128 then [b] else [129, b]
  | _ => wirePrefix 128 183 bs.length ++ bs

private def expected (n b : Nat) (root code : List UInt8) : List UInt8 :=
  let payload := stringWire (unsignedBytes n) ++ stringWire (unsignedBytes b) ++
    (160 :: root) ++ (160 :: code)
  wirePrefix 192 247 payload.length ++ payload

private def hash (bs : List UInt8) : Hash32 :=
  (Hash32.ofBytes? (Bytes.ofList bs)).getD HashConsts.literals.emptyCodeHash

private def rootBytes : List UInt8 := (List.range 32).map UInt8.ofNat
private def codeBytes : List UInt8 := (List.range 32).map (fun i ↦ UInt8.ofNat (255 - i))
private def wire (n b : Nat) (r : List UInt8 := rootBytes) (h : List UInt8 := codeBytes) :
    List UInt8 := (encodeAccount ⟨n, U256.ofNat b, hash h⟩ (hash r)).data.toList

#guard wire 0 0 = [248, 68, 128, 128] ++ (160 :: rootBytes) ++ (160 :: codeBytes)
#guard wire 127 128 = [248, 69, 127, 129, 128] ++
  (160 :: rootBytes) ++ (160 :: codeBytes)
#guard wire 128 127 = [248, 69, 129, 128, 127] ++
  (160 :: rootBytes) ++ (160 :: codeBytes)
#guard wire 255 256 = [248, 71, 129, 255, 130, 1, 0] ++
  (160 :: rootBytes) ++ (160 :: codeBytes)
#guard wire (2 ^ 256) 0 = [248, 101, 161, 1] ++ List.replicate 32 0 ++ [128] ++
  (160 :: rootBytes) ++ (160 :: codeBytes)
#guard wire (2 ^ 1024 + 17) 0 = [248, 198, 184, 129, 1] ++
  List.replicate 127 0 ++ [17, 128] ++ (160 :: rootBytes) ++ (160 :: codeBytes)
#guard wire (2 ^ (8 * 54)) 0 = [248, 123, 183, 1] ++ List.replicate 54 0 ++
  [128] ++ (160 :: rootBytes) ++ (160 :: codeBytes)
#guard wire (2 ^ (8 * 55)) 0 = [248, 125, 184, 56, 1] ++ List.replicate 55 0 ++
  [128] ++ (160 :: rootBytes) ++ (160 :: codeBytes)
#guard wire (2 ^ (8 * 185)) 0 = [248, 255, 184, 186, 1] ++ List.replicate 185 0 ++
  [128] ++ (160 :: rootBytes) ++ (160 :: codeBytes)
#guard wire (2 ^ (8 * 186)) 0 = [249, 1, 0, 184, 187, 1] ++ List.replicate 186 0 ++
  [128] ++ (160 :: rootBytes) ++ (160 :: codeBytes)

#guard ([0, 1, 127, 128, 255, 256, 2 ^ 256 - 1] : List Nat).all fun n ↦
  ([0, 1, 127, 128, 255, 256, 2 ^ 256 - 1] : List Nat).all fun b ↦
    wire n b == expected n b rootBytes codeBytes
-- Nonce is unbounded; balance boundaries run only within U256.
#guard (List.range 187).all fun j ↦
  let k := j + 1
  ([2 ^ (8 * k) - 1, 2 ^ (8 * k), 2 ^ (8 * k) + 1] : List Nat).all fun n ↦
    wire n 0 == expected n 0 rootBytes codeBytes
#guard (List.range 31).all fun j ↦
  let k := j + 1
  ([2 ^ (8 * k) - 1, 2 ^ (8 * k), 2 ^ (8 * k) + 1] : List Nat).all fun b ↦
    wire 0 b == expected 0 b rootBytes codeBytes

#guard (List.range 32).all fun i ↦
  ([0, 1, 127, 128, 255] : List UInt8).all fun marker ↦
    let r := rootBytes.set i marker
    let h := codeBytes.set i marker
    wire 0 0 r codeBytes == expected 0 0 r codeBytes &&
      wire 0 0 rootBytes h == expected 0 0 rootBytes h
#guard wire 0 0 codeBytes rootBytes = expected 0 0 codeBytes rootBytes
#guard wire 0x010002000300 0x800100ff000200 =
  expected 0x010002000300 0x800100ff000200 rootBytes codeBytes
#guard wire 0 0 (List.replicate 32 0) (List.replicate 32 255) =
  expected 0 0 (List.replicate 32 0) (List.replicate 32 255)

private def suppliedConsts : HashConsts :=
  { HashConsts.literals with emptyCodeHash := hash codeBytes, emptyTrieRoot := hash rootBytes }
#guard (encodeAccount (emptyAccount suppliedConsts) suppliedConsts.emptyTrieRoot).data.toList =
  expected 0 0 rootBytes codeBytes
#guard (encodeAccount (emptyAccount HashConsts.literals)
    HashConsts.literals.emptyTrieRoot).data.toList =
  [248, 68, 128, 128, 160] ++
    [86, 232, 31, 23, 27, 204, 85, 166, 255, 131, 69, 230, 146, 192, 248, 110,
      91, 72, 224, 27, 153, 108, 173, 192, 1, 98, 47, 181, 227, 99, 180, 33] ++
    [160] ++ [197, 210, 70, 1, 134, 247, 35, 60, 146, 126, 125, 178, 220, 199, 3, 192,
      229, 0, 182, 83, 202, 130, 39, 59, 123, 250, 216, 4, 93, 133, 164, 112]
