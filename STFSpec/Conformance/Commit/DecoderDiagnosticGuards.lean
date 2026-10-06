/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.RlpCanonical
import STFSpec.Commit.Compact

/-!
# Decoder field diagnostic seam regressions

Library `EthConformance`. These checks exercise the actual whole-input RLP and
compact decoders and distinguish the diagnostic declarations. They implement
no node dispatcher. Assigning these diagnostics in C14 order, propagating
child failures and preserving branch-list endings remain decoder obligations.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` §§3/4/5/7 (Q52).
-/

namespace STFSpec.Conformance.Commit.DecoderDiagnosticGuards

open STFSpec.Codec STFSpec.Commit

mutual
  /-- Compare complete RLP items structurally, including every nested byte payload. -/
  def sameItem : RlpItem → RlpItem → Bool
    | .bytes a, .bytes b => decide (a = b)
    | .list xs, .list ys => sameItems xs ys
    | _, _ => false
  /-- Compare complete ordered RLP item lists structurally, including their lengths. -/
  def sameItems : List RlpItem → List RlpItem → Bool
    | [], [] => true
    | x :: xs, y :: ys => sameItem x y && sameItems xs ys
    | _, _ => false
end

/-- Compare complete raw parse results, including exact codec diagnostics. -/
def sameRlp : Except RlpError RlpItem → Except RlpError RlpItem → Bool
  | .ok x, .ok y => sameItem x y
  | .error e, .error f => decide (e = f)
  | _, _ => false

/-- Byte construction for finite test vectors. -/
def b (xs : List UInt8) : ByteArray := xs.toByteArray

/-- Complete public compact result; this observes digits without storage access. -/
def compactView (wire : ByteArray) : Except TrieError (List Nat × Bool) :=
  (compactToNibbles wire).map (fun p ↦ (p.1.toList.map Fin.val, p.2))

/-- Full compact result comparison, retaining the original diagnostic. -/
def sameCompact : Except TrieError (List Nat × Bool) →
    Except TrieError (List Nat × Bool) → Bool
  | .ok x, .ok y => decide (x = y)
  | .error e, .error f => decide (e = f)
  | _, _ => false

/-- Every constructor and distinct payload controls. No dispatch is supplied. -/
def diagnostics : List Malformed :=
  [.rlp, .nonEmptyString, .compactPathList, .compactEmpty, .leafValueList, .pathEmpty,
   .badListLength 0, .badListLength 2, .badListLength 17,
   .refLength 0, .refLength 1, .refLength 32, .extChild,
   .occupancy 0, .occupancy 1, .occupancy 2, .cycle,
   .branchIndex 0 0, .branchIndex 1 0, .branchIndex 0 1, .branchIndex 15 15,
   .branchIndex 1000000 2000000, .branchIndex 2000000 1000000]

/-- Ordinary equality distinguishes all diagnostic constructors and payloads. -/
def diagnosticChecks : Bool := diagnostics.zipIdx.all fun (a, i) ↦
  diagnostics.zipIdx.all fun (c, j) ↦ decide (a = c) == decide (i = j)

/-- Construct a full hash payload through public byte contracts. -/
def hash (n : Nat) : STFSpec.Base.Hash32 :=
  STFSpec.Base.Hash32.ofBytes32 (STFSpec.Base.FixedBytes.ofNat n)

/-- Distinct wrapper and hash-payload controls plus every malformed diagnostic. -/
def errors : List TrieError :=
  [.missingRoot (hash 0), .missingRoot (hash 1),
   .unresolved (hash 0), .unresolved (hash 1)] ++
    diagnostics.map TrieError.malformed

/-- All wrappers retain the exact diagnostic/hash rather than aliasing. -/
def wrapperChecks : Bool := errors.zipIdx.all fun (a, i) ↦
  errors.zipIdx.all fun (c, j) ↦ decide (a = c) == decide (i = j)

/-- Actual whole-input codec results for minimal and competing C14 controls. -/
def rlpCases : List (ByteArray × Except RlpError RlpItem) :=
  [(b [194, 192, 192], .ok (.list [.list [], .list []])),
   (b [194, 32, 192], .ok (.list [.bytes (b [32]), .list []])),
   (b [194, 128, 192], .ok (.list [.bytes (b []), .list []])),
   (b [194, 192, 120], .ok (.list [.list [], .bytes (b [120])])),
   (b [194, 32, 128], .ok (.list [.bytes (b [32]), .bytes (b [])])),
   (b [194, 32, 120], .ok (.list [.bytes (b [32]), .bytes (b [120])])),
   (b [194, 0, 192], .ok (.list [.bytes (b [0]), .list []])),
   (b [194, 0, 120], .ok (.list [.bytes (b [0]), .bytes (b [120])])),
   (b [194, 16, 192], .ok (.list [.bytes (b [16]), .list []])),
   (b [196, 16, 194, 192, 192], .ok (.list [.bytes (b [16]), .list [.list [], .list []]])),
   (b [196, 16, 194, 32, 192], .ok (.list [.bytes (b [16]), .list [.bytes (b [32]), .list []]])),
   (b [196, 192, 129, 1, 128], .error (.nonCanonical "prefixed single byte")),
   (b [194, 32, 192, 128], .error .trailing)]

/-- Every flag and accepted padding/high-bit controls; no node validity check. -/
def compactCases : List (ByteArray × Except TrieError (List Nat × Bool)) :=
  [(b [], .error (.malformed .compactEmpty)),
   (b [0], .ok ([], false)),
   (b [16], .ok ([0], false)),
   (b [32], .ok ([], true)),
   (b [48], .ok ([0], true)),
   (b [64], .ok ([], false)),
   (b [80], .ok ([0], false)),
   (b [96], .ok ([], true)),
   (b [112], .ok ([0], true)),
   (b [128], .ok ([], false)),
   (b [144], .ok ([0], false)),
   (b [160], .ok ([], true)),
   (b [176], .ok ([0], true)),
   (b [192], .ok ([], false)),
   (b [208], .ok ([0], false)),
   (b [224], .ok ([], true)),
   (b [240], .ok ([0], true)),
   (b [15], .ok ([], false)),
   (b [47], .ok ([], true)),
   (b [111, 18], .ok ([1, 2], true)),
   (b [241, 35], .ok ([1, 2, 3], true)),
   (b [79], .ok ([], false)),
   (b [209, 35], .ok ([1, 2, 3], false))]

/-- Full actual codec results, without a diagnostic dispatcher. -/
def rlpChecks : Bool := rlpCases.all fun (wire, expected) ↦ sameRlp (Rlp.decode wire) expected

/-- Full actual compact results, including raw-empty priority. -/
def compactChecks : Bool := compactCases.all fun (wire, expected) ↦
  sameCompact (compactView wire) expected

#guard diagnosticChecks
#guard wrapperChecks
#guard rlpChecks
#guard compactChecks

end STFSpec.Conformance.Commit.DecoderDiagnosticGuards
