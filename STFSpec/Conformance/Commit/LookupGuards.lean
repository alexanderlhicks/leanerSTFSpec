/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import STFSpec.Commit

/-!
# Complete-value bare lookup controls

Library `EthConformance`. Arbitrary finite bare arities, paths and caches are
observed through the public operation and complete optional bytes/errors.
No observer depth, traversal budget or admission check is introduced.
Spec guidance: `STFSpec/informal/modules/EthCommit.md` C20/Q59/§4.
-/
namespace STFSpec.Conformance.Commit.LookupGuards
open STFSpec.Base STFSpec.Commit
private def bytes (xs : List UInt8) : ByteArray := xs.toByteArray
private def path (xs : List (Fin 16)) : Nibbles := Nibbles.ofList xs
private def hash (n : Nat) : Hash32 := Hash32.ofBytes32 (FixedBytes.ofNat n)
private def cache (n : Nat) : Enc := ⟨bytes [0, 255, UInt8.ofNat n], some (hash n)⟩
private def leaf (p : List (Fin 16)) (v : List UInt8) (n : Nat := 1) : Node :=
  .leaf (path p) (bytes v) (cache n)
private def same :
    Except TrieError (Option ByteArray) → Except TrieError (Option ByteArray) → Bool
  | .ok a, .ok b => decide (a = b)
  | .error a, .error b => decide (a = b)
  | _, _ => false
private def check (root : Ref) (p : List (Fin 16))
    (expected : Except TrieError (Option ByteArray)) : Bool :=
  same (lookup root (path p)) expected
private def wrap : Nat → Node → Node
  | 0, node => node
  | n + 1, node => .ext (path []) (wrap n node) (cache n)
private def branch (arity : Nat) (chosen : Nat) (node : Ref) : Node :=
  .branch (Array.ofFn (fun i : Fin arity =>
    if i.val = chosen then node else some (.hashed (hash 999))))
    (bytes [55]) (cache arity)

#guard check none [] (.ok none)
#guard check none [0, 15, 0] (.ok none)
#guard check (some (.hashed (hash 0))) [] (.error (.unresolved (hash 0)))
#guard check (some (.hashed (hash 1234))) [0] (.error (.unresolved (hash 1234)))
#guard check (some (leaf [] [])) [] (.ok (some (bytes [])))
#guard check (some (.branch #[] (bytes []) (cache 0))) [] (.ok none)
#guard check (some (.branch #[] (bytes [0, 255, 0]) (cache 0))) [] (.ok (some (bytes [0, 255, 0])))
#guard check (some (leaf [0, 1, 0, 15] [0, 255, 0])) [0, 1, 0, 15] (.ok (some (bytes [0, 255, 0])))
#guard check (some (leaf [0, 1] [1])) [1] (.ok none)
#guard check (some (leaf [1] [1])) [0, 1] (.ok none)
#guard check (some (leaf [] [1])) [0] (.ok none)
#guard check (some (.ext (path [0, 1]) (.hashed (hash 9)) (cache 4))) [0] (.ok none)
#guard check (some (.ext (path [0, 1]) (.hashed (hash 9)) (cache 4))) [0, 2] (.ok none)
#guard check (some (.ext (path [0, 1]) (.hashed (hash 9)) (cache 4))) [0, 1]
  (.error (.unresolved (hash 9)))
#guard check (some (.ext (path []) (leaf [0] [8]) (cache 7))) [0] (.ok (some (bytes [8])))
#guard check (some (.ext (path [0]) (.ext (path [1]) (leaf [2] [0, 8, 0]) (cache 9)) (cache 8)))
  [0, 1, 2] (.ok (some (bytes [0, 8, 0])))
#guard check (some (wrap 200 (leaf [] []))) [] (.ok (some (bytes [])))
#guard check (some (.ext (path [0]) (.branch #[] (bytes []) (cache 1)) (cache 2))) [1] (.ok none)
#guard check (some (.ext (path [0]) (.branch #[] (bytes []) (cache 1)) (cache 2))) [0, 15]
  (.error (.malformed (.branchIndex 15 0)))
#guard check (some (branch 17 15 (some (leaf [1] [0, 9, 255])))) [15, 1]
  (.ok (some (bytes [0, 9, 255])))
#guard (List.range 16).all fun i =>
  check (some (branch 16 i (some (leaf [0, 15] [UInt8.ofNat i, 0, 255]))))
    [⟨i % 16, Nat.mod_lt _ (by decide)⟩, 0, 15]
    (.ok (some (bytes [UInt8.ofNat i, 0, 255])))
#guard [0, 1, 15, 16, 17].all fun arity => (List.range 16).all fun i =>
  let digit : Fin 16 := ⟨i % 16, Nat.mod_lt _ (by decide)⟩
  check (some (branch arity i none)) [digit]
    (if i < arity then .ok none else .error (.malformed (.branchIndex i arity)))
#guard [0, 1, 15, 16, 17].all fun arity =>
  check (some (branch arity 0 (some (.hashed (hash 42))))) [] (.ok (some (bytes [55])))
#guard check (some (branch 1 0 (some (.hashed (hash 42))))) [0] (.error (.unresolved (hash 42)))
#guard check (some (branch 1 0 (some (.hashed (hash 42))))) [1]
  (.error (.malformed (.branchIndex 1 1)))
#guard check (some (branch 16 1 none)) [1] (.ok none)
#guard [0, 1, 2, 63, 64, 65, 129].all fun n =>
  let p := (List.range n).map fun i => (⟨i % 16, Nat.mod_lt _ (by decide)⟩ : Fin 16)
  check (some (leaf p [0, 255, UInt8.ofNat n])) p (.ok (some (bytes [0, 255, UInt8.ofNat n])))
#guard same (lookup (some (.leaf (path [0]) (bytes [255]) ⟨bytes [], none⟩)) (path [0]))
  (lookup (some (.leaf (path [0]) (bytes [255]) (cache 999))) (path [0]))
end STFSpec.Conformance.Commit.LookupGuards
