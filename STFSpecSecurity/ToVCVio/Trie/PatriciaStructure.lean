/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import ToVCVio.Trie.PatriciaNode

/-!
# Finite Patricia lookup and one-step prefix compression

Total lookup on resolved finite trees, including noncanonical trees. Packed path
joining has an ordinary List model equality. Prefix compression changes only the
outer constructor; no map canonicalizer or commitment interpretation is supplied.
Library `ToVCVio` in `STFSpecSecurity`.

Spec guidance: `STFSpec/informal/modules/ToVCVio.md`.
-/

namespace ToVCVio.Trie
open STFSpec.Commit

/-- Remove exactly the supplied prefix, or report absence. -/
def stripPrefix : List (Fin 16) → List (Fin 16) → Option (List (Fin 16))
  | [], key => some key
  | _ :: _, [] => none
  | a :: front, b :: key => if a = b then stripPrefix front key else none

/-- The empty prefix retains the complete key. -/
theorem stripPrefix_nil (key : List (Fin 16)) : stripPrefix [] key = some key := rfl
/-- A nonempty prefix cannot match an empty key. -/
theorem stripPrefix_short (a : Fin 16) (front : List (Fin 16)) :
    stripPrefix (a :: front) [] = none := rfl
/-- One digit comparison determines the next finite step. -/
theorem stripPrefix_cons (a b : Fin 16) (front key : List (Fin 16)) :
    stripPrefix (a :: front) (b :: key) =
      if a = b then stripPrefix front key else none := rfl
/-- Equal leading digits consume one digit from each list. -/
theorem stripPrefix_match (a : Fin 16) (front key : List (Fin 16)) :
    stripPrefix (a :: front) (a :: key) = stripPrefix front key := by
  simp [stripPrefix_cons]
/-- Unequal leading digits report absence. -/
theorem stripPrefix_mismatch (a b : Fin 16) (front key : List (Fin 16)) (h : a ≠ b) :
    stripPrefix (a :: front) (b :: key) = none := by simp [stripPrefix_cons, h]

/-- Successful removal is exactly finite concatenation. -/
theorem stripPrefix_some_iff (front key rest : List (Fin 16)) :
    stripPrefix front key = some rest ↔ key = front ++ rest := by
  induction front generalizing key with
  | nil => simp [stripPrefix_nil]
  | cons a front ih =>
    cases key with
    | nil => simp [stripPrefix_short]
    | cons b key =>
      by_cases h : a = b
      · subst b; simp [stripPrefix_match, ih]
      · simp [stripPrefix_mismatch _ _ _ _ h, Ne.symm h]

/-- Successive prefix removals compose through optional results. -/
theorem stripPrefix_append (front suffix key : List (Fin 16)) :
    stripPrefix (front ++ suffix) key =
      (stripPrefix front key).bind (stripPrefix suffix) := by
  induction front generalizing key with
  | nil => rfl
  | cons a front ih =>
    cases key with
    | nil => rfl
    | cons b key =>
      simp only [List.cons_append, stripPrefix_cons]
      split
      · exact ih key
      · rfl

/-- Removing a concatenated prefix retains the exact suffix. -/
theorem stripPrefix_concat (front rest : List (Fin 16)) :
    stripPrefix front (front ++ rest) = some rest :=
  (stripPrefix_some_iff _ _ _).mpr rfl
/-- Removing a path from itself leaves the empty remainder. -/
theorem stripPrefix_self (front : List (Fin 16)) : stripPrefix front front = some [] :=
  (stripPrefix_some_iff _ _ _).mpr (List.append_nil _).symm

mutual
  /-- Exact lookup on every finite resolved tree. -/
  def lookup (tree : FullTree) (key : List (Fin 16)) : Terminal :=
    match tree with
    | .leaf path value =>
      (stripPrefix path.toList key).bind (fun rest => if rest = [] then some value else none)
    | .extension path child => (stripPrefix path.toList key).bind (lookup child)
    | .branch children terminal =>
      match key with
      | [] => terminal
      | digit :: rest => lookupRoot (children digit) rest
  termination_by structural tree

  /-- The optional arm of lookup serves roots and numeric branch children. -/
  def lookupRoot (root : Option FullTree) (key : List (Fin 16)) : Terminal :=
    match root with
    | none => none
    | some tree => lookup tree key
  termination_by structural root
end

/-- A leaf matches exactly its complete remaining path. -/
theorem lookup_leaf (path : Nibbles) (value : PresentValue) (key : List (Fin 16)) :
    lookup (.leaf path value) key = if key = path.toList then some value else none := by
  simp only [lookup]
  cases h : stripPrefix path.toList key with
  | none =>
    have hn : key ≠ path.toList := by
      intro he; subst key; rw [stripPrefix_self] at h; contradiction
    simp [hn]
  | some rest =>
    have he := (stripPrefix_some_iff _ _ _).mp h
    by_cases hr : rest = []
    · subst rest; simp only [List.append_nil] at he; simp [he]
    · have hn : key ≠ path.toList := by
        intro hk
        have := congrArg List.length he
        have hz : rest.length = 0 := by rw [hk, List.length_append] at this; omega
        exact hr (List.eq_nil_iff_length_eq_zero.mpr hz)
      simp [hr, hn]

/-- Leaf presence is equivalent to exact path equality. -/
theorem lookup_leaf_some_iff (path : Nibbles) (value : PresentValue) (key : List (Fin 16)) :
    lookup (.leaf path value) key = some value ↔ key = path.toList := by
  rw [lookup_leaf]; split <;> simp_all
/-- Every leaf returns its value at its exact path. -/
theorem lookup_leaf_exact (path : Nibbles) (value : PresentValue) :
    lookup (.leaf path value) path.toList = some value := by simp [lookup_leaf]
/-- An empty-path leaf is observed at the empty key. -/
theorem lookup_leaf_empty (value : PresentValue) :
    lookup (.leaf (Nibbles.ofList []) value) [] = some value := by
  simp [lookup_leaf, Nibbles.toList_ofList]
/-- An extension consumes its entire segment before child lookup. -/
theorem lookup_extension (path : Nibbles) (child : FullTree) (key : List (Fin 16)) :
    lookup (.extension path child) key = (stripPrefix path.toList key).bind (lookup child) := rfl
/-- A complete extension prefix delegates to the child suffix. -/
theorem lookup_extension_append (path : Nibbles) (child : FullTree) (rest : List (Fin 16)) :
    lookup (.extension path child) (path.toList ++ rest) = lookup child rest := by
  rw [lookup_extension, stripPrefix_concat]; rfl
/-- Only the empty branch query observes its terminal. -/
theorem lookup_branch_nil (children : Fin 16 → Option FullTree) (terminal : Terminal) :
    lookup (.branch children terminal) [] = terminal := rfl
/-- A numeric digit selects exactly that optional child. -/
theorem lookup_branch_cons (children : Fin 16 → Option FullTree) (terminal : Terminal)
    (digit : Fin 16) (rest : List (Fin 16)) :
    lookup (.branch children terminal) (digit :: rest) = lookupRoot (children digit) rest := rfl
/-- An absent resolved root has no value at any key. -/
theorem lookupRoot_none (key : List (Fin 16)) : lookupRoot none key = none := rfl
/-- A present resolved root delegates directly to its tree. -/
theorem lookupRoot_some (tree : FullTree) (key : List (Fin 16)) :
    lookupRoot (some tree) key = lookup tree key := rfl

/-- Observe complete present bytes at a packed key. -/
def observe (root : Option FullTree) (key : Nibbles) : Option ByteArray :=
  (lookupRoot root key.toList).map Subtype.val
/-- Absent roots have no byte observation. -/
theorem observe_none (key : Nibbles) : observe none key = none := rfl
/-- Present roots expose complete bytes of the resolved value. -/
theorem observe_some (tree : FullTree) (key : Nibbles) :
    observe (some tree) key = (lookup tree key.toList).map Subtype.val := rfl

/-- Legible path join model. -/
def joinPathReference (p q : Nibbles) : Nibbles := Nibbles.ofList (p.toList ++ q.toList)

private def joinDigit (p q : Nibbles) (i : Nat) : Fin 16 :=
  if hp : i < p.size then p.get ⟨i, hp⟩
  else if hq : i - p.size < q.size then q.get ⟨i - p.size, hq⟩ else 0

/-- Packed join reads bounded digits directly without materializing either List. -/
def joinPath (p q : Nibbles) : Nibbles := Nibbles.generate (p.size + q.size) (joinDigit p q)

/-- The complete packed observer is finite List concatenation. -/
theorem joinPath_toList (p q : Nibbles) : (joinPath p q).toList = p.toList ++ q.toList := by
  apply List.ext_getElem
  · rw [Nibbles.length_toList, joinPath, Nibbles.size_generate, List.length_append,
      Nibbles.length_toList, Nibbles.length_toList]
  · intro i hi hj
    have hi' : i < p.size + q.size := by
      simpa only [List.length_append, Nibbles.length_toList] using hj
    rw [Nibbles.getElem_toList _ _ (by simpa only [Nibbles.length_toList] using hi)]
    change (Nibbles.generate (p.size + q.size) (joinDigit p q)).get
      ⟨i, by rw [Nibbles.size_generate]; exact hi'⟩ = _
    rw [Nibbles.get_generate _ _ i hi']
    by_cases hp : i < p.size
    · rw [List.getElem_append_left (by rwa [Nibbles.length_toList])]
      simp only [joinDigit, dite_eq_left hp]
      exact (Nibbles.getElem_toList p i hp).symm
    · have hq : i - p.size < q.size := by omega
      rw [List.getElem_append_right (by rw [Nibbles.length_toList]; omega)]
      simp only [joinDigit, dite_eq_right hp, dite_eq_left hq, Nibbles.length_toList]
      exact (Nibbles.getElem_toList q (i - p.size) hq).symm

/-- Ordinary equality with the reference, for all packed inputs. -/
theorem joinPath_eq_reference (p q : Nibbles) : joinPath p q = joinPathReference p q := by
  apply Nibbles.ext
  rw [joinPath_toList, joinPathReference, Nibbles.toList_ofList]
/-- Packed join retains both complete input lengths. -/
theorem joinPath_size (p q : Nibbles) : (joinPath p q).size = p.size + q.size := by
  rw [← Nibbles.length_toList, joinPath_toList, List.length_append,
    Nibbles.length_toList, Nibbles.length_toList]
/-- Joining an empty left path preserves the right path. -/
theorem joinPath_empty_left (q : Nibbles) : joinPath (Nibbles.ofList []) q = q := by
  apply Nibbles.ext; simp [joinPath_toList, Nibbles.toList_ofList]
/-- Joining an empty right path preserves the left path. -/
theorem joinPath_empty_right (p : Nibbles) : joinPath p (Nibbles.ofList []) = p := by
  apply Nibbles.ext; simp [joinPath_toList, Nibbles.toList_ofList]
/-- A positive right path makes the joined path positive. -/
theorem joinPath_positive_right (p q : Nibbles) (hq : 0 < q.size) :
    0 < (joinPath p q).size := by rw [joinPath_size]; omega

/-- Merge only the outer path, retaining an empty-prefix branch unchanged. -/
def prepend (p : Nibbles) : FullTree → FullTree
  | .leaf q value => .leaf (joinPath p q) value
  | .extension q child => .extension (joinPath p q) child
  | .branch children terminal =>
    if p.size = 0 then .branch children terminal else .extension p (.branch children terminal)
/-- A leaf absorbs the supplied prefix into its remaining path. -/
theorem prepend_leaf (p q : Nibbles) (value : PresentValue) :
    prepend p (.leaf q value) = .leaf (joinPath p q) value := rfl
/-- An extension absorbs the supplied prefix into its segment. -/
theorem prepend_extension (p q : Nibbles) (child : FullTree) :
    prepend p (.extension q child) = .extension (joinPath p q) child := rfl
/-- A branch is retained for an empty prefix and otherwise wrapped once. -/
theorem prepend_branch (p : Nibbles) (children : Fin 16 → Option FullTree) (terminal : Terminal) :
    prepend p (.branch children terminal) =
      if p.size = 0 then .branch children terminal else .extension p (.branch children terminal) :=
  rfl
/-- The empty prefix leaves every outer constructor unchanged. -/
theorem prepend_empty (tree : FullTree) : prepend (Nibbles.ofList []) tree = tree := by
  cases tree <;> simp [prepend, joinPath_empty_left, Nibbles.size_ofList]

/-- Prefix compression preserves lookup unconditionally, even for noncanonical trees. -/
theorem lookup_prepend (p : Nibbles) (tree : FullTree) (key : List (Fin 16)) :
    lookup (prepend p tree) key = (stripPrefix p.toList key).bind (lookup tree) := by
  cases tree with
  | leaf q value =>
    simp only [prepend_leaf, lookup, joinPath_toList, stripPrefix_append, Option.bind_assoc]
  | extension q child =>
    simp only [prepend_extension, lookup_extension, joinPath_toList, stripPrefix_append,
      Option.bind_assoc]
    apply congrArg (Option.bind (stripPrefix p.toList key))
    funext rest
    exact (lookup_extension q child rest).symm
  | branch children terminal =>
    rw [prepend_branch]
    split
    · next hz =>
      have he : p.toList = [] :=
        List.eq_nil_iff_length_eq_zero.mpr (by rw [Nibbles.length_toList, hz])
      rw [he, stripPrefix_nil]; rfl
    · exact lookup_extension _ _ _

/-- One-step prefix compression preserves the actual recursive shape predicate. -/
theorem prepend_canonical (p : Nibbles) (tree : FullTree) (h : Canonical tree) :
    Canonical (prepend p tree) := by
  cases h with
  | leaf q value => exact Canonical.leaf _ _
  | extension q children terminal positive child =>
    exact Canonical.extension _ _ _ (joinPath_positive_right p q positive) child
  | branch children terminal childrenCanonical occupancy =>
    rw [prepend_branch]; split
    · exact Canonical.branch _ _ childrenCanonical occupancy
    · next hp =>
        exact Canonical.extension _ _ _ (by omega)
          (Canonical.branch _ _ childrenCanonical occupancy)

/-- Observing a joined prefix after compression equals the original suffix observation. -/
theorem observe_prepend_join (p suffix : Nibbles) (tree : FullTree) :
    observe (some (prepend p tree)) (joinPath p suffix) = observe (some tree) suffix := by
  rw [observe_some, lookup_prepend, joinPath_toList, stripPrefix_concat]
  rfl

end ToVCVio.Trie
