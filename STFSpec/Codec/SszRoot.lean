/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.SszRootable
import STFSpec.Codec.SszMerkleizeProgressive
import STFSpec.Codec.SszMixInLength
import STFSpec.Codec.SszMixInActiveFields

/-!
# SSZ hash-tree roots

Library `EthCodec`. Roots follow actual finite values under local root support;
unused composite schemas are not visited. Reference: EELS
    `src/ethereum/utils/ssz.py:133–135,263–296`
and locked eth-remerkleable 0.1.31 `basic.py`, `core.py`, `complex.py`,
`byte_arrays.py`, `progressive.py`.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7 (Q79).
-/

namespace STFSpec.Codec

private def chunkCount (n : Nat) : Nat := (n + 31) / 32

private def capacity (n : Nat) : Nat :=
  2 ^ (if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1)

private theorem le_capacity (n : Nat) : n ≤ capacity n := by
  unfold capacity
  split
  · omega
  · have h := (Nat.log2_lt (by omega : n - 1 ≠ 0)).mp
      (Nat.lt_succ_self (Nat.log2 (n - 1)))
    omega

private theorem pack_size (b : ByteArray) : (Ssz.pack b).size = chunkCount b.size := by
  have h := congrArg List.length (Ssz.pack_toBytes b)
  simpa only [List.length_map, Array.length_toList, List.length_range, chunkCount] using h

private theorem packed_capacity (b : ByteArray) (n : Nat) (h : b.size ≤ n) :
    (Ssz.pack b).size ≤ capacity (chunkCount n) := by
  rw [pack_size]
  apply Nat.le_trans _ (le_capacity _)
  unfold chunkCount
  omega

private def digits (w n : Nat) : List UInt8 :=
  (List.range w).map (fun i ↦ UInt8.ofNat (n >>> (8 * i)))

private def uintBytes (w : Nat) (xs : List SszValue) : List UInt8 :=
  xs.flatMap (fun x ↦ digits w (match x with | .uint n => n | _ => 0))

private def boolBytes (xs : List SszValue) : List UInt8 :=
  xs.map (fun x ↦ match x with | .bool b => if b then 1 else 0 | _ => 0)

private theorem uintBytes_length (w : Nat) (xs : List SszValue) :
    (uintBytes w xs).length = xs.length * w := by
  induction xs with
  | nil => simp [uintBytes]
  | cons x xs ih =>
    change (digits w _ ++ uintBytes w xs).length = (xs.length + 1) * w
    rw [List.length_append, ih]
    simp [digits, Nat.add_mul, Nat.add_comm]

private theorem boolBytes_length (xs : List SszValue) :
    (boolBytes xs).length = xs.length := List.length_map _

private theorem uint_packed_capacity (w limit : Nat) (xs : List SszValue)
    (h : xs.length ≤ limit) :
    (Ssz.pack (uintBytes w xs).toByteArray).size ≤ capacity (chunkCount (limit * w)) := by
  apply packed_capacity
  rw [List.size_toByteArray, uintBytes_length]
  exact Nat.mul_le_mul_right w h

private theorem bool_packed_capacity (limit : Nat) (xs : List SszValue)
    (h : xs.length ≤ limit) :
    (Ssz.pack (boolBytes xs).toByteArray).size ≤ capacity (chunkCount limit) := by
  apply packed_capacity
  simpa only [List.size_toByteArray, boolBytes_length] using h

private theorem zip_value_mem {fields : List SszType} {xs : List SszValue}
    {p : SszType × SszValue} (h : p ∈ fields.zip xs) : p.2 ∈ xs := by
  induction fields generalizing xs with
  | nil => simp at h
  | cons f fs ih =>
    cases xs with
    | nil => simp at h
    | cons x xs =>
      simp only [List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem x (ih h)

private def sparseSlots (mask : List Bool) (rs : List Base.Bytes32) : List Base.Bytes32 :=
  match mask with
  | [] => []
  | false :: mask => (Base.FixedBytes.ofNat 0 : Base.Bytes32) :: sparseSlots mask rs
  | true :: mask => rs.headD (Base.FixedBytes.ofNat 0) :: sparseSlots mask rs.tail

private theorem sparseSlots_length (mask : List Bool) (rs : List Base.Bytes32) :
    (sparseSlots mask rs).length = mask.length := by
  induction mask generalizing rs with
  | nil => rfl
  | cons b mask ih => cases b <;> simp only [sparseSlots, List.length_cons, ih]

private theorem tail_getD {α : Type} (rs : List α) (i : Nat) (z : α) :
    rs.tail.getD i z = rs.getD (i + 1) z := by
  cases rs <;> simp

private theorem sparseSlots_getD (mask : List Bool) (rs : List Base.Bytes32) (i : Nat) :
    (sparseSlots mask rs).getD i (Base.FixedBytes.ofNat 0) =
      if mask.getD i false then
        rs.getD ((mask.take i).filter id).length (Base.FixedBytes.ofNat 0)
      else Base.FixedBytes.ofNat 0 := by
  induction mask generalizing rs i with
  | nil => simp [sparseSlots]
  | cons b mask ih =>
    cases i with
    | zero => cases b <;> simp only [sparseSlots, List.getD_cons_zero, List.take_zero,
        List.filter_nil, List.length_nil, Bool.false_eq_true, reduceIte, List.headD_eq_getD]
    | succ i =>
      cases b <;>
        rw [sparseSlots, List.getD_cons_succ, ih] <;>
        simp only [List.getD_cons_succ, List.take_succ_cons, List.filter_cons,
          id_eq, Bool.false_eq_true, reduceIte, List.length_cons, tail_getD]

private theorem sparseSlots_model (mask : List Bool) (rs : List Base.Bytes32) :
    sparseSlots mask rs =
      (List.range mask.length).map (fun i ↦
        if mask.getD i false then
          rs.getD ((mask.take i).filter id).length (Base.FixedBytes.ofNat 0)
        else Base.FixedBytes.ofNat 0) := by
  apply List.ext_getElem
  · simp only [sparseSlots_length, List.length_map, List.length_range]
  · intro i hi hj
    rw [List.getElem_eq_getD (Base.FixedBytes.ofNat 0 : Base.Bytes32)]
    rw [sparseSlots_getD]
    simp only [List.getElem_map, List.getElem_range]

private theorem aligned_roots {α β : Type} (P : α → Prop)
    (r : (a : α) → P a → β) (ps : List α) (hs : ∀ p ∈ ps, P p)
    (rs : List β) (hl : ps.length = rs.length)
    (hc : ∀ p ∈ ps.zip rs, ∀ hp : P p.1, r p.1 hp = p.2) :
    ps.attach.map (fun p ↦ r p.val (hs p.val p.property)) = rs := by
  induction ps generalizing rs with
  | nil => cases rs <;> simp_all
  | cons p ps ih =>
    cases rs with
    | nil => simp at hl
    | cons r0 rs =>
      simp only [List.attach_cons, List.map_cons, List.map_map]
      change r p _ :: _ = r0 :: rs
      congr 1
      · exact hc (p, r0) (by simp) _
      · exact ih (fun x hx ↦ hs x (by simp [hx])) rs (by simpa using hl)
          (fun q hq hp ↦ hc q (by simp [hq]) hp)

private def contentsChunks (elem : SszType) (xs : List SszValue)
    (child : {x // x ∈ xs} → Base.Bytes32) : Array Base.Bytes32 :=
  match elem with
  | .uint w => Ssz.pack (uintBytes w xs).toByteArray
  | .bool => Ssz.pack (boolBytes xs).toByteArray
  | .byteVector _ | .byteList _ | .list _ _ | .progressiveList _ |
    .progressiveByteList | .container _ | .progressiveContainer _ _ =>
      (xs.attach.map child).toArray

private def contentsLimit (elem : SszType) (limit : Nat) : Nat :=
  match elem with
  | .uint w => chunkCount (limit * w)
  | .bool => chunkCount limit
  | .byteVector _ | .byteList _ | .list _ _ | .progressiveList _ |
    .progressiveByteList | .container _ | .progressiveContainer _ _ => limit

private theorem contents_capacity (elem : SszType) (limit : Nat) (xs : List SszValue)
    (child : {x // x ∈ xs} → Base.Bytes32) (h : xs.length ≤ limit) :
    (contentsChunks elem xs child).size ≤ capacity (contentsLimit elem limit) := by
  cases elem with
  | uint w => exact uint_packed_capacity w limit xs h
  | bool => exact bool_packed_capacity limit xs h
  | _ =>
    apply Nat.le_trans _ (le_capacity limit)
    simpa only [contentsChunks, List.size_toArray, List.length_map, List.length_attach] using h

private def root (t : SszType) (v : SszValue) (h : Ssz.Rootable t v) : Base.Bytes32 :=
  match t, v with
  | .uint _, .uint n => Base.FixedBytes.ofLeNat n
  | .bool, .bool b => Base.FixedBytes.ofLeNat (if b then 1 else 0)
  | .byteVector n, .bytes b =>
      Ssz.merkleize (Ssz.pack b) (chunkCount n)
        (packed_capacity b n (Nat.le_of_eq ((Ssz.rootable_iff _ _).mp h)))
  | .byteList limit, .bytes b =>
      have hs := (Ssz.rootable_iff _ _).mp h
      Ssz.mixInLength
        (Ssz.merkleize (Ssz.pack b) (chunkCount limit) (packed_capacity b limit hs.1))
        b.size hs.2
  | .list elem limit, .list xs =>
      have hs := (Ssz.rootable_iff _ _).mp h
      let child := fun x : {x // x ∈ xs} ↦ root elem x.val (hs.2.2.1 x.val x.property)
      Ssz.mixInLength
        (Ssz.merkleize (contentsChunks elem xs child) (contentsLimit elem limit)
          (contents_capacity elem limit xs child hs.1)) xs.length hs.2.1
  | .progressiveList elem, .list xs =>
      have hs := (Ssz.rootable_iff _ _).mp h
      let child := fun x : {x // x ∈ xs} ↦ root elem x.val (hs.2.1 x.val x.property)
      Ssz.mixInLength (Ssz.merkleizeProgressive (contentsChunks elem xs child) 0)
        xs.length hs.1
  | .progressiveByteList, .bytes b =>
      Ssz.mixInLength (Ssz.merkleizeProgressive (Ssz.pack b) 0) b.size
        ((Ssz.rootable_iff _ _).mp h)
  | .container fields, .container xs =>
      have hs := (Ssz.rootable_iff _ _).mp h
      let rs := (fields.zip xs).attach.map
        (fun p ↦ root p.val.1 p.val.2 (hs.2.2 p.val p.property))
      Ssz.merkleize rs.toArray fields.length (by
        apply Nat.le_trans _ (le_capacity fields.length)
        simp only [rs, List.size_toArray, List.length_map, List.length_attach, List.length_zip]
        omega)
  | .progressiveContainer mask fields, .container xs =>
      have hs := (Ssz.rootable_iff _ _).mp h
      let rs := (fields.zip xs).attach.map
        (fun p ↦ root p.val.1 p.val.2 (hs.2.2.2.2 p.val p.property))
      Ssz.mixInActiveFields (Ssz.merkleizeProgressive (sparseSlots mask rs).toArray 0)
        mask hs.2.1
  | .uint _, .bool _ | .uint _, .bytes _ | .uint _, .list _ | .uint _, .container _ |
    .bool, .uint _ | .bool, .bytes _ | .bool, .list _ | .bool, .container _ |
    .byteVector _, .uint _ | .byteVector _, .bool _ | .byteVector _, .list _ |
    .byteVector _, .container _ | .byteList _, .uint _ | .byteList _, .bool _ |
    .byteList _, .list _ | .byteList _, .container _ | .list _ _, .uint _ |
    .list _ _, .bool _ | .list _ _, .bytes _ | .list _ _, .container _ |
    .progressiveList _, .uint _ | .progressiveList _, .bool _ |
    .progressiveList _, .bytes _ | .progressiveList _, .container _ |
    .progressiveByteList, .uint _ | .progressiveByteList, .bool _ |
    .progressiveByteList, .list _ | .progressiveByteList, .container _ |
    .container _, .uint _ | .container _, .bool _ | .container _, .bytes _ |
    .container _, .list _ | .progressiveContainer _ _, .uint _ |
    .progressiveContainer _ _, .bool _ | .progressiveContainer _ _, .bytes _ |
    .progressiveContainer _ _, .list _ => False.elim ((Ssz.rootable_iff _ _).mp h)
termination_by sizeOf v
decreasing_by
  all_goals
    first
    | have hm := List.sizeOf_lt_of_mem x.property
      simp only [SszValue.list.sizeOf_spec]
      omega
    | have hm := List.sizeOf_lt_of_mem (zip_value_mem p.property)
      simp only [SszValue.container.sizeOf_spec]
      omega

/-- Root of a locally supported SSZ value. Support concerns actual values and
local declared bounds; it supplies no decoder/source-class or guest bridge.
Pinned EELS `src/ethereum/utils/ssz.py:133–135`; constructor mapping is in the
spec guidance source-to-Lean rows. -/
def Ssz.hashTreeRoot (t : SszType) (v : SszValue)
    (h : Ssz.Rootable t v) : Base.Bytes32 := root t v h

private theorem uintBytes_map (w : Nat) (ns : List Nat) :
    uintBytes w (ns.map SszValue.uint) = ns.flatMap (digits w) := by
  simp only [uintBytes, List.flatMap_map]

private theorem boolBytes_map (bs : List Bool) :
    boolBytes (bs.map SszValue.bool) = bs.map (fun b ↦ if b then (1 : UInt8) else 0) := by
  rw [boolBytes, List.map_map]
  rfl

private theorem roots_values_eq (elem : SszType) (xs : List SszValue)
    (hs : ∀ x ∈ xs, Ssz.Rootable elem x) (rs : List Base.Bytes32)
    (hc : (xs.map (fun x ↦ (elem, x))).length = rs.length ∧
      ∀ p ∈ (xs.map (fun x ↦ (elem, x))).zip rs,
        ∀ hx : Ssz.Rootable p.1.1 p.1.2, Ssz.hashTreeRoot p.1.1 p.1.2 hx = p.2) :
    xs.attach.map (fun x ↦ root elem x.val (hs x.val x.property)) = rs := by
  apply aligned_roots (fun x ↦ Ssz.Rootable elem x) (root elem) xs hs rs
  · simpa only [List.length_map] using hc.1
  · intro p hp hx
    apply hc.2 ((elem, p.1), p.2) _ hx
    rw [List.zip_map_left]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩

private theorem roots_fields_eq (ps : List (SszType × SszValue))
    (hs : ∀ p ∈ ps, Ssz.Rootable p.1 p.2) (rs : List Base.Bytes32)
    (hc : ps.length = rs.length ∧ ∀ p ∈ ps.zip rs,
      ∀ hx : Ssz.Rootable p.1.1 p.1.2, Ssz.hashTreeRoot p.1.1 p.1.2 hx = p.2) :
    ps.attach.map (fun p ↦ root p.val.1 p.val.2 (hs p.val p.property)) = rs :=
  aligned_roots (fun p ↦ Ssz.Rootable p.1 p.2) (fun p ↦ root p.1 p.2) ps hs rs hc.1 hc.2

private theorem root_uint_step (w n : Nat) (h : Ssz.Rootable (.uint w) (.uint n)) :
    Ssz.hashTreeRoot (.uint w) (.uint n) h = Base.FixedBytes.ofLeNat n := by
  rw [Ssz.hashTreeRoot, root]

private theorem root_bool_step (b : Bool) (h : Ssz.Rootable .bool (.bool b)) :
    Ssz.hashTreeRoot .bool (.bool b) h = Base.FixedBytes.ofLeNat (if b then 1 else 0) := by
  rw [Ssz.hashTreeRoot, root]

private theorem root_vector_step (n : Nat) (b : ByteArray)
    (h : Ssz.Rootable (.byteVector n) (.bytes b))
    (hp : (Ssz.pack b).size ≤ capacity (chunkCount n)) :
    Ssz.hashTreeRoot (.byteVector n) (.bytes b) h =
      Ssz.merkleize (Ssz.pack b) (chunkCount n) hp := by
  rw [Ssz.hashTreeRoot, root]

private theorem root_bytes_step (limit : Nat) (b : ByteArray)
    (h : Ssz.Rootable (.byteList limit) (.bytes b))
    (hp : (Ssz.pack b).size ≤ capacity (chunkCount limit)) (hn : b.size < 2 ^ 256) :
    Ssz.hashTreeRoot (.byteList limit) (.bytes b) h =
      Ssz.mixInLength (Ssz.merkleize (Ssz.pack b) (chunkCount limit) hp) b.size hn := by
  rw [Ssz.hashTreeRoot, root]

private theorem root_list_step (elem : SszType) (limit : Nat) (xs : List SszValue)
    (h : Ssz.Rootable (.list elem limit) (.list xs)) :
    let hs := (Ssz.rootable_iff _ _).mp h
    let child := fun x : {x // x ∈ xs} ↦ root elem x.val (hs.2.2.1 x.val x.property)
    Ssz.hashTreeRoot (.list elem limit) (.list xs) h =
      Ssz.mixInLength
        (Ssz.merkleize (contentsChunks elem xs child) (contentsLimit elem limit)
          (contents_capacity elem limit xs child hs.1)) xs.length hs.2.1 := by
  dsimp only
  rw [Ssz.hashTreeRoot, root]

private theorem root_progressive_list_step (elem : SszType) (xs : List SszValue)
    (h : Ssz.Rootable (.progressiveList elem) (.list xs)) :
    let hs := (Ssz.rootable_iff _ _).mp h
    let child := fun x : {x // x ∈ xs} ↦ root elem x.val (hs.2.1 x.val x.property)
    Ssz.hashTreeRoot (.progressiveList elem) (.list xs) h =
      Ssz.mixInLength (Ssz.merkleizeProgressive (contentsChunks elem xs child) 0)
        xs.length hs.1 := by
  dsimp only
  rw [Ssz.hashTreeRoot, root]

private theorem root_progressive_bytes_step (b : ByteArray)
    (h : Ssz.Rootable .progressiveByteList (.bytes b)) (hn : b.size < 2 ^ 256) :
    Ssz.hashTreeRoot .progressiveByteList (.bytes b) h =
      Ssz.mixInLength (Ssz.merkleizeProgressive (Ssz.pack b) 0) b.size hn := by
  rw [Ssz.hashTreeRoot, root]

private theorem root_fields_step (fields : List SszType) (xs : List SszValue)
    (h : Ssz.Rootable (.container fields) (.container xs)) :
    let hs := (Ssz.rootable_iff _ _).mp h
    let rs := (fields.zip xs).attach.map
      (fun p ↦ root p.val.1 p.val.2 (hs.2.2 p.val p.property))
    Ssz.hashTreeRoot (.container fields) (.container xs) h =
      Ssz.merkleize rs.toArray fields.length (by
        apply Nat.le_trans _ (le_capacity fields.length)
        simp only [rs, List.size_toArray, List.length_map, List.length_attach, List.length_zip]
        omega) := by
  dsimp only
  rw [Ssz.hashTreeRoot, root]

private theorem root_progressive_fields_step (mask : List Bool) (fields : List SszType)
    (xs : List SszValue) (h : Ssz.Rootable (.progressiveContainer mask fields) (.container xs)) :
    let hs := (Ssz.rootable_iff _ _).mp h
    let rs := (fields.zip xs).attach.map
      (fun p ↦ root p.val.1 p.val.2 (hs.2.2.2.2 p.val p.property))
    Ssz.hashTreeRoot (.progressiveContainer mask fields) (.container xs) h =
      Ssz.mixInActiveFields (Ssz.merkleizeProgressive (sparseSlots mask rs).toArray 0)
        mask hs.2.1 := by
  dsimp only
  rw [Ssz.hashTreeRoot, root]

/-- Complete constructor-result equation on local support. -/
theorem Ssz.hashTreeRoot_eq (t : SszType) (v : SszValue)
    (h : Ssz.Rootable t v) :
  let R := Ssz.hashTreeRoot
  let result := R t v h
  let q : Nat → Nat := fun n => (n + 31) / 32
  let K : Nat → Nat := fun n =>
    2 ^ (if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1)
  let zero := (Base.FixedBytes.ofNat 0 : Base.Bytes32)
  let digits : Nat → Nat → List UInt8 := fun w n =>
    (List.range w).map (fun i => UInt8.ofNat (n >>> (8 * i)))
  let uintChunks : Nat → List Nat → Array Base.Bytes32 := fun w ns =>
    Ssz.pack ((ns.flatMap (digits w)).toByteArray)
  let boolChunks : List Bool → Array Base.Bytes32 := fun bs =>
    Ssz.pack ((bs.map (fun b => if b then (1 : UInt8) else 0)).toByteArray)
  let children : List (SszType × SszValue) → List Base.Bytes32 → Prop :=
    fun ps rs =>
      ps.length = rs.length ∧
      ∀ p ∈ ps.zip rs, ∀ hx : Ssz.Rootable p.1.1 p.1.2,
        R p.1.1 p.1.2 hx = p.2
  let slots : List Bool → List Base.Bytes32 → Array Base.Bytes32 := fun mask rs =>
    ((List.range mask.length).map (fun i =>
      if mask.getD i false then
        rs.getD ((mask.take i).filter id).length zero
      else zero)).toArray
  match t, v with
  | .uint _, .uint n =>
      result = (Base.FixedBytes.ofLeNat n : Base.Bytes32)
  | .bool, .bool b =>
      result = (Base.FixedBytes.ofLeNat (if b then 1 else 0) : Base.Bytes32)
  | .byteVector n, .bytes b =>
      ∀ hp : (Ssz.pack b).size ≤ K (q n),
        result = Ssz.merkleize (Ssz.pack b) (q n) hp
  | .byteList limit, .bytes b =>
      ∀ hp : (Ssz.pack b).size ≤ K (q limit), ∀ hn : b.size < 2 ^ 256,
        result = Ssz.mixInLength
          (Ssz.merkleize (Ssz.pack b) (q limit) hp) b.size hn
  | .list elem limit, .list xs =>
      match elem with
      | .uint w =>
          ∀ ns : List Nat, xs = ns.map SszValue.uint →
          ∀ hp : (uintChunks w ns).size ≤ K (q (limit * w)),
          ∀ hn : xs.length < 2 ^ 256,
            result = Ssz.mixInLength
              (Ssz.merkleize (uintChunks w ns) (q (limit * w)) hp) xs.length hn
      | .bool =>
          ∀ bs : List Bool, xs = bs.map SszValue.bool →
          ∀ hp : (boolChunks bs).size ≤ K (q limit),
          ∀ hn : xs.length < 2 ^ 256,
            result = Ssz.mixInLength
              (Ssz.merkleize (boolChunks bs) (q limit) hp) xs.length hn
      | .byteVector _ | .byteList _ | .list _ _ | .progressiveList _ |
        .progressiveByteList | .container _ | .progressiveContainer _ _ =>
          ∀ rs : List Base.Bytes32,
          children (xs.map (fun x => (elem, x))) rs →
          ∀ hp : rs.toArray.size ≤ K limit, ∀ hn : xs.length < 2 ^ 256,
            result = Ssz.mixInLength
              (Ssz.merkleize rs.toArray limit hp) xs.length hn
  | .progressiveList elem, .list xs =>
      match elem with
      | .uint w =>
          ∀ ns : List Nat, xs = ns.map SszValue.uint →
          ∀ hn : xs.length < 2 ^ 256,
            result = Ssz.mixInLength
              (Ssz.merkleizeProgressive (uintChunks w ns) 0) xs.length hn
      | .bool =>
          ∀ bs : List Bool, xs = bs.map SszValue.bool →
          ∀ hn : xs.length < 2 ^ 256,
            result = Ssz.mixInLength
              (Ssz.merkleizeProgressive (boolChunks bs) 0) xs.length hn
      | .byteVector _ | .byteList _ | .list _ _ | .progressiveList _ |
        .progressiveByteList |
        .container _ | .progressiveContainer _ _ =>
          ∀ rs : List Base.Bytes32,
          children (xs.map (fun x => (elem, x))) rs →
          ∀ hn : xs.length < 2 ^ 256,
            result = Ssz.mixInLength
              (Ssz.merkleizeProgressive rs.toArray 0) xs.length hn
  | .progressiveByteList, .bytes b =>
      ∀ hn : b.size < 2 ^ 256,
        result = Ssz.mixInLength
          (Ssz.merkleizeProgressive (Ssz.pack b) 0) b.size hn
  | .container fields, .container xs =>
      ∀ rs : List Base.Bytes32, children (fields.zip xs) rs →
      ∀ hp : rs.toArray.size ≤ K fields.length,
        result = Ssz.merkleize rs.toArray fields.length hp
  | .progressiveContainer mask fields, .container xs =>
      ∀ rs : List Base.Bytes32, children (fields.zip xs) rs →
      ∀ hm : mask.length ≤ 256,
        result = Ssz.mixInActiveFields
          (Ssz.merkleizeProgressive (slots mask rs) 0) mask hm
  | _, _ => False := by
  dsimp only
  cases t <;> cases v <;>
    first
    | exact False.elim ((Ssz.rootable_iff _ _).mp h)
    | skip
  case uint.uint => exact root_uint_step _ _ h
  case bool.bool => exact root_bool_step _ h
  case byteVector.bytes => exact root_vector_step _ _ h
  case byteList.bytes => exact root_bytes_step _ _ h
  case progressiveByteList.bytes => exact root_progressive_bytes_step _ h
  case list.list elem limit xs =>
    have hs := (Ssz.rootable_iff _ _).mp h
    cases elem with
    | uint w =>
      intro ns he hp hn
      subst xs
      rw [root_list_step]
      simp only [contentsChunks, contentsLimit, uintBytes_map]
      rfl
    | bool =>
      intro bs he hp hn
      subst xs
      rw [root_list_step]
      simp only [contentsChunks, contentsLimit, boolBytes_map]
      rfl
    | _ =>
      intro rs hc hp hn
      have he := roots_values_eq _ xs hs.2.2.1 rs hc
      subst rs
      rw [root_list_step]
      rfl
  case progressiveList.list elem xs =>
    have hs := (Ssz.rootable_iff _ _).mp h
    cases elem with
    | uint w =>
      intro ns he hn
      subst xs
      rw [root_progressive_list_step]
      simp only [contentsChunks, uintBytes_map]
      rfl
    | bool =>
      intro bs he hn
      subst xs
      rw [root_progressive_list_step]
      simp only [contentsChunks, boolBytes_map]
    | _ =>
      intro rs hc hn
      have he := roots_values_eq _ xs hs.2.1 rs hc
      subst rs
      rw [root_progressive_list_step]
      rfl
  case container.container fields xs =>
    intro rs hc hp
    have hs := (Ssz.rootable_iff _ _).mp h
    have he := roots_fields_eq _ hs.2.2 rs hc
    subst rs
    rw [root_fields_step]
  case progressiveContainer.container mask fields xs =>
    intro rs hc hm
    have hs := (Ssz.rootable_iff _ _).mp h
    have he := roots_fields_eq _ hs.2.2.2.2 rs hc
    subst rs
    rw [root_progressive_fields_step]
    simp only [sparseSlots_model]

end STFSpec.Codec
