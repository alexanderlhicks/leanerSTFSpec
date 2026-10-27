/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Independent SSZ root callers

Library `EthConformance`. Private public-law clients for the complete computational
root contract. The complete symbolic digests retain every byte and every ordered
SHA-256 preimage. No source execution, decoder, guest-validity, binding or host
resource bridge is asserted.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Conformance.Codec

open STFSpec.Codec

private theorem rootC0 (t : SszType) (v : SszValue)
    (h : Ssz.Rootable t v) :
  let R := Ssz.hashTreeRoot
  let result := R (t := t) (v := v) (h := h)
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
  exact Ssz.hashTreeRoot_eq (t := t) (v := v) (h := h)

private def RootLaw (R : (t : SszType) → (v : SszValue) →
    Ssz.Rootable t v → STFSpec.Base.Bytes32) : Prop :=
  ∀ t v h,
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
  | _, _ => False

private theorem actual_law : RootLaw Ssz.hashTreeRoot := rootC0

private abbrev Chunk := STFSpec.Base.Bytes32
private abbrev q (n : Nat) := (n + 31) / 32
private abbrev cap (n : Nat) := 2 ^ (if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1)
private abbrev Z : Chunk := STFSpec.Base.FixedBytes.ofNat 0
private abbrev L (n : Nat) : Chunk := STFSpec.Base.FixedBytes.ofLeNat n
private def D (a b : Chunk) : Chunk :=
  STFSpec.Hash.sha256 ((a.toBytes ++ b.toBytes).toByteArray)
private abbrev digits (w n : Nat) : List UInt8 :=
  (List.range w).map (fun i => UInt8.ofNat (n >>> (8 * i)))
private abbrev uintChunks (w : Nat) (ns : List Nat) : Array Chunk :=
  Ssz.pack (ns.flatMap (digits w)).toByteArray
private abbrev boolChunks (bs : List Bool) : Array Chunk :=
  Ssz.pack (bs.map (fun b => if b then (1 : UInt8) else 0)).toByteArray
private abbrev Kids (R : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Chunk)
    (ps : List (SszType × SszValue)) (rs : List Chunk) : Prop :=
  ps.length = rs.length ∧ ∀ p ∈ ps.zip rs,
    ∀ h : Ssz.Rootable p.1.1 p.1.2, R p.1.1 p.1.2 h = p.2
private abbrev slots (mask : List Bool) (rs : List Chunk) : Array Chunk :=
  ((List.range mask.length).map (fun i =>
    if mask.getD i false then rs.getD ((mask.take i).filter id).length Z else Z)).toArray
private def tree (d : Nat) (rs : List Chunk) : Chunk :=
  ((List.range d).foldl
    (fun layer _ => (List.range (layer.length / 2)).map (fun i =>
      D (layer.getD (2 * i) Z) (layer.getD (2 * i + 1) Z)))
    (rs ++ List.replicate (2 ^ d - rs.length) Z)).headD Z
private def progressive (rs : List Chunk) (d : Nat) : Chunk :=
  if rs = [] then Z else
    D (tree d (rs.take (2 ^ d))) (progressive (rs.drop (2 ^ d)) (d + 2))
termination_by rs.length
decreasing_by
  have hp := Nat.two_pow_pos d
  simp only [List.length_drop]
  have hn : rs.length > 0 := List.length_pos_iff.mpr (by assumption)
  omega

private theorem byte_length (b : ByteArray) : b.toList.length = b.size := by
  have hb := STFSpec.Base.Bytes.toByteArray_toList (STFSpec.Base.Bytes.ofByteArray b)
  rw [STFSpec.Base.Bytes.toByteArray_ofByteArray] at hb
  rw [hb, STFSpec.Base.Bytes.length_toList, STFSpec.Base.Bytes.size_ofByteArray]
private theorem bytes_roundtrip (xs : List UInt8) : xs.toByteArray.toList = xs := by
  have hb := STFSpec.Base.Bytes.toByteArray_toList (STFSpec.Base.Bytes.ofList xs)
  rw [STFSpec.Base.Bytes.toList_ofList] at hb
  exact hb
private theorem bytes_size (xs : List UInt8) : xs.toByteArray.size = xs.length := by
  rw [← byte_length, bytes_roundtrip]
private theorem pack_size (b : ByteArray) : (Ssz.pack b).size = q b.size := by
  have he := congrArg List.length (Ssz.pack_toBytes b)
  simpa only [List.length_map, Array.length_toList, List.length_range, q] using he
private theorem le_cap (n : Nat) : n ≤ cap n := by
  unfold cap
  split
  · omega
  · have hp := (Nat.lt_log2_self (n := n - 1))
    omega
private theorem packed_bound (b : ByteArray) (limit : Nat) (h : b.size ≤ limit) :
    (Ssz.pack b).size ≤ cap (q limit) := by
  rw [pack_size]
  exact Nat.le_trans (Nat.div_le_div_right (by omega : b.size + 31 ≤ limit + 31)) (le_cap _)
private theorem uint_size (w : Nat) (ns : List Nat) :
    (uintChunks w ns).size = q (ns.length * w) := by
  rw [uintChunks, pack_size, bytes_size]
  congr 1
  induction ns with
  | nil => simp
  | cons n ns ih => simp [List.flatMap_cons, digits, ih, Nat.add_mul, Nat.add_comm]
private theorem bool_size (bs : List Bool) : (boolChunks bs).size = q bs.length := by
  rw [boolChunks, pack_size, bytes_size, List.length_map]
private theorem tree_eq (rs : List Chunk) (limit : Nat) (h : rs.length ≤ cap limit) :
    Ssz.merkleize rs.toArray limit (by simpa only [List.size_toArray, cap] using h) =
      tree (if limit ≤ 1 then 0 else Nat.log2 (limit - 1) + 1) rs := by
  rw [Ssz.merkleize_eq]
  rfl
private theorem progressive_eq (rs : List Chunk) (d : Nat) :
    Ssz.merkleizeProgressive rs.toArray d = progressive rs d := by
  rw [Ssz.merkleizeProgressive_eq, progressive]
  simp only [List.isEmpty_toArray, List.isEmpty_iff]
  split
  · rfl
  · change D (tree d (rs.take (2 ^ d)))
      (Ssz.merkleizeProgressive (rs.drop (2 ^ d)).toArray (d + 2)) = _
    rw [progressive_eq]
termination_by rs.length
decreasing_by
  have hp := Nat.two_pow_pos d
  simp only [List.length_drop]
  have hn : rs.length > 0 := List.length_pos_iff.mpr (by assumption)
  omega
private theorem length_eq (r : Chunk) (n : Nat) (h : n < 2 ^ 256) :
    Ssz.mixInLength r n h = D r (L n) := Ssz.mixInLength_eq r n h
private theorem active_eq (r : Chunk) (mask : List Bool) (h : mask.length ≤ 256) :
    Ssz.mixInActiveFields r mask h =
      D r (L (mask.foldr (fun b n => (if b then 1 else 0) + 2 * n) 0)) :=
  Ssz.mixInActiveFields_eq r mask h

private theorem scalar (w n : Nat) (h : Ssz.Rootable (.uint w) (.uint n)) :
    Ssz.hashTreeRoot (.uint w) (.uint n) h = L n :=
  Ssz.hashTreeRoot_eq _ _ h
private theorem boolean (b : Bool) (h : Ssz.Rootable .bool (.bool b)) :
    Ssz.hashTreeRoot .bool (.bool b) h = L (if b then 1 else 0) :=
  Ssz.hashTreeRoot_eq _ _ h

/-! C1 / R00–R01: exact full scalar bytes, all supported widths and exclusions. -/
private theorem rootC1 :
    (∀ w ∈ [1, 2, 4, 8, 16, 32], ∀ n, n < 2 ^ (8 * w) →
      ∃ h : Ssz.Rootable (.uint w) (.uint n),
        (Ssz.hashTreeRoot (.uint w) (.uint n) h).toBytes.toList = digits 32 n) ∧
    (∀ b, ∃ h : Ssz.Rootable .bool (.bool b),
      Ssz.hashTreeRoot .bool (.bool b) h = L (if b then 1 else 0)) ∧
    (∀ w ∈ [0, 3, 33], ∀ n, ¬ Ssz.Rootable (.uint w) (.uint n)) ∧
    (∀ w, ¬ Ssz.Rootable (.uint w) (.uint (2 ^ (8 * w)))) ∧
    (¬ Ssz.Rootable .bool (.uint 0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw n hn
    have h := (Ssz.rootable_iff (.uint w) (.uint n)).mpr ⟨hw, hn⟩
    refine ⟨h, ?_⟩
    rw [scalar, L, STFSpec.Base.FixedBytes.toBytes_ofLeNat,
      STFSpec.Base.Bytes.toList_generate]
  · intro b
    have h := (Ssz.rootable_iff .bool (.bool b)).mpr trivial
    exact ⟨h, boolean b h⟩
  · intro w hw n h
    have hs := ((Ssz.rootable_iff _ _).mp h).1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw hs
    rcases hw with rfl | rfl | rfl <;> simp at hs
  · intro w h
    exact Nat.lt_irrefl _ ((Ssz.rootable_iff _ _).mp h).2
  · exact (Ssz.rootable_iff _ _).mp

private theorem scalar_endpoints (w : Nat) (hw : w ∈ [1, 2, 4, 8, 16, 32]) :
    (∃ h : Ssz.Rootable (.uint w) (.uint 0),
      Ssz.hashTreeRoot (.uint w) (.uint 0) h = L 0) ∧
    (∃ h : Ssz.Rootable (.uint w) (.uint (2 ^ (8 * w) - 1)),
      (Ssz.hashTreeRoot (.uint w) (.uint (2 ^ (8 * w) - 1)) h).toBytes.toList =
        digits 32 (2 ^ (8 * w) - 1)) := by
  have hp := Nat.two_pow_pos (8 * w)
  have hz := (Ssz.rootable_iff (.uint w) (.uint 0)).mpr ⟨hw, hp⟩
  exact ⟨⟨hz, scalar _ _ hz⟩, rootC1.1 w hw _ (by omega)⟩


private theorem vector_root (n : Nat) (b : ByteArray)
    (h : Ssz.Rootable (.byteVector n) (.bytes b)) :
    Ssz.hashTreeRoot (.byteVector n) (.bytes b) h =
      tree (if q n ≤ 1 then 0 else Nat.log2 (q n - 1) + 1) (Ssz.pack b).toList := by
  have hs := (Ssz.rootable_iff _ _).mp h
  have hp := packed_bound b n (Nat.le_of_eq hs)
  exact (Ssz.hashTreeRoot_eq _ _ h hp).trans
    (by simpa only [q] using tree_eq (Ssz.pack b).toList (q n) (by simpa using hp))
private theorem byte_root (limit : Nat) (b : ByteArray)
    (h : Ssz.Rootable (.byteList limit) (.bytes b)) :
    Ssz.hashTreeRoot (.byteList limit) (.bytes b) h =
      D (tree (if q limit ≤ 1 then 0 else Nat.log2 (q limit - 1) + 1)
        (Ssz.pack b).toList) (L b.size) := by
  have hs := (Ssz.rootable_iff _ _).mp h
  rw [Ssz.hashTreeRoot_eq _ _ h (packed_bound b limit hs.1) hs.2, length_eq]
  congr 1
  simpa only [q] using
    tree_eq (Ssz.pack b).toList (q limit) (by simpa using packed_bound b limit hs.1)
private def octets (n : Nat) : ByteArray := ((List.range n).map UInt8.ofNat).toByteArray
private theorem octets_size (n : Nat) : (octets n).size = n := by
  simp only [octets, bytes_size, List.length_map, List.length_range]

/-! C2 / R02–R05. The tree and complete ordered chunk-byte observations jointly
specify every SHA preimage. The vector equation never mixes the actual byte count. -/
private theorem rootC2 :
    (∀ n ∈ [0, 1, 31, 32, 33, 48, 96, 256],
      ∃ h : Ssz.Rootable (.byteVector n) (.bytes (octets n)),
        Ssz.hashTreeRoot (.byteVector n) (.bytes (octets n)) h =
          tree (if q n ≤ 1 then 0 else Nat.log2 (q n - 1) + 1)
            (Ssz.pack (octets n)).toList ∧
        (Ssz.pack (octets n)).size = q n ∧
        (Ssz.pack (octets n)).toList.map (fun r => r.toBytes.toList) =
          (List.range (q n)).map (fun i =>
            (((List.range n).map UInt8.ofNat).drop (32 * i)).take 32 ++
              List.replicate (32 - min 32 (n - 32 * i)) 0)) ∧
    (∀ limit ∈ [0, 1, 32, 33], ∀ h : Ssz.Rootable (.byteList limit) (.bytes ByteArray.empty),
      Ssz.hashTreeRoot (.byteList limit) (.bytes ByteArray.empty) h =
        D (tree (if q limit ≤ 1 then 0 else Nat.log2 (q limit - 1) + 1) []) (L 0)) := by
  constructor
  · intro n _
    have h := (Ssz.rootable_iff (.byteVector n) (.bytes (octets n))).mpr (octets_size n)
    refine ⟨h, vector_root _ _ h, ?_, ?_⟩
    · rw [pack_size, octets_size]
    · have hw := Ssz.pack_toBytes (octets n)
      rw [octets_size] at hw
      simpa only [octets, bytes_roundtrip, q] using hw
  · intro limit _ h
    rw [byte_root]
    have he : (Ssz.pack ByteArray.empty).toList = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [Array.length_toList, pack_size]
      rfl
    rw [he]
    rfl

private theorem pack_ordered_window (b : ByteArray) (i : Nat) :
    ((Ssz.pack b).toList.map (fun r => r.toBytes.toList)).getD i [] =
      if i < q b.size then
        (b.toList.drop (32 * i)).take 32 ++
          List.replicate (32 - min 32 (b.size - 32 * i)) 0
      else [] := by
  rw [Ssz.pack_toBytes]
  by_cases hi : i < q b.size
  · simp only [q] at hi ⊢
    simp [hi]
  · simp only [q] at hi ⊢
    simp [hi]

private theorem same_pack_distinct_byte_counts
    (h1 : Ssz.Rootable (.byteList 32) (.bytes ([165] : List UInt8).toByteArray))
    (h2 : Ssz.Rootable (.byteList 32) (.bytes ([165, 0] : List UInt8).toByteArray)) :
    (Ssz.pack ([165] : List UInt8).toByteArray).toList.map (fun r => r.toBytes.toList) =
      (Ssz.pack ([165, 0] : List UInt8).toByteArray).toList.map (fun r => r.toBytes.toList) ∧
    Ssz.hashTreeRoot (.byteList 32) (.bytes ([165] : List UInt8).toByteArray) h1 =
      D (tree 0 (Ssz.pack ([165] : List UInt8).toByteArray).toList) (L 1) ∧
    Ssz.hashTreeRoot (.byteList 32) (.bytes ([165, 0] : List UInt8).toByteArray) h2 =
      D (tree 0 (Ssz.pack ([165, 0] : List UInt8).toByteArray).toList) (L 2) := by
  refine ⟨?_, byte_root _ _ h1, byte_root _ _ h2⟩
  rw [Ssz.pack_toBytes, Ssz.pack_toBytes]
  simp only [bytes_size, bytes_roundtrip]
  decide


private theorem uint_list_root (w limit : Nat) (ns : List Nat)
    (h : Ssz.Rootable (.list (.uint w) limit) (.list (ns.map SszValue.uint))) :
    Ssz.hashTreeRoot (.list (.uint w) limit) (.list (ns.map SszValue.uint)) h =
      D (tree (if q (limit * w) ≤ 1 then 0 else Nat.log2 (q (limit * w) - 1) + 1)
        (uintChunks w ns).toList) (L ns.length) := by
  have hs := (Ssz.rootable_iff _ _).mp h
  have hp : (uintChunks w ns).size ≤ cap (q (limit * w)) := by
    rw [uint_size]
    apply Nat.le_trans _ (le_cap _)
    apply Nat.div_le_div_right
    have hh : ns.length ≤ limit := by simpa only [List.length_map] using hs.1
    exact Nat.add_le_add_right (Nat.mul_le_mul_right w hh) 31
  rw [Ssz.hashTreeRoot_eq _ _ h ns rfl hp hs.2.1, length_eq, List.length_map]
  congr 1
  simpa only [q, uintChunks, boolChunks, digits, Array.toArray_toList, List.length_map] using
    tree_eq (uintChunks w ns).toList (q (limit * w)) (by simpa using hp)
private theorem bool_list_root (limit : Nat) (bs : List Bool)
    (h : Ssz.Rootable (.list .bool limit) (.list (bs.map SszValue.bool))) :
    Ssz.hashTreeRoot (.list .bool limit) (.list (bs.map SszValue.bool)) h =
      D (tree (if q limit ≤ 1 then 0 else Nat.log2 (q limit - 1) + 1)
        (boolChunks bs).toList) (L bs.length) := by
  have hs := (Ssz.rootable_iff _ _).mp h
  have hp : (boolChunks bs).size ≤ cap (q limit) := by
    rw [bool_size]
    apply Nat.le_trans _ (le_cap _)
    apply Nat.div_le_div_right
    simpa only [List.length_map] using Nat.add_le_add_right hs.1 31
  rw [Ssz.hashTreeRoot_eq _ _ h bs rfl hp hs.2.1, length_eq, List.length_map]
  congr 1
  simpa only [q, uintChunks, boolChunks, digits, Array.toArray_toList, List.length_map] using
    tree_eq (boolChunks bs).toList (q limit) (by simpa using hp)

/-! C3 / R06–R07. Width eight is uint64. Basic list counts remain elements. -/
private theorem rootC3 :
    (∀ h : Ssz.Rootable (.list (.uint 8) 5)
        (.list ([1, 2, 3, 4, 5].map SszValue.uint)),
      Ssz.hashTreeRoot (.list (.uint 8) 5) (.list ([1, 2, 3, 4, 5].map SszValue.uint)) h =
        D (tree 1 (uintChunks 8 [1, 2, 3, 4, 5]).toList) (L 5)) ∧
    (uintChunks 8 [1, 2, 3, 4, 5]).size = 2 ∧
    (∀ h : Ssz.Rootable (.list .bool 33)
        (.list ((List.replicate 33 true).map SszValue.bool)),
      Ssz.hashTreeRoot (.list .bool 33)
        (.list ((List.replicate 33 true).map SszValue.bool)) h =
          D (tree 1 (boolChunks (List.replicate 33 true)).toList) (L 33)) ∧
    (boolChunks (List.replicate 33 true)).size = 2 ∧
    cap 0 = 1 ∧ cap 1 = 1 ∧ cap 3 = 4 := by
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · exact uint_list_root 8 5 [1, 2, 3, 4, 5]
  · rw [uint_size]
    rfl
  · exact bool_list_root 33 (List.replicate 33 true)
  · rw [bool_size]
    rfl

private def Composite : SszType → Prop
  | .uint _ | .bool => False
  | _ => True
private theorem composite_list_root (elem : SszType) (limit : Nat) (xs : List SszValue)
    (he : Composite elem) (h : Ssz.Rootable (.list elem limit) (.list xs))
    (rs : List Chunk) (hr : Kids Ssz.hashTreeRoot (xs.map (fun x => (elem, x))) rs) :
    Ssz.hashTreeRoot (.list elem limit) (.list xs) h =
      D (tree (if limit ≤ 1 then 0 else Nat.log2 (limit - 1) + 1) rs) (L xs.length) := by
  have hs := (Ssz.rootable_iff _ _).mp h
  have hp : rs.length ≤ cap limit := by
    have hl : xs.length = rs.length := by simpa only [List.length_map] using hr.1
    rw [← hl]
    exact Nat.le_trans hs.1 (le_cap limit)
  have hh : Ssz.hashTreeRoot (.list elem limit) (.list xs) h =
      Ssz.mixInLength
        (Ssz.merkleize rs.toArray limit
          (by simpa only [List.size_toArray, cap] using hp))
        xs.length hs.2.1 := by
    cases elem <;> first | exact False.elim he | exact Ssz.hashTreeRoot_eq _ _ h rs hr _ _
  rw [hh, length_eq, tree_eq _ _ hp]
private theorem composite_progressive_root (elem : SszType) (xs : List SszValue)
    (he : Composite elem) (h : Ssz.Rootable (.progressiveList elem) (.list xs))
    (rs : List Chunk) (hr : Kids Ssz.hashTreeRoot (xs.map (fun x => (elem, x))) rs) :
    Ssz.hashTreeRoot (.progressiveList elem) (.list xs) h =
      D (progressive rs 0) (L xs.length) := by
  have hs := (Ssz.rootable_iff _ _).mp h
  have hh : Ssz.hashTreeRoot (.progressiveList elem) (.list xs) h =
      Ssz.mixInLength (Ssz.merkleizeProgressive rs.toArray 0) xs.length hs.1 := by
    cases elem <;> first | exact False.elim he | exact Ssz.hashTreeRoot_eq _ _ h rs hr _
  rw [hh, length_eq, progressive_eq]

private theorem kids_available
    (R : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Chunk)
    (ps : List (SszType × SszValue)) (hs : ∀ p ∈ ps, Ssz.Rootable p.1 p.2) :
    ∃ rs, Kids R ps rs := by
  induction ps with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons p ps ih =>
    have hp := hs p (by simp)
    obtain ⟨rs, hr⟩ := ih (fun q hq => hs q (by simp [hq]))
    refine ⟨R p.1 p.2 hp :: rs, ?_, ?_⟩
    · simpa only [List.length_cons] using congrArg Nat.succ hr.1
    · intro q hq h
      simp only [List.zip_cons_cons, List.mem_cons] at hq
      rcases hq with rfl | hq
      · rfl
      · exact hr.2 q hq h

/-! C4 / R08–R10. Byte vectors are composite, retaining order and duplicates.
Empty actual composite payloads do not visit their malformed unused schemas. -/
private theorem rootC4 :
    (∀ n limit xs (h : Ssz.Rootable (.list (.byteVector n) limit) (.list xs)),
      ∃ rs, Kids Ssz.hashTreeRoot (xs.map (fun x => (.byteVector n, x))) rs ∧
        Ssz.hashTreeRoot (.list (.byteVector n) limit) (.list xs) h =
          D (tree (if limit ≤ 1 then 0 else Nat.log2 (limit - 1) + 1) rs) (L xs.length)) ∧
    (∃ h : Ssz.Rootable (.list (.container [.uint 3]) 0) (.list []),
      Ssz.hashTreeRoot (.list (.container [.uint 3]) 0) (.list []) h = D Z (L 0)) ∧
    (∃ h : Ssz.Rootable (.progressiveList (.container [])) (.list []),
      Ssz.hashTreeRoot (.progressiveList (.container [])) (.list []) h = D Z (L 0)) ∧
    ¬ Ssz.Rootable (.list (.uint 3) 0) (.list []) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n limit xs h
    have hs := (Ssz.rootable_iff _ _).mp h
    obtain ⟨rs, hr⟩ := kids_available Ssz.hashTreeRoot (xs.map (fun x => (.byteVector n, x)))
      (by intro p hp; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp; exact hs.2.2.1 x hx)
    exact ⟨rs, hr, composite_list_root (.byteVector n) limit xs trivial h rs hr⟩
  · have h : Ssz.Rootable (.list (.container [.uint 3]) 0) (.list []) := by
      apply (Ssz.rootable_iff _ _).mpr
      simp
    exact ⟨h, composite_list_root (.container [.uint 3]) 0 [] trivial h [] ⟨rfl, by simp⟩⟩
  · have h : Ssz.Rootable (.progressiveList (.container [])) (.list []) := by
      apply (Ssz.rootable_iff _ _).mpr
      simp
    refine ⟨h, ?_⟩
    rw [composite_progressive_root (.container []) [] trivial h [] ⟨rfl, by simp⟩]
    rw [progressive]
    rfl
  · rw [Ssz.rootable_iff]
    simp


private theorem progressive_bytes_root (b : ByteArray)
    (h : Ssz.Rootable .progressiveByteList (.bytes b)) :
    Ssz.hashTreeRoot .progressiveByteList (.bytes b) h =
      D (progressive (Ssz.pack b).toList 0) (L b.size) := by
  rw [Ssz.hashTreeRoot_eq _ _ h ((Ssz.rootable_iff _ _).mp h), length_eq]
  congr 1
  simpa using progressive_eq (Ssz.pack b).toList 0
private theorem progressive_uint_root (w : Nat) (ns : List Nat)
    (h : Ssz.Rootable (.progressiveList (.uint w)) (.list (ns.map SszValue.uint))) :
    Ssz.hashTreeRoot (.progressiveList (.uint w)) (.list (ns.map SszValue.uint)) h =
      D (progressive (uintChunks w ns).toList 0) (L ns.length) := by
  have hs := (Ssz.rootable_iff _ _).mp h
  rw [Ssz.hashTreeRoot_eq _ _ h ns rfl hs.1, length_eq, List.length_map]
  congr 1
  simpa only [uintChunks, digits, Array.toArray_toList] using
    progressive_eq (uintChunks w ns).toList 0

/-! C5 / R11–R12. All segment boundaries are in chunks, mixed lengths in elements
or bytes. The private tree fold specifies every ordered pair and zero padding. -/
private theorem rootC5 :
    (∀ b (h : Ssz.Rootable .progressiveByteList (.bytes b)),
      Ssz.hashTreeRoot .progressiveByteList (.bytes b) h =
        D (progressive (Ssz.pack b).toList 0) (L b.size)) ∧
    (∀ h : Ssz.Rootable (.progressiveList (.uint 8))
        (.list ([1, 2, 3, 4, 5].map SszValue.uint)),
      Ssz.hashTreeRoot (.progressiveList (.uint 8))
        (.list ([1, 2, 3, 4, 5].map SszValue.uint)) h =
          D (progressive (uintChunks 8 [1, 2, 3, 4, 5]).toList 0) (L 5)) ∧
    (∀ rs : List Chunk, rs.length ∈ [0, 1, 5, 6, 21, 22] →
      Ssz.merkleizeProgressive rs.toArray 0 =
        if rs = [] then Z else
          D (tree 0 (rs.take 1))
            (if rs.drop 1 = [] then Z else
              D (tree 2 ((rs.drop 1).take 4))
                (if rs.drop 5 = [] then Z else
                  D (tree 4 ((rs.drop 5).take 16))
                    (if rs.drop 21 = [] then Z else
                      D (tree 6 ((rs.drop 21).take 64)) Z)))) ∧
    (progressive [] 0 = Z) ∧
    (∀ a, progressive [a] 0 = D a Z) := by
  refine ⟨progressive_bytes_root, progressive_uint_root 8 [1, 2, 3, 4, 5], ?_, ?_, ?_⟩
  · intro rs hn
    rw [progressive_eq, progressive]
    split
    · rfl
    · rw [progressive]
      simp only [Nat.pow_zero, List.drop_drop, Nat.reduceAdd, Nat.reducePow]
      split
      · rfl
      · rw [progressive]
        simp only [List.drop_drop, Nat.reduceAdd, Nat.reducePow]
        split
        · rfl
        · rw [progressive]
          simp only [List.drop_drop, Nat.reduceAdd, Nat.reducePow]
          split
          · rfl
          · rw [progressive]
            have hl : rs.length ≤ 22 := by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
              omega
            have he : rs.drop 85 = [] := List.drop_eq_nil_iff.mpr (by omega)
            simp only [Nat.reduceAdd, Nat.reducePow, he, ite_true]
  · rw [progressive]
    rfl
  · intro a
    simp [progressive, tree]

private theorem container_root (fields : List SszType) (xs : List SszValue)
    (h : Ssz.Rootable (.container fields) (.container xs))
    (rs : List Chunk) (hr : Kids Ssz.hashTreeRoot (fields.zip xs) rs) :
    Ssz.hashTreeRoot (.container fields) (.container xs) h =
      tree (if fields.length ≤ 1 then 0 else Nat.log2 (fields.length - 1) + 1) rs := by
  have hs := (Ssz.rootable_iff _ _).mp h
  have hp : rs.length ≤ cap fields.length := by
    have hl : fields.length = rs.length := by
      have hh := hr.1
      rw [List.length_zip, hs.2.1, Nat.min_self] at hh
      exact hs.2.1.trans hh
    rw [← hl]
    exact le_cap _
  exact (Ssz.hashTreeRoot_eq _ _ h rs hr (by simpa only [List.size_toArray, cap] using hp)).trans
    (tree_eq rs fields.length hp)

/-! C6 / R13. Exact positional arity precedes zip; no count mix-in. -/
private theorem rootC6 :
    (∀ fields xs (h : Ssz.Rootable (.container fields) (.container xs)),
      fields ≠ [] ∧ fields.length = xs.length ∧
      ∃ rs, Kids Ssz.hashTreeRoot (fields.zip xs) rs ∧
        Ssz.hashTreeRoot (.container fields) (.container xs) h =
          tree (if fields.length ≤ 1 then 0 else Nat.log2 (fields.length - 1) + 1) rs) ∧
    (¬ Ssz.Rootable (.container []) (.container [])) ∧
    (∀ fields xs, fields.length ≠ xs.length →
      ¬ Ssz.Rootable (.container fields) (.container xs)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro fields xs h
    have hs := (Ssz.rootable_iff _ _).mp h
    obtain ⟨rs, hr⟩ := kids_available Ssz.hashTreeRoot (fields.zip xs) hs.2.2
    exact ⟨hs.1, hs.2.1, rs, hr, container_root fields xs h rs hr⟩
  · rw [Ssz.rootable_iff]
    simp
  · intro fields xs hn h
    exact hn ((Ssz.rootable_iff _ _).mp h).2.1


private theorem progressive_fields_root (mask : List Bool) (fields : List SszType)
    (xs : List SszValue) (h : Ssz.Rootable (.progressiveContainer mask fields) (.container xs))
    (rs : List Chunk) (hr : Kids Ssz.hashTreeRoot (fields.zip xs) rs) :
    Ssz.hashTreeRoot (.progressiveContainer mask fields) (.container xs) h =
      D (progressive (slots mask rs).toList 0)
        (L (mask.foldr (fun b n => (if b then 1 else 0) + 2 * n) 0)) := by
  have hs := (Ssz.rootable_iff _ _).mp h
  rw [Ssz.hashTreeRoot_eq _ _ h rs hr hs.2.1, active_eq]
  congr 1
  simpa only [slots, Z, Array.toArray_toList] using progressive_eq (slots mask rs).toList 0
private theorem slot_size (mask : List Bool) (rs : List Chunk) :
    (slots mask rs).size = mask.length := by
  simp only [slots, List.size_toArray, List.length_map, List.length_range]
private theorem true_rank (mask : List Bool) (i : Nat) (h : mask.getD i false = true) :
    ((mask.take i).filter id).length < (mask.filter id).length := by
  induction mask generalizing i with
  | nil => simp at h
  | cons b mask ih =>
    cases i with
    | zero =>
      simp at h
      subst b
      simp
    | succ i =>
      simp only [List.getD_cons_succ] at h
      have hh := ih i h
      cases b <;> simpa using hh

/-! C7 / R14–R16. Contents scan the finite mask, and full mask bits are mixed
separately. Width 256 has an additional source-class `more` naming obligation. -/
private theorem rootC7 :
    (∀ mask fields xs (h : Ssz.Rootable (.progressiveContainer mask fields) (.container xs)),
      ∃ rs, Kids Ssz.hashTreeRoot (fields.zip xs) rs ∧
        (slots mask rs).size = mask.length ∧
        (∀ i, mask.getD i false = true → ((mask.take i).filter id).length < rs.length) ∧
        Ssz.hashTreeRoot (.progressiveContainer mask fields) (.container xs) h =
          D (progressive (slots mask rs).toList 0)
            (L (mask.foldr (fun b n => (if b then 1 else 0) + 2 * n) 0))) ∧
    (∀ a b, slots [true, false, true] [a, b] = #[a, Z, b] ∧
      slots [false, true] [a] = #[Z, a] ∧ slots [true, true, true] [a, b, a] = #[a, b, a]) ∧
    (∀ mask fields xs, 256 < mask.length →
      ¬ Ssz.Rootable (.progressiveContainer mask fields) (.container xs)) ∧
    (∀ mask fields xs, mask.getLast? ≠ some true →
      ¬ Ssz.Rootable (.progressiveContainer mask fields) (.container xs)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro mask fields xs h
    have hs := (Ssz.rootable_iff _ _).mp h
    obtain ⟨rs, hr⟩ := kids_available Ssz.hashTreeRoot (fields.zip xs) hs.2.2.2.2
    refine ⟨rs, hr, slot_size _ _, ?_, progressive_fields_root mask fields xs h rs hr⟩
    intro i hi
    have hl : fields.length = rs.length := by
      have hh := hr.1
      rw [List.length_zip, hs.2.2.2.1, Nat.min_self] at hh
      exact hs.2.2.2.1.trans hh
    rw [← hl, ← hs.2.2.1]
    exact true_rank mask i hi
  · intro a b
    exact ⟨rfl, rfl, rfl⟩
  · intro mask fields xs hn h
    have hh := ((Ssz.rootable_iff _ _).mp h).2.1
    omega
  · intro mask fields xs hn h
    exact hn ((Ssz.rootable_iff _ _).mp h).1

private theorem mask_edge_witness (w : Nat) (hw : w ∈ [255, 256]) :
    ∃ _h : Ssz.Rootable
      (.progressiveContainer (List.replicate (w - 1) false ++ [true]) [.bool])
      (.container [.bool true]),
      (List.replicate (w - 1) false ++ [true]).length = w ∧
      (slots (List.replicate (w - 1) false ++ [true]) [L 1]).size = w := by
  have hb : Ssz.Rootable .bool (.bool true) := (Ssz.rootable_iff _ _).mpr trivial
  have hp : 0 < w ∧ w ≤ 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    omega
  have hl : (List.replicate (w - 1) false ++ [true]).length = w := by simp; omega
  have h : Ssz.Rootable
      (.progressiveContainer (List.replicate (w - 1) false ++ [true]) [.bool])
      (.container [.bool true]) := by
    apply (Ssz.rootable_iff _ _).mpr
    simp [hl, hp.2, hb]
  exact ⟨h, hl, (slot_size _ _).trans hl⟩


private theorem uint_values (w : Nat) (xs : List SszValue)
    (hs : ∀ x ∈ xs, Ssz.Rootable (.uint w) x) :
    ∃ ns : List Nat, xs = ns.map SszValue.uint := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    have hx := (Ssz.rootable_iff _ _).mp (hs x (by simp))
    obtain ⟨ns, rfl⟩ := ih (fun x hx => hs x (by simp [hx]))
    cases x with
    | uint n => exact ⟨n :: ns, rfl⟩
    | _ => exact False.elim hx
private theorem bool_values (xs : List SszValue)
    (hs : ∀ x ∈ xs, Ssz.Rootable .bool x) :
    ∃ bs : List Bool, xs = bs.map SszValue.bool := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    have hx := (Ssz.rootable_iff _ _).mp (hs x (by simp))
    obtain ⟨bs, rfl⟩ := ih (fun x hx => hs x (by simp [hx]))
    cases x with
    | bool b => exact ⟨b :: bs, rfl⟩
    | _ => exact False.elim hx
private theorem kids_transport
    (R G : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Chunk)
    (ps : List (SszType × SszValue)) (rs : List Chunk)
    (he : ∀ p ∈ ps, ∀ h : Ssz.Rootable p.1 p.2, R p.1 p.2 h = G p.1 p.2 h)
    (hr : Kids R ps rs) : Kids G ps rs := by
  refine ⟨hr.1, ?_⟩
  intro p hp h
  exact (he p.1 ((List.of_mem_zip hp).1) h).symm.trans (hr.2 p hp h)
private theorem zip_value_mem {fields : List SszType} {xs : List SszValue}
    {p : SszType × SszValue} (hp : p ∈ fields.zip xs) : p.2 ∈ xs :=
  (List.of_mem_zip hp).2

/-! C8 determination is a theorem about any two abstract functions satisfying the
entire recursive contract. Actual proper-child induction discharges every child
certificate; it does not assume that the two functions already agree. -/
private theorem root_law_unique
    (R G : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Chunk)
    (hr : RootLaw R) (hg : RootLaw G) (v : SszValue) :
    ∀ t h, R t v h = G t v h := by
  induction v using SszValue.rec
    (motive_2 := fun xs => ∀ x ∈ xs, ∀ t h, R t x h = G t x h) with
  | uint n =>
    intro t h
    have hs := (Ssz.rootable_iff _ _).mp h
    cases t <;> first
      | exact False.elim hs
      | exact (hr _ _ h).trans (hg _ _ h).symm
  | bool b =>
    intro t h
    have hs := (Ssz.rootable_iff _ _).mp h
    cases t <;> first
      | exact False.elim hs
      | exact (hr _ _ h).trans (hg _ _ h).symm
  | bytes b =>
    intro t h
    have hs := (Ssz.rootable_iff _ _).mp h
    cases t with
    | byteVector n =>
      have hp := packed_bound b n (Nat.le_of_eq hs)
      exact (hr _ _ h hp).trans (hg _ _ h hp).symm
    | byteList limit =>
      have hp := packed_bound b limit hs.1
      exact (hr _ _ h hp hs.2).trans (hg _ _ h hp hs.2).symm
    | progressiveByteList => exact (hr _ _ h hs).trans (hg _ _ h hs).symm
    | _ => exact False.elim hs
  | list xs ih =>
    intro t h
    have hs := (Ssz.rootable_iff _ _).mp h
    cases t with
    | list elem limit =>
      cases elem with
      | uint w =>
        obtain ⟨ns, rfl⟩ := uint_values w xs hs.2.2.1
        have hp : (uintChunks w ns).size ≤ cap (q (limit * w)) := by
          rw [uint_size]
          apply Nat.le_trans _ (le_cap _)
          apply Nat.div_le_div_right
          have hh : ns.length ≤ limit := by simpa only [List.length_map] using hs.1
          exact Nat.add_le_add_right (Nat.mul_le_mul_right w hh) 31
        exact (hr _ _ h ns rfl hp hs.2.1).trans (hg _ _ h ns rfl hp hs.2.1).symm
      | bool =>
        obtain ⟨bs, rfl⟩ := bool_values xs hs.2.2.1
        have hp : (boolChunks bs).size ≤ cap (q limit) := by
          rw [bool_size]
          apply Nat.le_trans _ (le_cap _)
          apply Nat.div_le_div_right
          simpa only [List.length_map] using Nat.add_le_add_right hs.1 31
        exact (hr _ _ h bs rfl hp hs.2.1).trans (hg _ _ h bs rfl hp hs.2.1).symm
      | byteVector n =>
        obtain ⟨rs, hk⟩ := kids_available R (xs.map (fun x => ((.byteVector n), x)))
          (by intro p hp; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp; exact hs.2.2.1 x hx)
        have he : ∀ p ∈ xs.map (fun x => ((.byteVector n), x)), ∀ h, R p.1 p.2 h = G p.1 p.2 h
            := by
          intro p hp hx
          obtain ⟨x, hmem, rfl⟩ := List.mem_map.mp hp
          exact ih x hmem _ _
        have hh := kids_transport R G _ rs he hk
        have hp : rs.toArray.size ≤ cap limit := by
          have hl : xs.length = rs.length := by simpa only [List.length_map] using hk.1
          simp only [List.size_toArray]
          rw [← hl]
          exact Nat.le_trans hs.1 (le_cap _)
        exact (hr _ _ h rs hk hp hs.2.1).trans (hg _ _ h rs hh hp hs.2.1).symm
      | byteList l =>
        obtain ⟨rs, hk⟩ := kids_available R (xs.map (fun x => ((.byteList l), x)))
          (by intro p hp; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp; exact hs.2.2.1 x hx)
        have he : ∀ p ∈ xs.map (fun x => ((.byteList l), x)), ∀ h, R p.1 p.2 h = G p.1 p.2 h := by
          intro p hp hx
          obtain ⟨x, hmem, rfl⟩ := List.mem_map.mp hp
          exact ih x hmem _ _
        have hh := kids_transport R G _ rs he hk
        have hp : rs.toArray.size ≤ cap limit := by
          have hl : xs.length = rs.length := by simpa only [List.length_map] using hk.1
          simp only [List.size_toArray]
          rw [← hl]
          exact Nat.le_trans hs.1 (le_cap _)
        exact (hr _ _ h rs hk hp hs.2.1).trans (hg _ _ h rs hh hp hs.2.1).symm
      | list e l =>
        obtain ⟨rs, hk⟩ := kids_available R (xs.map (fun x => ((.list e l), x)))
          (by intro p hp; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp; exact hs.2.2.1 x hx)
        have he : ∀ p ∈ xs.map (fun x => ((.list e l), x)), ∀ h, R p.1 p.2 h = G p.1 p.2 h := by
          intro p hp hx
          obtain ⟨x, hmem, rfl⟩ := List.mem_map.mp hp
          exact ih x hmem _ _
        have hh := kids_transport R G _ rs he hk
        have hp : rs.toArray.size ≤ cap limit := by
          have hl : xs.length = rs.length := by simpa only [List.length_map] using hk.1
          simp only [List.size_toArray]
          rw [← hl]
          exact Nat.le_trans hs.1 (le_cap _)
        exact (hr _ _ h rs hk hp hs.2.1).trans (hg _ _ h rs hh hp hs.2.1).symm
      | progressiveList e =>
        obtain ⟨rs, hk⟩ := kids_available R (xs.map (fun x => ((.progressiveList e), x)))
          (by intro p hp; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp; exact hs.2.2.1 x hx)
        have he : ∀ p ∈ xs.map (fun x => ((.progressiveList e), x)), ∀ h, R p.1 p.2 h = G p.1
            p.2 h := by
          intro p hp hx
          obtain ⟨x, hmem, rfl⟩ := List.mem_map.mp hp
          exact ih x hmem _ _
        have hh := kids_transport R G _ rs he hk
        have hp : rs.toArray.size ≤ cap limit := by
          have hl : xs.length = rs.length := by simpa only [List.length_map] using hk.1
          simp only [List.size_toArray]
          rw [← hl]
          exact Nat.le_trans hs.1 (le_cap _)
        exact (hr _ _ h rs hk hp hs.2.1).trans (hg _ _ h rs hh hp hs.2.1).symm
      | progressiveByteList =>
        obtain ⟨rs, hk⟩ := kids_available R (xs.map (fun x => ((.progressiveByteList), x)))
          (by intro p hp; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp; exact hs.2.2.1 x hx)
        have he : ∀ p ∈ xs.map (fun x => ((.progressiveByteList), x)), ∀ h, R p.1 p.2 h = G p.1
            p.2 h := by
          intro p hp hx
          obtain ⟨x, hmem, rfl⟩ := List.mem_map.mp hp
          exact ih x hmem _ _
        have hh := kids_transport R G _ rs he hk
        have hp : rs.toArray.size ≤ cap limit := by
          have hl : xs.length = rs.length := by simpa only [List.length_map] using hk.1
          simp only [List.size_toArray]
          rw [← hl]
          exact Nat.le_trans hs.1 (le_cap _)
        exact (hr _ _ h rs hk hp hs.2.1).trans (hg _ _ h rs hh hp hs.2.1).symm
      | container fs =>
        obtain ⟨rs, hk⟩ := kids_available R (xs.map (fun x => ((.container fs), x)))
          (by intro p hp; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp; exact hs.2.2.1 x hx)
        have he : ∀ p ∈ xs.map (fun x => ((.container fs), x)), ∀ h, R p.1 p.2 h = G p.1 p.2 h
            := by
          intro p hp hx
          obtain ⟨x, hmem, rfl⟩ := List.mem_map.mp hp
          exact ih x hmem _ _
        have hh := kids_transport R G _ rs he hk
        have hp : rs.toArray.size ≤ cap limit := by
          have hl : xs.length = rs.length := by simpa only [List.length_map] using hk.1
          simp only [List.size_toArray]
          rw [← hl]
          exact Nat.le_trans hs.1 (le_cap _)
        exact (hr _ _ h rs hk hp hs.2.1).trans (hg _ _ h rs hh hp hs.2.1).symm
      | progressiveContainer m fs =>
        obtain ⟨rs, hk⟩ := kids_available R (xs.map (fun x => ((.progressiveContainer m fs), x)))
          (by intro p hp; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp; exact hs.2.2.1 x hx)
        have he : ∀ p ∈ xs.map (fun x => ((.progressiveContainer m fs), x)), ∀ h, R p.1 p.2 h =
            G p.1 p.2 h := by
          intro p hp hx
          obtain ⟨x, hmem, rfl⟩ := List.mem_map.mp hp
          exact ih x hmem _ _
        have hh := kids_transport R G _ rs he hk
        have hp : rs.toArray.size ≤ cap limit := by
          have hl : xs.length = rs.length := by simpa only [List.length_map] using hk.1
          simp only [List.size_toArray]
          rw [← hl]
          exact Nat.le_trans hs.1 (le_cap _)
        exact (hr _ _ h rs hk hp hs.2.1).trans (hg _ _ h rs hh hp hs.2.1).symm
    | progressiveList elem =>
      cases elem with
      | uint w =>
        obtain ⟨ns, rfl⟩ := uint_values w xs hs.2.1
        exact (hr _ _ h ns rfl hs.1).trans (hg _ _ h ns rfl hs.1).symm
      | bool =>
        obtain ⟨bs, rfl⟩ := bool_values xs hs.2.1
        exact (hr _ _ h bs rfl hs.1).trans (hg _ _ h bs rfl hs.1).symm
      | byteVector n =>
        obtain ⟨rs, hk⟩ := kids_available R (xs.map (fun x => ((.byteVector n), x)))
          (by intro p hp; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp; exact hs.2.1 x hx)
        have he : ∀ p ∈ xs.map (fun x => ((.byteVector n), x)), ∀ h, R p.1 p.2 h = G p.1 p.2 h
            := by
          intro p hp hx
          obtain ⟨x, hmem, rfl⟩ := List.mem_map.mp hp
          exact ih x hmem _ _
        have hh := kids_transport R G _ rs he hk
        exact (hr _ _ h rs hk hs.1).trans (hg _ _ h rs hh hs.1).symm
      | byteList l =>
        obtain ⟨rs, hk⟩ := kids_available R (xs.map (fun x => ((.byteList l), x)))
          (by intro p hp; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp; exact hs.2.1 x hx)
        have he : ∀ p ∈ xs.map (fun x => ((.byteList l), x)), ∀ h, R p.1 p.2 h = G p.1 p.2 h := by
          intro p hp hx
          obtain ⟨x, hmem, rfl⟩ := List.mem_map.mp hp
          exact ih x hmem _ _
        have hh := kids_transport R G _ rs he hk
        exact (hr _ _ h rs hk hs.1).trans (hg _ _ h rs hh hs.1).symm
      | list e l =>
        obtain ⟨rs, hk⟩ := kids_available R (xs.map (fun x => ((.list e l), x)))
          (by intro p hp; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp; exact hs.2.1 x hx)
        have he : ∀ p ∈ xs.map (fun x => ((.list e l), x)), ∀ h, R p.1 p.2 h = G p.1 p.2 h := by
          intro p hp hx
          obtain ⟨x, hmem, rfl⟩ := List.mem_map.mp hp
          exact ih x hmem _ _
        have hh := kids_transport R G _ rs he hk
        exact (hr _ _ h rs hk hs.1).trans (hg _ _ h rs hh hs.1).symm
      | progressiveList e =>
        obtain ⟨rs, hk⟩ := kids_available R (xs.map (fun x => ((.progressiveList e), x)))
          (by intro p hp; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp; exact hs.2.1 x hx)
        have he : ∀ p ∈ xs.map (fun x => ((.progressiveList e), x)), ∀ h, R p.1 p.2 h = G p.1
            p.2 h := by
          intro p hp hx
          obtain ⟨x, hmem, rfl⟩ := List.mem_map.mp hp
          exact ih x hmem _ _
        have hh := kids_transport R G _ rs he hk
        exact (hr _ _ h rs hk hs.1).trans (hg _ _ h rs hh hs.1).symm
      | progressiveByteList =>
        obtain ⟨rs, hk⟩ := kids_available R (xs.map (fun x => ((.progressiveByteList), x)))
          (by intro p hp; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp; exact hs.2.1 x hx)
        have he : ∀ p ∈ xs.map (fun x => ((.progressiveByteList), x)), ∀ h, R p.1 p.2 h = G p.1
            p.2 h := by
          intro p hp hx
          obtain ⟨x, hmem, rfl⟩ := List.mem_map.mp hp
          exact ih x hmem _ _
        have hh := kids_transport R G _ rs he hk
        exact (hr _ _ h rs hk hs.1).trans (hg _ _ h rs hh hs.1).symm
      | container fs =>
        obtain ⟨rs, hk⟩ := kids_available R (xs.map (fun x => ((.container fs), x)))
          (by intro p hp; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp; exact hs.2.1 x hx)
        have he : ∀ p ∈ xs.map (fun x => ((.container fs), x)), ∀ h, R p.1 p.2 h = G p.1 p.2 h
            := by
          intro p hp hx
          obtain ⟨x, hmem, rfl⟩ := List.mem_map.mp hp
          exact ih x hmem _ _
        have hh := kids_transport R G _ rs he hk
        exact (hr _ _ h rs hk hs.1).trans (hg _ _ h rs hh hs.1).symm
      | progressiveContainer m fs =>
        obtain ⟨rs, hk⟩ := kids_available R (xs.map (fun x => ((.progressiveContainer m fs), x)))
          (by intro p hp; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp; exact hs.2.1 x hx)
        have he : ∀ p ∈ xs.map (fun x => ((.progressiveContainer m fs), x)), ∀ h, R p.1 p.2 h =
            G p.1 p.2 h := by
          intro p hp hx
          obtain ⟨x, hmem, rfl⟩ := List.mem_map.mp hp
          exact ih x hmem _ _
        have hh := kids_transport R G _ rs he hk
        exact (hr _ _ h rs hk hs.1).trans (hg _ _ h rs hh hs.1).symm
    | _ => exact False.elim hs
  | container xs ih =>
    intro t h
    have hs := (Ssz.rootable_iff _ _).mp h
    cases t with
    | container fields =>
      obtain ⟨rs, hk⟩ := kids_available R (fields.zip xs) hs.2.2
      have he : ∀ p ∈ fields.zip xs, ∀ h, R p.1 p.2 h = G p.1 p.2 h := by
        intro p hp hx
        exact ih p.2 (zip_value_mem hp) _ hx
      have hh := kids_transport R G _ rs he hk
      have hp : rs.toArray.size ≤ cap fields.length := by
        have hl := hk.1
        rw [List.length_zip, hs.2.1, Nat.min_self] at hl
        simp only [List.size_toArray]
        rw [← hl, ← hs.2.1]
        exact le_cap _
      exact (hr _ _ h rs hk hp).trans (hg _ _ h rs hh hp).symm
    | progressiveContainer mask fields =>
      obtain ⟨rs, hk⟩ := kids_available R (fields.zip xs) hs.2.2.2.2
      have he : ∀ p ∈ fields.zip xs, ∀ h, R p.1 p.2 h = G p.1 p.2 h := by
        intro p hp hx
        exact ih p.2 (zip_value_mem hp) _ hx
      have hh := kids_transport R G _ rs he hk
      exact (hr _ _ h rs hk hs.2.1).trans (hg _ _ h rs hh hs.2.1).symm
    | _ => exact False.elim hs
  | nil =>
    rename_i y hy t hh
    exact False.elim (List.not_mem_nil hy)
  | cons x xs hx hxs =>
    rename_i y hy t hh
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx t hh
    · exact hxs y hy t hh

private theorem rootC8 :
    (∀ t v (h h' : Ssz.Rootable t v),
      Ssz.hashTreeRoot t v h = Ssz.hashTreeRoot t v h') ∧
    (∀ R, RootLaw R → ∀ t v h, R t v h = Ssz.hashTreeRoot t v h) ∧
    (∀ ps, (∀ p ∈ ps, Ssz.Rootable p.1 p.2) →
      ∃ rs, Kids Ssz.hashTreeRoot ps rs) := by
  refine ⟨?_, ?_, kids_available Ssz.hashTreeRoot⟩
  · intro t v h h'
    rfl
  · intro R hR t v h
    exact root_law_unique R Ssz.hashTreeRoot hR actual_law v t h


/-! C9 / R18. Conditional nameless source interpretation of the actual Amsterdam
field order. These local recipes assert no decoder, Python class, guest, security
or resource bridge. Rooting remains separate from later execution validity.
EELS at the pin: `src/ethereum/forks/amsterdam/execution_engine/types.py:39–96`,
`src/ethereum/forks/amsterdam/execution_engine/requests.py:41–126`,
`src/ethereum/forks/amsterdam/blocks.py:38–63`.
Widths below are bytes; timestamp remains uint64. -/
private abbrev withdrawalFields : List SszType := [.uint 8, .uint 8, .byteVector 20, .uint 8]
private abbrev depositFields : List SszType :=
  [.byteVector 48, .byteVector 32, .uint 8, .byteVector 96, .uint 8]
private abbrev withdrawalRequestFields : List SszType := [.byteVector 20, .byteVector 48, .uint 8]
private abbrev consolidationFields : List SszType := [.byteVector 20, .byteVector 48,
    .byteVector 48]
private abbrev builderDepositFields : List SszType :=
  [.byteVector 48, .byteVector 32, .uint 8, .byteVector 96]
private abbrev builderExitFields : List SszType := [.byteVector 20, .byteVector 48]
private abbrev requestsFields : List SszType :=
  [.progressiveList (.container depositFields),
   .progressiveList (.container withdrawalRequestFields),
   .progressiveList (.container consolidationFields),
   .progressiveList (.container builderDepositFields),
   .progressiveList (.container builderExitFields)]
private abbrev payloadFields : List SszType :=
  [.byteVector 32, .byteVector 20, .byteVector 32, .byteVector 32,
   .byteVector 256, .byteVector 32, .uint 8, .uint 8, .uint 8, .uint 8,
   .byteList 32, .uint 32, .byteVector 32,
   .progressiveList .progressiveByteList, .progressiveList (.container withdrawalFields),
   .uint 8, .uint 8, .progressiveByteList, .uint 8]
private abbrev requestFields : List SszType :=
  [.progressiveContainer (List.replicate 19 true) payloadFields,
   .progressiveList (.byteVector 32), .byteVector 32,
   .progressiveContainer (List.replicate 5 true) requestsFields]

private theorem rootC9 :
    ([requestFields.length, payloadFields.length, requestsFields.length,
      withdrawalFields.length, depositFields.length, withdrawalRequestFields.length,
      consolidationFields.length, builderDepositFields.length, builderExitFields.length] =
      [4, 19, 5, 4, 5, 3, 3, 4, 2]) ∧
    (∀ fields ∈ [requestFields, withdrawalFields, depositFields, withdrawalRequestFields,
        consolidationFields, builderDepositFields, builderExitFields],
      ∀ xs (h : Ssz.Rootable (.container fields) (.container xs)),
        ∃ rs, Kids Ssz.hashTreeRoot (fields.zip xs) rs ∧
          Ssz.hashTreeRoot (.container fields) (.container xs) h =
            tree (if fields.length ≤ 1 then 0 else Nat.log2 (fields.length - 1) + 1) rs) ∧
    (∀ fields ∈ [payloadFields, requestsFields],
      ∀ xs (h : Ssz.Rootable (.progressiveContainer
          (List.replicate fields.length true) fields) (.container xs)),
        ∃ rs, Kids Ssz.hashTreeRoot (fields.zip xs) rs ∧
          Ssz.hashTreeRoot (.progressiveContainer (List.replicate fields.length true) fields)
            (.container xs) h =
              D (progressive (slots (List.replicate fields.length true) rs).toList 0)
                (L ((List.replicate fields.length true).foldr
                  (fun b n => (if b then 1 else 0) + 2 * n) 0))) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro fields _ xs h
    have hs := (Ssz.rootable_iff _ _).mp h
    obtain ⟨rs, hk⟩ := kids_available Ssz.hashTreeRoot (fields.zip xs) hs.2.2
    exact ⟨rs, hk, container_root fields xs h rs hk⟩
  · intro fields _ xs h
    have hs := (Ssz.rootable_iff _ _).mp h
    obtain ⟨rs, hk⟩ := kids_available Ssz.hashTreeRoot (fields.zip xs) hs.2.2.2.2
    exact ⟨rs, hk, progressive_fields_root _ fields xs h rs hk⟩


/-! Complete finite byte and tree instantiations of the preceding groups. -/
private theorem chunks_observation_inj (rs ss : List Chunk)
    (h : rs.map (fun r => r.toBytes.toList) = ss.map (fun r => r.toBytes.toList)) : rs = ss := by
  induction rs generalizing ss with
  | nil => cases ss <;> simp_all
  | cons r rs ih =>
    cases ss with
    | nil => simp at h
    | cons s ss =>
      simp only [List.map_cons, List.cons.injEq] at h
      have he : r = s := STFSpec.Base.FixedBytes.toBytes_inj.mp (STFSpec.Base.Bytes.ext h.1)
      subst s
      exact congrArg (List.cons r) (ih ss h.2)
private theorem pack_as (xs : List UInt8) (rs : List Chunk)
    (h : rs.map (fun r => r.toBytes.toList) =
      (List.range (q xs.length)).map (fun i => (xs.drop (32 * i)).take 32 ++
        List.replicate (32 - min 32 (xs.length - 32 * i)) 0)) :
    (Ssz.pack xs.toByteArray).toList = rs := by
  apply chunks_observation_inj
  rw [Ssz.pack_toBytes, bytes_size, bytes_roundtrip]
  exact h.symm
private abbrev rangeChunk (start count : Nat) : Chunk :=
  L ((List.range count).foldr (fun i n => (start + i) + 256 * n) 0)

private theorem rootC1_layouts :
    (∀ w ∈ [1, 2, 4, 8, 16, 32],
      digits 32 (2 ^ (8 * w) - 1) = List.replicate w 255 ++ List.replicate (32 - w) 0) ∧
    digits 32 258 = [2, 1] ++ List.replicate 30 0 ∧
    digits 32 0 = List.replicate 32 0 ∧ digits 32 1 = 1 :: List.replicate 31 0 := by
  refine ⟨?_, by decide, by decide, by decide⟩
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem rootC2_a5_layout :
    (Ssz.pack ([165] : List UInt8).toByteArray).toList.map (fun r => r.toBytes.toList) =
      [165 :: List.replicate 31 0] := by
  rw [Ssz.pack_toBytes, bytes_size, bytes_roundtrip]
  decide

private theorem rootC2_tree_layouts (a b c d e f g h : Chunk) :
    tree 0 [] = Z ∧ tree 0 [a] = a ∧ tree 1 [a, b] = D a b ∧
    tree 2 [a, b, c] = D (D a b) (D c Z) ∧
    tree 3 [a, b, c, d, e, f, g, h] = D (D (D a b) (D c d)) (D (D e f) (D g h)) := by
  simp [tree, List.range_succ]
private theorem rootC3_packing_layouts :
    (uintChunks 8 [1, 2, 3, 4, 5]).toList.map (fun r => r.toBytes.toList) =
      [[1] ++ List.replicate 7 0 ++ [2] ++ List.replicate 7 0 ++
        [3] ++ List.replicate 7 0 ++ [4] ++ List.replicate 7 0,
       5 :: List.replicate 31 0] ∧
    (boolChunks (List.replicate 33 true)).toList.map (fun r => r.toBytes.toList) =
      [List.replicate 32 1, 1 :: List.replicate 31 0] := by
  constructor
  all_goals
    rw [Ssz.pack_toBytes, bytes_size, bytes_roundtrip]
    decide

private abbrev leafBytes (r : Chunk) := r.toBytes.toByteArray
private theorem leaf_size (r : Chunk) : (leafBytes r).size = 32 := by
  rw [STFSpec.Base.Bytes.size_toByteArray, STFSpec.Base.FixedBytes.size_toBytes]
private theorem leaf_pack (r : Chunk) : (Ssz.pack (leafBytes r)).toList = [r] := by
  apply chunks_observation_inj
  rw [Ssz.pack_toBytes, leaf_size]
  rw [STFSpec.Base.Bytes.toByteArray_toList]
  have hl : r.toBytes.toList.length = 32 := by
    rw [STFSpec.Base.Bytes.length_toList, STFSpec.Base.FixedBytes.size_toBytes]
  simp only [List.map_cons, List.map_nil]
  change _ = [r.toBytes.toList]
  simp [List.take_of_length_le (Nat.le_of_eq hl)]
private theorem leaf_root (r : Chunk)
    (h : Ssz.Rootable (.byteVector 32) (.bytes (leafBytes r))) :
    Ssz.hashTreeRoot (.byteVector 32) (.bytes (leafBytes r)) h = r := by
  rw [vector_root, leaf_pack]
  rfl
private theorem vector_leaf_support (r : Chunk) : Ssz.Rootable (.byteVector 32) (.bytes
    (leafBytes r)) :=
  (Ssz.rootable_iff _ _).mpr (leaf_size r)
private theorem vector_kids (rs : List Chunk) :
    Kids Ssz.hashTreeRoot
      ((rs.map (fun r => SszValue.bytes (leafBytes r))).map (fun x => (.byteVector 32, x))) rs
          := by
  induction rs with
  | nil => exact ⟨rfl, by simp⟩
  | cons r rs ih =>
    refine ⟨by simpa only [List.map_cons, List.length_cons] using congrArg Nat.succ ih.1, ?_⟩
    intro p hp hh
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact leaf_root r hh
    · exact ih.2 p hp hh

private theorem rootC4_order (a b : Chunk)
    (h : Ssz.Rootable (.list (.byteVector 32) 2)
      (.list ([a, b].map (fun r => .bytes (leafBytes r))))) :
    Ssz.hashTreeRoot (.list (.byteVector 32) 2)
      (.list ([a, b].map (fun r => .bytes (leafBytes r)))) h = D (D a b) (L 2) := by
  rw [composite_list_root (.byteVector 32) 2 _ trivial h [a, b] (vector_kids [a, b])]
  change D (tree 1 [a, b]) (L 2) = _
  rw [(rootC2_tree_layouts a b Z Z Z Z Z Z).2.2.1]

private theorem rootC5_small_layouts (a b c : Chunk) :
    progressive [] 0 = Z ∧ progressive [a] 0 = D a Z ∧
    progressive [a, b] 0 = D a (D (D (D b Z) (D Z Z)) Z) ∧
    progressive [a, b, c] 0 = D a (D (D (D b c) (D Z Z)) Z) := by
  simp [progressive, tree, List.range_succ]

private theorem rootC6_fields
    (h : Ssz.Rootable (.container [.uint 1, .uint 2, .bool])
      (.container [.uint 1, .uint 258, .bool true])) :
    Ssz.hashTreeRoot (.container [.uint 1, .uint 2, .bool])
      (.container [.uint 1, .uint 258, .bool true]) h = D (D (L 1) (L 258)) (D (L 1) Z) := by
  have hk : Kids Ssz.hashTreeRoot
      ([SszType.uint 1, .uint 2, .bool].zip [SszValue.uint 1, .uint 258, .bool true])
      [L 1, L 258, L 1] := by
    refine ⟨rfl, ?_⟩
    intro p hp hh
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact scalar 1 1 hh
    · exact scalar 2 258 hh
    · exact boolean true hh
  have he := container_root _ _ h [L 1, L 258, L 1] hk
  apply he.trans
  change tree 2 [L 1, L 258, L 1] = _
  exact (rootC2_tree_layouts (L 1) (L 258) (L 1) Z Z Z Z Z).2.2.2.1

private theorem rootC7_sparse_layouts (a b c : Chunk) :
    progressive (slots [true, false, true] [a, b]).toList 0 =
      D a (D (D (D Z b) (D Z Z)) Z) ∧
    progressive (slots [false, true] [a]).toList 0 =
      D Z (D (D (D a Z) (D Z Z)) Z) ∧
    progressive (slots [true, true, true] [a, b, c]).toList 0 =
      D a (D (D (D b c) (D Z Z)) Z) ∧
    ([true, false, true].foldr (fun b n => (if b then 1 else 0) + 2 * n) 0 = 5) ∧
    ([false, true].foldr (fun b n => (if b then 1 else 0) + 2 * n) 0 = 2) := by
  simp [progressive, tree, List.range_succ]


private theorem pack_singleton (n : Nat) (hn : n ∈ [1, 2, 3, 165]) :
    (Ssz.pack ([UInt8.ofNat n] : List UInt8).toByteArray).toList = [L n] := by
  apply pack_as
  simp only [List.map_cons, List.map_nil, L, STFSpec.Base.FixedBytes.toBytes_ofLeNat,
    STFSpec.Base.Bytes.toList_generate]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> decide
private theorem pack_empty : (Ssz.pack ByteArray.empty).toList = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [Array.length_toList, pack_size]
  rfl
private theorem single_byte_root (n : Nat) (hn : n ∈ [1, 2, 3, 165])
    (h : Ssz.Rootable (.byteVector 1) (.bytes [UInt8.ofNat n].toByteArray)) :
    Ssz.hashTreeRoot (.byteVector 1) (.bytes [UInt8.ofNat n].toByteArray) h = L n := by
  rw [vector_root, pack_singleton n hn]
  rfl
private theorem rootC4_vector1
    (h : Ssz.Rootable (.list (.byteVector 1) 3)
      (.list ([1, 2, 3].map (fun n => .bytes [UInt8.ofNat n].toByteArray)))) :
    Ssz.hashTreeRoot (.list (.byteVector 1) 3)
      (.list ([1, 2, 3].map (fun n => .bytes [UInt8.ofNat n].toByteArray))) h =
        D (D (D (L 1) (L 2)) (D (L 3) Z)) (L 3) := by
  have hk : Kids Ssz.hashTreeRoot
      (([1, 2, 3].map (fun n => SszValue.bytes [UInt8.ofNat n].toByteArray)).map
        (fun x => (.byteVector 1, x))) [L 1, L 2, L 3] := by
    refine ⟨rfl, ?_⟩
    intro p hp hh
    simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left,
      List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact single_byte_root 1 (by simp) hh
    · exact single_byte_root 2 (by simp) hh
    · exact single_byte_root 3 (by simp) hh
  rw [composite_list_root (.byteVector 1) 3 _ trivial h _ hk]
  change D (tree 2 [L 1, L 2, L 3]) (L 3) = _
  rw [(rootC2_tree_layouts (L 1) (L 2) (L 3) Z Z Z Z Z).2.2.2.1]

private theorem activity_tail (n : Nat) :
    (List.replicate n false ++ [true]).foldr
      (fun b n => (if b then 1 else 0) + 2 * n) 0 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, List.foldr_cons, Bool.false_eq_true,
      ite_false, Nat.zero_add]
    rw [ih, Nat.pow_succ, Nat.mul_comm]
private theorem slots_false (mask : List Bool) (rs : List Chunk) :
    (slots (false :: mask) rs).toList = Z :: (slots mask rs).toList := by
  simp only [List.length_cons, List.range_succ_eq_map, List.map_cons,
    List.map_map, List.getD_cons_zero, Bool.false_eq_true, ite_false]
  rfl
private theorem slots_final (n : Nat) (a : Chunk) :
    (slots (List.replicate n false ++ [true]) [a]).toList = List.replicate n Z ++ [a] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, slots_false, ih]
    rfl
private theorem rootC7_edge_layouts :
    (∀ n ∈ [254, 255], ∀ a : Chunk,
      (slots (List.replicate n false ++ [true]) [a]).toList =
        List.replicate n Z ++ [a]) ∧
    digits 32 (2 ^ 254) = List.replicate 31 0 ++ [64] ∧
    digits 32 (2 ^ 255) = List.replicate 31 0 ++ [128] := by
  exact ⟨fun n _ a => slots_final n a, by decide, by decide⟩

private theorem rootC8_nested :
    ∃ h : Ssz.Rootable (.progressiveList .progressiveByteList)
      (.list [.bytes ByteArray.empty, .bytes ([165] : List UInt8).toByteArray]),
      Ssz.hashTreeRoot (.progressiveList .progressiveByteList)
        (.list [.bytes ByteArray.empty, .bytes ([165] : List UInt8).toByteArray]) h =
          D (D (D Z (L 0))
            (D (D (D (D (D (L 165) Z) (L 1)) Z) (D Z Z)) Z)) (L 2) := by
  have h0 : Ssz.Rootable .progressiveByteList (.bytes ByteArray.empty) := by
    apply (Ssz.rootable_iff _ _).mpr
    decide
  have h1 : Ssz.Rootable .progressiveByteList (.bytes ([165] : List UInt8).toByteArray) := by
    apply (Ssz.rootable_iff _ _).mpr
    change ([165] : List UInt8).toByteArray.size < 2 ^ 256
    rw [bytes_size]
    decide
  have h : Ssz.Rootable (.progressiveList .progressiveByteList)
      (.list [.bytes ByteArray.empty, .bytes ([165] : List UInt8).toByteArray]) := by
    apply (Ssz.rootable_iff _ _).mpr
    simp [h0, h1]
  have he0 : ∀ hx : Ssz.Rootable .progressiveByteList (.bytes ByteArray.empty),
      Ssz.hashTreeRoot .progressiveByteList (.bytes ByteArray.empty) hx = D Z (L 0) := by
    intro hx
    rw [progressive_bytes_root, pack_empty, progressive]
    rfl
  have he1 : ∀ hx : Ssz.Rootable .progressiveByteList (.bytes ([165] : List UInt8).toByteArray),
      Ssz.hashTreeRoot .progressiveByteList (.bytes ([165] : List UInt8).toByteArray) hx =
        D (D (L 165) Z) (L 1) := by
    intro hx
    rw [progressive_bytes_root]
    have hp : (Ssz.pack ([165] : List UInt8).toByteArray).toList = [L 165] := by
      simpa only [show UInt8.ofNat 165 = (165 : UInt8) from by decide] using
        pack_singleton 165 (by simp)
    rw [hp]
    rw [(rootC5_small_layouts (L 165) Z Z).2.1, bytes_size]
    simp only [List.length_cons, List.length_nil]
  have hk : Kids Ssz.hashTreeRoot
      [(.progressiveByteList, .bytes ByteArray.empty),
       (.progressiveByteList, .bytes ([165] : List UInt8).toByteArray)]
      [D Z (L 0), D (D (L 165) Z) (L 1)] := by
    refine ⟨rfl, ?_⟩
    intro p hp hx
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl
    · exact he0 hx
    · exact he1 hx
  refine ⟨h, ?_⟩
  rw [composite_progressive_root .progressiveByteList _ trivial h _ hk]
  rw [(rootC5_small_layouts (D Z (L 0)) (D (D (L 165) Z) (L 1)) Z).2.2.1]
  simp only [List.length_cons, List.length_nil]


private theorem rootC3_available :
    Ssz.Rootable (.list (.uint 8) 5) (.list ([1, 2, 3, 4, 5].map SszValue.uint)) ∧
    Ssz.Rootable (.list .bool 33) (.list ((List.replicate 33 true).map SszValue.bool)) ∧
    Ssz.Rootable (.list (.uint 8) 0) (.list []) ∧
    Ssz.Rootable (.list .bool 0) (.list []) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (Ssz.rootable_iff _ _).mpr
    refine ⟨by decide, by decide, ?_, by decide⟩
    intro x hx
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
    apply (Ssz.rootable_iff _ _).mpr
    refine ⟨by decide, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
  · apply (Ssz.rootable_iff _ _).mpr
    refine ⟨by decide, by decide, ?_, trivial⟩
    intro x hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    exact (Ssz.rootable_iff _ _).mpr trivial
  · apply (Ssz.rootable_iff _ _).mpr
    simp
  · apply (Ssz.rootable_iff _ _).mpr
    simp
private theorem rootC2_available (n : Nat) :
    Ssz.Rootable (.byteList n) (.bytes ByteArray.empty) := by
  apply (Ssz.rootable_iff _ _).mpr
  simp
private theorem rootC5_composite_available (rs : List Chunk)
    (hn : rs.length ∈ [0, 1, 5, 6, 21, 22]) :
    ∃ h : Ssz.Rootable (.progressiveList (.byteVector 32))
      (.list (rs.map (fun r => .bytes (leafBytes r)))),
      Ssz.hashTreeRoot (.progressiveList (.byteVector 32))
        (.list (rs.map (fun r => .bytes (leafBytes r)))) h =
          D (progressive rs 0) (L rs.length) := by
  have hcount : rs.length < 2 ^ 256 := by
    have h22 : rs.length ≤ 22 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      omega
    exact Nat.lt_of_le_of_lt h22 (by decide)
  have h : Ssz.Rootable (.progressiveList (.byteVector 32))
      (.list (rs.map (fun r => .bytes (leafBytes r)))) := by
    apply (Ssz.rootable_iff _ _).mpr
    refine ⟨by simpa only [List.length_map] using hcount, ?_, trivial⟩
    intro x hx
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hx
    exact vector_leaf_support r
  refine ⟨h, ?_⟩
  rw [composite_progressive_root (.byteVector 32) _ trivial h rs (vector_kids rs)]
  simp only [List.length_map]

end STFSpec.Conformance.Codec
