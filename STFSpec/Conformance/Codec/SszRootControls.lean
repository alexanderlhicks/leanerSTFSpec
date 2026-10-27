/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Complete SSZ root controls

Library `EthConformance`. rootP0–rootP9 use the Codec facade and public equations.
Expected roots retain every leaf byte and the complete ordered SHA-256 expression.
No SHA collision, source-runtime, guest, security or cost assertion is supplied.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–4/§7.
-/

namespace STFSpec.Conformance.Codec

open STFSpec.Codec

private theorem rootP0 (t : SszType) (v : SszValue)
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
  | _, _ => False := Ssz.hashTreeRoot_eq t v h

private theorem scalar_root (w n : Nat) (h : Ssz.Rootable (.uint w) (.uint n)) :
    Ssz.hashTreeRoot (.uint w) (.uint n) h = Base.FixedBytes.ofLeNat n :=
  Ssz.hashTreeRoot_eq _ _ h

private theorem bool_root (b : Bool) (h : Ssz.Rootable .bool (.bool b)) :
    Ssz.hashTreeRoot .bool (.bool b) h = Base.FixedBytes.ofLeNat (if b then 1 else 0) :=
  Ssz.hashTreeRoot_eq _ _ h

-- R00: every one of the six supported widths, both endpoints, every output byte.
private theorem rootP1_endpoints (w : Nat) (hw : w ∈ [1, 2, 4, 8, 16, 32])
    (h0 : Ssz.Rootable (.uint w) (.uint 0))
    (hm : Ssz.Rootable (.uint w) (.uint (2 ^ (8 * w) - 1))) :
    (Ssz.hashTreeRoot (.uint w) (.uint 0) h0).toBytes.toList = List.replicate 32 0 ∧
    (Ssz.hashTreeRoot (.uint w) (.uint (2 ^ (8 * w) - 1)) hm).toBytes.toList =
      List.replicate w 255 ++ List.replicate (32 - w) 0 := by
  rw [scalar_root, scalar_root, Base.FixedBytes.toBytes_ofLeNat,
    Base.FixedBytes.toBytes_ofLeNat, Base.Bytes.toList_generate, Base.Bytes.toList_generate]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem rootP1_uint16 (h : Ssz.Rootable (.uint 2) (.uint 258)) :
    (Ssz.hashTreeRoot (.uint 2) (.uint 258) h).toBytes.toList =
      [2, 1] ++ List.replicate 30 0 := by
  rw [scalar_root, Base.FixedBytes.toBytes_ofLeNat, Base.Bytes.toList_generate]
  decide

-- R01: Bool is byte-valued; activity masks have a different packing rule.
private theorem rootP1_bool (b : Bool) (h : Ssz.Rootable .bool (.bool b)) :
    (Ssz.hashTreeRoot .bool (.bool b) h).toBytes.toList =
      (if b then (1 : UInt8) else 0) :: List.replicate 31 0 := by
  rw [bool_root, Base.FixedBytes.toBytes_ofLeNat, Base.Bytes.toList_generate]
  cases b <;> decide

private theorem rootP1_excluded (w n : Nat) :
    ¬ Ssz.Rootable (.uint 0) (.uint n) ∧
    ¬ Ssz.Rootable (.uint 3) (.uint n) ∧
    ¬ Ssz.Rootable (.uint 33) (.uint n) ∧
    ¬ Ssz.Rootable (.uint w) (.uint (2 ^ (8 * w))) ∧
    ¬ Ssz.Rootable .bool (.uint n) ∧ ¬ Ssz.Rootable (.uint w) (.bool false) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact (by decide : ¬0 ∈ [1, 2, 4, 8, 16, 32]) ((Ssz.rootable_iff _ _).mp h).1
  · intro h; exact (by decide : ¬3 ∈ [1, 2, 4, 8, 16, 32]) ((Ssz.rootable_iff _ _).mp h).1
  · intro h; exact (by decide : ¬33 ∈ [1, 2, 4, 8, 16, 32]) ((Ssz.rootable_iff _ _).mp h).1
  · intro h; exact Nat.lt_irrefl _ ((Ssz.rootable_iff _ _).mp h).2
  · intro h; exact (Ssz.rootable_iff _ _).mp h
  · intro h; exact (Ssz.rootable_iff _ _).mp h

private theorem byteList_ingress (b : ByteArray) :
    (Base.Bytes.ofByteArray b).toList = b.toList := by
  rw [← Base.Bytes.toByteArray_toList, Base.Bytes.toByteArray_ofByteArray]

private theorem byteList_length (b : ByteArray) : b.toList.length = b.size := by
  rw [← byteList_ingress, Base.Bytes.length_toList, Base.Bytes.size_ofByteArray]

private theorem byteList_roundtrip (xs : List UInt8) : xs.toByteArray.toList = xs := by
  rw [← byteList_ingress, Base.Bytes.toList_ofByteArray, List.toList_data_toByteArray]

private theorem pack_size (b : ByteArray) : (Ssz.pack b).size = (b.size + 31) / 32 := by
  have h := congrArg List.length (Ssz.pack_toBytes b)
  simpa only [List.length_map, Array.length_toList, List.length_range] using h

private theorem packed_inj (a b : Array Base.Bytes32)
    (h : a.toList.map (fun c ↦ c.toBytes.toList) =
      b.toList.map (fun c ↦ c.toBytes.toList)) : a = b := by
  apply Array.toList_inj.mp
  apply (List.map_inj_right _).mp h
  intro x y hxy
  exact Base.FixedBytes.toBytes_inj.mp (Base.Bytes.toList_inj.mp hxy)

private def zero : Base.Bytes32 := Base.FixedBytes.ofNat 0

private def pair (a b : Base.Bytes32) : Base.Bytes32 :=
  Hash.sha256 ((a.toBytes ++ b.toBytes).toByteArray)

private def leaf (bs : List UInt8) (h : bs.length ≤ 32) : Base.Bytes32 :=
  (Base.FixedBytes.ofBytes? (Base.Bytes.ofList
    (bs ++ List.replicate (32 - bs.length) 0))).get (by
      apply Option.isSome_iff_ne_none.mpr
      intro hn
      apply (Base.FixedBytes.ofBytes?_eq_none_iff.mp hn)
      rw [Base.Bytes.size_ofList, List.length_append, List.length_replicate]
      omega)

private theorem leaf_bytes (bs : List UInt8) (h : bs.length ≤ 32) :
    (leaf bs h).toBytes.toList = bs ++ List.replicate (32 - bs.length) 0 := by
  have hb : (leaf bs h).toBytes = Base.Bytes.ofList
      (bs ++ List.replicate (32 - bs.length) 0) := by
    apply (Base.FixedBytes.ofBytes?_eq_some_iff.mp _).2
    exact (Option.some_get _).symm
  rw [hb, Base.Bytes.toList_ofList]

private theorem zero_bytes : zero.toBytes.toList = List.replicate 32 0 := by
  rw [zero, Base.FixedBytes.toBytes_ofNat, Base.Bytes.toList_generate]
  decide

private theorem leaf_empty : leaf [] (by decide) = zero := by
  apply Base.FixedBytes.toBytes_inj.mp
  apply Base.Bytes.toList_inj.mp
  rw [leaf_bytes, zero_bytes]
  rfl

private def foldModel {α : Type} (p : α → α → α) (z : α) (d : Nat)
    (xs : List α) : α :=
  ((List.range d).foldl
    (fun layer _ ↦ (List.range (layer.length / 2)).map
      (fun i ↦ p (layer.getD (2 * i) z) (layer.getD (2 * i + 1) z)))
    (xs ++ List.replicate (2 ^ d - xs.length) z)).headD z

private theorem foldModel_two {α : Type} (p : α → α → α) (z a b : α) :
    foldModel p z 1 [a, b] = p a b := by
  simp [foldModel, List.range_succ]

private theorem ordinary_model (cs : Array Base.Bytes32) (limit : Nat)
    (h : cs.size ≤ 2 ^ (if limit ≤ 1 then 0 else Nat.log2 (limit - 1) + 1)) :
    Ssz.merkleize cs limit h =
      foldModel pair zero (if limit ≤ 1 then 0 else Nat.log2 (limit - 1) + 1) cs.toList :=
  Ssz.merkleize_eq cs limit h

private theorem ordinary_one (a : Base.Bytes32)
    (h : (#[a] : Array Base.Bytes32).size ≤ 2 ^ (if 1 ≤ 1 then 0 else Nat.log2 (1 - 1) + 1)) :
    Ssz.merkleize #[a] 1 h = a := by
  rw [ordinary_model]
  rfl

private theorem ordinary_two (a b : Base.Bytes32)
    (h : (#[a, b] : Array Base.Bytes32).size ≤ 2 ^ (if 2 ≤ 1 then 0 else Nat.log2 (2 - 1) + 1)) :
    Ssz.merkleize #[a, b] 2 h = pair a b := by
  rw [ordinary_model]
  exact foldModel_two pair zero a b

private theorem length_pair (a : Base.Bytes32) (n : Nat) (h : n < 2 ^ 256) :
    Ssz.mixInLength a n h = pair a (Base.FixedBytes.ofLeNat n) :=
  Ssz.mixInLength_eq a n h

private theorem vector_root (n : Nat) (b : ByteArray)
    (h : Ssz.Rootable (.byteVector n) (.bytes b))
    (hp : (Ssz.pack b).size ≤ 2 ^ (if (n + 31) / 32 ≤ 1 then 0 else Nat.log2 ((n + 31) / 32 -
        1) + 1)) :
    Ssz.hashTreeRoot (.byteVector n) (.bytes b) h = Ssz.merkleize (Ssz.pack b) ((n + 31) / 32)
        hp :=
  Ssz.hashTreeRoot_eq _ _ h hp

private def ramp (start count : Nat) : List UInt8 :=
  (List.range' start count).map UInt8.ofNat

private theorem ramp_length (start count : Nat) : (ramp start count).length = count := by
  simp [ramp]

private theorem ramp_window (start count off len : Nat) :
    ((ramp start count).drop off).take len = ramp (start + off) (min len (count - off)) := by
  unfold ramp
  rw [← List.map_drop, ← List.map_take, List.drop_range']
  simp only [Nat.mul_one]
  by_cases h : count - off ≤ len
  · rw [List.take_range'_of_length_le h, Nat.min_eq_right h]
  · rw [List.take_range'_of_length_ge (by omega), Nat.min_eq_left (by omega)]

private def windows (bs : List UInt8) : List Base.Bytes32 :=
  (List.range ((bs.length + 31) / 32)).map (fun i ↦
    leaf ((bs.drop (32 * i)).take 32) (by simp only [List.length_take]; exact Nat.min_le_left _ _))

private theorem pack_windows (bs : List UInt8) :
    Ssz.pack bs.toByteArray = (windows bs).toArray := by
  apply packed_inj
  rw [Ssz.pack_toBytes]
  simp only [windows, byteList_roundtrip, List.size_toByteArray, List.map_map]
  apply List.map_congr_left
  intro i hi
  dsimp only [Function.comp]
  simpa only [List.length_take, List.length_drop] using
    (leaf_bytes ((bs.drop (32 * i)).take 32)
      (by simp only [List.length_take]; exact Nat.min_le_left _ _)).symm

private theorem foldModel_three {α : Type} (p : α → α → α) (z a b c : α) :
    foldModel p z 2 [a, b, c] = p (p a b) (p c z) := by
  simp [foldModel, List.range_succ]

private theorem foldModel_eight {α : Type} (p : α → α → α) (z a b c d e f g h : α) :
    foldModel p z 3 [a, b, c, d, e, f, g, h] =
      p (p (p a b) (p c d)) (p (p e f) (p g h)) := by
  simp [foldModel, List.range_succ]

private theorem ordinary_three (a b c : Base.Bytes32)
    (h : (#[a, b, c] : Array Base.Bytes32).size ≤ 2 ^ (if 3 ≤ 1 then 0 else Nat.log2 (3 - 1) +
        1)) :
    Ssz.merkleize #[a, b, c] 3 h = pair (pair a b) (pair c zero) := by
  rw [ordinary_model]
  exact foldModel_three pair zero a b c

private theorem ordinary_eight (a b c d e f g h : Base.Bytes32)
    (hp : (#[a, b, c, d, e, f, g, h] : Array Base.Bytes32).size ≤
      2 ^ (if 8 ≤ 1 then 0 else Nat.log2 (8 - 1) + 1)) :
    Ssz.merkleize #[a, b, c, d, e, f, g, h] 8 hp =
      pair (pair (pair a b) (pair c d)) (pair (pair e f) (pair g h)) := by
  rw [ordinary_model]
  exact foldModel_eight pair zero a b c d e f g h

private theorem vector_chunks (n : Nat) (b : ByteArray)
    (h : Ssz.Rootable (.byteVector n) (.bytes b)) (cs : Array Base.Bytes32)
    (hc : Ssz.pack b = cs)
    (hp : cs.size ≤ 2 ^ (if (n + 31) / 32 ≤ 1 then 0 else Nat.log2 ((n + 31) / 32 - 1) + 1)) :
    Ssz.hashTreeRoot (.byteVector n) (.bytes b) h = Ssz.merkleize cs ((n + 31) / 32) hp := by
  subst cs
  exact vector_root n b h hp

-- R02/R03: complete ordered packed windows for ByteVector0.
private theorem pack_vector0 :
    Ssz.pack (([] : List UInt8)).toByteArray = #[] := by
  apply Array.size_eq_zero_iff.mp
  rw [pack_size, List.size_toByteArray]
  rfl

private theorem rootP2_vector0
    (h : Ssz.Rootable (.byteVector 0) (.bytes (([] : List UInt8)).toByteArray)) :
    Ssz.hashTreeRoot (.byteVector 0) (.bytes (([] : List UInt8)).toByteArray) h = zero := by
  rw [vector_chunks 0 _ h #[] pack_vector0 (by decide)]
  rw [ordinary_model]
  rfl

-- R02/R03: complete ordered packed windows for ByteVector1.
private theorem pack_vector1 :
    Ssz.pack (([165] : List UInt8)).toByteArray = #[leaf ([165]) (by decide)] := by
  apply packed_inj
  rw [Ssz.pack_toBytes]
  simp only [byteList_roundtrip, List.size_toByteArray, List.map_cons, List.map_nil, leaf_bytes]
  decide

private theorem rootP2_vector1
    (h : Ssz.Rootable (.byteVector 1) (.bytes (([165] : List UInt8)).toByteArray)) :
    Ssz.hashTreeRoot (.byteVector 1) (.bytes (([165] : List UInt8)).toByteArray) h = leaf ([165])
      (by decide) := by
  rw [vector_chunks 1 _ h #[leaf ([165]) (by decide)] pack_vector1 (by decide)]
  exact ordinary_one _ _

-- R02/R03: complete ordered packed windows for ByteVector31.
private theorem pack_vector31 :
    Ssz.pack (ramp 0 31).toByteArray = #[leaf (ramp 0 31) (by simp [ramp])] := by
  apply packed_inj
  rw [Ssz.pack_toBytes]
  simp only [byteList_roundtrip, List.size_toByteArray, List.map_cons, List.map_nil, leaf_bytes]
  decide

private theorem rootP2_vector31
    (h : Ssz.Rootable (.byteVector 31) (.bytes (ramp 0 31).toByteArray)) :
    Ssz.hashTreeRoot (.byteVector 31) (.bytes (ramp 0 31).toByteArray) h = leaf (ramp 0 31)
      (by simp [ramp]) := by
  rw [vector_chunks 31 _ h #[leaf (ramp 0 31) (by simp [ramp])] pack_vector31 (by decide)]
  exact ordinary_one _ _

-- R02/R03: complete ordered packed windows for ByteVector32.
private theorem pack_vector32 :
    Ssz.pack (ramp 0 32).toByteArray = #[leaf (ramp 0 32) (by simp [ramp])] := by
  apply packed_inj
  rw [Ssz.pack_toBytes]
  simp only [byteList_roundtrip, List.size_toByteArray, List.map_cons, List.map_nil, leaf_bytes]
  decide

private theorem rootP2_vector32
    (h : Ssz.Rootable (.byteVector 32) (.bytes (ramp 0 32).toByteArray)) :
    Ssz.hashTreeRoot (.byteVector 32) (.bytes (ramp 0 32).toByteArray) h = leaf (ramp 0 32)
      (by simp [ramp]) := by
  rw [vector_chunks 32 _ h #[leaf (ramp 0 32) (by simp [ramp])] pack_vector32 (by decide)]
  exact ordinary_one _ _

-- R02/R03: complete ordered packed windows for ByteVector33.
private theorem pack_vector33 :
    Ssz.pack (ramp 0 33).toByteArray = #[leaf (ramp 0 32) (by simp [ramp]), leaf ([32])
      (by decide)] := by
  apply packed_inj
  rw [Ssz.pack_toBytes]
  simp only [byteList_roundtrip, List.size_toByteArray, List.map_cons, List.map_nil, leaf_bytes]
  decide

private theorem rootP2_vector33
    (h : Ssz.Rootable (.byteVector 33) (.bytes (ramp 0 33).toByteArray)) :
    Ssz.hashTreeRoot (.byteVector 33) (.bytes (ramp 0 33).toByteArray) h = pair (leaf (ramp 0 32)
      (by simp [ramp])) (leaf ([32]) (by decide)) := by
  rw [vector_chunks 33 _ h #[leaf (ramp 0 32) (by simp [ramp]), leaf ([32]) (by decide)]
    pack_vector33 (by decide)]
  exact ordinary_two _ _ _

-- R02/R03: complete ordered packed windows for ByteVector48.
private theorem pack_vector48 :
    Ssz.pack (ramp 0 48).toByteArray = #[leaf (ramp 0 32) (by simp [ramp]), leaf (ramp 32 16)
      (by simp [ramp])] := by
  apply packed_inj
  rw [Ssz.pack_toBytes]
  simp only [byteList_roundtrip, List.size_toByteArray, List.map_cons, List.map_nil, leaf_bytes]
  decide

private theorem rootP2_vector48
    (h : Ssz.Rootable (.byteVector 48) (.bytes (ramp 0 48).toByteArray)) :
    Ssz.hashTreeRoot (.byteVector 48) (.bytes (ramp 0 48).toByteArray) h = pair (leaf (ramp 0 32)
      (by simp [ramp])) (leaf (ramp 32 16) (by simp [ramp])) := by
  rw [vector_chunks 48 _ h #[leaf (ramp 0 32) (by simp [ramp]), leaf (ramp 32 16) (by simp [ramp])]
    pack_vector48 (by decide)]
  exact ordinary_two _ _ _

-- R02/R03: complete ordered packed windows for ByteVector96.
private theorem pack_vector96 :
    Ssz.pack (ramp 0 96).toByteArray = #[leaf (ramp 0 32) (by simp [ramp]), leaf (ramp 32 32)
      (by simp [ramp]), leaf (ramp 64 32) (by simp [ramp])] := by
  apply packed_inj
  rw [Ssz.pack_toBytes]
  simp only [byteList_roundtrip, List.size_toByteArray, List.map_cons, List.map_nil, leaf_bytes]
  decide

private theorem rootP2_vector96
    (h : Ssz.Rootable (.byteVector 96) (.bytes (ramp 0 96).toByteArray)) :
    Ssz.hashTreeRoot (.byteVector 96) (.bytes (ramp 0 96).toByteArray) h = pair (pair (leaf (ramp 0
      32) (by simp [ramp])) (leaf (ramp 32 32) (by simp [ramp]))) (pair (leaf (ramp 64 32)
      (by simp [ramp])) zero) := by
  rw [vector_chunks 96 _ h #[leaf (ramp 0 32) (by simp [ramp]), leaf (ramp 32 32) (by simp [ramp]),
    leaf (ramp 64 32) (by simp [ramp])] pack_vector96 (by decide)]
  exact ordinary_three _ _ _ _

-- R02/R03: complete ordered packed windows for ByteVector256.
private theorem pack_vector256 :
    Ssz.pack (ramp 0 256).toByteArray = #[leaf (ramp 0 32) (by simp [ramp]), leaf (ramp 32 32)
      (by simp [ramp]), leaf (ramp 64 32) (by simp [ramp]), leaf (ramp 96 32) (by simp [ramp]),
      leaf (ramp 128 32) (by simp [ramp]), leaf (ramp 160 32) (by simp [ramp]), leaf (ramp 192 32)
      (by simp [ramp]), leaf (ramp 224 32) (by simp [ramp])] := by
  rw [pack_windows]
  simp [windows, ramp_length, ramp_window, List.range_succ]

private theorem rootP2_vector256
    (h : Ssz.Rootable (.byteVector 256) (.bytes (ramp 0 256).toByteArray)) :
    Ssz.hashTreeRoot (.byteVector 256) (.bytes (ramp 0 256).toByteArray) h = pair (pair (pair (leaf
      (ramp 0 32) (by simp [ramp])) (leaf (ramp 32 32) (by simp [ramp]))) (pair (leaf (ramp 64 32)
      (by simp [ramp])) (leaf (ramp 96 32) (by simp [ramp])))) (pair (pair (leaf (ramp 128 32)
      (by simp [ramp])) (leaf (ramp 160 32) (by simp [ramp]))) (pair (leaf (ramp 192 32)
      (by simp [ramp])) (leaf (ramp 224 32) (by simp [ramp])))) := by
  rw [vector_chunks 256 _ h #[leaf (ramp 0 32) (by simp [ramp]), leaf (ramp 32 32)
    (by simp [ramp]), leaf (ramp 64 32) (by simp [ramp]), leaf (ramp 96 32) (by simp [ramp]), leaf
    (ramp 128 32) (by simp [ramp]), leaf (ramp 160 32) (by simp [ramp]), leaf (ramp 192 32)
    (by simp [ramp]), leaf (ramp 224 32) (by simp [ramp])] pack_vector256 (by decide)]
  exact ordinary_eight _ _ _ _ _ _ _ _ _

private theorem word_zero : (Base.FixedBytes.ofLeNat 0 : Base.Bytes32) = zero := by
  apply Base.FixedBytes.toBytes_inj.mp
  apply Base.Bytes.toList_inj.mp
  rw [Base.FixedBytes.toBytes_ofLeNat, Base.Bytes.toList_generate, zero_bytes]
  decide

private theorem foldModel_empty_one {α : Type} (p : α → α → α) (z : α) :
    foldModel p z 1 [] = p z z := by
  simp [foldModel, List.range_succ]

private theorem ordinary_empty_zero
    (hp : (#[] : Array Base.Bytes32).size ≤ 2 ^ (if 0 ≤ 1 then 0 else Nat.log2 (0 - 1) + 1)) :
    Ssz.merkleize #[] 0 hp = zero := by
  rw [ordinary_model]
  rfl

private theorem ordinary_empty_one
    (hp : (#[] : Array Base.Bytes32).size ≤ 2 ^ (if 1 ≤ 1 then 0 else Nat.log2 (1 - 1) + 1)) :
    Ssz.merkleize #[] 1 hp = zero := by
  rw [ordinary_model]
  rfl

private theorem ordinary_empty_two
    (hp : (#[] : Array Base.Bytes32).size ≤ 2 ^ (if 2 ≤ 1 then 0 else Nat.log2 (2 - 1) + 1)) :
    Ssz.merkleize #[] 2 hp = pair zero zero := by
  rw [ordinary_model]
  exact foldModel_empty_one pair zero

private theorem bytes_chunks (limit : Nat) (b : ByteArray)
    (h : Ssz.Rootable (.byteList limit) (.bytes b)) (cs : Array Base.Bytes32)
    (hc : Ssz.pack b = cs)
    (hp : cs.size ≤ 2 ^ (if (limit + 31) / 32 ≤ 1 then 0 else Nat.log2 ((limit + 31) / 32 - 1) +
        1))
    (hn : b.size < 2 ^ 256) :
    Ssz.hashTreeRoot (.byteList limit) (.bytes b) h =
      Ssz.mixInLength (Ssz.merkleize cs ((limit + 31) / 32) hp) b.size hn := by
  subst cs
  exact Ssz.hashTreeRoot_eq _ _ h hp hn

-- R04: declared byte limits retain their contents-tree capacity at empty input.
private theorem rootP2_emptyByteList0
    (h : Ssz.Rootable (.byteList 0) (.bytes ([] : List UInt8).toByteArray)) :
    Ssz.hashTreeRoot (.byteList 0) (.bytes ([] : List UInt8).toByteArray) h =
      pair (zero) zero := by
  rw [bytes_chunks 0 _ h #[] pack_vector0 (by decide) (by decide)]
  rw [ordinary_empty_zero, length_pair]
  simp only [List.size_toByteArray, List.length_nil, word_zero]

-- R04: declared byte limits retain their contents-tree capacity at empty input.
private theorem rootP2_emptyByteList1
    (h : Ssz.Rootable (.byteList 1) (.bytes ([] : List UInt8).toByteArray)) :
    Ssz.hashTreeRoot (.byteList 1) (.bytes ([] : List UInt8).toByteArray) h =
      pair (zero) zero := by
  rw [bytes_chunks 1 _ h #[] pack_vector0 (by decide) (by decide)]
  rw [ordinary_empty_one, length_pair]
  simp only [List.size_toByteArray, List.length_nil, word_zero]

-- R04: declared byte limits retain their contents-tree capacity at empty input.
private theorem rootP2_emptyByteList32
    (h : Ssz.Rootable (.byteList 32) (.bytes ([] : List UInt8).toByteArray)) :
    Ssz.hashTreeRoot (.byteList 32) (.bytes ([] : List UInt8).toByteArray) h =
      pair (zero) zero := by
  rw [bytes_chunks 32 _ h #[] pack_vector0 (by decide) (by decide)]
  rw [ordinary_empty_one, length_pair]
  simp only [List.size_toByteArray, List.length_nil, word_zero]

-- R04: declared byte limits retain their contents-tree capacity at empty input.
private theorem rootP2_emptyByteList33
    (h : Ssz.Rootable (.byteList 33) (.bytes ([] : List UInt8).toByteArray)) :
    Ssz.hashTreeRoot (.byteList 33) (.bytes ([] : List UInt8).toByteArray) h =
      pair (pair zero zero) zero := by
  rw [bytes_chunks 33 _ h #[] pack_vector0 (by decide) (by decide)]
  rw [ordinary_empty_two, length_pair]
  simp only [List.size_toByteArray, List.length_nil, word_zero]

-- R05: the complete contents agree, while actual byte counts remain 1/2.
private theorem rootP2_byteCount1
    (h : Ssz.Rootable (.byteList 32) (.bytes (([165] : List UInt8)).toByteArray)) :
    Ssz.hashTreeRoot (.byteList 32) (.bytes (([165] : List UInt8)).toByteArray) h =
      pair (leaf [165] (by decide)) (Base.FixedBytes.ofLeNat 1) := by
  rw [bytes_chunks 32 _ h #[leaf [165] (by decide)] pack_vector1 (by decide) (by decide)]
  rw [ordinary_one, length_pair]
  rfl

private theorem pack_tailZero :
    Ssz.pack ([165, 0] : List UInt8).toByteArray = #[leaf [165] (by decide)] := by
  apply packed_inj
  rw [Ssz.pack_toBytes]
  simp only [byteList_roundtrip, List.size_toByteArray, List.map_cons, List.map_nil, leaf_bytes]
  decide

-- R05: the complete contents agree, while actual byte counts remain 1/2.
private theorem rootP2_byteCount2
    (h : Ssz.Rootable (.byteList 32) (.bytes (([165, 0] : List UInt8)).toByteArray)) :
    Ssz.hashTreeRoot (.byteList 32) (.bytes (([165, 0] : List UInt8)).toByteArray) h =
      pair (leaf [165] (by decide)) (Base.FixedBytes.ofLeNat 2) := by
  rw [bytes_chunks 32 _ h #[leaf [165] (by decide)] pack_tailZero (by decide) (by decide)]
  rw [ordinary_one, length_pair]
  rfl

private theorem rootP2_byteList33
    (h : Ssz.Rootable (.byteList 33) (.bytes (ramp 0 33).toByteArray)) :
    Ssz.hashTreeRoot (.byteList 33) (.bytes (ramp 0 33).toByteArray) h =
      pair (pair (leaf (ramp 0 32) (by simp [ramp])) (leaf [32] (by decide)))
        (Base.FixedBytes.ofLeNat 33) := by
  rw [bytes_chunks 33 _ h
    #[leaf (ramp 0 32) (by simp [ramp]), leaf [32] (by decide)] pack_vector33
    (by decide) (by simp only [List.size_toByteArray, ramp_length]; decide)]
  rw [ordinary_two, length_pair]
  rfl

private theorem rootP2_samePack_actualCount :
    Ssz.pack ([165] : List UInt8).toByteArray = Ssz.pack ([165, 0] : List UInt8).toByteArray ∧
    ([165] : List UInt8).toByteArray.size = 1 ∧
    ([165, 0] : List UInt8).toByteArray.size = 2 := by
  rw [pack_vector1, pack_tailZero]
  exact ⟨rfl, rfl, rfl⟩

private def leDigits (w n : Nat) : List UInt8 :=
  (List.range w).map (fun i ↦ UInt8.ofNat (n >>> (8 * i)))

private theorem leDigits_function (w : Nat) :
    leDigits w = fun n ↦ (List.range w).map (fun i ↦ UInt8.ofNat (n >>> (8 * i))) := by
  funext n
  rfl

private theorem flatDigits_length (w : Nat) (ns : List Nat) :
    (ns.flatMap (leDigits w)).length = ns.length * w := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
    change (leDigits w n ++ ns.flatMap (leDigits w)).length = (ns.length + 1) * w
    rw [List.length_append, ih]
    simp [leDigits, Nat.add_mul, Nat.add_comm]

private theorem rootP3_uint_size (w : Nat) (ns : List Nat) :
    (Ssz.pack (ns.flatMap (leDigits w)).toByteArray).size = (ns.length * w + 31) / 32 := by
  rw [pack_size, List.size_toByteArray, flatDigits_length]

private theorem rootP3_bool_size (bs : List Bool) :
    (Ssz.pack (bs.map (fun b ↦ if b then (1 : UInt8) else 0)).toByteArray).size =
      (bs.length + 31) / 32 := by
  rw [pack_size, List.size_toByteArray, List.length_map]

private def cap (n : Nat) : Nat := 2 ^ (if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1)

private theorem cap_covers (n : Nat) : n ≤ cap n := by
  unfold cap
  split
  · omega
  · have hu := (Nat.log2_lt (by omega : n - 1 ≠ 0)).mp (Nat.lt_succ_self (Nat.log2 (n - 1)))
    omega

private theorem rootP3_declared_uint_capacity (w limit : Nat) (ns : List Nat)
    (h : Ssz.Rootable (.list (.uint w) limit) (.list (ns.map .uint))) :
    (Ssz.pack (ns.flatMap (leDigits w)).toByteArray).size ≤ cap ((limit * w + 31) / 32) ∧
    ns.length < 2 ^ 256 ∧ w ∈ [1, 2, 4, 8, 16, 32] := by
  have hs := (Ssz.rootable_iff _ _).mp h
  have hn : ns.length ≤ limit := by simpa only [List.length_map] using hs.1
  refine ⟨?_, ?_, hs.2.2.2⟩
  · rw [rootP3_uint_size]
    apply Nat.le_trans _ (cap_covers _)
    have hm := Nat.mul_le_mul_right w hn
    omega
  · simpa only [List.length_map] using hs.2.1

-- The source integer-width unit is 8 * w bits. Only supported byte widths divide 32.
private theorem rootP3_width_units (n w : Nat) (hw : w ∈ [1, 2, 4, 8, 16, 32]) :
    32 % w = 0 ∧ (n + (32 / w) - 1) / (32 / w) = (n * w + 31) / 32 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> omega

private theorem uint_list_chunks (w limit : Nat) (ns : List Nat)
    (h : Ssz.Rootable (.list (.uint w) limit) (.list (ns.map .uint)))
    (cs : Array Base.Bytes32) (hc : Ssz.pack (ns.flatMap (leDigits w)).toByteArray = cs)
    (hp : cs.size ≤ cap ((limit * w + 31) / 32)) (hn : ns.length < 2 ^ 256) :
    Ssz.hashTreeRoot (.list (.uint w) limit) (.list (ns.map .uint)) h =
      Ssz.mixInLength (Ssz.merkleize cs ((limit * w + 31) / 32) hp) ns.length hn := by
  subst cs
  dsimp only [cap, leDigits] at hp ⊢
  have he := Ssz.hashTreeRoot_eq (.list (.uint w) limit) (.list (ns.map .uint)) h
  dsimp only at he
  have hr := he ns rfl hp (by simpa only [List.length_map] using hn)
  simpa only [List.length_map, ← leDigits_function] using hr

private theorem bool_list_chunks (limit : Nat) (bs : List Bool)
    (h : Ssz.Rootable (.list .bool limit) (.list (bs.map .bool)))
    (cs : Array Base.Bytes32)
    (hc : Ssz.pack (bs.map (fun b ↦ if b then (1 : UInt8) else 0)).toByteArray = cs)
    (hp : cs.size ≤ cap ((limit + 31) / 32)) (hn : bs.length < 2 ^ 256) :
    Ssz.hashTreeRoot (.list .bool limit) (.list (bs.map .bool)) h =
      Ssz.mixInLength (Ssz.merkleize cs ((limit + 31) / 32) hp) bs.length hn := by
  subst cs
  dsimp only [cap] at hp ⊢
  have he := Ssz.hashTreeRoot_eq (.list .bool limit) (.list (bs.map .bool)) h
  dsimp only at he
  have hr := he bs rfl hp (by simpa only [List.length_map] using hn)
  simpa only [List.length_map] using hr

private def firstFour64 : List UInt8 :=
  [1] ++ List.replicate 7 0 ++ [2] ++ List.replicate 7 0 ++
    [3] ++ List.replicate 7 0 ++ [4] ++ List.replicate 7 0

private theorem pack_uint64_five :
    Ssz.pack (([1, 2, 3, 4, 5] : List Nat).flatMap (leDigits 8)).toByteArray =
      #[leaf firstFour64 (by decide), leaf [5] (by decide)] := by
  apply packed_inj
  rw [Ssz.pack_toBytes]
  simp only [byteList_roundtrip, List.size_toByteArray, List.map_cons, List.map_nil, leaf_bytes]
  decide

-- R06: 40 bytes form 2 chunks, but the mixed-in count is 5 elements.
private theorem rootP3_uint64_five
    (h : Ssz.Rootable (.list (.uint 8) 5) (.list ([1, 2, 3, 4, 5].map .uint))) :
    Ssz.hashTreeRoot (.list (.uint 8) 5) (.list ([1, 2, 3, 4, 5].map .uint)) h =
      pair (pair (leaf firstFour64 (by decide)) (leaf [5] (by decide)))
        (Base.FixedBytes.ofLeNat 5) := by
  rw [uint_list_chunks 8 5 [1, 2, 3, 4, 5] h
    #[leaf firstFour64 (by decide), leaf [5] (by decide)] pack_uint64_five
    (by decide) (by decide)]
  change Ssz.mixInLength (Ssz.merkleize _ 2 _) 5 _ = _
  erw [ordinary_two, length_pair]

private theorem pack_bool33 :
    Ssz.pack ((List.replicate 33 true).map
      (fun b ↦ if b then (1 : UInt8) else 0)).toByteArray =
      #[leaf (List.replicate 32 1) (by decide), leaf [1] (by decide)] := by
  apply packed_inj
  rw [Ssz.pack_toBytes]
  simp only [byteList_roundtrip, List.size_toByteArray, List.map_cons, List.map_nil, leaf_bytes]
  decide

-- R07: 33 Bool values use 33 bytes. Activity bits would use 5 bytes.
private theorem rootP3_bool33
    (h : Ssz.Rootable (.list .bool 33) (.list ((List.replicate 33 true).map .bool))) :
    Ssz.hashTreeRoot (.list .bool 33) (.list ((List.replicate 33 true).map .bool)) h =
      pair (pair (leaf (List.replicate 32 1) (by decide)) (leaf [1] (by decide)))
        (Base.FixedBytes.ofLeNat 33) := by
  rw [bool_list_chunks 33 (List.replicate 33 true) h
    #[leaf (List.replicate 32 1) (by decide), leaf [1] (by decide)] pack_bool33
    (by decide) (by decide)]
  change Ssz.mixInLength (Ssz.merkleize _ 2 _) 33 _ = _
  erw [ordinary_two, length_pair]

private def Children (ps : List (SszType × SszValue)) (rs : List Base.Bytes32) : Prop :=
  ps.length = rs.length ∧ ∀ p ∈ ps.zip rs,
    ∀ hx : Ssz.Rootable p.1.1 p.1.2, Ssz.hashTreeRoot p.1.1 p.1.2 hx = p.2

private def Composite : SszType → Prop
  | .uint _ | .bool => False
  | .byteVector _ | .byteList _ | .list _ _ | .progressiveList _ |
    .progressiveByteList | .container _ | .progressiveContainer _ _ => True

private theorem composite_list_root (elem : SszType) (limit : Nat) (xs : List SszValue)
    (h : Ssz.Rootable (.list elem limit) (.list xs)) (he : Composite elem)
    (rs : List Base.Bytes32) (hc : Children (xs.map (fun x ↦ (elem, x))) rs)
    (hp : rs.toArray.size ≤ cap limit) (hn : xs.length < 2 ^ 256) :
    Ssz.hashTreeRoot (.list elem limit) (.list xs) h =
      Ssz.mixInLength (Ssz.merkleize rs.toArray limit hp) xs.length hn := by
  cases elem with
  | uint w => exact False.elim he
  | bool => exact False.elim he
  | _ => exact Ssz.hashTreeRoot_eq _ _ h rs hc hp hn

private theorem children_map {α : Type} (as : List α) (elem : SszType)
    (value : α → SszValue) (roots : α → Base.Bytes32)
    (he : ∀ a ∈ as, ∀ hx : Ssz.Rootable elem (value a),
      Ssz.hashTreeRoot elem (value a) hx = roots a) :
    Children (as.map (fun a ↦ (elem, value a))) (as.map roots) := by
  constructor
  · simp
  · intro p hp hx
    rw [List.zip_map'] at hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    exact he a ha hx

private theorem pack_one_byte (b : UInt8) :
    Ssz.pack ([b] : List UInt8).toByteArray = #[leaf [b] (by simp)] := by
  apply packed_inj
  rw [Ssz.pack_toBytes]
  simp only [byteList_roundtrip, List.size_toByteArray, List.length_cons, List.length_nil,
    List.map_cons, List.map_nil, leaf_bytes]
  rfl

private theorem vector_one_byte (b : UInt8)
    (h : Ssz.Rootable (.byteVector 1) (.bytes ([b] : List UInt8).toByteArray)) :
    Ssz.hashTreeRoot (.byteVector 1) (.bytes ([b] : List UInt8).toByteArray) h =
      leaf [b] (by simp) := by
  rw [vector_chunks 1 _ h #[leaf [b] (by simp)] (pack_one_byte b) (by change 1 ≤ 1; decide)]
  exact ordinary_one _ _

private theorem pack_whole_chunk (a : Base.Bytes32) :
    Ssz.pack a.toBytes.toByteArray = #[a] := by
  apply packed_inj
  rw [Ssz.pack_toBytes, Base.Bytes.size_toByteArray, Base.FixedBytes.size_toBytes,
    Base.Bytes.toByteArray_toList]
  change [(a.toBytes.toList.take 32 ++ [])] = [a.toBytes.toList]
  have hl : a.toBytes.toList.length ≤ 32 := by
    rw [Base.Bytes.length_toList, Base.FixedBytes.size_toBytes]
    exact Nat.le_refl _
  rw [List.take_of_length_le hl, List.append_nil]

private def value32 (a : Base.Bytes32) : SszValue := .bytes a.toBytes.toByteArray

private theorem vector_whole_chunk (a : Base.Bytes32)
    (h : Ssz.Rootable (.byteVector 32) (value32 a)) :
    Ssz.hashTreeRoot (.byteVector 32) (value32 a) h = a := by
  erw [vector_chunks 32 _ h #[a] (pack_whole_chunk a) (by change 1 ≤ 1; decide)]
  exact ordinary_one _ _

-- R08: byte vectors, including a 1-byte vector, are composite list elements.
private theorem rootP4_vector1_three
    (h : Ssz.Rootable (.list (.byteVector 1) 3)
      (.list ([1, 2, 3].map (fun b : UInt8 ↦ .bytes [b].toByteArray)))) :
    Ssz.hashTreeRoot (.list (.byteVector 1) 3)
      (.list ([1, 2, 3].map (fun b : UInt8 ↦ .bytes [b].toByteArray))) h =
      pair (pair (pair (leaf [1] (by decide)) (leaf [2] (by decide)))
        (pair (leaf [3] (by decide)) zero)) (Base.FixedBytes.ofLeNat 3) := by
  have hc := children_map ([1, 2, 3] : List UInt8) (.byteVector 1)
    (fun b ↦ .bytes [b].toByteArray) (fun b ↦ leaf [b] (by simp))
    (fun b _ hx ↦ vector_one_byte b hx)
  rw [composite_list_root _ 3 _ h (by trivial)
    [leaf [1] (by decide), leaf [2] (by decide), leaf [3] (by decide)] hc
    (by decide) (by decide)]
  change Ssz.mixInLength (Ssz.merkleize _ 3 _) 3 _ = _
  erw [ordinary_three, length_pair]

-- R09: every byte of both supplied chunks survives, with order and duplicates.
private theorem rootP4_vector32_pair (a b : Base.Bytes32)
    (h : Ssz.Rootable (.list (.byteVector 32) 2) (.list [value32 a, value32 b])) :
    Ssz.hashTreeRoot (.list (.byteVector 32) 2) (.list [value32 a, value32 b]) h =
      pair (pair a b) (Base.FixedBytes.ofLeNat 2) := by
  have hc := children_map [a, b] (.byteVector 32) value32 id
    (fun x _ hx ↦ vector_whole_chunk x hx)
  rw [composite_list_root _ 2 _ h (by trivial) [a, b] hc (by change 2 ≤ 2; decide)
    (by change 2 < 2 ^ 256; decide)]
  change Ssz.mixInLength (Ssz.merkleize _ 2 _) 2 _ = _
  erw [ordinary_two, length_pair]

private theorem rootP4_unused_support :
    Ssz.Rootable (.list (.container [.uint 3]) 0) (.list []) ∧
    Ssz.Rootable (.progressiveList (.container [])) (.list []) ∧
    ¬ Ssz.Rootable (.list (.uint 3) 0) (.list []) := by
  constructor
  · apply (Ssz.rootable_iff _ _).mpr
    exact ⟨by decide, by decide, by simp, trivial⟩
  constructor
  · apply (Ssz.rootable_iff _ _).mpr
    exact ⟨by decide, by simp, trivial⟩
  · intro h
    exact (by decide : ¬3 ∈ [1, 2, 4, 8, 16, 32]) ((Ssz.rootable_iff _ _).mp h).2.2.2

-- R10: no recursive call visits the unsupported unused composite schema.
private theorem rootP4_empty_unused
    (h : Ssz.Rootable (.list (.container [.uint 3]) 0) (.list [])) :
    Ssz.hashTreeRoot (.list (.container [.uint 3]) 0) (.list []) h = pair zero zero := by
  rw [composite_list_root _ 0 [] h (by trivial) [] (by constructor <;> simp)
    (by decide) (by decide)]
  change Ssz.mixInLength (Ssz.merkleize #[] 0 _) 0 _ = _
  erw [ordinary_empty_zero, length_pair, word_zero]

private def progressiveFormula {α : Type} (p : α → α → α) (z : α)
    (d : Nat) (xs : List α) : α :=
  match xs with
  | [] => z
  | x :: xs => p (foldModel p z d ((x::xs).take (2 ^ d)))
      (progressiveFormula p z (d + 2) ((x::xs).drop (2 ^ d)))
termination_by xs.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  have hp := Nat.two_pow_pos d
  omega

private theorem progressive_model (cs : Array Base.Bytes32) (d : Nat) :
    Ssz.merkleizeProgressive cs d = progressiveFormula pair zero d cs.toList := by
  rw [Ssz.merkleizeProgressive_eq]
  cases hx : cs.toList with
  | nil =>
    have he : cs.isEmpty = true := by rw [← Array.isEmpty_toList, hx]; rfl
    simp only [he, reduceIte, progressiveFormula]
    rfl
  | cons x xs =>
    have he : cs.isEmpty = false := by rw [← Array.isEmpty_toList, hx]; rfl
    simp only [he, Bool.false_eq_true, reduceIte]
    rw [progressiveFormula, progressive_model]
    rfl
termination_by cs.size
decreasing_by
  simp only [List.size_toArray, List.length_drop, List.length_cons]
  have hl := congrArg List.length hx
  simp only [Array.length_toList, List.length_cons] at hl
  have hp := Nat.two_pow_pos d
  omega

private theorem formula_one {α : Type} (p : α → α → α) (z a : α) :
    progressiveFormula p z 0 [a] = p a z := by
  rw [progressiveFormula]
  simp [foldModel, progressiveFormula]

private theorem formula_two {α : Type} (p : α → α → α) (z a b : α) :
    progressiveFormula p z 0 [a, b] = p a (p (p (p b z) (p z z)) z) := by
  simp [progressiveFormula, foldModel, List.range_succ]

private theorem formula_three {α : Type} (p : α → α → α) (z a b c : α) :
    progressiveFormula p z 0 [a, b, c] = p a (p (p (p b c) (p z z)) z) := by
  simp [progressiveFormula, foldModel, List.range_succ]

private theorem progressive_empty (d : Nat) : Ssz.merkleizeProgressive #[] d = zero := by
  rw [progressive_model]
  simp only [progressiveFormula]

private theorem progressive_one (a : Base.Bytes32) :
    Ssz.merkleizeProgressive #[a] 0 = pair a zero := by
  rw [progressive_model]
  exact formula_one pair zero a

private theorem progressive_two (a b : Base.Bytes32) :
    Ssz.merkleizeProgressive #[a, b] 0 =
      pair a (pair (pair (pair b zero) (pair zero zero)) zero) := by
  rw [progressive_model]
  exact formula_two pair zero a b

private theorem progressive_three (a b c : Base.Bytes32) :
    Ssz.merkleizeProgressive #[a, b, c] 0 =
      pair a (pair (pair (pair b c) (pair zero zero)) zero) := by
  rw [progressive_model]
  exact formula_three pair zero a b c

private theorem progressive_bytes_chunks (b : ByteArray)
    (h : Ssz.Rootable .progressiveByteList (.bytes b)) (cs : Array Base.Bytes32)
    (hc : Ssz.pack b = cs) (hn : b.size < 2 ^ 256) :
    Ssz.hashTreeRoot .progressiveByteList (.bytes b) h =
      Ssz.mixInLength (Ssz.merkleizeProgressive cs 0) b.size hn := by
  subst cs
  exact Ssz.hashTreeRoot_eq _ _ h hn

-- R11: zero is the contents root; the final empty-list root still includes the mix.
private theorem rootP5_empty_bytes
    (h : Ssz.Rootable .progressiveByteList (.bytes ([] : List UInt8).toByteArray)) :
    Ssz.hashTreeRoot .progressiveByteList (.bytes ([] : List UInt8).toByteArray) h =
      pair zero zero := by
  rw [progressive_bytes_chunks _ h #[] pack_vector0 (by decide), progressive_empty,
    length_pair]
  simp only [List.size_toByteArray, List.length_nil, word_zero]

private theorem rootP5_one_byte
    (h : Ssz.Rootable .progressiveByteList (.bytes ([165] : List UInt8).toByteArray)) :
    Ssz.hashTreeRoot .progressiveByteList (.bytes ([165] : List UInt8).toByteArray) h =
      pair (pair (leaf [165] (by decide)) zero) (Base.FixedBytes.ofLeNat 1) := by
  rw [progressive_bytes_chunks _ h #[leaf [165] (by decide)] pack_vector1 (by decide),
    progressive_one, length_pair]
  rfl

private theorem progressive_uint_chunks (w : Nat) (ns : List Nat)
    (h : Ssz.Rootable (.progressiveList (.uint w)) (.list (ns.map .uint)))
    (cs : Array Base.Bytes32) (hc : Ssz.pack (ns.flatMap (leDigits w)).toByteArray = cs)
    (hn : ns.length < 2 ^ 256) :
    Ssz.hashTreeRoot (.progressiveList (.uint w)) (.list (ns.map .uint)) h =
      Ssz.mixInLength (Ssz.merkleizeProgressive cs 0) ns.length hn := by
  subst cs
  have he := Ssz.hashTreeRoot_eq (.progressiveList (.uint w)) (.list (ns.map .uint)) h
  dsimp only at he
  have hr := he ns rfl (by simpa only [List.length_map] using hn)
  simpa only [List.length_map, ← leDigits_function] using hr

private theorem rootP5_uint64_five
    (h : Ssz.Rootable (.progressiveList (.uint 8)) (.list ([1, 2, 3, 4, 5].map .uint))) :
    Ssz.hashTreeRoot (.progressiveList (.uint 8)) (.list ([1, 2, 3, 4, 5].map .uint)) h =
      pair (pair (leaf firstFour64 (by decide))
        (pair (pair (pair (leaf [5] (by decide)) zero) (pair zero zero)) zero))
        (Base.FixedBytes.ofLeNat 5) := by
  rw [progressive_uint_chunks 8 [1, 2, 3, 4, 5] h
    #[leaf firstFour64 (by decide), leaf [5] (by decide)] pack_uint64_five (by decide)]
  change Ssz.mixInLength (Ssz.merkleizeProgressive _ 0) 5 _ = _
  erw [progressive_two, length_pair]

private theorem composite_progressive_root (elem : SszType) (xs : List SszValue)
    (h : Ssz.Rootable (.progressiveList elem) (.list xs)) (he : Composite elem)
    (rs : List Base.Bytes32) (hc : Children (xs.map (fun x ↦ (elem, x))) rs)
    (hn : xs.length < 2 ^ 256) :
    Ssz.hashTreeRoot (.progressiveList elem) (.list xs) h =
      Ssz.mixInLength (Ssz.merkleizeProgressive rs.toArray 0) xs.length hn := by
  cases elem with
  | uint w => exact False.elim he
  | bool => exact False.elim he
  | _ => exact Ssz.hashTreeRoot_eq _ _ h rs hc hn

private theorem rootP5_empty_unused
    (h : Ssz.Rootable (.progressiveList (.container [])) (.list [])) :
    Ssz.hashTreeRoot (.progressiveList (.container [])) (.list []) h = pair zero zero := by
  rw [composite_progressive_root _ [] h (by trivial) [] (by constructor <;> simp)
    (by decide), progressive_empty, length_pair]
  simp only [List.length_nil, word_zero]

-- R12: full symbolic recurrence, covering 0/1/5/6/21/22 ordered chunk boundaries.
private theorem rootP5_boundaries (cs : List Base.Bytes32)
    (_boundary : cs.length ∈ [0, 1, 5, 6, 21, 22])
    (h : Ssz.Rootable (.progressiveList (.byteVector 32)) (.list (cs.map value32))) :
    Ssz.hashTreeRoot (.progressiveList (.byteVector 32)) (.list (cs.map value32)) h =
      pair (progressiveFormula pair zero 0 cs) (Base.FixedBytes.ofLeNat cs.length) := by
  have hc := children_map cs (.byteVector 32) value32 id
    (fun x _ hx ↦ vector_whole_chunk x hx)
  have hs := (Ssz.rootable_iff _ _).mp h
  have hn : (cs.map value32).length < 2 ^ 256 := hs.1
  have hr := composite_progressive_root (.byteVector 32) (cs.map value32) h (by trivial)
    cs (by simpa only [List.map_map, List.map_id, Function.comp_def] using hc) hn
  rw [progressive_model, length_pair] at hr
  simpa only [List.length_map, List.toList_toArray] using hr

private theorem fields_root (fields : List SszType) (xs : List SszValue)
    (h : Ssz.Rootable (.container fields) (.container xs))
    (rs : List Base.Bytes32) (hc : Children (fields.zip xs) rs)
    (hp : rs.toArray.size ≤ cap fields.length) :
    Ssz.hashTreeRoot (.container fields) (.container xs) h =
      Ssz.merkleize rs.toArray fields.length hp := Ssz.hashTreeRoot_eq _ _ h rs hc hp

-- R13: exact ordinary field order; no length mix-in accompanies the 3 fields.
private theorem rootP6_fields
    (h : Ssz.Rootable (.container [.uint 1, .uint 2, .bool])
      (.container [.uint 1, .uint 258, .bool true])) :
    Ssz.hashTreeRoot (.container [.uint 1, .uint 2, .bool])
      (.container [.uint 1, .uint 258, .bool true]) h =
      pair (pair (Base.FixedBytes.ofLeNat 1) (Base.FixedBytes.ofLeNat 258))
        (pair (Base.FixedBytes.ofLeNat 1) zero) := by
  have hc : Children
      (([.uint 1, .uint 2, .bool] : List SszType).zip [.uint 1, .uint 258, .bool true])
      [Base.FixedBytes.ofLeNat 1, Base.FixedBytes.ofLeNat 258, Base.FixedBytes.ofLeNat 1] := by
    constructor
    · rfl
    · intro p hp hx
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact scalar_root 1 1 hx
      · exact scalar_root 2 258 hx
      · exact bool_root true hx
  rw [fields_root _ _ h _ hc (by decide)]
  change Ssz.merkleize _ 3 _ = _
  erw [ordinary_three]

private theorem rootP6_exact_arity (fields : List SszType) (xs : List SszValue)
    (h : Ssz.Rootable (.container fields) (.container xs)) :
    fields ≠ [] ∧ fields.length = xs.length ∧
      ∀ p ∈ fields.zip xs, Ssz.Rootable p.1 p.2 := (Ssz.rootable_iff _ _).mp h

private theorem rootP6_wrong_arity (fields : List SszType) (xs : List SszValue)
    (hn : fields.length ≠ xs.length) :
    ¬ Ssz.Rootable (.container fields) (.container xs) := by
  intro h
  exact hn ((Ssz.rootable_iff _ _).mp h).2.1

private def slots (mask : List Bool) (rs : List Base.Bytes32) : Array Base.Bytes32 :=
  ((List.range mask.length).map (fun i ↦
    if mask.getD i false then rs.getD ((mask.take i).filter id).length zero else zero)).toArray

private def scan (mask : List Bool) (rs : List Base.Bytes32) : List Base.Bytes32 :=
  match mask with
  | [] => []
  | false :: mask => zero :: scan mask rs
  | true :: mask => rs.getD 0 zero :: scan mask rs.tail

private theorem scan_length (mask : List Bool) (rs : List Base.Bytes32) :
    (scan mask rs).length = mask.length := by
  induction mask generalizing rs with
  | nil => rfl
  | cons b mask ih => cases b <;> simp only [scan, List.length_cons, ih]

private theorem tail_getD {α : Type} (xs : List α) (i : Nat) (z : α) :
    xs.tail.getD i z = xs.getD (i + 1) z := by cases xs <;> simp

private theorem scan_getD (mask : List Bool) (rs : List Base.Bytes32) (i : Nat) :
    (scan mask rs).getD i zero =
      if mask.getD i false then rs.getD ((mask.take i).filter id).length zero else zero := by
  induction mask generalizing rs i with
  | nil => simp [scan]
  | cons b mask ih =>
    cases i with
    | zero => cases b <;> simp only [scan, List.getD_cons_zero, List.take_zero,
        List.filter_nil, List.length_nil, Bool.false_eq_true, reduceIte]
    | succ i =>
      cases b <;> rw [scan, List.getD_cons_succ, ih] <;>
        simp only [List.getD_cons_succ, List.take_succ_cons, List.filter_cons, id_eq,
          Bool.false_eq_true, reduceIte, List.length_cons, tail_getD]

private theorem rootP7_scan_model (mask : List Bool) (rs : List Base.Bytes32) :
    (scan mask rs).toArray = slots mask rs := by
  apply congrArg List.toArray
  apply List.ext_getElem
  · simp only [scan_length, List.length_map, List.length_range]
  · intro i hi hj
    rw [List.getElem_eq_getD zero, scan_getD]
    simp only [List.getElem_map, List.getElem_range]

private theorem rootP7_slots_length (mask : List Bool) (rs : List Base.Bytes32) :
    (slots mask rs).size = mask.length := by
  rw [← rootP7_scan_model, List.size_toArray, scan_length]

private theorem rank_lt_population (mask : List Bool) (i : Nat)
    (hi : mask.getD i false = true) :
    ((mask.take i).filter id).length < (mask.filter id).length := by
  induction mask generalizing i with
  | nil => simp at hi
  | cons b mask ih =>
    cases i with
    | zero =>
      simp only [List.getD_cons_zero] at hi
      subst b
      simp
    | succ i =>
      simp only [List.getD_cons_succ] at hi
      have h := ih i hi
      cases b <;> simp_all

private theorem rootP7_actual_rank (mask : List Bool) (fields : List SszType)
    (xs : List SszValue) (h : Ssz.Rootable (.progressiveContainer mask fields) (.container xs))
    (rs : List Base.Bytes32) (hc : Children (fields.zip xs) rs) (i : Nat)
    (hi : mask.getD i false = true) :
    ((mask.take i).filter id).length < rs.length := by
  have hs := (Ssz.rootable_iff _ _).mp h
  have hl := hc.1
  simp only [List.length_zip] at hl
  have hp := hs.2.2.1
  have ha := hs.2.2.2.1
  have hr := rank_lt_population mask i hi
  omega

private theorem progressive_fields_root (mask : List Bool) (fields : List SszType)
    (xs : List SszValue) (h : Ssz.Rootable (.progressiveContainer mask fields) (.container xs))
    (rs : List Base.Bytes32) (hc : Children (fields.zip xs) rs) (hm : mask.length ≤ 256) :
    Ssz.hashTreeRoot (.progressiveContainer mask fields) (.container xs) h =
      Ssz.mixInActiveFields (Ssz.merkleizeProgressive (slots mask rs) 0) mask hm :=
  Ssz.hashTreeRoot_eq _ _ h rs hc hm

private theorem activity_pair (root : Base.Bytes32) (mask : List Bool) (hm : mask.length ≤ 256) :
    Ssz.mixInActiveFields root mask hm = pair root
      (Base.FixedBytes.ofLeNat (mask.foldr (fun b n ↦ (if b then 1 else 0) + 2 * n) 0)) :=
  Ssz.mixInActiveFields_eq root mask hm

private theorem fields32_children (rs : List Base.Bytes32) :
    Children ((List.replicate rs.length (.byteVector 32)).zip (rs.map value32)) rs := by
  induction rs with
  | nil => constructor <;> simp
  | cons r rs ih =>
    constructor
    · simp
    · intro p hp hx
      simp only [List.length_cons, List.replicate_succ, List.map_cons, List.zip_cons_cons,
        List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact vector_whole_chunk r hx
      · exact ih.2 p hp hx

private theorem progressive_fields32 (mask : List Bool) (rs : List Base.Bytes32)
    (h : Ssz.Rootable (.progressiveContainer mask (List.replicate rs.length (.byteVector 32)))
      (.container (rs.map value32))) (hm : mask.length ≤ 256) :
    Ssz.hashTreeRoot (.progressiveContainer mask (List.replicate rs.length (.byteVector 32)))
      (.container (rs.map value32)) h =
      Ssz.mixInActiveFields (Ssz.merkleizeProgressive (slots mask rs) 0) mask hm :=
  progressive_fields_root mask _ _ h rs (fields32_children rs) hm

private theorem slots_sparse (a b : Base.Bytes32) :
    slots [true, false, true] [a, b] = #[a, zero, b] := by
  rw [← rootP7_scan_model]
  rfl

private theorem slots_leading (a : Base.Bytes32) :
    slots [false, true] [a] = #[zero, a] := by
  rw [← rootP7_scan_model]
  rfl

private theorem slots_three (a b c : Base.Bytes32) :
    slots [true, true, true] [a, b, c] = #[a, b, c] := by
  rw [← rootP7_scan_model]
  rfl

-- R14: exactly [a, Z, b], and low-first activity 5. There are 3 contents slots.
private theorem rootP7_sparse (a b : Base.Bytes32)
    (h : Ssz.Rootable (.progressiveContainer [true, false, true] [.byteVector 32, .byteVector 32])
      (.container [value32 a, value32 b])) :
    Ssz.hashTreeRoot (.progressiveContainer [true, false, true] [.byteVector 32, .byteVector 32])
      (.container [value32 a, value32 b]) h =
      pair (pair a (pair (pair (pair zero b) (pair zero zero)) zero))
        (Base.FixedBytes.ofLeNat 5) := by
  erw [progressive_fields32 [true, false, true] [a, b] h (by decide), slots_sparse,
    progressive_three, activity_pair]
  rfl

-- R15: leading false and the field order with all 3 bits true have complete root equations.
private theorem rootP7_leading (a : Base.Bytes32)
    (h : Ssz.Rootable (.progressiveContainer [false, true] [.byteVector 32])
      (.container [value32 a])) :
    Ssz.hashTreeRoot (.progressiveContainer [false, true] [.byteVector 32])
      (.container [value32 a]) h =
      pair (pair zero (pair (pair (pair a zero) (pair zero zero)) zero))
        (Base.FixedBytes.ofLeNat 2) := by
  erw [progressive_fields32 [false, true] [a] h (by decide), slots_leading,
    progressive_two, activity_pair]
  rfl

private theorem rootP7_alltrue3 (a b c : Base.Bytes32)
    (h : Ssz.Rootable (.progressiveContainer [true, true, true]
      [.byteVector 32, .byteVector 32, .byteVector 32]) (.container [value32 a, value32 b,
          value32 c]))
        :
    Ssz.hashTreeRoot (.progressiveContainer [true, true, true]
      [.byteVector 32, .byteVector 32, .byteVector 32]) (.container [value32 a, value32 b,
          value32 c])
        h =
      pair (pair a (pair (pair (pair b c) (pair zero zero)) zero))
        (Base.FixedBytes.ofLeNat 7) := by
  erw [progressive_fields32 [true, true, true] [a, b, c] h (by decide), slots_three,
    progressive_three, activity_pair]
  rfl

private def lastMask (width : Nat) : List Bool := List.replicate (width - 1) false ++ [true]

private theorem slots_last (n : Nat) (a : Base.Bytes32) :
    slots (List.replicate n false ++ [true]) [a] =
      (List.replicate n zero ++ [a]).toArray := by
  rw [← rootP7_scan_model]
  apply congrArg List.toArray
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, scan, ih]

private theorem last_mask_number (n : Nat) :
    (List.replicate n false ++ [true]).foldr
      (fun b n ↦ (if b then 1 else 0) + 2 * n) 0 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, List.foldr_cons,
      Bool.false_eq_true, reduceIte, Nat.zero_add]
    rw [ih, Nat.pow_succ, Nat.mul_comm]

-- R16: contents retain the exact finite width, with a single final active root.
private theorem rootP7_wide (width : Nat) (_hw : width ∈ [255, 256]) (a : Base.Bytes32)
    (h : Ssz.Rootable (.progressiveContainer (lastMask width) [.byteVector 32])
      (.container [value32 a])) :
    Ssz.hashTreeRoot (.progressiveContainer (lastMask width) [.byteVector 32])
      (.container [value32 a]) h =
      pair (progressiveFormula pair zero 0 (List.replicate (width - 1) zero ++ [a]))
        (Base.FixedBytes.ofLeNat (2 ^ (width - 1))) := by
  have hm := ((Ssz.rootable_iff _ _).mp h).2.1
  dsimp only [lastMask] at hm
  erw [progressive_fields32 (lastMask width) [a] h hm]
  dsimp only [lastMask]
  rw [slots_last, progressive_model, activity_pair, last_mask_number]

private theorem rootP7_activity_bytes255 :
    (Base.FixedBytes.ofLeNat (2 ^ 254) : Base.Bytes32).toBytes.toList =
      List.replicate 31 0 ++ [64] := by
  rw [Base.FixedBytes.toBytes_ofLeNat, Base.Bytes.toList_generate]
  decide

private theorem rootP7_activity_bytes256 :
    (Base.FixedBytes.ofLeNat (2 ^ 255) : Base.Bytes32).toBytes.toList =
      List.replicate 31 0 ++ [128] := by
  rw [Base.FixedBytes.toBytes_ofLeNat, Base.Bytes.toList_generate]
  decide

private theorem vector32_support (a : Base.Bytes32) : Ssz.Rootable (.byteVector 32) (value32 a) :=
  by
  apply (Ssz.rootable_iff _ _).mpr
  exact (Base.Bytes.size_toByteArray _).trans (Base.FixedBytes.size_toBytes _)

private theorem rootP7_wide_support (width : Nat) (hw : width ∈ [255, 256]) (a : Base.Bytes32) :
    Ssz.Rootable (.progressiveContainer (lastMask width) [.byteVector 32])
      (.container [value32 a]) := by
  have hb : 1 ≤ width ∧ width ≤ 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    omega
  apply (Ssz.rootable_iff _ _).mpr
  refine ⟨?_, ?_, ?_, rfl, ?_⟩
  · simp [lastMask]
  · simp only [lastMask, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil]
    omega
  · simp [lastMask]
  · intro p hp
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false]
      at hp
    subst p
    exact vector32_support a

private theorem rootP7_excluded (mask : List Bool) (fields : List SszType) (xs : List SszValue) :
    ¬ Ssz.Rootable (.progressiveContainer [] fields) (.container xs) ∧
    ¬ Ssz.Rootable (.progressiveContainer (mask ++ [false]) fields) (.container xs) ∧
    ¬ Ssz.Rootable (.progressiveContainer (lastMask 257) fields) (.container xs) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; have hs := ((Ssz.rootable_iff _ _).mp h).1; simp at hs
  · intro h; have hs := ((Ssz.rootable_iff _ _).mp h).1; simp at hs
  · intro h
    have hs := ((Ssz.rootable_iff _ _).mp h).2.1
    simp only [lastMask, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil] at hs
    omega

private def RootLaw (F : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Base.Bytes32) :
    Prop :=
  ∀ (t : SszType) (v : SszValue) (h : Ssz.Rootable t v),
  let R := F
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

private def ChildGraph
    (F : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Base.Bytes32)
    (ps : List (SszType × SszValue)) (rs : List Base.Bytes32) : Prop :=
  ps.length = rs.length ∧ ∀ p ∈ ps.zip rs,
    ∀ hx : Ssz.Rootable p.1.1 p.1.2, F p.1.1 p.1.2 hx = p.2

private def actualRoots
    (F : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Base.Bytes32)
    (ps : List (SszType × SszValue)) (hs : ∀ p ∈ ps, Ssz.Rootable p.1 p.2) : List Base.Bytes32 :=
  ps.attach.map (fun p ↦ F p.val.1 p.val.2 (hs p.val p.property))

private theorem actualRoots_graph
    (F : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Base.Bytes32)
    (ps : List (SszType × SszValue)) (hs : ∀ p ∈ ps, Ssz.Rootable p.1 p.2) :
    ChildGraph F ps (actualRoots F ps hs) := by
  induction ps with
  | nil => constructor <;> simp [actualRoots]
  | cons p ps ih =>
    constructor
    · simp [actualRoots]
    · intro q hq hx
      simp only [actualRoots, List.attach_cons, List.map_cons, List.map_map,
        List.zip_cons_cons, List.mem_cons] at hq
      rcases hq with rfl | hq
      · rfl
      · exact (ih (fun x hx ↦ hs x (List.mem_cons_of_mem _ hx))).2 q hq hx

private theorem zip_left_mem {α β : Type} {ps : List α} {rs : List β} {q : α × β}
    (h : q ∈ ps.zip rs) : q.1 ∈ ps := by
  induction ps generalizing rs with
  | nil => simp at h
  | cons p ps ih =>
    cases rs with
    | nil => simp at h
    | cons r rs =>
      simp only [List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem p (ih h)

private theorem zip_right_mem {α β : Type} {ps : List α} {rs : List β} {q : α × β}
    (h : q ∈ ps.zip rs) : q.2 ∈ rs := by
  induction ps generalizing rs with
  | nil => simp at h
  | cons p ps ih =>
    cases rs with
    | nil => simp at h
    | cons r rs =>
      simp only [List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem r (ih h)

private theorem graph_transport
    (F : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Base.Bytes32)
    (xs : List SszValue)
    (ih : ∀ x ∈ xs, ∀ t (hx : Ssz.Rootable t x), F t x hx = Ssz.hashTreeRoot t x hx)
    (ps : List (SszType × SszValue)) (hm : ∀ p ∈ ps, p.2 ∈ xs)
    (rs : List Base.Bytes32) (hc : ChildGraph Ssz.hashTreeRoot ps rs) :
    ChildGraph F ps rs := by
  refine ⟨hc.1, ?_⟩
  intro p hp hx
  exact (ih p.1.2 (hm p.1 (zip_left_mem hp)) p.1.1 hx).trans (hc.2 p hp hx)

private theorem rootP8_uint_projection (w : Nat) (xs : List SszValue)
    (hs : ∀ x ∈ xs, Ssz.Rootable (.uint w) x) :
    ∃ ns : List Nat, xs = ns.map .uint := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    have hx := hs x (List.mem_cons_self)
    have ht := ih (fun y hy ↦ hs y (List.mem_cons_of_mem _ hy))
    cases x with
    | uint n =>
      obtain ⟨ns, he⟩ := ht
      exact ⟨n::ns, by simp only [List.map_cons, he]⟩
    | _ => exact False.elim ((Ssz.rootable_iff _ _).mp hx)

private theorem rootP8_bool_projection (xs : List SszValue)
    (hs : ∀ x ∈ xs, Ssz.Rootable .bool x) :
    ∃ bs : List Bool, xs = bs.map .bool := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    have hx := hs x (List.mem_cons_self)
    have ht := ih (fun y hy ↦ hs y (List.mem_cons_of_mem _ hy))
    cases x with
    | bool b =>
      obtain ⟨bs, he⟩ := ht
      exact ⟨b::bs, by simp only [List.map_cons, he]⟩
    | _ => exact False.elim ((Ssz.rootable_iff _ _).mp hx)

private theorem rootP8_pack_capacity (b : ByteArray) (limit : Nat) (h : b.size ≤ limit) :
    (Ssz.pack b).size ≤ cap ((limit + 31) / 32) := by
  rw [pack_size]
  apply Nat.le_trans _ (cap_covers _)
  omega

private theorem rootP8_children_available (ps : List (SszType × SszValue))
    (hs : ∀ p ∈ ps, Ssz.Rootable p.1 p.2) :
    ∃ rs : List Base.Bytes32, Children ps rs :=
  ⟨actualRoots Ssz.hashTreeRoot ps hs, actualRoots_graph Ssz.hashTreeRoot ps hs⟩

private theorem rootP8_proof_independent (t : SszType) (v : SszValue)
    (h k : Ssz.Rootable t v) : Ssz.hashTreeRoot t v h = Ssz.hashTreeRoot t v k := rfl

private theorem rootP8_whole_law : RootLaw Ssz.hashTreeRoot := Ssz.hashTreeRoot_eq

private theorem law_composite_list
    (F : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Base.Bytes32) (law : RootLaw F)
    (elem : SszType) (limit : Nat) (xs : List SszValue)
    (h : Ssz.Rootable (.list elem limit) (.list xs)) (he : Composite elem)
    (rs : List Base.Bytes32) (hc : ChildGraph F (xs.map (fun x ↦ (elem, x))) rs)
    (hp : rs.toArray.size ≤ cap limit) (hn : xs.length < 2 ^ 256) :
    F (.list elem limit) (.list xs) h =
      Ssz.mixInLength (Ssz.merkleize rs.toArray limit hp) xs.length hn := by
  cases elem with
  | uint w => exact False.elim he
  | bool => exact False.elim he
  | _ => exact law _ _ h rs hc hp hn

private theorem law_composite_progressive
    (F : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Base.Bytes32) (law : RootLaw F)
    (elem : SszType) (xs : List SszValue)
    (h : Ssz.Rootable (.progressiveList elem) (.list xs)) (he : Composite elem)
    (rs : List Base.Bytes32) (hc : ChildGraph F (xs.map (fun x ↦ (elem, x))) rs)
    (hn : xs.length < 2 ^ 256) :
    F (.progressiveList elem) (.list xs) h =
      Ssz.mixInLength (Ssz.merkleizeProgressive rs.toArray 0) xs.length hn := by
  cases elem with
  | uint w => exact False.elim he
  | bool => exact False.elim he
  | _ => exact law _ _ h rs hc hn

private theorem determine_uint
    (F : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Base.Bytes32) (law : RootLaw F)
    (w n : Nat) (h : Ssz.Rootable (.uint w) (.uint n)) :
    F (.uint w) (.uint n) h = Ssz.hashTreeRoot (.uint w) (.uint n) h := by
  have hf : F (.uint w) (.uint n) h = Base.FixedBytes.ofLeNat n := law _ _ h
  exact hf.trans (scalar_root w n h).symm

private theorem determine_bool
    (F : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Base.Bytes32) (law : RootLaw F)
    (b : Bool) (h : Ssz.Rootable .bool (.bool b)) :
    F .bool (.bool b) h = Ssz.hashTreeRoot .bool (.bool b) h := by
  have hf : F .bool (.bool b) h = Base.FixedBytes.ofLeNat (if b then 1 else 0) := law _ _ h
  exact hf.trans (bool_root b h).symm

private theorem determine_vector
    (F : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Base.Bytes32) (law : RootLaw F)
    (n : Nat) (b : ByteArray) (h : Ssz.Rootable (.byteVector n) (.bytes b)) :
    F (.byteVector n) (.bytes b) h = Ssz.hashTreeRoot (.byteVector n) (.bytes b) h := by
  have hp := rootP8_pack_capacity b n (Nat.le_of_eq ((Ssz.rootable_iff _ _).mp h))
  have hf := law (.byteVector n) (.bytes b) h hp
  exact hf.trans (vector_root n b h hp).symm

private theorem determine_bytes
    (F : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Base.Bytes32) (law : RootLaw F)
    (limit : Nat) (b : ByteArray) (h : Ssz.Rootable (.byteList limit) (.bytes b)) :
    F (.byteList limit) (.bytes b) h = Ssz.hashTreeRoot (.byteList limit) (.bytes b) h := by
  have hs := (Ssz.rootable_iff _ _).mp h
  have hp := rootP8_pack_capacity b limit hs.1
  have hf := law (.byteList limit) (.bytes b) h hp hs.2
  exact hf.trans (Ssz.hashTreeRoot_eq _ _ h hp hs.2).symm

private theorem determine_progressive_bytes
    (F : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Base.Bytes32) (law : RootLaw F)
    (b : ByteArray) (h : Ssz.Rootable .progressiveByteList (.bytes b)) :
    F .progressiveByteList (.bytes b) h = Ssz.hashTreeRoot .progressiveByteList (.bytes b) h := by
  have hn := (Ssz.rootable_iff _ _).mp h
  have hf := law .progressiveByteList (.bytes b) h hn
  exact hf.trans (Ssz.hashTreeRoot_eq _ _ h hn).symm

private theorem determine_composite_list
    (F : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Base.Bytes32) (law : RootLaw F)
    (elem : SszType) (limit : Nat) (xs : List SszValue)
    (ih : ∀ x ∈ xs, ∀ t (hx : Ssz.Rootable t x), F t x hx = Ssz.hashTreeRoot t x hx)
    (h : Ssz.Rootable (.list elem limit) (.list xs)) (he : Composite elem) :
    F (.list elem limit) (.list xs) h = Ssz.hashTreeRoot (.list elem limit) (.list xs) h := by
  have hs := (Ssz.rootable_iff _ _).mp h
  let ps := xs.map (fun x ↦ (elem, x))
  have hps : ∀ p ∈ ps, Ssz.Rootable p.1 p.2 := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    exact hs.2.2.1 x hx
  let rs := actualRoots Ssz.hashTreeRoot ps hps
  have hr := actualRoots_graph Ssz.hashTreeRoot ps hps
  have hf := graph_transport F xs ih ps (by
    intro p hp; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp; exact hx) rs hr
  have hp : rs.toArray.size ≤ cap limit := by
    rw [List.size_toArray, ← hr.1]
    simp only [ps, List.length_map]
    exact Nat.le_trans hs.1 (cap_covers limit)
  exact (law_composite_list F law elem limit xs h he rs hf hp hs.2.1).trans
    (composite_list_root elem limit xs h he rs hr hp hs.2.1).symm

private theorem determine_list
    (F : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Base.Bytes32) (law : RootLaw F)
    (elem : SszType) (limit : Nat) (xs : List SszValue)
    (ih : ∀ x ∈ xs, ∀ t (hx : Ssz.Rootable t x), F t x hx = Ssz.hashTreeRoot t x hx)
    (h : Ssz.Rootable (.list elem limit) (.list xs)) :
    F (.list elem limit) (.list xs) h = Ssz.hashTreeRoot (.list elem limit) (.list xs) h := by
  have hs := (Ssz.rootable_iff _ _).mp h
  cases elem with
  | uint w =>
    obtain ⟨ns, he⟩ := rootP8_uint_projection w xs hs.2.2.1
    subst xs
    have hp := (rootP3_declared_uint_capacity w limit ns h).1
    have hf := law (.list (.uint w) limit) (.list (ns.map .uint)) h ns rfl hp hs.2.1
    have hr := Ssz.hashTreeRoot_eq (.list (.uint w) limit) (.list (ns.map .uint)) h
      ns rfl hp hs.2.1
    exact hf.trans hr.symm
  | bool =>
    obtain ⟨bs, he⟩ := rootP8_bool_projection xs hs.2.2.1
    subst xs
    have hp : (Ssz.pack (bs.map (fun b ↦ if b then (1 : UInt8) else 0)).toByteArray).size ≤
        cap ((limit + 31) / 32) := by
      rw [rootP3_bool_size]
      apply Nat.le_trans _ (cap_covers _)
      have hl := hs.1
      simp only [List.length_map] at hl
      omega
    have hf := law (.list .bool limit) (.list (bs.map .bool)) h bs rfl hp hs.2.1
    have hr := Ssz.hashTreeRoot_eq (.list .bool limit) (.list (bs.map .bool)) h
      bs rfl hp hs.2.1
    exact hf.trans hr.symm
  | _ => exact determine_composite_list F law _ limit xs ih h (by trivial)

private theorem determine_composite_progressive
    (F : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Base.Bytes32) (law : RootLaw F)
    (elem : SszType) (xs : List SszValue)
    (ih : ∀ x ∈ xs, ∀ t (hx : Ssz.Rootable t x), F t x hx = Ssz.hashTreeRoot t x hx)
    (h : Ssz.Rootable (.progressiveList elem) (.list xs)) (he : Composite elem) :
    F (.progressiveList elem) (.list xs) h = Ssz.hashTreeRoot (.progressiveList elem) (.list xs) h
      := by
  have hs := (Ssz.rootable_iff _ _).mp h
  let ps := xs.map (fun x ↦ (elem, x))
  have hps : ∀ p ∈ ps, Ssz.Rootable p.1 p.2 := by
    intro p hp; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp; exact hs.2.1 x hx
  let rs := actualRoots Ssz.hashTreeRoot ps hps
  have hr := actualRoots_graph Ssz.hashTreeRoot ps hps
  have hf := graph_transport F xs ih ps (by
    intro p hp; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp; exact hx) rs hr
  exact (law_composite_progressive F law elem xs h he rs hf hs.1).trans
    (composite_progressive_root elem xs h he rs hr hs.1).symm

private theorem determine_progressive_list
    (F : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Base.Bytes32) (law : RootLaw F)
    (elem : SszType) (xs : List SszValue)
    (ih : ∀ x ∈ xs, ∀ t (hx : Ssz.Rootable t x), F t x hx = Ssz.hashTreeRoot t x hx)
    (h : Ssz.Rootable (.progressiveList elem) (.list xs)) :
    F (.progressiveList elem) (.list xs) h = Ssz.hashTreeRoot (.progressiveList elem) (.list xs) h
      := by
  have hs := (Ssz.rootable_iff _ _).mp h
  cases elem with
  | uint w =>
    obtain ⟨ns, he⟩ := rootP8_uint_projection w xs hs.2.1
    subst xs
    have hf := law (.progressiveList (.uint w)) (.list (ns.map .uint)) h ns rfl hs.1
    have hr := Ssz.hashTreeRoot_eq (.progressiveList (.uint w)) (.list (ns.map .uint)) h
      ns rfl hs.1
    exact hf.trans hr.symm
  | bool =>
    obtain ⟨bs, he⟩ := rootP8_bool_projection xs hs.2.1
    subst xs
    have hf := law (.progressiveList .bool) (.list (bs.map .bool)) h bs rfl hs.1
    have hr := Ssz.hashTreeRoot_eq (.progressiveList .bool) (.list (bs.map .bool)) h
      bs rfl hs.1
    exact hf.trans hr.symm
  | _ => exact determine_composite_progressive F law _ xs ih h (by trivial)

private theorem determine_fields
    (F : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Base.Bytes32) (law : RootLaw F)
    (fields : List SszType) (xs : List SszValue)
    (ih : ∀ x ∈ xs, ∀ t (hx : Ssz.Rootable t x), F t x hx = Ssz.hashTreeRoot t x hx)
    (h : Ssz.Rootable (.container fields) (.container xs)) :
    F (.container fields) (.container xs) h = Ssz.hashTreeRoot (.container fields) (.container xs)
      h := by
  have hs := (Ssz.rootable_iff _ _).mp h
  let ps := fields.zip xs
  let rs := actualRoots Ssz.hashTreeRoot ps hs.2.2
  have hr := actualRoots_graph Ssz.hashTreeRoot ps hs.2.2
  have hf := graph_transport F xs ih ps (fun _ hp ↦ zip_right_mem hp) rs hr
  have hp : rs.toArray.size ≤ cap fields.length := by
    rw [List.size_toArray, ← hr.1]
    apply Nat.le_trans _ (cap_covers _)
    simp only [ps, List.length_zip]
    exact Nat.min_le_left _ _
  exact (law (.container fields) (.container xs) h rs hf hp).trans
    (Ssz.hashTreeRoot_eq _ _ h rs hr hp).symm

private theorem determine_progressive_fields
    (F : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Base.Bytes32) (law : RootLaw F)
    (mask : List Bool) (fields : List SszType) (xs : List SszValue)
    (ih : ∀ x ∈ xs, ∀ t (hx : Ssz.Rootable t x), F t x hx = Ssz.hashTreeRoot t x hx)
    (h : Ssz.Rootable (.progressiveContainer mask fields) (.container xs)) :
    F (.progressiveContainer mask fields) (.container xs) h =
      Ssz.hashTreeRoot (.progressiveContainer mask fields) (.container xs) h := by
  have hs := (Ssz.rootable_iff _ _).mp h
  let ps := fields.zip xs
  let rs := actualRoots Ssz.hashTreeRoot ps hs.2.2.2.2
  have hr := actualRoots_graph Ssz.hashTreeRoot ps hs.2.2.2.2
  have hf := graph_transport F xs ih ps (fun _ hp ↦ zip_right_mem hp) rs hr
  exact (law (.progressiveContainer mask fields) (.container xs) h rs hf hs.2.1).trans
    (Ssz.hashTreeRoot_eq _ _ h rs hr hs.2.1).symm

-- Complete recursive equation determines every supported result, by proper actual children.
private theorem rootP8_determined
    (F : (t : SszType) → (v : SszValue) → Ssz.Rootable t v → Base.Bytes32) (law : RootLaw F)
    (t : SszType) (v : SszValue) (h : Ssz.Rootable t v) : F t v h = Ssz.hashTreeRoot t v h := by
  have allValues : ∀ v : SszValue, ∀ t (h : Ssz.Rootable t v), F t v h = Ssz.hashTreeRoot t v h :=
    by
    intro v
    refine SszValue.rec
      (motive_1 := fun v ↦ ∀ t (h : Ssz.Rootable t v), F t v h = Ssz.hashTreeRoot t v h)
      (motive_2 := fun xs ↦ ∀ x ∈ xs, ∀ t (h : Ssz.Rootable t x), F t x h = Ssz.hashTreeRoot t x h)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ v
    · intro n t h
      cases t <;> first
        | exact False.elim ((Ssz.rootable_iff _ _).mp h)
        | exact determine_uint F law _ n h
    · intro b t h
      cases t <;> first
        | exact False.elim ((Ssz.rootable_iff _ _).mp h)
        | exact determine_bool F law b h
    · intro b t h
      cases t <;> first
        | exact False.elim ((Ssz.rootable_iff _ _).mp h)
        | exact determine_vector F law _ b h
        | exact determine_bytes F law _ b h
        | exact determine_progressive_bytes F law b h
    · intro xs ih t h
      cases t <;> first
        | exact False.elim ((Ssz.rootable_iff _ _).mp h)
        | exact determine_list F law _ _ xs ih h
        | exact determine_progressive_list F law _ xs ih h
    · intro xs ih t h
      cases t <;> first
        | exact False.elim ((Ssz.rootable_iff _ _).mp h)
        | exact determine_fields F law _ xs ih h
        | exact determine_progressive_fields F law _ _ xs ih h
    · intro x hx
      exact False.elim (List.not_mem_nil hx)
    · intro x xs ihx ihxs y hy t h
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ihx t h
      · exact ihxs y hy t h
  exact allValues v t h

-- R17: both inner byte counts 0/1 and outer element count 2 survive in full.
private theorem rootP8_nested
    (h : Ssz.Rootable (.progressiveList .progressiveByteList)
      (.list [.bytes ([] : List UInt8).toByteArray, .bytes ([165] : List UInt8).toByteArray])) :
    Ssz.hashTreeRoot (.progressiveList .progressiveByteList)
      (.list [.bytes ([] : List UInt8).toByteArray, .bytes ([165] : List UInt8).toByteArray]) h =
      let a := pair zero zero
      let b := pair (pair (leaf [165] (by decide)) zero) (Base.FixedBytes.ofLeNat 1)
      pair (pair a (pair (pair (pair b zero) (pair zero zero)) zero))
        (Base.FixedBytes.ofLeNat 2) := by
  dsimp only
  have hc : Children
      [(.progressiveByteList, .bytes ([] : List UInt8).toByteArray),
        (.progressiveByteList, .bytes ([165] : List UInt8).toByteArray)]
      [pair zero zero,
        pair (pair (leaf [165] (by decide)) zero) (Base.FixedBytes.ofLeNat 1)] := by
    constructor
    · rfl
    · intro p hp hx
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
        List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact rootP5_empty_bytes hx
      · exact rootP5_one_byte hx
  rw [composite_progressive_root .progressiveByteList _ h (by trivial) _ hc (by decide)]
  change Ssz.mixInLength (Ssz.merkleizeProgressive _ 0) 2 _ = _
  erw [progressive_two, length_pair]

private theorem rootP8_count255 :
    (Base.FixedBytes.ofLeNat 255 : Base.Bytes32).toBytes.toList =
      [255] ++ List.replicate 31 0 := by
  rw [Base.FixedBytes.toBytes_ofLeNat, Base.Bytes.toList_generate]
  decide

private theorem rootP8_count256 :
    (Base.FixedBytes.ofLeNat 256 : Base.Bytes32).toBytes.toList =
      [0, 1] ++ List.replicate 30 0 := by
  rw [Base.FixedBytes.toBytes_ofLeNat, Base.Bytes.toList_generate]
  decide

private theorem rootP8_largest_count :
    (Base.FixedBytes.ofLeNat (2 ^ 256 - 1) : Base.Bytes32).toBytes.toList =
      List.replicate 32 255 ∧ ¬ (2 ^ 256 < 2 ^ 256) := by
  constructor
  · rw [Base.FixedBytes.toBytes_ofLeNat, Base.Bytes.toList_generate]
    decide
  · exact Nat.lt_irrefl _

private theorem rootP8_count_excluded (b : ByteArray) (hn : b.size = 2 ^ 256) :
    ¬ Ssz.Rootable .progressiveByteList (.bytes b) := by
  intro h
  have hs : b.size < 2 ^ 256 := (Ssz.rootable_iff _ _).mp h
  rw [hn] at hs
  exact Nat.lt_irrefl _ hs

private theorem rootP7_population_excluded (mask : List Bool) (fields : List SszType)
    (xs : List SszValue) (hn : (mask.filter id).length ≠ fields.length) :
    ¬ Ssz.Rootable (.progressiveContainer mask fields) (.container xs) := by
  intro h
  exact hn ((Ssz.rootable_iff _ _).mp h).2.2.1

private theorem rootP7_arity_excluded (mask : List Bool) (fields : List SszType)
    (xs : List SszValue) (hn : fields.length ≠ xs.length) :
    ¬ Ssz.Rootable (.progressiveContainer mask fields) (.container xs) := by
  intro h
  exact hn ((Ssz.rootable_iff _ _).mp h).2.2.2.1

-- R18: explicit nameless Amsterdam schema recipes; source field names/classes are separate.
private def withdrawalFields : List SszType := [.uint 8, .uint 8, .byteVector 20, .uint 8]
private def depositFields : List SszType := [.byteVector 48, .byteVector 32, .uint 8, .byteVector
  96, .uint 8]
private def withdrawalRequestFields : List SszType := [.byteVector 20, .byteVector 48, .uint 8]
private def consolidationFields : List SszType := [.byteVector 20, .byteVector 48, .byteVector 48]
private def builderDepositFields : List SszType := [.byteVector 48, .byteVector 32, .uint
  8, .byteVector 96]
private def builderExitFields : List SszType := [.byteVector 20, .byteVector 48]
private def executionRequestsFields : List SszType :=
  [.progressiveList (.container depositFields),
    .progressiveList (.container withdrawalRequestFields),
    .progressiveList (.container consolidationFields),
    .progressiveList (.container builderDepositFields),
    .progressiveList (.container builderExitFields)]
private def payloadFields : List SszType :=
  [.byteVector 32, .byteVector 20, .byteVector 32, .byteVector 32, .byteVector 256, .byteVector 32,
    .uint 8, .uint 8, .uint 8, .uint 8, .byteList 32, .uint 32, .byteVector 32,
    .progressiveList .progressiveByteList, .progressiveList (.container withdrawalFields),
    .uint 8, .uint 8, .progressiveByteList, .uint 8]
private def payloadType : SszType := .progressiveContainer (List.replicate 19 true) payloadFields
private def executionRequestsType : SszType :=
  .progressiveContainer (List.replicate 5 true) executionRequestsFields
private def newPayloadFields : List SszType :=
  [payloadType, .progressiveList (.byteVector 32), .byteVector 32, executionRequestsType]

private theorem rootP9_arities :
    withdrawalFields.length = 4 ∧ depositFields.length = 5 ∧
    withdrawalRequestFields.length = 3 ∧ consolidationFields.length = 3 ∧
    builderDepositFields.length = 4 ∧ builderExitFields.length = 2 ∧
    executionRequestsFields.length = 5 ∧ payloadFields.length = 19 ∧ newPayloadFields.length = 4 :=
      by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem rootP9_units :
    payloadFields.getD 9 .bool = .uint 8 ∧
    payloadFields.getD 11 .bool = .uint 32 ∧
    payloadFields.getD 10 .bool = .byteList 32 ∧
    payloadFields.getD 13 .bool = .progressiveList .progressiveByteList ∧
    payloadFields.getD 14 .bool = .progressiveList (.container withdrawalFields) ∧
    payloadFields.getD 17 .bool = .progressiveByteList := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem ordinary_recipe (fields : List SszType) (xs : List SszValue)
    (h : Ssz.Rootable (.container fields) (.container xs))
    (rs : List Base.Bytes32) (hc : Children (fields.zip xs) rs) :
    Ssz.hashTreeRoot (.container fields) (.container xs) h =
      foldModel pair zero (if fields.length ≤ 1 then 0 else Nat.log2 (fields.length - 1) + 1)
          rs := by
  have hp : rs.toArray.size ≤ cap fields.length := by
    rw [List.size_toArray, ← hc.1]
    simp only [List.length_zip]
    exact Nat.le_trans (Nat.min_le_left _ _) (cap_covers _)
  have hr := (fields_root fields xs h rs hc hp).trans (ordinary_model rs.toArray fields.length hp)
  simpa only [List.toList_toArray] using hr

private theorem slots_alltrue (rs : List Base.Bytes32) :
    slots (List.replicate rs.length true) rs = rs.toArray := by
  rw [← rootP7_scan_model]
  apply congrArg List.toArray
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.length_cons, List.replicate_succ, scan, List.getD_cons_zero,
        List.tail_cons, ih]

private theorem alltrue_number (n : Nat) :
    (List.replicate n true).foldr (fun b m ↦ (if b then 1 else 0) + 2 * m) 0 = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.foldr_cons, reduceIte, ih, Nat.pow_succ]
    have hp := Nat.two_pow_pos n
    omega

private theorem alltrue_recipe (fields : List SszType) (xs : List SszValue)
    (h : Ssz.Rootable (.progressiveContainer (List.replicate fields.length true) fields)
      (.container xs)) (rs : List Base.Bytes32) (hc : Children (fields.zip xs) rs) :
    Ssz.hashTreeRoot (.progressiveContainer (List.replicate fields.length true) fields)
      (.container xs) h = pair (progressiveFormula pair zero 0 rs)
        (Base.FixedBytes.ofLeNat (2 ^ fields.length - 1)) := by
  have hs := (Ssz.rootable_iff _ _).mp h
  have hl := hc.1
  simp only [List.length_zip] at hl
  have ha := hs.2.2.2.1
  have hn : rs.length = fields.length := by omega
  have hslots : slots (List.replicate fields.length true) rs = rs.toArray := by
    rw [← hn]
    exact slots_alltrue rs
  have hr := progressive_fields_root _ fields xs h rs hc hs.2.1
  rw [hslots, progressive_model, activity_pair, alltrue_number] at hr
  simpa only [List.toList_toArray] using hr

private theorem rootP9_payload (xs : List SszValue)
    (h : Ssz.Rootable payloadType (.container xs)) (rs : List Base.Bytes32)
    (hc : Children (payloadFields.zip xs) rs) :
    Ssz.hashTreeRoot payloadType (.container xs) h =
      pair (progressiveFormula pair zero 0 rs) (Base.FixedBytes.ofLeNat (2 ^ 19 - 1)) :=
  alltrue_recipe payloadFields xs h rs hc

private theorem rootP9_requests (xs : List SszValue)
    (h : Ssz.Rootable executionRequestsType (.container xs)) (rs : List Base.Bytes32)
    (hc : Children (executionRequestsFields.zip xs) rs) :
    Ssz.hashTreeRoot executionRequestsType (.container xs) h =
      pair (progressiveFormula pair zero 0 rs) (Base.FixedBytes.ofLeNat 31) :=
  alltrue_recipe executionRequestsFields xs h rs hc

private theorem foldModel_four {α : Type} (p : α → α → α) (z a b c d : α) :
    foldModel p z 2 [a, b, c, d] = p (p a b) (p c d) := by
  simp [foldModel, List.range_succ]

private theorem rootP9_newPayload (xs : List SszValue)
    (h : Ssz.Rootable (.container newPayloadFields) (.container xs))
    (payload versioned beacon requests : Base.Bytes32)
    (hc : Children (newPayloadFields.zip xs) [payload, versioned, beacon, requests]) :
    Ssz.hashTreeRoot (.container newPayloadFields) (.container xs) h =
      pair (pair payload versioned) (pair beacon requests) := by
  rw [ordinary_recipe _ _ h _ hc]
  exact foldModel_four pair zero payload versioned beacon requests

private theorem rootP9_withdrawal (xs : List SszValue)
    (h : Ssz.Rootable (.container withdrawalFields) (.container xs)) (rs : List Base.Bytes32)
    (hc : Children (withdrawalFields.zip xs) rs) :
    Ssz.hashTreeRoot (.container withdrawalFields) (.container xs) h = foldModel pair zero 2 rs :=
  ordinary_recipe withdrawalFields xs h rs hc

private theorem rootP9_deposit (xs : List SszValue)
    (h : Ssz.Rootable (.container depositFields) (.container xs)) (rs : List Base.Bytes32)
    (hc : Children (depositFields.zip xs) rs) :
    Ssz.hashTreeRoot (.container depositFields) (.container xs) h = foldModel pair zero 3 rs :=
  ordinary_recipe depositFields xs h rs hc

private theorem rootP9_withdrawalRequest (xs : List SszValue)
    (h : Ssz.Rootable (.container withdrawalRequestFields) (.container xs)) (rs : List
        Base.Bytes32)
    (hc : Children (withdrawalRequestFields.zip xs) rs) :
    Ssz.hashTreeRoot (.container withdrawalRequestFields) (.container xs) h = foldModel pair zero 2
      rs :=
  ordinary_recipe withdrawalRequestFields xs h rs hc

private theorem rootP9_consolidation (xs : List SszValue)
    (h : Ssz.Rootable (.container consolidationFields) (.container xs)) (rs : List Base.Bytes32)
    (hc : Children (consolidationFields.zip xs) rs) :
    Ssz.hashTreeRoot (.container consolidationFields) (.container xs) h = foldModel pair zero 2 rs
      :=
  ordinary_recipe consolidationFields xs h rs hc

private theorem rootP9_builderDeposit (xs : List SszValue)
    (h : Ssz.Rootable (.container builderDepositFields) (.container xs)) (rs : List Base.Bytes32)
    (hc : Children (builderDepositFields.zip xs) rs) :
    Ssz.hashTreeRoot (.container builderDepositFields) (.container xs) h = foldModel pair zero 2 rs
      :=
  ordinary_recipe builderDepositFields xs h rs hc

private theorem rootP9_builderExit (xs : List SszValue)
    (h : Ssz.Rootable (.container builderExitFields) (.container xs)) (rs : List Base.Bytes32)
    (hc : Children (builderExitFields.zip xs) rs) :
    Ssz.hashTreeRoot (.container builderExitFields) (.container xs) h = foldModel pair zero 1 rs :=
  ordinary_recipe builderExitFields xs h rs hc

-- The complete whole-root recipes above have actual child certificates under C.
private theorem rootP9_payload_witnesses (xs : List SszValue)
    (h : Ssz.Rootable payloadType (.container xs)) :
    ∃ rs : List Base.Bytes32, rs.length = 19 ∧ Children (payloadFields.zip xs) rs := by
  have hs := (Ssz.rootable_iff _ _).mp h
  obtain ⟨rs, hr⟩ := rootP8_children_available (payloadFields.zip xs) hs.2.2.2.2
  refine ⟨rs, ?_, hr⟩
  have hl := hr.1
  simp only [List.length_zip] at hl
  have ha := hs.2.2.2.1
  change 19 = xs.length at ha
  change min 19 xs.length = rs.length at hl
  omega

private def emptyBytes (n : Nat) : SszValue := .bytes (List.replicate n (0 : UInt8)).toByteArray
private def emptyPayload : SszValue := .container
  [emptyBytes 32, emptyBytes 20, emptyBytes 32, emptyBytes 32, emptyBytes 256, emptyBytes 32,
    .uint 0, .uint 0, .uint 0, .uint 0, emptyBytes 0, .uint 0, emptyBytes 32, .list [], .list [],
    .uint 0, .uint 0, emptyBytes 0, .uint 0]
private def emptyRequests : SszValue := .container [.list [], .list [], .list [], .list [],
    .list []]
private def emptyNewPayload : SszValue := .container [emptyPayload, .list [], emptyBytes
  32, emptyRequests]

private theorem empty_vector_support (n : Nat) : Ssz.Rootable (.byteVector n) (emptyBytes n) := by
  apply (Ssz.rootable_iff _ _).mpr
  simp only [emptyBytes, List.size_toByteArray, List.length_replicate]

private theorem empty_uint_support (w : Nat) (hw : w ∈ [1, 2, 4, 8, 16, 32]) :
    Ssz.Rootable (.uint w) (.uint 0) := by
  apply (Ssz.rootable_iff _ _).mpr
  exact ⟨hw, Nat.two_pow_pos _⟩

private theorem empty_bytes_support (limit : Nat) : Ssz.Rootable (.byteList limit) (emptyBytes 0)
  := by
  apply (Ssz.rootable_iff _ _).mpr
  exact ⟨Nat.zero_le _, Nat.two_pow_pos _⟩

private theorem empty_progressive_bytes_support : Ssz.Rootable .progressiveByteList (emptyBytes 0)
  := by
  apply (Ssz.rootable_iff _ _).mpr
  exact Nat.two_pow_pos _

private theorem empty_progressive_support (elem : SszType) (he : Composite elem) :
    Ssz.Rootable (.progressiveList elem) (.list []) := by
  apply (Ssz.rootable_iff _ _).mpr
  refine ⟨Nat.two_pow_pos _, ?_, ?_⟩
  · intro x hx; exact False.elim (List.not_mem_nil hx)
  · cases elem with
    | uint w => exact False.elim he
    | bool => exact False.elim he
    | _ => trivial

private theorem alltrue_support (fields : List SszType) (xs : List SszValue)
    (hpos : 0 < fields.length) (hwidth : fields.length ≤ 256) (ha : fields.length = xs.length)
    (hc : ∀ p ∈ fields.zip xs, Ssz.Rootable p.1 p.2) :
    Ssz.Rootable (.progressiveContainer (List.replicate fields.length true) fields) (.container xs)
      := by
  apply (Ssz.rootable_iff _ _).mpr
  refine ⟨?_, ?_, ?_, ha, hc⟩
  · rw [List.getLast?_replicate, ite_eq_right (Nat.ne_of_gt hpos)]
  · simpa only [List.length_replicate] using hwidth
  · simp only [List.filter_replicate_of_pos (show id true = true from rfl), List.length_replicate]

private theorem rootP9_empty_requests_support : Ssz.Rootable executionRequestsType emptyRequests :=
  by
  apply alltrue_support executionRequestsFields _ (by decide) (by decide) rfl
  intro p hp
  simp only [executionRequestsFields, List.zip_cons_cons, List.zip_nil_right,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    exact empty_progressive_support _ (by trivial)

private theorem rootP9_empty_payload_support : Ssz.Rootable payloadType emptyPayload := by
  apply alltrue_support payloadFields _ (by decide) (by decide) rfl
  intro p hp
  simp only [payloadFields, List.zip_cons_cons, List.zip_nil_right,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl
  · exact empty_vector_support 32
  · exact empty_vector_support 20
  · exact empty_vector_support 32
  · exact empty_vector_support 32
  · exact empty_vector_support 256
  · exact empty_vector_support 32
  · exact empty_uint_support 8 (by decide)
  · exact empty_uint_support 8 (by decide)
  · exact empty_uint_support 8 (by decide)
  · exact empty_uint_support 8 (by decide)
  · exact empty_bytes_support 32
  · exact empty_uint_support 32 (by decide)
  · exact empty_vector_support 32
  · exact empty_progressive_support _ (by trivial)
  · exact empty_progressive_support _ (by trivial)
  · exact empty_uint_support 8 (by decide)
  · exact empty_uint_support 8 (by decide)
  · exact empty_progressive_bytes_support
  · exact empty_uint_support 8 (by decide)

private theorem rootP9_empty_newPayload_support :
    Ssz.Rootable (.container newPayloadFields) emptyNewPayload := by
  apply (Ssz.rootable_iff _ _).mpr
  refine ⟨by simp [newPayloadFields], rfl, ?_⟩
  intro p hp
  simp only [newPayloadFields, List.zip_cons_cons, List.zip_nil_right,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact rootP9_empty_payload_support
  · apply (Ssz.rootable_iff _ _).mpr
    exact ⟨by decide, by simp, trivial⟩
  · exact empty_vector_support 32
  · exact rootP9_empty_requests_support

private theorem rootP1_domain (w : Nat) (hw : w ∈ [1, 2, 4, 8, 16, 32]) :
    Ssz.Rootable (.uint w) (.uint 0) ∧ Ssz.Rootable (.uint w) (.uint (2 ^ (8 * w) - 1)) := by
  refine ⟨empty_uint_support w hw, ?_⟩
  apply (Ssz.rootable_iff _ _).mpr
  refine ⟨hw, ?_⟩
  have hp := Nat.two_pow_pos (8 * w)
  omega

private theorem rootP2_vector_domain (bs : List UInt8) :
    Ssz.Rootable (.byteVector bs.length) (.bytes bs.toByteArray) := by
  apply (Ssz.rootable_iff _ _).mpr
  exact List.size_toByteArray

private theorem rootP2_bytes_domain (bs : List UInt8) (limit : Nat)
    (hl : bs.length ≤ limit) (hn : bs.length < 2 ^ 256) :
    Ssz.Rootable (.byteList limit) (.bytes bs.toByteArray) := by
  apply (Ssz.rootable_iff _ _).mpr
  simpa only [List.size_toByteArray] using And.intro hl hn

private theorem rootP3_finite_domain :
    Ssz.Rootable (.list (.uint 8) 5) (.list ([1, 2, 3, 4, 5].map .uint)) ∧
    Ssz.Rootable (.list .bool 33) (.list ((List.replicate 33 true).map .bool)) := by
  constructor
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
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact (Ssz.rootable_iff _ _).mpr trivial

private theorem rootP8_nested_domain :
    Ssz.Rootable (.progressiveList .progressiveByteList)
      (.list [.bytes ([] : List UInt8).toByteArray, .bytes ([165] : List UInt8).toByteArray]) := by
  have h0 : Ssz.Rootable .progressiveByteList (.bytes ([] : List UInt8).toByteArray) :=
    (Ssz.rootable_iff _ _).mpr (Nat.two_pow_pos _)
  have h1 : Ssz.Rootable .progressiveByteList (.bytes ([165] : List UInt8).toByteArray) := by
    apply (Ssz.rootable_iff _ _).mpr
    decide
  apply (Ssz.rootable_iff _ _).mpr
  refine ⟨by decide, ?_, trivial⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact h0
  · exact h1

end STFSpec.Conformance.Codec
