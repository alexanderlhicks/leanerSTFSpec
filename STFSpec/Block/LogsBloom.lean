/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core.Logs
import STFSpec.Hash.KeccakQuery
import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.UInt.Bitwise

/-!
# Ordered logs bloom

Library `EthBlock`. A local 256-byte buffer receives three bit updates for each
oracle answer, in address-then-topic order. The private positional model and
ordinary refinement identify the complete public result and sequential effects.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§2.10/3–7.
-/

namespace STFSpec.Block
open STFSpec.Base STFSpec.Hash
open STFSpec.Vm

/-! ### Private byte representation and full numeric observation -/

private def positional : List UInt8 → Nat
  | [] => 0
  | x :: xs => x.toNat * 256 ^ xs.length + positional xs

private def bitwise : List UInt8 → Nat
  | [] => 0
  | x :: xs => (x.toNat <<< (8 * xs.length)) ||| bitwise xs

private theorem positional_lt (xs : List UInt8) : positional xs < 256 ^ xs.length := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    simp only [positional, List.length_cons, Nat.pow_succ]
    have hx := x.toNat_lt
    have hp := Nat.pow_pos (a := 256) (n := xs.length) (by decide)
    have hm := Nat.mul_le_mul_right (256 ^ xs.length) (show x.toNat + 1 ≤ 256 by omega)
    simp only [Nat.add_mul, Nat.one_mul] at hm
    omega

private theorem positional_eq_bitwise (xs : List UInt8) : positional xs = bitwise xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hpow : 256 ^ xs.length = 2 ^ (8 * xs.length) := by rw [Nat.pow_mul]
    simp only [positional, bitwise]
    rw [hpow, ← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt
      (by rw [← hpow]; exact positional_lt xs), ih]

private theorem fold_positional (xs : List UInt8) (acc : Nat) :
    xs.foldl (fun acc byte ↦ 256 * acc + byte.toNat) acc =
      acc * 256 ^ xs.length + positional xs := by
  induction xs generalizing acc with
  | nil => simp [positional]
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, List.length_cons, positional, Nat.pow_succ]
    simp only [Nat.add_mul]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.add_assoc]

private theorem bitwise_set (xs : List UInt8) (i : Nat) (hi : i < xs.length) (mask : UInt8) :
    bitwise (xs.set i (xs[i] ||| mask)) =
      bitwise xs ||| (mask.toNat <<< (8 * (xs.length - 1 - i))) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.getElem_cons_zero, bitwise,
        UInt8.toNat_or, Nat.shiftLeft_or_distrib, List.length_cons,
        Nat.add_sub_cancel, Nat.sub_zero]
      rw [Nat.or_assoc, Nat.or_comm (mask.toNat <<< (8 * xs.length)), ← Nat.or_assoc]
    | succ i =>
      have hi' : i < xs.length := by simpa using hi
      simp only [List.set_cons_succ, List.getElem_cons_succ, bitwise, List.length_set]
      rw [ih i hi']
      simp only [List.length_cons]
      rw [show xs.length + 1 - 1 - (i + 1) = xs.length - 1 - i by omega]
      rw [Nat.or_assoc]

private def mask (b : Nat) : UInt8 := 1 <<< UInt8.ofNat (b % 8)

private theorem mask_toNat (b : Nat) : (mask b).toNat = 2 ^ (b % 8) := by
  have hm : b % 8 < 8 := Nat.mod_lt _ (by decide)
  have hm256 : b % 8 < 256 := by omega
  have hp : 2 ^ (b % 8) < 256 := by
    exact Nat.pow_lt_pow_right (by decide) hm
  simp only [mask, UInt8.toNat_shiftLeft, UInt8.toNat_ofNat_of_lt' hm256,
    Nat.mod_eq_of_lt hm, UInt8.toNat_one, Nat.one_shiftLeft]
  exact Nat.mod_eq_of_lt hp

private def setBit (bytes : ByteArray) (hs : bytes.size = 256) (b : Nat) (hb : b < 2048) :
    ByteArray :=
  bytes.set (255 - b / 8) ((bytes[255 - b / 8]'(by omega)) ||| mask b) (by omega)

private theorem size_setBit (bytes : ByteArray) (hs : bytes.size = 256) (b : Nat) (hb : b < 2048) :
    (setBit bytes hs b hb).size = 256 := by
  unfold setBit
  change (bytes.data.set _ _ _).size = 256
  rw [Array.size_set]
  exact hs

private def observe (bytes : ByteArray) : Nat := positional bytes.data.toList

private theorem observe_setBit (bytes : ByteArray) (hs : bytes.size = 256)
    (b : Nat) (hb : b < 2048) :
    observe (setBit bytes hs b hb) = observe bytes ||| 2 ^ b := by
  have hi : 255 - b / 8 < bytes.size := by omega
  have hl : bytes.data.toList.length = 256 := by simpa using hs
  have hget : bytes[255 - b / 8] =
      bytes.data.toList[255 - b / 8]'(by rw [hl]; omega) := by
    rfl
  simp only [observe, positional_eq_bitwise, setBit, ByteArray.data_set,
    Array.toList_set, hget]
  rw [bitwise_set _ _ (by rw [hl]; omega), mask_toNat, hl]
  have hexp : b % 8 + 8 * (256 - 1 - (255 - b / 8)) = b := by omega
  rw [Nat.shiftLeft_eq, ← Nat.pow_add, hexp]

private theorem observe_eq_fold (bytes : ByteArray) :
    observe bytes = (Bytes.ofByteArray bytes).toList.foldl
      (fun acc byte ↦ 256 * acc + byte.toNat) 0 := by
  rw [Bytes.toList_ofByteArray, fold_positional]
  simp only [Nat.zero_mul, Nat.zero_add]
  rfl

private theorem observe_fixed (bytes : ByteArray) (x : FixedBytes 256)
    (hx : FixedBytes.ofBytes? (Bytes.ofByteArray bytes) = some x) :
    observe bytes = x.toNat := by
  have h := (FixedBytes.ofBytes?_eq_some_iff.mp hx).2
  rw [observe_eq_fold, ← h, ← FixedBytes.toNat_eq_fold]

private def finish (bytes : ByteArray) (hs : bytes.size = 256) : FixedBytes 256 :=
  (FixedBytes.ofBytes? (Bytes.ofByteArray bytes)).get (by
    apply Option.isSome_iff_ne_none.mpr
    intro hn
    exact FixedBytes.ofBytes?_eq_none_iff.mp hn (by rw [Bytes.size_ofByteArray, hs]))

private theorem finish_success (bytes : ByteArray) (hs : bytes.size = 256) :
    FixedBytes.ofBytes? (Bytes.ofByteArray bytes) = some (finish bytes hs) := by
  exact (Option.some_get _).symm

/-! ### Hash-byte selectors and source orientation -/

private theorem byte_fixed {n : Nat} (x : FixedBytes n) (i : Nat) (hi : i < n) :
    (x.toBytes[i]'(by rw [FixedBytes.size_toBytes]; exact hi)).toNat =
      (x.toNat / 2 ^ (8 * (n - 1 - i))) % 256 := by
  have hx : x.toBytes = Bytes.generate n
      (fun j ↦ UInt8.ofNat (x.toNat >>> (8 * (n - 1 - j)))) := by
    calc
      x.toBytes = (FixedBytes.ofNat x.toNat).toBytes :=
        congrArg FixedBytes.toBytes (FixedBytes.ofNat_toNat x).symm
      _ = _ := FixedBytes.toBytes_ofNat _
  simp only [hx]
  rw [Bytes.getElem_generate _ _ i hi, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow]

private theorem byte_hash (x : Hash32) (i : Nat) (hi : i < 32) :
    (x.toBytes[i]'(by rw [Hash32.size_toBytes]; exact hi)).toNat =
      (x.toNat / 2 ^ (8 * (31 - i))) % 256 := by
  simpa only [Hash32.toBytes_toBytes32, Hash32.toNat_toBytes32] using
    byte_fixed x.toBytes32 i hi

private def pair (x : Hash32) (j : Nat) (hj : j + 1 < 32) : Nat :=
  let bytes := x.toBytes
  256 * (bytes[j]'(by rw [Hash32.size_toBytes]; omega)).toNat +
    (bytes[j + 1]'(by rw [Hash32.size_toBytes]; exact hj)).toNat

private theorem pair_eq (x : Hash32) (j : Nat) (hj : j + 1 < 32) :
    pair x j hj = (x.toNat / 2 ^ (8 * (30 - j))) % 65536 := by
  have he : 8 * (31 - j) = 8 * (30 - j) + 8 := by omega
  have he' : 31 - (j + 1) = 30 - j := by omega
  rw [pair, byte_hash x j (by omega), byte_hash x (j + 1) hj]
  simp only [he, he', Nat.pow_add]
  rw [show 2 ^ 8 = 256 from rfl, ← Nat.div_div_eq_div_mul]
  symm
  simpa only [Nat.mul_comm, Nat.add_comm] using
    (Nat.mod_mul (x := x.toNat / 2 ^ (8 * (30 - j))) (a := 256) (b := 256))

private theorem selector_mod (x : Hash32) (j : Nat) (hj : j + 1 < 32) :
    pair x j hj % 2048 = (x.toNat / 2 ^ (8 * (30 - j))) % 2048 := by
  rw [pair_eq, Nat.mod_mod_of_dvd _ (by decide : 2048 ∣ 65536)]

private def selector (x : Hash32) (j : Nat) (hj : j + 1 < 32) : Nat := pair x j hj &&& 2047

private theorem selector_eq (x : Hash32) (j : Nat) (hj : j + 1 < 32) :
    selector x j hj = (x.toNat / 2 ^ (8 * (30 - j))) % 2048 := by
  unfold selector
  rw [show 2047 = 2 ^ 11 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact selector_mod x j hj

/-- The pinned EELS byte index `(2047 - b) / 8` (`bloom.py`) equals the big-endian
byte `255 - b / 8` used here; recorded as a checked correspondence, not a client. -/
private theorem byte_index_from_top (b : Nat) (hb : b < 2048) :
    (2047 - b) / 8 = 255 - b / 8 := by omega

/-- The pinned EELS bit `7 - (2047 - b) % 8` within that byte equals `b % 8`. -/
private theorem bit_index_from_top (b : Nat) (hb : b < 2048) :
    7 - (2047 - b) % 8 = b % 8 := by omega

private theorem selector_lt (x : Hash32) (j : Nat) (hj : j + 1 < 32) :
    selector x j hj < 2048 := by
  rw [selector_eq]
  exact Nat.mod_lt _ (by decide)

/-! ### Ordered packed construction and complete action refinement -/

private def zeroBuffer : { bytes : ByteArray // bytes.size = 256 } :=
  ⟨(Bytes.generate 256 (fun _ ↦ 0)).toByteArray, by
    rw [Bytes.size_toByteArray, Bytes.size_generate]⟩

private def setThree (buffer : { bytes : ByteArray // bytes.size = 256 })
    (h : Hash32) : { bytes : ByteArray // bytes.size = 256 } :=
  let a := selector h 0 (by decide)
  let b := selector h 2 (by decide)
  let c := selector h 4 (by decide)
  let first := setBit buffer.val buffer.property a (selector_lt h 0 (by decide))
  let hs := size_setBit buffer.val buffer.property a (selector_lt h 0 (by decide))
  let second := setBit first hs b (selector_lt h 2 (by decide))
  let hs' := size_setBit first hs b (selector_lt h 2 (by decide))
  ⟨setBit second hs' c (selector_lt h 4 (by decide)),
    size_setBit second hs' c (selector_lt h 4 (by decide))⟩

private def addToBloom {m : Type → Type} [Monad m] [KeccakQuery m]
    (buffer : { bytes : ByteArray // bytes.size = 256 }) (entry : ByteArray) :
    m { bytes : ByteArray // bytes.size = 256 } := do
  let h ← KeccakQuery.keccak entry
  pure (setThree buffer h)

private def modelStep {m : Type → Type} [Monad m] [KeccakQuery m]
    (acc : Nat) (entry : ByteArray) : m Nat := do
  let h ← KeccakQuery.keccak entry
  pure (acc ||| 2 ^ ((h.toNat / 2 ^ 240) % 2048) |||
    2 ^ ((h.toNat / 2 ^ 224) % 2048) ||| 2 ^ ((h.toNat / 2 ^ 208) % 2048))

private def preimages (logs : List Core.Log) : List ByteArray :=
  logs.flatMap fun log ↦ log.address.toBytes.toByteArray ::
    log.topics.toList.map (fun topic ↦ topic.toBytes.toByteArray)

private theorem observe_setThree
    (buffer : { bytes : ByteArray // bytes.size = 256 }) (h : Hash32) :
    observe (setThree buffer h).val = observe buffer.val |||
      2 ^ ((h.toNat / 2 ^ 240) % 2048) |||
      2 ^ ((h.toNat / 2 ^ 224) % 2048) ||| 2 ^ ((h.toNat / 2 ^ 208) % 2048) := by
  simp only [setThree, observe_setBit, selector_eq]

private theorem finish_eq (buffer : { bytes : ByteArray // bytes.size = 256 }) :
    finish buffer.val buffer.property = (FixedBytes.ofNat (observe buffer.val) : Bloom) := by
  rw [observe_fixed _ _ (finish_success _ _), FixedBytes.ofNat_toNat]

private theorem positional_replicate_zero (n : Nat) :
    positional (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, positional, ih]

private theorem observe_zero : observe zeroBuffer.val = 0 := by
  simp only [observe, zeroBuffer, Bytes.toList_toByteArray, Bytes.toList_generate,
    List.map_const', List.length_range, positional_replicate_zero]

private theorem fold_finish {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (entries : List ByteArray) (buffer : { bytes : ByteArray // bytes.size = 256 }) :
    (do let out ← entries.foldlM addToBloom buffer
        pure (finish out.val out.property) : m Bloom) =
      (do let out ← entries.foldlM modelStep (observe buffer.val)
          pure (FixedBytes.ofNat out : Bloom)) := by
  induction entries generalizing buffer with
  | nil => simp only [List.foldlM_nil, pure_bind, finish_eq]
  | cons entry entries ih =>
    simp only [List.foldlM_cons, addToBloom, modelStep, bind_assoc, pure_bind]
    congr 1
    funext h
    rw [ih, observe_setThree]

private theorem fold_logs {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (logs : List Core.Log) (buffer : { bytes : ByteArray // bytes.size = 256 }) :
    logs.foldlM (fun buffer log ↦ do
      let buffer ← addToBloom buffer log.address.toBytes.toByteArray
      log.topics.foldlM (fun buffer topic ↦
        addToBloom buffer topic.toBytes.toByteArray) buffer) buffer =
      (preimages logs).foldlM addToBloom buffer (m := m) := by
  induction logs generalizing buffer with
  | nil => rfl
  | cons log logs ih =>
    simp only [List.foldlM_cons, ih, preimages, List.flatMap_cons,
      List.foldlM_cons, List.foldlM_append, List.foldlM_map, Array.foldlM_toList,
      bind_assoc]

/-! ### Public operation and laws -/

/-- Complete logs bloom, pinned EELS `src/ethereum/forks/amsterdam/bloom.py:29–87`.
Each log queries its complete address, then every topic in order, exactly once.
Duplicates are retained; data is ignored. The supplied oracle's effects and
failures pass through the ordinary monadic traversal unchanged. -/
def logsBloom {m : Type → Type} [Monad m] [KeccakQuery m]
    (logs : Array Core.Log) : m Bloom := do
  let buffer ← logs.foldlM (fun buffer log ↦ do
    let buffer ← addToBloom buffer log.address.toBytes.toByteArray
    log.topics.foldlM (fun buffer topic ↦
      addToBloom buffer topic.toBytes.toByteArray) buffer) zeroBuffer
  pure (finish buffer.val buffer.property)

/-- Complete ordinary action equation under lawful sequencing. No stable, pure
or concrete oracle-answer premise is used: the fold retains every query and its
position in the same evolving monadic context. -/
theorem logsBloom_eq {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (logs : Array Core.Log) :
    logsBloom logs = (do
      let result ← (logs.toList.flatMap (fun log ↦ log.address.toBytes.toByteArray ::
        log.topics.toList.map (fun topic ↦ topic.toBytes.toByteArray))).foldlM
        (fun acc entry ↦ do
          let h ← KeccakQuery.keccak entry
          pure (acc ||| 2 ^ ((h.toNat / 2 ^ 240) % 2048) |||
            2 ^ ((h.toNat / 2 ^ 224) % 2048) ||| 2 ^ ((h.toNat / 2 ^ 208) % 2048))) 0
      pure (FixedBytes.ofNat result : Bloom) : m Bloom) := by
  unfold logsBloom
  rw [← Array.foldlM_toList, fold_logs, fold_finish, observe_zero]
  rfl

/-- Empty logs issue no query and return the complete zero bloom. -/
theorem logsBloom_empty {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m] :
    logsBloom (m := m) #[] = pure (FixedBytes.ofNat 0 : Bloom) := by
  rw [logsBloom_eq]
  simp only [List.flatMap_nil, List.foldlM_nil, pure_bind]

private theorem fold_or {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (entries : List ByteArray) (a b : Nat) :
    (do let out ← entries.foldlM modelStep b
        pure (a ||| out) : m Nat) = entries.foldlM modelStep (a ||| b) := by
  induction entries generalizing b with
  | nil => simp only [List.foldlM_nil, pure_bind]
  | cons entry entries ih =>
    simp only [List.foldlM_cons, modelStep, bind_assoc, pure_bind]
    congr 1
    funext h
    rw [ih]
    simp only [Nat.or_assoc]

private theorem ofNat_or (a b : Nat) :
    (FixedBytes.ofNat (a ||| b) : Bloom) =
      FixedBytes.ofNat ((FixedBytes.ofNat a : Bloom).toNat |||
        (FixedBytes.ofNat b : Bloom).toNat) := by
  apply FixedBytes.toNat_inj.mp
  simp only [FixedBytes.toNat_ofNat, Nat.or_mod_two_pow, Nat.mod_mod]

/-- Sequential append law. Both component actions run in one evolving oracle
context, retaining repeated queries and their current answers. Only the returned
blooms are combined; no effect or failure is commuted, reset or suppressed. -/
theorem logsBloom_append {m : Type → Type} [Monad m] [LawfulMonad m] [KeccakQuery m]
    (a b : Array Core.Log) :
    logsBloom (a ++ b) = (do
      let ba ← logsBloom a
      let bb ← logsBloom b
      pure (FixedBytes.ofNat (ba.toNat ||| bb.toNat) : Bloom) : m Bloom) := by
  simp only [logsBloom_eq, Array.toList_append, List.flatMap_append,
    List.foldlM_append, bind_assoc, pure_bind]
  change (do
    let first ← (preimages a.toList).foldlM modelStep 0
    let out ← (preimages b.toList).foldlM modelStep first
    pure (FixedBytes.ofNat out : Bloom) : m Bloom) = _
  congr 1
  funext first
  have h := fold_or (m := m) (preimages b.toList) first 0
  simp only [Nat.or_zero] at h
  rw [← h]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext second
  exact congrArg pure (ofNat_or first second)

end STFSpec.Block
