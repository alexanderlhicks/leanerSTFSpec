/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec

/-!
# Independent generic SSZ schema callers

Library `EthConformance`. Full polymorphic signatures and equations retain the
actual supplied dictionary, value and single-operation proof. No validity, WF,
inverse or other-operation premise is assumed, and no instances are declared.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7.
-/

namespace STFSpec.Conformance.Codec

open STFSpec.Codec

private def encodeSignature :
    {α : Type} → (s : SszSchema α) →
      (a : α) → Ssz.Serializable s.type (s.toValue a) → ByteArray :=
  @SszSchema.encodeBytes

private def rootSignature :
    {α : Type} → (s : SszSchema α) →
      (a : α) → Ssz.Rootable s.type (s.toValue a) → Base.Bytes32 :=
  @SszSchema.hashTreeRoot

private theorem encode_equation {α : Type} (s : SszSchema α)
    (a : α) (h : Ssz.Serializable s.type (s.toValue a)) :
    @SszSchema.encodeBytes α s a h = Ssz.encode s.type (s.toValue a) h :=
  @SszSchema.encodeBytes_eq α s a h

private theorem root_equation {α : Type} (s : SszSchema α)
    (a : α) (h : Ssz.Rootable s.type (s.toValue a)) :
    @SszSchema.hashTreeRoot α s a h = Ssz.hashTreeRoot s.type (s.toValue a) h :=
  @SszSchema.hashTreeRoot_eq α s a h

private theorem independent_encoders {α : Type} (s t : SszSchema α) (a b : α)
    (hs : Ssz.Serializable s.type (s.toValue a))
    (ht : Ssz.Serializable t.type (t.toValue b)) :
    (@SszSchema.encodeBytes α s a hs, @SszSchema.encodeBytes α t b ht) =
      (Ssz.encode s.type (s.toValue a) hs, Ssz.encode t.type (t.toValue b) ht) := by
  rw [@SszSchema.encodeBytes_eq α s, @SszSchema.encodeBytes_eq α t]

private theorem independent_roots {α : Type} (s t : SszSchema α) (a b : α)
    (hs : Ssz.Rootable s.type (s.toValue a))
    (ht : Ssz.Rootable t.type (t.toValue b)) :
    (@SszSchema.hashTreeRoot α s a hs, @SszSchema.hashTreeRoot α t b ht) =
      (Ssz.hashTreeRoot s.type (s.toValue a) hs,
        Ssz.hashTreeRoot t.type (t.toValue b) ht) := by
  rw [@SszSchema.hashTreeRoot_eq α s, @SszSchema.hashTreeRoot_eq α t]

private theorem bytes_from_raw_law {α : Type} (s : SszSchema α) (a : α)
    (h : Ssz.Serializable s.type (s.toValue a)) (b : ByteArray)
    (hb : Ssz.encode s.type (s.toValue a) h = b) :
    @SszSchema.encodeBytes α s a h = b := by
  rw [@SszSchema.encodeBytes_eq α s, hb]

private theorem root_from_raw_law {α : Type} (s : SszSchema α) (a : α)
    (h : Ssz.Rootable s.type (s.toValue a)) (r : Base.Bytes32)
    (hr : Ssz.hashTreeRoot s.type (s.toValue a) h = r) :
    @SszSchema.hashTreeRoot α s a h = r := by
  rw [@SszSchema.hashTreeRoot_eq α s, hr]

end STFSpec.Conformance.Codec
