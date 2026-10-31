/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Codec.SszEncode
import STFSpec.Codec.SszRoot

/-!
# Typed SSZ forward wrappers

Library `EthCodec`. A five-field metadata carrier supplies the raw descriptor and
conversion. Each forward call takes only its actual raw operation's support proof.
Instance owners separately prove descriptor well-formedness and both adapter laws;
the carrier supplies no such certificates and this module supplies no instances.
Reference: EELS `src/ethereum/utils/ssz.py:129–146` at the pin.
Spec guidance: `STFSpec/informal/modules/EthCodec.md` §§3–7 (Q81).
-/

namespace STFSpec.Codec

/-- SSZ schema metadata; EELS `src/ethereum/utils/ssz.py:129–146,179–325`.
Each actual instance separately owes all three certification obligations in §7. -/
class SszSchema (α : Type) where
  /-- Raw descriptor selected by the schema owner. -/
  type : SszType
  /-- Source field names in order (F13); instance owners check the reference records. -/
  fieldNames : List String
  /-- Owner's wire-domain predicate, independent of execution validity. -/
  valid : α → Prop
  /-- Convert the complete value to its raw SSZ model. -/
  toValue : α → SszValue
  /-- Partial inverse metadata; the carrier itself certifies no inverse law. -/
  ofValue? : SszValue → Option α

/-- Forward bytes through the supplied dictionary and exact value-local support;
EELS `src/ethereum/utils/ssz.py:129–131`. Source correspondence remains separate. -/
def SszSchema.encodeBytes {α : Type} [s : SszSchema α]
    (a : α) (h : Ssz.Serializable s.type (s.toValue a)) : ByteArray :=
  Ssz.encode s.type (s.toValue a) h

/-- The complete ordinary raw-call equation, without unrelated schema premises. -/
theorem SszSchema.encodeBytes_eq {α : Type} [s : SszSchema α]
    (a : α) (h : Ssz.Serializable s.type (s.toValue a)) :
    SszSchema.encodeBytes a h = Ssz.encode s.type (s.toValue a) h := rfl

/-- Forward the root through the supplied dictionary and exact value-local support;
EELS `src/ethereum/utils/ssz.py:133–135`. Source correspondence remains separate. -/
def SszSchema.hashTreeRoot {α : Type} [s : SszSchema α]
    (a : α) (h : Ssz.Rootable s.type (s.toValue a)) : Base.Bytes32 :=
  Ssz.hashTreeRoot s.type (s.toValue a) h

/-- The complete ordinary raw-call equation, without unrelated schema premises. -/
theorem SszSchema.hashTreeRoot_eq {α : Type} [s : SszSchema α]
    (a : α) (h : Ssz.Rootable s.type (s.toValue a)) :
    SszSchema.hashTreeRoot a h = Ssz.hashTreeRoot s.type (s.toValue a) h := rfl

end STFSpec.Codec
