/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash

/-!
# Public-law RIPEMD-160 digest clients

Clients use only the Hash and Base public equations. No compression, digest,
padding or private byte-container representation is unfolded.
-/

open STFSpec.Base STFSpec.Hash STFSpec.Hash.Ripemd160

namespace STFSpec.Conformance.Hash

example (msg : ByteArray) : (ripemd160 msg).toBytes.size = 20 := size_ripemd160 msg

example (msg : ByteArray) : (pad msg).toList.take msg.size = msg.data.toList := pad_prefix msg

example (n : Nat) : Uint.ofLeBytes (lengthTrailer n) = (8 * n) % 2 ^ 64 := by
  rw [lengthTrailer_value, bitLength_mod]

-- This theorem exercises the MD4 low-64-bit length rule at a conceptual length.
example : Uint.ofLeBytes (lengthTrailer (2 ^ 61)) = 0 := by
  rw [lengthTrailer_value, bitLength_mod]

example (word : UInt32) :
    parseWord (wordByte word 0) (wordByte word 1) (wordByte word 2) (wordByte word 3) = word :=
  parseWord_wordByte word

example (state : Vector UInt32 5) (word : Fin 5) (byte : Fin 4) :
    (serialize state)[4 * word.val + byte.val]'(by rw [size_serialize]; omega) =
      wordByte state[word.val] byte.val := serialize_get state word byte

-- Caller discharges the complete-block premise through the public padding bound.
example (msg : ByteArray) (h : 64 ≤ msg.size) :
    (parseBlock (pad msg) 0)[15] =
      parseWord ((pad msg)[60]'(by rw [size_pad]; have := paddedLength_ge msg.size; omega))
        ((pad msg)[61]'(by rw [size_pad]; have := paddedLength_ge msg.size; omega))
        ((pad msg)[62]'(by rw [size_pad]; have := paddedLength_ge msg.size; omega))
        ((pad msg)[63]'(by rw [size_pad]; have := paddedLength_ge msg.size; omega)) := by
  apply parseBlock_get
  rw [size_pad]
  have := paddedLength_ge msg.size
  omega

-- A split block stream preserves the IV exactly once and the ascending offsets.
example (bytes : Bytes) (state : Vector UInt32 5) :
    blocks bytes 3 0 state = blocks bytes 2 64 (blocks bytes 1 0 state) := by
  simpa using blocks_add bytes 1 2 0 state

example (bytes : Bytes) (state : Vector UInt32 5) :
    ripemd160ToModel (blocks bytes 3 0 state) =
      Model.blocks bytes.toList 0 3 (ripemd160ToModel state) := blocks_model bytes 3 0 state

example (msg : ByteArray) : Model.Digest msg.data.toList (ripemd160 msg).toBytes.toList :=
  ripemd160_digest msg

example (n zeros : Nat) (hmod : (n + 1 + zeros) % 64 = 56) : zeroCount n ≤ zeros :=
  zeroCount_minimal n zeros hmod

example (a b c d : UInt8) :
    (parseWord a b c d).toNat = Uint.ofLeBytes (Bytes.ofList [a, b, c, d]) :=
  parseWord_value a b c d

example (bytes : Bytes) (offset : Nat) (h : bytes.size ≤ offset) :
    parseBlock bytes offset = Vector.replicate 16 0 := parseBlock_of_size_le bytes offset h

end STFSpec.Conformance.Hash
