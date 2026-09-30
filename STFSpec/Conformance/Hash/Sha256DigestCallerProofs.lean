/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash

/-!
# Public-law SHA-256 digest clients

Clients use only the Hash and Base public equations. No compression, digest,
padding or private byte-container representation is unfolded.
-/

open STFSpec.Base STFSpec.Hash STFSpec.Hash.Sha256

namespace STFSpec.Conformance.Hash

example (msg : ByteArray) : (sha256 msg).toBytes.size = 32 := size_sha256 msg

example (msg : ByteArray) : (pad msg).toList.take msg.size = msg.data.toList := pad_prefix msg

example (n : Nat) : Uint.ofBeBytes (lengthTrailer n) = (8 * n) % 2 ^ 64 := by
  rw [lengthTrailer_value, bitLength_mod]

example (n : Nat) (h : 8 * n < 2 ^ 64) : Uint.ofBeBytes (lengthTrailer n) = 8 * n := by
  rw [lengthTrailer_value, bitLength_of_fipsDomain _ h]

-- This theorem exercises the approved total extension at a conceptual length.
example : Uint.ofBeBytes (lengthTrailer (2 ^ 61)) = 0 := by
  rw [lengthTrailer_value, bitLength_mod]

example (word : UInt32) :
    parseWord (wordByte word 0) (wordByte word 1) (wordByte word 2) (wordByte word 3) = word :=
  parseWord_wordByte word

example (state : Vector UInt32 8) (word : Fin 8) (byte : Fin 4) :
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
example (bytes : Bytes) (state : Vector UInt32 8) :
    blocks bytes 3 0 state = blocks bytes 2 64 (blocks bytes 1 0 state) := by
  simpa using blocks_add bytes 1 2 0 state

example (bytes : Bytes) (state : Vector UInt32 8) :
    wordsModel (blocks bytes 3 0 state) =
      Model.blocks bytes.toList 0 3 (wordsModel state) := blocks_model bytes 3 0 state

example (msg : ByteArray) : Model.Digest msg.data.toList (sha256 msg).toBytes.toList :=
  sha256_digest msg

example (msg : ByteArray) (h : 8 * msg.size < 2 ^ 64) :
    Model.DigestOnPad (Model.fipsPad msg.data.toList) (sha256 msg).toBytes.toList :=
  sha256_fipsDigest msg h

end STFSpec.Conformance.Hash
