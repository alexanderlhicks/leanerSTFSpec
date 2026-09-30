/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Hash.Blake2Parameters

/-!
# Raw BLAKE2F parser guards

Library `EthConformance`. Primary EIP-152 examples 3–8:
https://eips.ethereum.org/EIPS/eip-152#test-cases . These are parser-only
observations, including example 3's raw flag 2 and example 8's maximum rounds.
The asymmetric byte sequence independently exercises every lane and endian seam.
Spec guidance: `STFSpec/informal/modules/EthHash.md` §§3–4.
-/

namespace STFSpec.Conformance.Hash.Blake2Parameters
open STFSpec.Hash.Blake2b

private def eip152Input (roundsBytes : Vector UInt8 4) (flag : UInt8) : ByteArray :=
  ⟨roundsBytes.toArray ++ #[
      72, 201, 189, 242, 103, 230, 9, 106, 59, 167, 202, 132, 133, 174, 103, 187, 43, 248,
      148, 254, 114, 243, 110, 60, 241, 54, 29, 95, 58, 245, 79, 165, 209, 130, 230, 173,
      127, 82, 14, 81, 31, 108, 62, 43, 140, 104, 5, 155, 107, 189, 65, 251, 171, 217, 131,
      31, 121, 33, 126, 19, 25, 205, 224, 91, 97, 98, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
    ] ++ #[flag]⟩

set_option maxRecDepth 1024 in
private theorem eip152Input_size (roundsBytes : Vector UInt8 4) (flag : UInt8) :
    (eip152Input roundsBytes flag).size = 213 := by
  simp only [eip152Input, ByteArray.size, Array.size_append, Vector.size_toArray]
  rfl

private def eip152Params (roundsBytes : Vector UInt8 4) (flag : UInt8) : Params :=
  getParameters (eip152Input roundsBytes flag) (eip152Input_size roundsBytes flag)

-- EIP-152 example 3.
#guard eip152Params #v[0, 0, 0, 12] 2 =
  ({ rounds := 12
     h := #v[
       7640891576939301192, 13503953896175478587, 4354685564936845355, 11912009170470909681,
       5840696475078001361, 11170449401992604703, 2270897969802886507, 6620516959819538809
     ]
     m := #v[6513249, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
     t0 := 3
     t1 := 0
     f := 2 } : Params)

-- EIP-152 example 4.
#guard eip152Params #v[0, 0, 0, 0] 1 =
  ({ rounds := 0
     h := #v[
       7640891576939301192, 13503953896175478587, 4354685564936845355, 11912009170470909681,
       5840696475078001361, 11170449401992604703, 2270897969802886507, 6620516959819538809
     ]
     m := #v[6513249, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
     t0 := 3
     t1 := 0
     f := 1 } : Params)

-- EIP-152 example 5.
#guard eip152Params #v[0, 0, 0, 12] 1 =
  ({ rounds := 12
     h := #v[
       7640891576939301192, 13503953896175478587, 4354685564936845355, 11912009170470909681,
       5840696475078001361, 11170449401992604703, 2270897969802886507, 6620516959819538809
     ]
     m := #v[6513249, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
     t0 := 3
     t1 := 0
     f := 1 } : Params)

-- EIP-152 example 6.
#guard eip152Params #v[0, 0, 0, 12] 0 =
  ({ rounds := 12
     h := #v[
       7640891576939301192, 13503953896175478587, 4354685564936845355, 11912009170470909681,
       5840696475078001361, 11170449401992604703, 2270897969802886507, 6620516959819538809
     ]
     m := #v[6513249, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
     t0 := 3
     t1 := 0
     f := 0 } : Params)

-- EIP-152 example 7.
#guard eip152Params #v[0, 0, 0, 1] 1 =
  ({ rounds := 1
     h := #v[
       7640891576939301192, 13503953896175478587, 4354685564936845355, 11912009170470909681,
       5840696475078001361, 11170449401992604703, 2270897969802886507, 6620516959819538809
     ]
     m := #v[6513249, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
     t0 := 3
     t1 := 0
     f := 1 } : Params)

-- EIP-152 example 8.
#guard eip152Params #v[255, 255, 255, 255] 1 =
  ({ rounds := 4294967295
     h := #v[
       7640891576939301192, 13503953896175478587, 4354685564936845355, 11912009170470909681,
       5840696475078001361, 11170449401992604703, 2270897969802886507, 6620516959819538809
     ]
     m := #v[6513249, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
     t0 := 3
     t1 := 0
     f := 1 } : Params)

-- Raw flags cover the full byte domain; no Boolean coercion or rejection occurs.
#guard (List.range 256).all (fun f ↦ (eip152Params #v[1, 2, 3, 4] (UInt8.ofNat f)).f.toNat == f)

-- The high round bit is parsed without evaluating any compression rounds.
#guard (eip152Params #v[128, 0, 0, 0] 255).rounds.toNat = 2147483648

private def asymmetricInput : ByteArray :=
  ⟨Array.ofFn (fun i : Fin 213 ↦ UInt8.ofNat (37 * i.val + 11))⟩

private theorem asymmetricInput_size : asymmetricInput.size = 213 := by
  simp [asymmetricInput, ByteArray.size]

#guard getParameters asymmetricInput asymmetricInput_size =
  ({ rounds := 187716986
     h := #v[
       11708611582549935263, 14602218496056224967, 17495825409579226351,
       1942688249392741399, 4764237568877880383, 7657563007424236647, 10551168821435675791,
       13444775730646998199
     ]
     m := #v[
       16338382644169999583, 785245483983514631, 3606794803468653615, 6500120242015009879,
       9393726056026449023, 12287332965254548647, 15180939878760838351,
       18074546792283839735, 2521409632097354783, 5342677476605783111, 8236283290617222255,
       11129890199845321879, 14023497113351611583, 16917104026874612967,
       1363966866688128015, 4185516186173266999
     ]
     t0 := 7078841624719623263
     t1 := 9972447438731062407
     f := 175 } : Params)

#guard (serialize (getParameters asymmetricInput asymmetricInput_size)).data = asymmetricInput.data
#guard (serialize (eip152Params #v[255, 255, 255, 255] 2)).data =
  (eip152Input #v[255, 255, 255, 255] 2).data

end STFSpec.Conformance.Hash.Blake2Parameters
