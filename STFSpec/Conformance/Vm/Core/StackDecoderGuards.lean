/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Vm.Core

/-!
# Complete scalar decoder controls

Library `EthConformance`. All 256 bytes per decoder are compared with frozen
complete literal results, including both ordered pair coordinates and exact errors.
Spec guidance: `STFSpec/informal/modules/EthVmCore.md` §§3/4/7.
-/

namespace STFSpec.Conformance.Vm.Core.StackDecoderGuards
open STFSpec.Vm.Core

private def single (x : UInt8) (expected : Option Nat) : Bool :=
  match decodeSingle x, expected with
  | .ok n, some m => n == m
  | .error .invalidParameter, none => true
  | _, _ => false

private def pair (x : UInt8) (expected : Option (Nat × Nat)) : Bool :=
  match decodePair x, expected with
  | .ok (n,m), some (i,j) => n == i && m == j
  | .error .invalidParameter, none => true
  | _, _ => false

#guard single 0 (some 145)
#guard single 1 (some 146)
#guard single 2 (some 147)
#guard single 3 (some 148)
#guard single 4 (some 149)
#guard single 5 (some 150)
#guard single 6 (some 151)
#guard single 7 (some 152)
#guard single 8 (some 153)
#guard single 9 (some 154)
#guard single 10 (some 155)
#guard single 11 (some 156)
#guard single 12 (some 157)
#guard single 13 (some 158)
#guard single 14 (some 159)
#guard single 15 (some 160)
#guard single 16 (some 161)
#guard single 17 (some 162)
#guard single 18 (some 163)
#guard single 19 (some 164)
#guard single 20 (some 165)
#guard single 21 (some 166)
#guard single 22 (some 167)
#guard single 23 (some 168)
#guard single 24 (some 169)
#guard single 25 (some 170)
#guard single 26 (some 171)
#guard single 27 (some 172)
#guard single 28 (some 173)
#guard single 29 (some 174)
#guard single 30 (some 175)
#guard single 31 (some 176)
#guard single 32 (some 177)
#guard single 33 (some 178)
#guard single 34 (some 179)
#guard single 35 (some 180)
#guard single 36 (some 181)
#guard single 37 (some 182)
#guard single 38 (some 183)
#guard single 39 (some 184)
#guard single 40 (some 185)
#guard single 41 (some 186)
#guard single 42 (some 187)
#guard single 43 (some 188)
#guard single 44 (some 189)
#guard single 45 (some 190)
#guard single 46 (some 191)
#guard single 47 (some 192)
#guard single 48 (some 193)
#guard single 49 (some 194)
#guard single 50 (some 195)
#guard single 51 (some 196)
#guard single 52 (some 197)
#guard single 53 (some 198)
#guard single 54 (some 199)
#guard single 55 (some 200)
#guard single 56 (some 201)
#guard single 57 (some 202)
#guard single 58 (some 203)
#guard single 59 (some 204)
#guard single 60 (some 205)
#guard single 61 (some 206)
#guard single 62 (some 207)
#guard single 63 (some 208)
#guard single 64 (some 209)
#guard single 65 (some 210)
#guard single 66 (some 211)
#guard single 67 (some 212)
#guard single 68 (some 213)
#guard single 69 (some 214)
#guard single 70 (some 215)
#guard single 71 (some 216)
#guard single 72 (some 217)
#guard single 73 (some 218)
#guard single 74 (some 219)
#guard single 75 (some 220)
#guard single 76 (some 221)
#guard single 77 (some 222)
#guard single 78 (some 223)
#guard single 79 (some 224)
#guard single 80 (some 225)
#guard single 81 (some 226)
#guard single 82 (some 227)
#guard single 83 (some 228)
#guard single 84 (some 229)
#guard single 85 (some 230)
#guard single 86 (some 231)
#guard single 87 (some 232)
#guard single 88 (some 233)
#guard single 89 (some 234)
#guard single 90 (some 235)
#guard single 91 none
#guard single 92 none
#guard single 93 none
#guard single 94 none
#guard single 95 none
#guard single 96 none
#guard single 97 none
#guard single 98 none
#guard single 99 none
#guard single 100 none
#guard single 101 none
#guard single 102 none
#guard single 103 none
#guard single 104 none
#guard single 105 none
#guard single 106 none
#guard single 107 none
#guard single 108 none
#guard single 109 none
#guard single 110 none
#guard single 111 none
#guard single 112 none
#guard single 113 none
#guard single 114 none
#guard single 115 none
#guard single 116 none
#guard single 117 none
#guard single 118 none
#guard single 119 none
#guard single 120 none
#guard single 121 none
#guard single 122 none
#guard single 123 none
#guard single 124 none
#guard single 125 none
#guard single 126 none
#guard single 127 none
#guard single 128 (some 17)
#guard single 129 (some 18)
#guard single 130 (some 19)
#guard single 131 (some 20)
#guard single 132 (some 21)
#guard single 133 (some 22)
#guard single 134 (some 23)
#guard single 135 (some 24)
#guard single 136 (some 25)
#guard single 137 (some 26)
#guard single 138 (some 27)
#guard single 139 (some 28)
#guard single 140 (some 29)
#guard single 141 (some 30)
#guard single 142 (some 31)
#guard single 143 (some 32)
#guard single 144 (some 33)
#guard single 145 (some 34)
#guard single 146 (some 35)
#guard single 147 (some 36)
#guard single 148 (some 37)
#guard single 149 (some 38)
#guard single 150 (some 39)
#guard single 151 (some 40)
#guard single 152 (some 41)
#guard single 153 (some 42)
#guard single 154 (some 43)
#guard single 155 (some 44)
#guard single 156 (some 45)
#guard single 157 (some 46)
#guard single 158 (some 47)
#guard single 159 (some 48)
#guard single 160 (some 49)
#guard single 161 (some 50)
#guard single 162 (some 51)
#guard single 163 (some 52)
#guard single 164 (some 53)
#guard single 165 (some 54)
#guard single 166 (some 55)
#guard single 167 (some 56)
#guard single 168 (some 57)
#guard single 169 (some 58)
#guard single 170 (some 59)
#guard single 171 (some 60)
#guard single 172 (some 61)
#guard single 173 (some 62)
#guard single 174 (some 63)
#guard single 175 (some 64)
#guard single 176 (some 65)
#guard single 177 (some 66)
#guard single 178 (some 67)
#guard single 179 (some 68)
#guard single 180 (some 69)
#guard single 181 (some 70)
#guard single 182 (some 71)
#guard single 183 (some 72)
#guard single 184 (some 73)
#guard single 185 (some 74)
#guard single 186 (some 75)
#guard single 187 (some 76)
#guard single 188 (some 77)
#guard single 189 (some 78)
#guard single 190 (some 79)
#guard single 191 (some 80)
#guard single 192 (some 81)
#guard single 193 (some 82)
#guard single 194 (some 83)
#guard single 195 (some 84)
#guard single 196 (some 85)
#guard single 197 (some 86)
#guard single 198 (some 87)
#guard single 199 (some 88)
#guard single 200 (some 89)
#guard single 201 (some 90)
#guard single 202 (some 91)
#guard single 203 (some 92)
#guard single 204 (some 93)
#guard single 205 (some 94)
#guard single 206 (some 95)
#guard single 207 (some 96)
#guard single 208 (some 97)
#guard single 209 (some 98)
#guard single 210 (some 99)
#guard single 211 (some 100)
#guard single 212 (some 101)
#guard single 213 (some 102)
#guard single 214 (some 103)
#guard single 215 (some 104)
#guard single 216 (some 105)
#guard single 217 (some 106)
#guard single 218 (some 107)
#guard single 219 (some 108)
#guard single 220 (some 109)
#guard single 221 (some 110)
#guard single 222 (some 111)
#guard single 223 (some 112)
#guard single 224 (some 113)
#guard single 225 (some 114)
#guard single 226 (some 115)
#guard single 227 (some 116)
#guard single 228 (some 117)
#guard single 229 (some 118)
#guard single 230 (some 119)
#guard single 231 (some 120)
#guard single 232 (some 121)
#guard single 233 (some 122)
#guard single 234 (some 123)
#guard single 235 (some 124)
#guard single 236 (some 125)
#guard single 237 (some 126)
#guard single 238 (some 127)
#guard single 239 (some 128)
#guard single 240 (some 129)
#guard single 241 (some 130)
#guard single 242 (some 131)
#guard single 243 (some 132)
#guard single 244 (some 133)
#guard single 245 (some 134)
#guard single 246 (some 135)
#guard single 247 (some 136)
#guard single 248 (some 137)
#guard single 249 (some 138)
#guard single 250 (some 139)
#guard single 251 (some 140)
#guard single 252 (some 141)
#guard single 253 (some 142)
#guard single 254 (some 143)
#guard single 255 (some 144)
#guard pair 0 (some (9, 16))
#guard pair 1 (some (9, 15))
#guard pair 2 (some (9, 14))
#guard pair 3 (some (9, 13))
#guard pair 4 (some (9, 12))
#guard pair 5 (some (9, 11))
#guard pair 6 (some (9, 10))
#guard pair 7 (some (9, 21))
#guard pair 8 (some (8, 21))
#guard pair 9 (some (7, 21))
#guard pair 10 (some (6, 21))
#guard pair 11 (some (5, 21))
#guard pair 12 (some (4, 21))
#guard pair 13 (some (3, 21))
#guard pair 14 (some (2, 21))
#guard pair 15 (some (1, 21))
#guard pair 16 (some (10, 16))
#guard pair 17 (some (10, 15))
#guard pair 18 (some (10, 14))
#guard pair 19 (some (10, 13))
#guard pair 20 (some (10, 12))
#guard pair 21 (some (10, 11))
#guard pair 22 (some (10, 20))
#guard pair 23 (some (9, 20))
#guard pair 24 (some (8, 20))
#guard pair 25 (some (7, 20))
#guard pair 26 (some (6, 20))
#guard pair 27 (some (5, 20))
#guard pair 28 (some (4, 20))
#guard pair 29 (some (3, 20))
#guard pair 30 (some (2, 20))
#guard pair 31 (some (1, 20))
#guard pair 32 (some (11, 16))
#guard pair 33 (some (11, 15))
#guard pair 34 (some (11, 14))
#guard pair 35 (some (11, 13))
#guard pair 36 (some (11, 12))
#guard pair 37 (some (11, 19))
#guard pair 38 (some (10, 19))
#guard pair 39 (some (9, 19))
#guard pair 40 (some (8, 19))
#guard pair 41 (some (7, 19))
#guard pair 42 (some (6, 19))
#guard pair 43 (some (5, 19))
#guard pair 44 (some (4, 19))
#guard pair 45 (some (3, 19))
#guard pair 46 (some (2, 19))
#guard pair 47 (some (1, 19))
#guard pair 48 (some (12, 16))
#guard pair 49 (some (12, 15))
#guard pair 50 (some (12, 14))
#guard pair 51 (some (12, 13))
#guard pair 52 (some (12, 18))
#guard pair 53 (some (11, 18))
#guard pair 54 (some (10, 18))
#guard pair 55 (some (9, 18))
#guard pair 56 (some (8, 18))
#guard pair 57 (some (7, 18))
#guard pair 58 (some (6, 18))
#guard pair 59 (some (5, 18))
#guard pair 60 (some (4, 18))
#guard pair 61 (some (3, 18))
#guard pair 62 (some (2, 18))
#guard pair 63 (some (1, 18))
#guard pair 64 (some (13, 16))
#guard pair 65 (some (13, 15))
#guard pair 66 (some (13, 14))
#guard pair 67 (some (13, 17))
#guard pair 68 (some (12, 17))
#guard pair 69 (some (11, 17))
#guard pair 70 (some (10, 17))
#guard pair 71 (some (9, 17))
#guard pair 72 (some (8, 17))
#guard pair 73 (some (7, 17))
#guard pair 74 (some (6, 17))
#guard pair 75 (some (5, 17))
#guard pair 76 (some (4, 17))
#guard pair 77 (some (3, 17))
#guard pair 78 (some (2, 17))
#guard pair 79 (some (1, 17))
#guard pair 80 (some (14, 16))
#guard pair 81 (some (14, 15))
#guard pair 82 none
#guard pair 83 none
#guard pair 84 none
#guard pair 85 none
#guard pair 86 none
#guard pair 87 none
#guard pair 88 none
#guard pair 89 none
#guard pair 90 none
#guard pair 91 none
#guard pair 92 none
#guard pair 93 none
#guard pair 94 none
#guard pair 95 none
#guard pair 96 none
#guard pair 97 none
#guard pair 98 none
#guard pair 99 none
#guard pair 100 none
#guard pair 101 none
#guard pair 102 none
#guard pair 103 none
#guard pair 104 none
#guard pair 105 none
#guard pair 106 none
#guard pair 107 none
#guard pair 108 none
#guard pair 109 none
#guard pair 110 none
#guard pair 111 none
#guard pair 112 none
#guard pair 113 none
#guard pair 114 none
#guard pair 115 none
#guard pair 116 none
#guard pair 117 none
#guard pair 118 none
#guard pair 119 none
#guard pair 120 none
#guard pair 121 none
#guard pair 122 none
#guard pair 123 none
#guard pair 124 none
#guard pair 125 none
#guard pair 126 none
#guard pair 127 none
#guard pair 128 (some (1, 16))
#guard pair 129 (some (1, 15))
#guard pair 130 (some (1, 14))
#guard pair 131 (some (1, 13))
#guard pair 132 (some (1, 12))
#guard pair 133 (some (1, 11))
#guard pair 134 (some (1, 10))
#guard pair 135 (some (1, 9))
#guard pair 136 (some (1, 8))
#guard pair 137 (some (1, 7))
#guard pair 138 (some (1, 6))
#guard pair 139 (some (1, 5))
#guard pair 140 (some (1, 4))
#guard pair 141 (some (1, 3))
#guard pair 142 (some (1, 2))
#guard pair 143 (some (1, 29))
#guard pair 144 (some (2, 16))
#guard pair 145 (some (2, 15))
#guard pair 146 (some (2, 14))
#guard pair 147 (some (2, 13))
#guard pair 148 (some (2, 12))
#guard pair 149 (some (2, 11))
#guard pair 150 (some (2, 10))
#guard pair 151 (some (2, 9))
#guard pair 152 (some (2, 8))
#guard pair 153 (some (2, 7))
#guard pair 154 (some (2, 6))
#guard pair 155 (some (2, 5))
#guard pair 156 (some (2, 4))
#guard pair 157 (some (2, 3))
#guard pair 158 (some (2, 28))
#guard pair 159 (some (1, 28))
#guard pair 160 (some (3, 16))
#guard pair 161 (some (3, 15))
#guard pair 162 (some (3, 14))
#guard pair 163 (some (3, 13))
#guard pair 164 (some (3, 12))
#guard pair 165 (some (3, 11))
#guard pair 166 (some (3, 10))
#guard pair 167 (some (3, 9))
#guard pair 168 (some (3, 8))
#guard pair 169 (some (3, 7))
#guard pair 170 (some (3, 6))
#guard pair 171 (some (3, 5))
#guard pair 172 (some (3, 4))
#guard pair 173 (some (3, 27))
#guard pair 174 (some (2, 27))
#guard pair 175 (some (1, 27))
#guard pair 176 (some (4, 16))
#guard pair 177 (some (4, 15))
#guard pair 178 (some (4, 14))
#guard pair 179 (some (4, 13))
#guard pair 180 (some (4, 12))
#guard pair 181 (some (4, 11))
#guard pair 182 (some (4, 10))
#guard pair 183 (some (4, 9))
#guard pair 184 (some (4, 8))
#guard pair 185 (some (4, 7))
#guard pair 186 (some (4, 6))
#guard pair 187 (some (4, 5))
#guard pair 188 (some (4, 26))
#guard pair 189 (some (3, 26))
#guard pair 190 (some (2, 26))
#guard pair 191 (some (1, 26))
#guard pair 192 (some (5, 16))
#guard pair 193 (some (5, 15))
#guard pair 194 (some (5, 14))
#guard pair 195 (some (5, 13))
#guard pair 196 (some (5, 12))
#guard pair 197 (some (5, 11))
#guard pair 198 (some (5, 10))
#guard pair 199 (some (5, 9))
#guard pair 200 (some (5, 8))
#guard pair 201 (some (5, 7))
#guard pair 202 (some (5, 6))
#guard pair 203 (some (5, 25))
#guard pair 204 (some (4, 25))
#guard pair 205 (some (3, 25))
#guard pair 206 (some (2, 25))
#guard pair 207 (some (1, 25))
#guard pair 208 (some (6, 16))
#guard pair 209 (some (6, 15))
#guard pair 210 (some (6, 14))
#guard pair 211 (some (6, 13))
#guard pair 212 (some (6, 12))
#guard pair 213 (some (6, 11))
#guard pair 214 (some (6, 10))
#guard pair 215 (some (6, 9))
#guard pair 216 (some (6, 8))
#guard pair 217 (some (6, 7))
#guard pair 218 (some (6, 24))
#guard pair 219 (some (5, 24))
#guard pair 220 (some (4, 24))
#guard pair 221 (some (3, 24))
#guard pair 222 (some (2, 24))
#guard pair 223 (some (1, 24))
#guard pair 224 (some (7, 16))
#guard pair 225 (some (7, 15))
#guard pair 226 (some (7, 14))
#guard pair 227 (some (7, 13))
#guard pair 228 (some (7, 12))
#guard pair 229 (some (7, 11))
#guard pair 230 (some (7, 10))
#guard pair 231 (some (7, 9))
#guard pair 232 (some (7, 8))
#guard pair 233 (some (7, 23))
#guard pair 234 (some (6, 23))
#guard pair 235 (some (5, 23))
#guard pair 236 (some (4, 23))
#guard pair 237 (some (3, 23))
#guard pair 238 (some (2, 23))
#guard pair 239 (some (1, 23))
#guard pair 240 (some (8, 16))
#guard pair 241 (some (8, 15))
#guard pair 242 (some (8, 14))
#guard pair 243 (some (8, 13))
#guard pair 244 (some (8, 12))
#guard pair 245 (some (8, 11))
#guard pair 246 (some (8, 10))
#guard pair 247 (some (8, 9))
#guard pair 248 (some (8, 22))
#guard pair 249 (some (7, 22))
#guard pair 250 (some (6, 22))
#guard pair 251 (some (5, 22))
#guard pair 252 (some (4, 22))
#guard pair 253 (some (3, 22))
#guard pair 254 (some (2, 22))
#guard pair 255 (some (1, 22))

end STFSpec.Conformance.Vm.Core.StackDecoderGuards
