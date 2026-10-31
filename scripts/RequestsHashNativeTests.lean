/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

import STFSpec.Block
import STFSpec.Conformance.Block.RequestsHashGuards
import Lean

/-!
# Complete compiled execution-request commitment observations

Library `EthConformance`. Inputs transcribed from the independently frozen catalog;
the parser checks exact input identity and every output digest byte.
Spec guidance: `STFSpec/informal/modules/EthBlock.md` §§3/4/7.
-/

open STFSpec.Block Lean

private def digit (n : Nat) : Char := Char.ofNat (if n < 10 then 48 + n else 87 + n)
private def hex (data : ByteArray) : String :=
  String.ofList (data.data.toList.flatMap fun b ↦ [digit (b.toNat / 16), digit (b.toNat % 16)])
private def nibble (c : Char) : Except String Nat :=
  if '0' ≤ c ∧ c ≤ '9' then .ok (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then .ok (c.toNat - 87)
  else .error "noncanonical input hex"
private def unhex : List Char → Except String (List UInt8)
  | [] => .ok []
  | a :: b :: rest => do
    let x ← nibble a
    let y ← nibble b
    return UInt8.ofNat (16 * x + y) :: (← unhex rest)
  | [_] => .error "odd input hex"
private def emit (value : Json) : IO Unit := do (← IO.getStdout).putStrLn value.compress
private def emitCase (id : String) (texts : List String) : IO Unit := do
  let requests ← IO.ofExcept (texts.mapM fun text ↦ do
    let bytes ← unhex text.toList
    return bytes.toByteArray)
  emit (Json.mkObj [("id", toJson id), ("requests_hex", toJson (requests.map hex)),
    ("actual_hex", toJson (hex (computeRequestsHash requests).toBytes.toByteArray))])

/-- Emit every ordered request and all 32 actual digest bytes for the frozen catalog. -/
def main : IO Unit := do
  emit (Json.mkObj [("schema", toJson "requests-hash-v1"), ("count", toJson (298 : Nat))])
  emitCase "empty_list"
    []
  emitCase "one_empty"
    [""]
  emitCase "two_empty"
    ["",
     ""]
  emitCase "three_empty"
    ["",
     "",
     ""]
  emitCase "abc"
    ["616263"]
  emitCase "empty_then_abc"
    ["",
     "616263"]
  emitCase "abc_then_empty"
    ["616263",
     ""]
  emitCase "empty_abc_empty"
    ["",
     "616263",
     ""]
  emitCase "duplicate_abc"
    ["616263",
     "616263"]
  emitCase "a_b"
    ["61",
     "62"]
  emitCase "b_a"
    ["62",
     "61"]
  emitCase "ab"
    ["6162"]
  emitCase "a_bc"
    ["61",
     "6263"]
  emitCase "ab_c"
    ["6162",
     "63"]
  emitCase "prefix_increasing"
    ["00ff00",
     "01ff01",
     "02ff02",
     "03ff03",
     "04ff04"]
  emitCase "prefix_decreasing"
    ["04ff04",
     "03ff03",
     "02ff02",
     "01ff01",
     "00ff00"]
  emitCase "prefix_arbitrary"
    ["ff00",
     "8000",
     "0500",
     "00",
     ""]
  emitCase "inner_pattern_1"
    ["0b"]
  emitCase "inner_pattern_2"
    ["0b30"]
  emitCase "inner_pattern_31"
    ["0b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83a8cdf2173c61"]
  emitCase "inner_pattern_32"
    ["0b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83a8cdf2173c6186"]
  emitCase "inner_pattern_54"
    [("0b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83a8cdf2173c6186abd0f51a3f64" ++
      "89aed3f81d42678cb1d6fb20456a8fb4")]
  emitCase "inner_pattern_55"
    [("0b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83a8cdf2173c6186abd0f51a3f64" ++
      "89aed3f81d42678cb1d6fb20456a8fb4d9")]
  emitCase "inner_pattern_56"
    [("0b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83a8cdf2173c6186abd0f51a3f64" ++
      "89aed3f81d42678cb1d6fb20456a8fb4d9fe")]
  emitCase "inner_pattern_57"
    [("0b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83a8cdf2173c6186abd0f51a3f64" ++
      "89aed3f81d42678cb1d6fb20456a8fb4d9fe23")]
  emitCase "inner_pattern_63"
    [("0b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83a8cdf2173c6186abd0f51a3f64" ++
      "89aed3f81d42678cb1d6fb20456a8fb4d9fe23486d92b7dc01")]
  emitCase "inner_pattern_64"
    [("0b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83a8cdf2173c6186abd0f51a3f64" ++
      "89aed3f81d42678cb1d6fb20456a8fb4d9fe23486d92b7dc0126")]
  emitCase "inner_pattern_65"
    [("0b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83a8cdf2173c6186abd0f51a3f64" ++
      "89aed3f81d42678cb1d6fb20456a8fb4d9fe23486d92b7dc01264b")]
  emitCase "inner_pattern_119"
    [("0b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83a8cdf2173c6186abd0f51a3f64" ++
      "89aed3f81d42678cb1d6fb20456a8fb4d9fe23486d92b7dc01264b7095badf04294e7398bde2" ++
      "072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82a7ccf1163b60" ++
      "85aacff419")]
  emitCase "inner_pattern_120"
    [("0b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83a8cdf2173c6186abd0f51a3f64" ++
      "89aed3f81d42678cb1d6fb20456a8fb4d9fe23486d92b7dc01264b7095badf04294e7398bde2" ++
      "072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82a7ccf1163b60" ++
      "85aacff4193e")]
  emitCase "inner_pattern_127"
    [("0b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83a8cdf2173c6186abd0f51a3f64" ++
      "89aed3f81d42678cb1d6fb20456a8fb4d9fe23486d92b7dc01264b7095badf04294e7398bde2" ++
      "072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82a7ccf1163b60" ++
      "85aacff4193e6388add2f71c41")]
  emitCase "inner_pattern_128"
    [("0b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83a8cdf2173c6186abd0f51a3f64" ++
      "89aed3f81d42678cb1d6fb20456a8fb4d9fe23486d92b7dc01264b7095badf04294e7398bde2" ++
      "072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82a7ccf1163b60" ++
      "85aacff4193e6388add2f71c4166")]
  emitCase "inner_pattern_129"
    [("0b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83a8cdf2173c6186abd0f51a3f64" ++
      "89aed3f81d42678cb1d6fb20456a8fb4d9fe23486d92b7dc01264b7095badf04294e7398bde2" ++
      "072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82a7ccf1163b60" ++
      "85aacff4193e6388add2f71c41668b")]
  emitCase "outer_4_digests"
    ["00ff",
     "01fe",
     "02fd",
     "03fc"]
  emitCase "outer_5_digests"
    ["00ff",
     "01fe",
     "02fd",
     "03fc",
     "04fb"]
  emitCase "outer_7_digests"
    ["00ff",
     "01fe",
     "02fd",
     "03fc",
     "04fb",
     "05fa",
     "06f9"]
  emitCase "outer_8_digests"
    ["00ff",
     "01fe",
     "02fd",
     "03fc",
     "04fb",
     "05fa",
     "06f9",
     "07f8"]
  emitCase "outer_16_digests"
    ["00ff",
     "01fe",
     "02fd",
     "03fc",
     "04fb",
     "05fa",
     "06f9",
     "07f8",
     "08f7",
     "09f6",
     "0af5",
     "0bf4",
     "0cf3",
     "0df2",
     "0ef1",
     "0ff0"]
  emitCase "outer_17_digests"
    ["00ff",
     "01fe",
     "02fd",
     "03fc",
     "04fb",
     "05fa",
     "06f9",
     "07f8",
     "08f7",
     "09f6",
     "0af5",
     "0bf4",
     "0cf3",
     "0df2",
     "0ef1",
     "0ff0",
     "10ef"]
  emitCase "all_byte_values"
    [("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425" ++
      "262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b" ++
      "4c4d4e4f505152535455565758595a5b5c5d5e5f606162636465666768696a6b6c6d6e6f7071" ++
      "72737475767778797a7b7c7d7e7f808182838485868788898a8b8c8d8e8f9091929394959697" ++
      "98999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadaeafb0b1b2b3b4b5b6b7b8b9babbbcbd" ++
      "bebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3" ++
      "e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff")]
  emitCase "all_byte_values_reverse"
    [("fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0dfdedddcdbda" ++
      "d9d8d7d6d5d4d3d2d1d0cfcecdcccbcac9c8c7c6c5c4c3c2c1c0bfbebdbcbbbab9b8b7b6b5b4" ++
      "b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e" ++
      "8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a6968" ++
      "67666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a4948474645444342" ++
      "41403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c" ++
      "1b1a191817161514131211100f0e0d0c0b0a09080706050403020100")]
  emitCase "all_singletons_as_requests"
    ["00",
     "01",
     "02",
     "03",
     "04",
     "05",
     "06",
     "07",
     "08",
     "09",
     "0a",
     "0b",
     "0c",
     "0d",
     "0e",
     "0f",
     "10",
     "11",
     "12",
     "13",
     "14",
     "15",
     "16",
     "17",
     "18",
     "19",
     "1a",
     "1b",
     "1c",
     "1d",
     "1e",
     "1f",
     "20",
     "21",
     "22",
     "23",
     "24",
     "25",
     "26",
     "27",
     "28",
     "29",
     "2a",
     "2b",
     "2c",
     "2d",
     "2e",
     "2f",
     "30",
     "31",
     "32",
     "33",
     "34",
     "35",
     "36",
     "37",
     "38",
     "39",
     "3a",
     "3b",
     "3c",
     "3d",
     "3e",
     "3f",
     "40",
     "41",
     "42",
     "43",
     "44",
     "45",
     "46",
     "47",
     "48",
     "49",
     "4a",
     "4b",
     "4c",
     "4d",
     "4e",
     "4f",
     "50",
     "51",
     "52",
     "53",
     "54",
     "55",
     "56",
     "57",
     "58",
     "59",
     "5a",
     "5b",
     "5c",
     "5d",
     "5e",
     "5f",
     "60",
     "61",
     "62",
     "63",
     "64",
     "65",
     "66",
     "67",
     "68",
     "69",
     "6a",
     "6b",
     "6c",
     "6d",
     "6e",
     "6f",
     "70",
     "71",
     "72",
     "73",
     "74",
     "75",
     "76",
     "77",
     "78",
     "79",
     "7a",
     "7b",
     "7c",
     "7d",
     "7e",
     "7f",
     "80",
     "81",
     "82",
     "83",
     "84",
     "85",
     "86",
     "87",
     "88",
     "89",
     "8a",
     "8b",
     "8c",
     "8d",
     "8e",
     "8f",
     "90",
     "91",
     "92",
     "93",
     "94",
     "95",
     "96",
     "97",
     "98",
     "99",
     "9a",
     "9b",
     "9c",
     "9d",
     "9e",
     "9f",
     "a0",
     "a1",
     "a2",
     "a3",
     "a4",
     "a5",
     "a6",
     "a7",
     "a8",
     "a9",
     "aa",
     "ab",
     "ac",
     "ad",
     "ae",
     "af",
     "b0",
     "b1",
     "b2",
     "b3",
     "b4",
     "b5",
     "b6",
     "b7",
     "b8",
     "b9",
     "ba",
     "bb",
     "bc",
     "bd",
     "be",
     "bf",
     "c0",
     "c1",
     "c2",
     "c3",
     "c4",
     "c5",
     "c6",
     "c7",
     "c8",
     "c9",
     "ca",
     "cb",
     "cc",
     "cd",
     "ce",
     "cf",
     "d0",
     "d1",
     "d2",
     "d3",
     "d4",
     "d5",
     "d6",
     "d7",
     "d8",
     "d9",
     "da",
     "db",
     "dc",
     "dd",
     "de",
     "df",
     "e0",
     "e1",
     "e2",
     "e3",
     "e4",
     "e5",
     "e6",
     "e7",
     "e8",
     "e9",
     "ea",
     "eb",
     "ec",
     "ed",
     "ee",
     "ef",
     "f0",
     "f1",
     "f2",
     "f3",
     "f4",
     "f5",
     "f6",
     "f7",
     "f8",
     "f9",
     "fa",
     "fb",
     "fc",
     "fd",
     "fe",
     "ff"]
  emitCase "singleton_00"
    ["00"]
  emitCase "singleton_01"
    ["01"]
  emitCase "singleton_02"
    ["02"]
  emitCase "singleton_03"
    ["03"]
  emitCase "singleton_04"
    ["04"]
  emitCase "singleton_05"
    ["05"]
  emitCase "singleton_06"
    ["06"]
  emitCase "singleton_07"
    ["07"]
  emitCase "singleton_08"
    ["08"]
  emitCase "singleton_09"
    ["09"]
  emitCase "singleton_0a"
    ["0a"]
  emitCase "singleton_0b"
    ["0b"]
  emitCase "singleton_0c"
    ["0c"]
  emitCase "singleton_0d"
    ["0d"]
  emitCase "singleton_0e"
    ["0e"]
  emitCase "singleton_0f"
    ["0f"]
  emitCase "singleton_10"
    ["10"]
  emitCase "singleton_11"
    ["11"]
  emitCase "singleton_12"
    ["12"]
  emitCase "singleton_13"
    ["13"]
  emitCase "singleton_14"
    ["14"]
  emitCase "singleton_15"
    ["15"]
  emitCase "singleton_16"
    ["16"]
  emitCase "singleton_17"
    ["17"]
  emitCase "singleton_18"
    ["18"]
  emitCase "singleton_19"
    ["19"]
  emitCase "singleton_1a"
    ["1a"]
  emitCase "singleton_1b"
    ["1b"]
  emitCase "singleton_1c"
    ["1c"]
  emitCase "singleton_1d"
    ["1d"]
  emitCase "singleton_1e"
    ["1e"]
  emitCase "singleton_1f"
    ["1f"]
  emitCase "singleton_20"
    ["20"]
  emitCase "singleton_21"
    ["21"]
  emitCase "singleton_22"
    ["22"]
  emitCase "singleton_23"
    ["23"]
  emitCase "singleton_24"
    ["24"]
  emitCase "singleton_25"
    ["25"]
  emitCase "singleton_26"
    ["26"]
  emitCase "singleton_27"
    ["27"]
  emitCase "singleton_28"
    ["28"]
  emitCase "singleton_29"
    ["29"]
  emitCase "singleton_2a"
    ["2a"]
  emitCase "singleton_2b"
    ["2b"]
  emitCase "singleton_2c"
    ["2c"]
  emitCase "singleton_2d"
    ["2d"]
  emitCase "singleton_2e"
    ["2e"]
  emitCase "singleton_2f"
    ["2f"]
  emitCase "singleton_30"
    ["30"]
  emitCase "singleton_31"
    ["31"]
  emitCase "singleton_32"
    ["32"]
  emitCase "singleton_33"
    ["33"]
  emitCase "singleton_34"
    ["34"]
  emitCase "singleton_35"
    ["35"]
  emitCase "singleton_36"
    ["36"]
  emitCase "singleton_37"
    ["37"]
  emitCase "singleton_38"
    ["38"]
  emitCase "singleton_39"
    ["39"]
  emitCase "singleton_3a"
    ["3a"]
  emitCase "singleton_3b"
    ["3b"]
  emitCase "singleton_3c"
    ["3c"]
  emitCase "singleton_3d"
    ["3d"]
  emitCase "singleton_3e"
    ["3e"]
  emitCase "singleton_3f"
    ["3f"]
  emitCase "singleton_40"
    ["40"]
  emitCase "singleton_41"
    ["41"]
  emitCase "singleton_42"
    ["42"]
  emitCase "singleton_43"
    ["43"]
  emitCase "singleton_44"
    ["44"]
  emitCase "singleton_45"
    ["45"]
  emitCase "singleton_46"
    ["46"]
  emitCase "singleton_47"
    ["47"]
  emitCase "singleton_48"
    ["48"]
  emitCase "singleton_49"
    ["49"]
  emitCase "singleton_4a"
    ["4a"]
  emitCase "singleton_4b"
    ["4b"]
  emitCase "singleton_4c"
    ["4c"]
  emitCase "singleton_4d"
    ["4d"]
  emitCase "singleton_4e"
    ["4e"]
  emitCase "singleton_4f"
    ["4f"]
  emitCase "singleton_50"
    ["50"]
  emitCase "singleton_51"
    ["51"]
  emitCase "singleton_52"
    ["52"]
  emitCase "singleton_53"
    ["53"]
  emitCase "singleton_54"
    ["54"]
  emitCase "singleton_55"
    ["55"]
  emitCase "singleton_56"
    ["56"]
  emitCase "singleton_57"
    ["57"]
  emitCase "singleton_58"
    ["58"]
  emitCase "singleton_59"
    ["59"]
  emitCase "singleton_5a"
    ["5a"]
  emitCase "singleton_5b"
    ["5b"]
  emitCase "singleton_5c"
    ["5c"]
  emitCase "singleton_5d"
    ["5d"]
  emitCase "singleton_5e"
    ["5e"]
  emitCase "singleton_5f"
    ["5f"]
  emitCase "singleton_60"
    ["60"]
  emitCase "singleton_61"
    ["61"]
  emitCase "singleton_62"
    ["62"]
  emitCase "singleton_63"
    ["63"]
  emitCase "singleton_64"
    ["64"]
  emitCase "singleton_65"
    ["65"]
  emitCase "singleton_66"
    ["66"]
  emitCase "singleton_67"
    ["67"]
  emitCase "singleton_68"
    ["68"]
  emitCase "singleton_69"
    ["69"]
  emitCase "singleton_6a"
    ["6a"]
  emitCase "singleton_6b"
    ["6b"]
  emitCase "singleton_6c"
    ["6c"]
  emitCase "singleton_6d"
    ["6d"]
  emitCase "singleton_6e"
    ["6e"]
  emitCase "singleton_6f"
    ["6f"]
  emitCase "singleton_70"
    ["70"]
  emitCase "singleton_71"
    ["71"]
  emitCase "singleton_72"
    ["72"]
  emitCase "singleton_73"
    ["73"]
  emitCase "singleton_74"
    ["74"]
  emitCase "singleton_75"
    ["75"]
  emitCase "singleton_76"
    ["76"]
  emitCase "singleton_77"
    ["77"]
  emitCase "singleton_78"
    ["78"]
  emitCase "singleton_79"
    ["79"]
  emitCase "singleton_7a"
    ["7a"]
  emitCase "singleton_7b"
    ["7b"]
  emitCase "singleton_7c"
    ["7c"]
  emitCase "singleton_7d"
    ["7d"]
  emitCase "singleton_7e"
    ["7e"]
  emitCase "singleton_7f"
    ["7f"]
  emitCase "singleton_80"
    ["80"]
  emitCase "singleton_81"
    ["81"]
  emitCase "singleton_82"
    ["82"]
  emitCase "singleton_83"
    ["83"]
  emitCase "singleton_84"
    ["84"]
  emitCase "singleton_85"
    ["85"]
  emitCase "singleton_86"
    ["86"]
  emitCase "singleton_87"
    ["87"]
  emitCase "singleton_88"
    ["88"]
  emitCase "singleton_89"
    ["89"]
  emitCase "singleton_8a"
    ["8a"]
  emitCase "singleton_8b"
    ["8b"]
  emitCase "singleton_8c"
    ["8c"]
  emitCase "singleton_8d"
    ["8d"]
  emitCase "singleton_8e"
    ["8e"]
  emitCase "singleton_8f"
    ["8f"]
  emitCase "singleton_90"
    ["90"]
  emitCase "singleton_91"
    ["91"]
  emitCase "singleton_92"
    ["92"]
  emitCase "singleton_93"
    ["93"]
  emitCase "singleton_94"
    ["94"]
  emitCase "singleton_95"
    ["95"]
  emitCase "singleton_96"
    ["96"]
  emitCase "singleton_97"
    ["97"]
  emitCase "singleton_98"
    ["98"]
  emitCase "singleton_99"
    ["99"]
  emitCase "singleton_9a"
    ["9a"]
  emitCase "singleton_9b"
    ["9b"]
  emitCase "singleton_9c"
    ["9c"]
  emitCase "singleton_9d"
    ["9d"]
  emitCase "singleton_9e"
    ["9e"]
  emitCase "singleton_9f"
    ["9f"]
  emitCase "singleton_a0"
    ["a0"]
  emitCase "singleton_a1"
    ["a1"]
  emitCase "singleton_a2"
    ["a2"]
  emitCase "singleton_a3"
    ["a3"]
  emitCase "singleton_a4"
    ["a4"]
  emitCase "singleton_a5"
    ["a5"]
  emitCase "singleton_a6"
    ["a6"]
  emitCase "singleton_a7"
    ["a7"]
  emitCase "singleton_a8"
    ["a8"]
  emitCase "singleton_a9"
    ["a9"]
  emitCase "singleton_aa"
    ["aa"]
  emitCase "singleton_ab"
    ["ab"]
  emitCase "singleton_ac"
    ["ac"]
  emitCase "singleton_ad"
    ["ad"]
  emitCase "singleton_ae"
    ["ae"]
  emitCase "singleton_af"
    ["af"]
  emitCase "singleton_b0"
    ["b0"]
  emitCase "singleton_b1"
    ["b1"]
  emitCase "singleton_b2"
    ["b2"]
  emitCase "singleton_b3"
    ["b3"]
  emitCase "singleton_b4"
    ["b4"]
  emitCase "singleton_b5"
    ["b5"]
  emitCase "singleton_b6"
    ["b6"]
  emitCase "singleton_b7"
    ["b7"]
  emitCase "singleton_b8"
    ["b8"]
  emitCase "singleton_b9"
    ["b9"]
  emitCase "singleton_ba"
    ["ba"]
  emitCase "singleton_bb"
    ["bb"]
  emitCase "singleton_bc"
    ["bc"]
  emitCase "singleton_bd"
    ["bd"]
  emitCase "singleton_be"
    ["be"]
  emitCase "singleton_bf"
    ["bf"]
  emitCase "singleton_c0"
    ["c0"]
  emitCase "singleton_c1"
    ["c1"]
  emitCase "singleton_c2"
    ["c2"]
  emitCase "singleton_c3"
    ["c3"]
  emitCase "singleton_c4"
    ["c4"]
  emitCase "singleton_c5"
    ["c5"]
  emitCase "singleton_c6"
    ["c6"]
  emitCase "singleton_c7"
    ["c7"]
  emitCase "singleton_c8"
    ["c8"]
  emitCase "singleton_c9"
    ["c9"]
  emitCase "singleton_ca"
    ["ca"]
  emitCase "singleton_cb"
    ["cb"]
  emitCase "singleton_cc"
    ["cc"]
  emitCase "singleton_cd"
    ["cd"]
  emitCase "singleton_ce"
    ["ce"]
  emitCase "singleton_cf"
    ["cf"]
  emitCase "singleton_d0"
    ["d0"]
  emitCase "singleton_d1"
    ["d1"]
  emitCase "singleton_d2"
    ["d2"]
  emitCase "singleton_d3"
    ["d3"]
  emitCase "singleton_d4"
    ["d4"]
  emitCase "singleton_d5"
    ["d5"]
  emitCase "singleton_d6"
    ["d6"]
  emitCase "singleton_d7"
    ["d7"]
  emitCase "singleton_d8"
    ["d8"]
  emitCase "singleton_d9"
    ["d9"]
  emitCase "singleton_da"
    ["da"]
  emitCase "singleton_db"
    ["db"]
  emitCase "singleton_dc"
    ["dc"]
  emitCase "singleton_dd"
    ["dd"]
  emitCase "singleton_de"
    ["de"]
  emitCase "singleton_df"
    ["df"]
  emitCase "singleton_e0"
    ["e0"]
  emitCase "singleton_e1"
    ["e1"]
  emitCase "singleton_e2"
    ["e2"]
  emitCase "singleton_e3"
    ["e3"]
  emitCase "singleton_e4"
    ["e4"]
  emitCase "singleton_e5"
    ["e5"]
  emitCase "singleton_e6"
    ["e6"]
  emitCase "singleton_e7"
    ["e7"]
  emitCase "singleton_e8"
    ["e8"]
  emitCase "singleton_e9"
    ["e9"]
  emitCase "singleton_ea"
    ["ea"]
  emitCase "singleton_eb"
    ["eb"]
  emitCase "singleton_ec"
    ["ec"]
  emitCase "singleton_ed"
    ["ed"]
  emitCase "singleton_ee"
    ["ee"]
  emitCase "singleton_ef"
    ["ef"]
  emitCase "singleton_f0"
    ["f0"]
  emitCase "singleton_f1"
    ["f1"]
  emitCase "singleton_f2"
    ["f2"]
  emitCase "singleton_f3"
    ["f3"]
  emitCase "singleton_f4"
    ["f4"]
  emitCase "singleton_f5"
    ["f5"]
  emitCase "singleton_f6"
    ["f6"]
  emitCase "singleton_f7"
    ["f7"]
  emitCase "singleton_f8"
    ["f8"]
  emitCase "singleton_f9"
    ["f9"]
  emitCase "singleton_fa"
    ["fa"]
  emitCase "singleton_fb"
    ["fb"]
  emitCase "singleton_fc"
    ["fc"]
  emitCase "singleton_fd"
    ["fd"]
  emitCase "singleton_fe"
    ["fe"]
  emitCase "singleton_ff"
    ["ff"]
  emit (Json.mkObj [("end", toJson true), ("count", toJson (298 : Nat))])
