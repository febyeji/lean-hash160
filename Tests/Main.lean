import LeanHash160

namespace LeanHash160.Tests

private def hexDigit (value : Nat) : Char :=
  if value < 10 then Char.ofNat (0x30 + value) else Char.ofNat (0x57 + value)

private def byteHex (byte : UInt8) : String :=
  String.ofList [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)]

private def toHex (bytes : ByteArray) : String :=
  String.join (bytes.data.toList.map byteHex)

private def repeatedByte (byte : UInt8) (count : Nat) : ByteArray := Id.run do
  let mut output := ByteArray.empty
  for _ in [0:count] do
    output := output.push byte
  return output

private def patternedBytes (count : Nat) : ByteArray := Id.run do
  let mut output := ByteArray.empty
  for index in [0:count] do
    output := output.push (UInt8.ofNat index)
  return output

private structure Vector where
  name : String
  input : ByteArray
  expected : String

private structure BoundaryVector where
  length : Nat
  sha256 : String
  ripemd160 : String
  hash160 : String

private def runVectors
    (algorithm : String) (digest : ByteArray → ByteArray)
    (vectors : List Vector) : IO Bool := do
  let mut allPassed := true
  for vector in vectors do
    let actual := toHex (digest vector.input)
    let passed := actual == vector.expected
    if !passed then
      allPassed := false
    IO.println s!"[{if passed then "PASS" else "FAIL"}] {algorithm} {vector.name}"
    if !passed then
      IO.println s!"  expected: {vector.expected}"
      IO.println s!"  actual:   {actual}"
  return allPassed

private def runBoundaryVectors (vectors : List BoundaryVector) : IO Bool := do
  let mut allPassed := true
  for vector in vectors do
    let input := patternedBytes vector.length
    let results := [
      ("SHA-256", toHex (SHA256.hash input), vector.sha256),
      ("RIPEMD-160", toHex (RIPEMD160.hash input), vector.ripemd160),
      ("HASH160", toHex (hash160 input), vector.hash160)
    ]
    for (algorithm, actual, expected) in results do
      let passed := actual == expected
      if !passed then
        allPassed := false
      IO.println s!"[{if passed then "PASS" else "FAIL"}] {algorithm} boundary-{vector.length}"
      if !passed then
        IO.println s!"  expected: {expected}"
        IO.println s!"  actual:   {actual}"
  return allPassed

private def sha256Vectors : List Vector := [
  { name := "empty", input := ByteArray.empty,
    expected := "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" },
  { name := "abc", input := "abc".toUTF8,
    expected := "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" },
  { name := "56-byte multi-block",
    input := "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8,
    expected := "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" },
  { name := "million a", input := repeatedByte 0x61 1000000,
    expected := "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0" }
]

private def ripemd160Vectors : List Vector := [
  { name := "empty", input := ByteArray.empty,
    expected := "9c1185a5c5e9fc54612808977ee8f548b2258d31" },
  { name := "a", input := "a".toUTF8,
    expected := "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe" },
  { name := "abc", input := "abc".toUTF8,
    expected := "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc" },
  { name := "message digest", input := "message digest".toUTF8,
    expected := "5d0689ef49d2fae572b881b123a85ffa21595f36" },
  { name := "alphabet", input := "abcdefghijklmnopqrstuvwxyz".toUTF8,
    expected := "f71c27109c692c1b56bbdceb5b9d2865b3708dbc" },
  { name := "56-byte multi-block",
    input := "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8,
    expected := "12a053384a9c0c88e405a06c27dcf49ada62eb2b" },
  { name := "alphanumeric",
    input := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789".toUTF8,
    expected := "b0e20b6e3116640286ed3a87a5713079b21f5189" },
  { name := "eight numeric blocks",
    input := "12345678901234567890123456789012345678901234567890123456789012345678901234567890".toUTF8,
    expected := "9b752e45573d4b39f4dbd3323cab82bf63326bfb" },
  { name := "million a", input := repeatedByte 0x61 1000000,
    expected := "52783243c1697bdbe16d37f97f68f08325dc1528" }
]

private def oracleCompressedKey : ByteArray := ⟨#[
  0x02, 0xd7, 0x92, 0x4d, 0x4f, 0x7d, 0x43, 0xea, 0x96, 0x5a, 0x46,
  0x5a, 0xe3, 0x09, 0x5f, 0xf4, 0x11, 0x31, 0xe5, 0x94, 0x6f, 0x3c,
  0x85, 0xf7, 0x9e, 0x44, 0xad, 0xbc, 0xf8, 0xe2, 0x7e, 0x08, 0x0e]⟩

private def hash160Vectors : List Vector := [
  { name := "empty", input := ByteArray.empty,
    expected := "b472a266d0bd89c13706a4132ccfb16f7c3b9fcb" },
  { name := "abc", input := "abc".toUTF8,
    expected := "bb1be98c142444d7a56aa3981c3942a978e4dc33" },
  { name := "compressed public key", input := oracleCompressedKey,
    expected := "9fc5dbe5efdce10374a4dd4053c93af540211718" }
]

/-!
Expected values were generated independently with Python's `hashlib` backed
by OpenSSL. These lengths exercise both sides of the 56-byte padding boundary
and transitions between 64-byte compression blocks.
-/
private def boundaryVectors : List BoundaryVector := [
  { length := 55,
    sha256 := "463eb28e72f82e0a96c0a4cc53690c571281131f672aa229e0d45ae59b598b59",
    ripemd160 := "3c86963b3ff646a65ae42996e9664c747cc7e5e6",
    hash160 := "bf13f7b98f39c80e64ac320ce6550f2f1faa1ce1" },
  { length := 56,
    sha256 := "da2ae4d6b36748f2a318f23e7ab1dfdf45acdc9d049bd80e59de82a60895f562",
    ripemd160 := "ebdd79cfd4fd9949ef8089673d2620427f487cfb",
    hash160 := "6e02e5a92245d871fa8b65679d9f2457164ecd6f" },
  { length := 63,
    sha256 := "29af2686fd53374a36b0846694cc342177e428d1647515f078784d69cdb9e488",
    ripemd160 := "6d31d3d634b4a7aa15914c239576eb1956f2d9a4",
    hash160 := "81bd7fb9b40411d56281be8aae04cc1bb2a39cd9" },
  { length := 64,
    sha256 := "fdeab9acf3710362bd2658cdc9a29e8f9c757fcf9811603a8c447cd1d9151108",
    ripemd160 := "2581f5e9f957b44b0fa24d31996de47409dd1e0f",
    hash160 := "dd21d9434f79e153b82e7d204ea5279200d0d022" },
  { length := 65,
    sha256 := "4bfd2c8b6f1eec7a2afeb48b934ee4b2694182027e6d0fc075074f2fabb31781",
    ripemd160 := "109949b95341eeea7365e8ac4d0d3883d98f709a",
    hash160 := "e79158e0bceab6687018993aee8786b990a82373" },
  { length := 119,
    sha256 := "da18797ed7c3a777f0847f429724a2d8cd5138e6ed2895c3fa1a6d39d18f7ec6",
    ripemd160 := "ad430b4283203a7b7f338b9d252dfdbf807402bf",
    hash160 := "16471071648e50df4d1f610d4687c94925c6be95" },
  { length := 120,
    sha256 := "f52b23db1fbb6ded89ef42a23ce0c8922c45f25c50b568a93bf1c075420bbb7c",
    ripemd160 := "b89cdc109009f1982c8b34fca446953584d3f6c4",
    hash160 := "6d643b3340eefc1230ebfef4793e6cf75d7994cb" },
  { length := 127,
    sha256 := "92ca0fa6651ee2f97b884b7246a562fa71250fedefe5ebf270d31c546bfea976",
    ripemd160 := "2be8e565e24a87171f0700ecafa3c2942c97023e",
    hash160 := "ba6f3b23090ba113d3bc6fef9e84d8abfc721521" },
  { length := 128,
    sha256 := "471fb943aa23c511f6f72f8d1652d9c880cfa392ad80503120547703e56a2be5",
    ripemd160 := "7c4d36070c1e1176b2960a1b0dd2319d547cf8eb",
    hash160 := "99c7ab3b5ebfade50ebf9d47c3342610493b55b5" },
  { length := 129,
    sha256 := "5099c6a56203f9687f7d33f4bfdf576d31dc91f6b695ecea38b2770c87631135",
    ripemd160 := "1f15f104f445db8ef02bb601a67e60c373377fa6",
    hash160 := "35f416861de6de240ce1dc04133c063cdfc1b356" },
  { length := 255,
    sha256 := "3f8591112c6bbe5c963965954e293108b7208ed2af893e500d859368c654eabe",
    ripemd160 := "258a3b50d3df2564dd57d3dfa39d684650a05450",
    hash160 := "faf87bcb4f3c22b61879bb54007f6f2df540ca8d" },
  { length := 256,
    sha256 := "40aff2e9d2d8922e47afd4648e6967497158785fbd1da870e7110266bf944880",
    ripemd160 := "9c4fa072db2c871a5635e37f791e93ab45049676",
    hash160 := "07a536d93e0b9a779874e1287a226b8230cda46e" },
  { length := 1024,
    sha256 := "785b0751fc2c53dc14a4ce3d800e69ef9ce1009eb327ccf458afe09c242c26c9",
    ripemd160 := "29ea7f13cac242905ae2dc1a36d5985815b30356",
    hash160 := "3c35b9197c713096d6d24f662c65b77587554c00" }
]

def main : IO UInt32 := do
  let sha256Passed ← runVectors "SHA-256" SHA256.hash sha256Vectors
  let ripemd160Passed ← runVectors "RIPEMD-160" RIPEMD160.hash ripemd160Vectors
  let hash160Passed ← runVectors "HASH160" hash160 hash160Vectors
  let boundaryPassed ← runBoundaryVectors boundaryVectors
  let lengthsPassed :=
    (SHA256.hash ByteArray.empty).size == 32 &&
    (RIPEMD160.hash ByteArray.empty).size == 20 &&
    (hash160 ByteArray.empty).size == 20
  IO.println s!"[{if lengthsPassed then "PASS" else "FAIL"}] digest lengths"
  return if sha256Passed && ripemd160Passed && hash160Passed && boundaryPassed && lengthsPassed then 0
    else 1

end LeanHash160.Tests

def main : IO UInt32 := LeanHash160.Tests.main
