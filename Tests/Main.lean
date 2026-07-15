import LeanHash160

namespace LeanHash160.Tests

private def hexDigit (value : Nat) : Char :=
  if value < 10 then Char.ofNat (0x30 + value) else Char.ofNat (0x57 + value)

private def byteHex (byte : UInt8) : String :=
  String.mk [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)]

private def toHex (bytes : ByteArray) : String :=
  String.join (bytes.data.toList.map byteHex)

private def repeatedByte (byte : UInt8) (count : Nat) : ByteArray := Id.run do
  let mut output := ByteArray.empty
  for _ in [0:count] do
    output := output.push byte
  return output

private structure Vector where
  name : String
  input : ByteArray
  expected : String

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
  { name := "alphanumeric",
    input := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789".toUTF8,
    expected := "b0e20b6e3116640286ed3a87a5713079b21f5189" },
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

def main : IO UInt32 := do
  let sha256Passed ← runVectors "SHA-256" SHA256.hash sha256Vectors
  let ripemd160Passed ← runVectors "RIPEMD-160" RIPEMD160.hash ripemd160Vectors
  let hash160Passed ← runVectors "HASH160" hash160 hash160Vectors
  let lengthsPassed :=
    (SHA256.hash ByteArray.empty).size == 32 &&
    (RIPEMD160.hash ByteArray.empty).size == 20 &&
    (hash160 ByteArray.empty).size == 20
  IO.println s!"[{if lengthsPassed then "PASS" else "FAIL"}] digest lengths"
  return if sha256Passed && ripemd160Passed && hash160Passed && lengthsPassed then 0 else 1

end LeanHash160.Tests

def main : IO UInt32 := LeanHash160.Tests.main
