import Init.Data.ByteArray

/-!
Shared byte-oriented primitives for 512-bit-block hash functions.

This module owns message padding and integer encoding so that the public hash
implementations can focus on their compression functions.
-/

namespace LeanHash160.Internal

inductive Endianness where
  | big
  | little

@[inline] def rotateLeft32 (word : UInt32) (amount : Nat) : UInt32 :=
  let amount := amount % 32
  if amount == 0 then word
  else
    (word <<< UInt32.ofNat amount) |||
      (word >>> UInt32.ofNat (32 - amount))

@[inline] def rotateRight32 (word : UInt32) (amount : Nat) : UInt32 :=
  let amount := amount % 32
  if amount == 0 then word
  else
    (word >>> UInt32.ofNat amount) |||
      (word <<< UInt32.ofNat (32 - amount))

/-- Read a 32-bit word from a complete block. -/
def readUInt32 (endianness : Endianness) (bytes : ByteArray) (offset : Nat) : UInt32 :=
  match endianness with
  | .big => Id.run do
      let mut word : UInt32 := 0
      for index in [0:4] do
        word := (word <<< 8) ||| (bytes.get! (offset + index)).toUInt32
      return word
  | .little => Id.run do
      let mut word : UInt32 := 0
      for index in [0:4] do
        word := word |||
          ((bytes.get! (offset + index)).toUInt32 <<< UInt32.ofNat (8 * index))
      return word

/-- Append a 32-bit word to a byte array. -/
def appendUInt32
    (endianness : Endianness) (output : ByteArray) (word : UInt32) : ByteArray :=
  Id.run do
    let mut output := output
    for index in [0:4] do
      let byteIndex := match endianness with
        | .big => 3 - index
        | .little => index
      output := output.push
        (((word >>> UInt32.ofNat (8 * byteIndex)) &&& 0xff).toUInt8)
    return output

private def appendBitLength
    (endianness : Endianness) (output : ByteArray) (byteLength : Nat) : ByteArray :=
  Id.run do
    let mut output := output
    let bitLength := UInt64.ofNat byteLength * 8
    for index in [0:8] do
      let byteIndex := match endianness with
        | .big => 7 - index
        | .little => index
      output := output.push
        (((bitLength >>> UInt64.ofNat (8 * byteIndex)) &&& 0xff).toUInt8)
    return output

/--
Pad a message to a non-empty sequence of 64-byte blocks. The standard input
domain is fewer than `2^64` bits; the 64-bit conversion also gives a defined
low-64-bit extension for larger values.
-/
def padMessage (lengthEndianness : Endianness) (bytes : ByteArray) : ByteArray :=
  Id.run do
    let mut padded := bytes.push 0x80
    while padded.size % 64 != 56 do
      padded := padded.push 0
    return appendBitLength lengthEndianness padded bytes.size

end LeanHash160.Internal
