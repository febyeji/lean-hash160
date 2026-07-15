import Init.Data.ByteArray

/-!
Pure Lean implementation of RIPEMD-160.

Adapted from `powdr-labs/evm-semantics` commit
`601183cb2d959748243d59093c144652a6f10716`, Apache-2.0.
-/

namespace LeanHash160.RIPEMD160

def initialState : Array UInt32 := #[
  0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]

def leftConstants : Array UInt32 := #[
  0x00000000, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e]

def rightConstants : Array UInt32 := #[
  0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0x00000000]

def leftWordOrder : Array Nat := #[
   0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15,
   7,  4, 13,  1, 10,  6, 15,  3, 12,  0,  9,  5,  2, 14, 11,  8,
   3, 10, 14,  4,  9, 15,  8,  1,  2,  7,  0,  6, 13, 11,  5, 12,
   1,  9, 11, 10,  0,  8, 12,  4, 13,  3,  7, 15, 14,  5,  6,  2,
   4,  0,  5,  9,  7, 12,  2, 10, 14,  1,  3,  8, 11,  6, 15, 13]

def rightWordOrder : Array Nat := #[
   5, 14,  7,  0,  9,  2, 11,  4, 13,  6, 15,  8,  1, 10,  3, 12,
   6, 11,  3,  7,  0, 13,  5, 10, 14, 15,  8, 12,  4,  9,  1,  2,
  15,  5,  1,  3,  7, 14,  6,  9, 11,  8, 12,  2, 10,  0,  4, 13,
   8,  6,  4,  1,  3, 11, 15,  0,  5, 12,  2, 13,  9,  7, 10, 14,
  12, 15, 10,  4,  1,  5,  8,  7,  6,  2, 13, 14,  0,  3,  9, 11]

def leftRotations : Array Nat := #[
  11, 14, 15, 12,  5,  8,  7,  9, 11, 13, 14, 15,  6,  7,  9,  8,
   7,  6,  8, 13, 11,  9,  7, 15,  7, 12, 15,  9, 11,  7, 13, 12,
  11, 13,  6,  7, 14,  9, 13, 15, 14,  8, 13,  6,  5, 12,  7,  5,
  11, 12, 14, 15, 14, 15,  9,  8,  9, 14,  5,  6,  8,  6,  5, 12,
   9, 15,  5, 11,  6,  8, 13, 12,  5, 12, 13, 14, 11,  8,  5,  6]

def rightRotations : Array Nat := #[
   8,  9,  9, 11, 13, 15, 15,  5,  7,  7,  8, 11, 14, 14, 12,  6,
   9, 13, 15,  7, 12,  8,  9, 11,  7,  7, 12,  7,  6, 15, 13, 11,
   9,  7, 15, 11,  8,  6,  6, 14, 12, 13,  5, 14, 13, 13,  7,  5,
  15,  5,  8, 11, 14, 14,  6, 14,  6,  9, 12,  9, 12,  5, 15,  8,
   8,  5, 12,  9, 12,  5, 14,  6,  8, 13,  6,  5, 15, 13, 11, 11]

@[inline] def rotateLeft (word : UInt32) (amount : Nat) : UInt32 :=
  (word <<< UInt32.ofNat amount) |||
    (word >>> UInt32.ofNat (32 - amount))

@[inline] def complement (word : UInt32) : UInt32 :=
  word ^^^ 0xffffffff

@[inline] def roundFunction (group : Nat) (x y z : UInt32) : UInt32 :=
  match group with
  | 0 => x ^^^ y ^^^ z
  | 1 => (x &&& y) ||| (complement x &&& z)
  | 2 => (x ||| complement y) ^^^ z
  | 3 => (x &&& z) ||| (y &&& complement z)
  | _ => x ^^^ (y ||| complement z)

/-- Read four bytes as a little-endian word, zero-padding past the end. -/
def readLE32 (bytes : ByteArray) (offset : Nat) : UInt32 := Id.run do
  let mut word : UInt32 := 0
  for index in [0:4] do
    let byte : UInt32 :=
      if h : offset + index < bytes.size then
        bytes[offset + index].toUInt32
      else
        0
    word := word ||| (byte <<< UInt32.ofNat (8 * index))
  return word

/-- Append one word as four little-endian bytes. -/
def writeLE32 (output : ByteArray) (word : UInt32) : ByteArray := Id.run do
  let mut output := output
  for index in [0:4] do
    output := output.push
      (((word >>> UInt32.ofNat (8 * index)) &&& 0xff).toUInt8)
  return output

/-- Apply the RIPEMD-160 compression function to one 64-byte block. -/
def compressBlock
    (state : Array UInt32) (bytes : ByteArray) (blockOffset : Nat) :
    Array UInt32 := Id.run do
  let mut words : Array UInt32 := Array.mkArray 16 0
  for round in [0:16] do
    words := words.set! round (readLE32 bytes (blockOffset + round * 4))

  let mut a := state[0]!
  let mut b := state[1]!
  let mut c := state[2]!
  let mut d := state[3]!
  let mut e := state[4]!
  for round in [0:80] do
    let group := round / 16
    let temporary := a + roundFunction group b c d +
      words[leftWordOrder[round]!]! + leftConstants[group]!
    let temporary := rotateLeft temporary leftRotations[round]! + e
    a := e
    e := d
    d := rotateLeft c 10
    c := b
    b := temporary

  let mut rightA := state[0]!
  let mut rightB := state[1]!
  let mut rightC := state[2]!
  let mut rightD := state[3]!
  let mut rightE := state[4]!
  for round in [0:80] do
    let group := round / 16
    let rightGroup := 4 - group
    let temporary := rightA + roundFunction rightGroup rightB rightC rightD +
      words[rightWordOrder[round]!]! + rightConstants[group]!
    let temporary := rotateLeft temporary rightRotations[round]! + rightE
    rightA := rightE
    rightE := rightD
    rightD := rotateLeft rightC 10
    rightC := rightB
    rightB := temporary

  return #[
    state[1]! + c + rightD,
    state[2]! + d + rightE,
    state[3]! + e + rightA,
    state[4]! + a + rightB,
    state[0]! + b + rightC]

/-- Compute the 20-byte RIPEMD-160 digest of `bytes`. -/
def hash (bytes : ByteArray) : ByteArray := Id.run do
  let mut state := initialState
  let fullBlocks := bytes.size / 64
  for block in [0:fullBlocks] do
    state := compressBlock state bytes (block * 64)

  let remainderOffset := fullBlocks * 64
  let remainderSize := bytes.size - remainderOffset
  let mut tail := ByteArray.empty
  for index in [0:remainderSize] do
    tail := tail.push bytes[remainderOffset + index]!
  tail := tail.push 0x80
  while tail.size % 64 ≠ 56 do
    tail := tail.push 0

  let bitLength := bytes.size * 8
  for index in [0:8] do
    let shift := 8 * index
    tail := tail.push ((bitLength >>> shift) &&& 0xff).toUInt8

  let tailBlocks := tail.size / 64
  for block in [0:tailBlocks] do
    state := compressBlock state tail (block * 64)

  let mut output := ByteArray.empty
  for index in [0:5] do
    output := writeLE32 output state[index]!
  return output

end LeanHash160.RIPEMD160
