import LeanHash160.Internal

/-!
Pure Lean implementation of RIPEMD-160 following the original algorithm
specification by Dobbertin, Bosselaers, and Preneel.
-/

namespace LeanHash160.RIPEMD160

private structure State where
  h0 : UInt32
  h1 : UInt32
  h2 : UInt32
  h3 : UInt32
  h4 : UInt32

private def initialState : State := {
  h0 := 0x67452301
  h1 := 0xefcdab89
  h2 := 0x98badcfe
  h3 := 0x10325476
  h4 := 0xc3d2e1f0
}

private def leftConstants : Array UInt32 := #[
  0x00000000, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e]

private def rightConstants : Array UInt32 := #[
  0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0x00000000]

private def leftWordOrder : Array Nat := #[
   0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15,
   7,  4, 13,  1, 10,  6, 15,  3, 12,  0,  9,  5,  2, 14, 11,  8,
   3, 10, 14,  4,  9, 15,  8,  1,  2,  7,  0,  6, 13, 11,  5, 12,
   1,  9, 11, 10,  0,  8, 12,  4, 13,  3,  7, 15, 14,  5,  6,  2,
   4,  0,  5,  9,  7, 12,  2, 10, 14,  1,  3,  8, 11,  6, 15, 13]

private def rightWordOrder : Array Nat := #[
   5, 14,  7,  0,  9,  2, 11,  4, 13,  6, 15,  8,  1, 10,  3, 12,
   6, 11,  3,  7,  0, 13,  5, 10, 14, 15,  8, 12,  4,  9,  1,  2,
  15,  5,  1,  3,  7, 14,  6,  9, 11,  8, 12,  2, 10,  0,  4, 13,
   8,  6,  4,  1,  3, 11, 15,  0,  5, 12,  2, 13,  9,  7, 10, 14,
  12, 15, 10,  4,  1,  5,  8,  7,  6,  2, 13, 14,  0,  3,  9, 11]

private def leftRotations : Array Nat := #[
  11, 14, 15, 12,  5,  8,  7,  9, 11, 13, 14, 15,  6,  7,  9,  8,
   7,  6,  8, 13, 11,  9,  7, 15,  7, 12, 15,  9, 11,  7, 13, 12,
  11, 13,  6,  7, 14,  9, 13, 15, 14,  8, 13,  6,  5, 12,  7,  5,
  11, 12, 14, 15, 14, 15,  9,  8,  9, 14,  5,  6,  8,  6,  5, 12,
   9, 15,  5, 11,  6,  8, 13, 12,  5, 12, 13, 14, 11,  8,  5,  6]

private def rightRotations : Array Nat := #[
   8,  9,  9, 11, 13, 15, 15,  5,  7,  7,  8, 11, 14, 14, 12,  6,
   9, 13, 15,  7, 12,  8,  9, 11,  7,  7, 12,  7,  6, 15, 13, 11,
   9,  7, 15, 11,  8,  6,  6, 14, 12, 13,  5, 14, 13, 13,  7,  5,
  15,  5,  8, 11, 14, 14,  6, 14,  6,  9, 12,  9, 12,  5, 15,  8,
   8,  5, 12,  9, 12,  5, 14,  6,  8, 13,  6,  5, 15, 13, 11, 11]

@[inline] private def complement (word : UInt32) : UInt32 :=
  word ^^^ 0xffffffff

@[inline] private def roundFunction (group : Nat) (x y z : UInt32) : UInt32 :=
  match group with
  | 0 => x ^^^ y ^^^ z
  | 1 => (x &&& y) ||| (complement x &&& z)
  | 2 => (x ||| complement y) ^^^ z
  | 3 => (x &&& z) ||| (y &&& complement z)
  | _ => x ^^^ (y ||| complement z)

private structure Lane where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32

private def Lane.next
    (lane : Lane) (group : Nat) (word constant : UInt32) (rotation : Nat) : Lane :=
  let nextB := Internal.rotateLeft32
    (lane.a + roundFunction group lane.b lane.c lane.d + word + constant) rotation + lane.e
  {
    a := lane.e
    b := nextB
    c := lane.b
    d := Internal.rotateLeft32 lane.c 10
    e := lane.d
  }

private def compressBlock
    (state : State) (bytes : ByteArray) (blockOffset : Nat) : State := Id.run do
  let mut words : Array UInt32 := Array.replicate 16 0
  for index in [0:16] do
    words := words.set! index
      (Internal.readUInt32 .little bytes (blockOffset + index * 4))

  let initialLane : Lane := {
    a := state.h0, b := state.h1, c := state.h2, d := state.h3, e := state.h4
  }
  let mut left := initialLane
  let mut right := initialLane
  for round in [0:80] do
    let group := round / 16
    left := left.next group words[leftWordOrder[round]!]!
      leftConstants[group]! leftRotations[round]!
    right := right.next (4 - group) words[rightWordOrder[round]!]!
      rightConstants[group]! rightRotations[round]!

  return {
    h0 := state.h1 + left.c + right.d
    h1 := state.h2 + left.d + right.e
    h2 := state.h3 + left.e + right.a
    h3 := state.h4 + left.a + right.b
    h4 := state.h0 + left.b + right.c
  }

private def State.toBytes (state : State) : ByteArray :=
  [state.h0, state.h1, state.h2, state.h3, state.h4].foldl
    (Internal.appendUInt32 .little) ByteArray.empty

/-- Compute the 20-byte RIPEMD-160 digest of `bytes`. -/
def hash (bytes : ByteArray) : ByteArray := Id.run do
  let padded := Internal.padMessage .little bytes
  let mut state := initialState
  for block in [0:padded.size / 64] do
    state := compressBlock state padded (block * 64)
  return state.toBytes

end LeanHash160.RIPEMD160
