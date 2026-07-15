import Init.Data.ByteArray

/-!
Pure Lean implementation of SHA-256 (FIPS 180-4).

Adapted from `powdr-labs/evm-semantics` commit
`601183cb2d959748243d59093c144652a6f10716`, Apache-2.0.
-/

namespace LeanHash160.SHA256

/-- SHA-256 initial hash values from FIPS 180-4 section 5.3.3. -/
def initialState : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- SHA-256 round constants from FIPS 180-4 section 4.2.2. -/
def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

@[inline] def rotateRight (word : UInt32) (amount : Nat) : UInt32 :=
  (word >>> UInt32.ofNat amount) |||
    (word <<< UInt32.ofNat (32 - amount))

@[inline] def shiftRight (word : UInt32) (amount : Nat) : UInt32 :=
  word >>> UInt32.ofNat amount

@[inline] def choose (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ ((x ^^^ 0xffffffff) &&& z)

@[inline] def majority (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

@[inline] def bigSigma0 (x : UInt32) : UInt32 :=
  rotateRight x 2 ^^^ rotateRight x 13 ^^^ rotateRight x 22

@[inline] def bigSigma1 (x : UInt32) : UInt32 :=
  rotateRight x 6 ^^^ rotateRight x 11 ^^^ rotateRight x 25

@[inline] def smallSigma0 (x : UInt32) : UInt32 :=
  rotateRight x 7 ^^^ rotateRight x 18 ^^^ shiftRight x 3

@[inline] def smallSigma1 (x : UInt32) : UInt32 :=
  rotateRight x 17 ^^^ rotateRight x 19 ^^^ shiftRight x 10

/-- Read four bytes as a big-endian word, zero-padding past the end. -/
def readBE32 (bytes : ByteArray) (offset : Nat) : UInt32 := Id.run do
  let mut word : UInt32 := 0
  for index in [0:4] do
    let byte : UInt32 :=
      if h : offset + index < bytes.size then
        bytes[offset + index].toUInt32
      else
        0
    word := (word <<< 8) ||| byte
  return word

/-- Append one word as four big-endian bytes. -/
def writeBE32 (output : ByteArray) (word : UInt32) : ByteArray := Id.run do
  let mut output := output
  for index in [0:4] do
    let shift := UInt32.ofNat (8 * (3 - index))
    output := output.push (((word >>> shift) &&& 0xff).toUInt8)
  return output

/-- Apply the SHA-256 compression function to one 64-byte block. -/
def compressBlock
    (state : Array UInt32) (bytes : ByteArray) (blockOffset : Nat) :
    Array UInt32 := Id.run do
  let mut schedule : Array UInt32 := Array.mkArray 64 0
  for round in [0:16] do
    schedule := schedule.set! round (readBE32 bytes (blockOffset + round * 4))
  for round in [16:64] do
    let word := smallSigma1 schedule[round - 2]! + schedule[round - 7]! +
      smallSigma0 schedule[round - 15]! + schedule[round - 16]!
    schedule := schedule.set! round word

  let mut a := state[0]!
  let mut b := state[1]!
  let mut c := state[2]!
  let mut d := state[3]!
  let mut e := state[4]!
  let mut f := state[5]!
  let mut g := state[6]!
  let mut h := state[7]!

  for round in [0:64] do
    let temporary1 := h + bigSigma1 e + choose e f g +
      roundConstants[round]! + schedule[round]!
    let temporary2 := bigSigma0 a + majority a b c
    h := g
    g := f
    f := e
    e := d + temporary1
    d := c
    c := b
    b := a
    a := temporary1 + temporary2

  return #[
    state[0]! + a, state[1]! + b, state[2]! + c, state[3]! + d,
    state[4]! + e, state[5]! + f, state[6]! + g, state[7]! + h]

/-- Compute the 32-byte SHA-256 digest of `bytes`. -/
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
    let shift := 8 * (7 - index)
    tail := tail.push ((bitLength >>> shift) &&& 0xff).toUInt8

  let tailBlocks := tail.size / 64
  for block in [0:tailBlocks] do
    state := compressBlock state tail (block * 64)

  let mut output := ByteArray.empty
  for index in [0:8] do
    output := writeBE32 output state[index]!
  return output

end LeanHash160.SHA256
