import LeanHash160.Internal

/-!
Pure Lean implementation of SHA-256 as specified by FIPS 180-4.
-/

namespace LeanHash160.SHA256

private structure State where
  h0 : UInt32
  h1 : UInt32
  h2 : UInt32
  h3 : UInt32
  h4 : UInt32
  h5 : UInt32
  h6 : UInt32
  h7 : UInt32

private def initialState : State := {
  h0 := 0x6a09e667, h1 := 0xbb67ae85, h2 := 0x3c6ef372, h3 := 0xa54ff53a
  h4 := 0x510e527f, h5 := 0x9b05688c, h6 := 0x1f83d9ab, h7 := 0x5be0cd19
}

private def roundConstants : Array UInt32 := #[
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

@[inline] private def choose (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ ((x ^^^ 0xffffffff) &&& z)

@[inline] private def majority (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

@[inline] private def bigSigma0 (x : UInt32) : UInt32 :=
  Internal.rotateRight32 x 2 ^^^ Internal.rotateRight32 x 13 ^^^
    Internal.rotateRight32 x 22

@[inline] private def bigSigma1 (x : UInt32) : UInt32 :=
  Internal.rotateRight32 x 6 ^^^ Internal.rotateRight32 x 11 ^^^
    Internal.rotateRight32 x 25

@[inline] private def smallSigma0 (x : UInt32) : UInt32 :=
  Internal.rotateRight32 x 7 ^^^ Internal.rotateRight32 x 18 ^^^ (x >>> 3)

@[inline] private def smallSigma1 (x : UInt32) : UInt32 :=
  Internal.rotateRight32 x 17 ^^^ Internal.rotateRight32 x 19 ^^^ (x >>> 10)

private structure WorkingState where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32

private def WorkingState.next
    (working : WorkingState) (word constant : UInt32) : WorkingState :=
  let t1 := working.h + bigSigma1 working.e +
    choose working.e working.f working.g + constant + word
  let t2 := bigSigma0 working.a + majority working.a working.b working.c
  {
    a := t1 + t2
    b := working.a
    c := working.b
    d := working.c
    e := working.d + t1
    f := working.e
    g := working.f
    h := working.g
  }

private def compressBlock
    (state : State) (bytes : ByteArray) (blockOffset : Nat) : State := Id.run do
  let mut schedule : Array UInt32 := Array.replicate 64 0
  for round in [0:16] do
    schedule := schedule.set! round
      (Internal.readUInt32 .big bytes (blockOffset + round * 4))
  for round in [16:64] do
    let word := smallSigma1 schedule[round - 2]! + schedule[round - 7]! +
      smallSigma0 schedule[round - 15]! + schedule[round - 16]!
    schedule := schedule.set! round word

  let mut working : WorkingState := {
    a := state.h0, b := state.h1, c := state.h2, d := state.h3
    e := state.h4, f := state.h5, g := state.h6, h := state.h7
  }
  for round in [0:64] do
    working := working.next schedule[round]! roundConstants[round]!

  return {
    h0 := state.h0 + working.a, h1 := state.h1 + working.b
    h2 := state.h2 + working.c, h3 := state.h3 + working.d
    h4 := state.h4 + working.e, h5 := state.h5 + working.f
    h6 := state.h6 + working.g, h7 := state.h7 + working.h
  }

private def State.toBytes (state : State) : ByteArray :=
  [state.h0, state.h1, state.h2, state.h3, state.h4, state.h5, state.h6, state.h7].foldl
    (Internal.appendUInt32 .big) ByteArray.empty

/-- Compute the 32-byte SHA-256 digest of `bytes`. -/
def hash (bytes : ByteArray) : ByteArray := Id.run do
  let padded := Internal.padMessage .big bytes
  let mut state := initialState
  for block in [0:padded.size / 64] do
    state := compressBlock state padded (block * 64)
  return state.toBytes

end LeanHash160.SHA256
