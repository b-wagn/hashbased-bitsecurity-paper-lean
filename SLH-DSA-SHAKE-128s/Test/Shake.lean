/-!
# SHAKE256 (FIPS 202), for running the specification on test vectors
-/

namespace SlhDsaTest

/-- Round constants of Keccak-f[1600]. -/
def roundConstants : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- Rotation offsets, indexed by `x + 5 * y`. -/
def rotations : Array UInt64 := #[
  0, 1, 62, 28, 27,
  36, 44, 6, 55, 20,
  3, 10, 43, 25, 39,
  41, 45, 15, 21, 8,
  18, 2, 61, 56, 14]

@[inline] def rotl (value shift : UInt64) : UInt64 :=
  if shift = 0 then value else (value <<< shift) ||| (value >>> (64 - shift))

/-- One round of Keccak-f[1600] on 25 lanes, lane `(x, y)` at index `x + 5 * y`. -/
def round (a : Array UInt64) (rc : UInt64) : Array UInt64 := Id.run do
  -- θ
  let c := Array.ofFn fun (x : Fin 5) =>
    a[x.val]! ^^^ a[x.val + 5]! ^^^ a[x.val + 10]! ^^^ a[x.val + 15]! ^^^ a[x.val + 20]!
  let d := Array.ofFn fun (x : Fin 5) =>
    c[(x.val + 4) % 5]! ^^^ rotl c[(x.val + 1) % 5]! 1
  let a := Array.ofFn fun (i : Fin 25) => a[i.val]! ^^^ d[i.val % 5]!
  -- ρ and π: B[y, 2x + 3y] = rot(A[x, y], r[x, y])
  let mut b := Array.replicate 25 (0 : UInt64)
  for x in [0:5] do
    for y in [0:5] do
      b := b.set! (y + 5 * ((2 * x + 3 * y) % 5)) (rotl a[x + 5 * y]! rotations[x + 5 * y]!)
  -- χ
  let a := Array.ofFn fun (i : Fin 25) =>
    let x := i.val % 5
    let y := i.val / 5
    b[i.val]! ^^^ ((~~~ b[(x + 1) % 5 + 5 * y]!) &&& b[(x + 2) % 5 + 5 * y]!)
  -- ι
  return a.set! 0 (a[0]! ^^^ rc)

def keccakF (a : Array UInt64) : Array UInt64 :=
  roundConstants.foldl round a

/-- XOR a full rate block (little-endian lanes) into the state. -/
def absorbBlock (a : Array UInt64) (block : ByteArray) : Array UInt64 := Id.run do
  let mut a := a
  for i in [0:block.size / 8] do
    let mut lane : UInt64 := 0
    for j in [0:8] do
      lane := lane ||| (block[8 * i + j]!.toUInt64 <<< (8 * j).toUInt64)
    a := a.set! i (a[i]! ^^^ lane)
  return a

/-- SHAKE256 with `outputBytes` bytes of output. -/
def shake256 (input : ByteArray) (outputBytes : Nat) : ByteArray := Id.run do
  let rate := 136
  -- pad10*1 with the SHAKE domain bits
  let padLength := rate - input.size % rate
  let mut padded := input
  for i in [0:padLength] do
    let byte : UInt8 :=
      (if i = 0 then 0x1F else 0) ||| (if i = padLength - 1 then 0x80 else 0)
    padded := padded.push byte
  let mut state := Array.replicate 25 (0 : UInt64)
  for blockIndex in [0:padded.size / rate] do
    state := keccakF (absorbBlock state (padded.extract (blockIndex * rate) ((blockIndex + 1) * rate)))
  let mut out := ByteArray.empty
  while out.size < outputBytes do
    for i in [0:rate / 8] do
      for j in [0:8] do
        if out.size < outputBytes then
          out := out.push (state[i]! >>> (8 * j).toUInt64).toUInt8
    if out.size < outputBytes then
      state := keccakF state
  return out

end SlhDsaTest
