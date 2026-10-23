import «SLH-DSA-SHAKE-128s».Statement.Parameters
import Mathlib.Data.BitVec

/-! Fixed-width values and byte strings for SLH-DSA-SHAKE-128s. -/

namespace SlhDsaSecurity

abbrev Bytes := List UInt8
abbrev Digest := BitVec (8 * n)
abbrev HashOutput := BitVec (8 * messageDigestBytes)

/-- The standard public key `(PK.seed, PK.root)`. -/
structure PublicKey where
  seed : Digest
  root : Digest
deriving DecidableEq

/-- The standard secret key. FORS and WOTS secrets are derived as needed. -/
structure SecretKey where
  seed : Digest
  prf : Digest
  publicKey : PublicKey
deriving DecidableEq

/-- A pure SLH-DSA signing request, including its context. Overlong contexts are rejected. -/
structure Message where
  message : Bytes
  context : Bytes
deriving DecidableEq

/-- Fixed-width big-endian serialization, FIPS 205 Algorithm 3. -/
def bytesBE (byteCount : Nat) (value : BitVec (8 * byteCount)) : Bytes :=
  (List.ofFn fun i : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * i.val) 8)).reverse

end SlhDsaSecurity
