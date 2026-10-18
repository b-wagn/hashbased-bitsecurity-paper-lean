/-!
# XMSS instance parameters

The parameters of the XMSS instance for Ethereum's post-quantum consensus that do not depend on
the WOTS encoding. Everything else in `Scheme/` is defined in terms of these constants. The two
encodings fix the remaining parameters: the target-sum encoding in `TargetSum.lean` (`v = 42`
chains, target sum `T = 195`, at most `A_max = 2^32` randomizer trials), and the WOTS encoding
with a checksum of SLH-DSA (FIPS 205) in `Checksum.lean` (`len_1 = 43` message digits and
`len_2 = 3` checksum digits, `v = 46` chains, a single randomizer).

| Symbol  | Lean             | Value  | Meaning                     |
|---------|------------------|--------|-----------------------------|
| `n`     | `digestBits`     | 128    | hash output length (bits)   |
| `ℓ_msg` | `messageBits`    | 256    | message length              |
| `w`     | `winternitzBits` | 3      | chunk size in bits          |
| `h`     | `treeHeight`     | 32     | Merkle tree height          |
| `L`     | `lifetime`       | `2^32` | lifetime (number of epochs) |

The public parameter and the randomizers are hash outputs, so their lengths are `ℓ_p = ℓ_rnd = n`.
The master seed has 256 bits and the tweak has 128 bits (16 bytes); both are fixed by the byte
layout in `Types.lean` and `Hashing.lean`.
-/

namespace XmssSecurity

/-- `n`: the output length of the hash function `H : {0,1}^* → {0,1}^n`, in bits. -/
def digestBits : Nat := 128

/-- `ℓ_msg`: message length in bits. -/
def messageBits : Nat := 256

/-- `h`: the Merkle tree height. -/
def treeHeight : Nat := 32

/-- `L = 2^h`: the lifetime, i.e. the number of epochs (leaf indices). -/
def lifetime : Nat := 2 ^ treeHeight

/-- `w`: the Winternitz chunk size in bits. -/
def winternitzBits : Nat := 3

/-- `2^w`: the number of values on a hash chain. -/
def chainLength : Nat := 2 ^ winternitzBits

end XmssSecurity
