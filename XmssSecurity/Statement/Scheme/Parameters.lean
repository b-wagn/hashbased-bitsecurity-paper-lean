/-!
# XMSS instance parameters

The parameter table of the XMSS instance for Ethereum's post-quantum consensus (`doc/xmss/main.tex`
of the leanVM repository, Section 1). Everything else in `Scheme/` is defined in terms
of these constants, so this file is the single place to read the concrete numbers.

| Symbol  | Lean                  | Value   | Meaning                                 |
|---------|-----------------------|---------|-----------------------------------------|
| `n`     | `digestBits`          | 128     | hash value and Merkle node length (bits)|
| —       | `hashOutputBits`      | 256     | output length of the hash function `H`  |
| `ℓ_msg` | `messageBits`         | 256     | message length                          |
| `ℓ_p`   | `publicParameterBits` | 128     | public parameter length                 |
| `ℓ_rnd` | `randomnessBits`      | 192     | randomizer length                       |
| `w`     | `winternitzBits`      | 3       | chunk size in bits                      |
| `v`     | `numChains`           | 42      | code length (number of chains)          |
| `T`     | `targetSum`           | 195     | target sum                              |
| `h`     | `treeHeight`          | 32      | Merkle tree height                      |
| `L`     | `lifetime`            | `2^32`  | lifetime (number of epochs)             |
| `A_max` | `signingAttemptLimit` | `2^32`  | maximum randomizer trials per signature |

The master seed has 256 bits and the tweak has 128 bits (16 bytes); both are fixed by the byte
layout in `Types.lean` and `Hashing.lean`.
-/

namespace XmssSecurity

/-- `n`: hash value and Merkle node length in bits. -/
def digestBits : Nat := 128

/-- Output length of the hash function `H : {0,1}^* → {0,1}^256`. -/
def hashOutputBits : Nat := 256

/-- `ℓ_msg`: message length in bits. -/
def messageBits : Nat := 256

/-- `ℓ_p`: public parameter length in bits. -/
def publicParameterBits : Nat := 128

/-- `ℓ_rnd`: randomizer length in bits. -/
def randomnessBits : Nat := 192

/-- `A_max`: encoding attempts per signature. -/
def signingAttemptLimit : Nat := 2 ^ 32

/-- `h`: the Merkle tree height. -/
def treeHeight : Nat := 32

/-- `L = 2^h`: the lifetime, i.e. the number of epochs (leaf indices). -/
def lifetime : Nat := 2 ^ treeHeight

/-- `w`: the Winternitz chunk size in bits. -/
def winternitzBits : Nat := 3

/-- `2^w`: the number of values on a hash chain. -/
def chainLength : Nat := 2 ^ winternitzBits

/-- `v`: the code length, i.e. the number of chains. -/
def numChains : Nat := 42

/-- `T`: the target sum of the code. -/
def targetSum : Nat := 195

end XmssSecurity
