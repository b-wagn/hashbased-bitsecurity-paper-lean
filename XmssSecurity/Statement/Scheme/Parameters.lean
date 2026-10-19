/-!
# XMSS instance parameters

Parameters shared by both encodings. `TargetSum.lean` and `Checksum.lean` fix the chain counts
and signing attempts. Seeds have 256 bits; public parameters and randomizers have `digestBits`
bits (`Types.lean`), and hash tweaks have 16 bytes (`Hashing.lean`).
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
def winternitzBits : Nat := 4

/-- `2^w`: the number of values on a hash chain. -/
def chainLength : Nat := 2 ^ winternitzBits

end XmssSecurity
