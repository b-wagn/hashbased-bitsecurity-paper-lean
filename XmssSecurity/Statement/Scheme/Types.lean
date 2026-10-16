import XmssSecurity.Statement.Scheme.Parameters
import XmssSecurity.Statement.RandomOracleModel

/-!
# XMSS types

The data types of the XMSS instance (`doc/xmss/main.tex` of the leanVM repository), in terms of
the constants of `Parameters.lean`: seeds, digests, messages, indices, encodings, keys, and
signatures. It also fixes the random-oracle world of XMSS: the hash function `H` maps byte strings
to 256-bit outputs and is the random oracle `HashSpec`, so every hash call is an oracle query.
-/

open OracleComp OracleSpec

namespace XmssSecurity

/-! ## Basic types -/

abbrev MasterSeed := BitVec 256

abbrev Digest := BitVec digestBits
abbrev HashOutput := BitVec hashOutputBits
abbrev Message := BitVec messageBits
abbrev PublicParameter := BitVec publicParameterBits
abbrev Randomness := BitVec randomnessBits
/-- `idx < L`. -/
abbrev LeafIndex := Fin lifetime
abbrev ChainIndex := Fin numChains
abbrev Digit := Fin chainLength
/-- A chain step; the tweak carries `2^w * i + step`. -/
abbrev ChainStep := Fin (chainLength - 1)
/-- A level of the stored tree, `0` the leaves and `h` the root. -/
abbrev MerkleHeight := Fin (treeHeight + 1)
/-- A level of the authentication path, below the root; the tweak carries `level + 1`. -/
abbrev MerkleLevel := Fin treeHeight
/-- A node within a level. Level `ℓ` only uses the values below `2^(h - ℓ)`. -/
abbrev MerkleNode := Fin lifetime
abbrev Encoding := ChainIndex → Digit
abbrev HashInput := List UInt8

/-! ## Keys and signatures -/

/-- `pk = (root, P)`. -/
structure PublicKey where
  root : Digest
  parameter : PublicParameter
deriving DecidableEq

/-- Cached chain starts, chain values and Merkle nodes, together with the public parameter. -/
structure SecretKey where
  parameter : PublicParameter
  chainStart : LeafIndex → ChainIndex → Digest
  chainValue : LeafIndex → ChainIndex → Digit → Digest
  treeValue : MerkleHeight → MerkleNode → Digest

/-- `sigma = (rho, sigma_OTS, path_ep)`: the encoding randomness, the `v` chain values and the `h` authentication nodes. -/
structure Signature where
  randomness : Randomness
  chainValue : ChainIndex → Digest
  authPath : Fin treeHeight → Digest
deriving DecidableEq

/-! ## The random-oracle world of XMSS -/

/-- A hash query takes an arbitrary byte string and returns 32 bytes. -/
abbrev HashSpec := RandomOracleModel.HashSpec HashInput HashOutput

/-- Private uniform sampling and the shared hash oracle. Only hash calls count toward the query budget. -/
abbrev OracleWorld := RandomOracleModel.World HashInput HashOutput

end XmssSecurity
