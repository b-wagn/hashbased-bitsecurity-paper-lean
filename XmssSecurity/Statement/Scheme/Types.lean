import XmssSecurity.Statement.Scheme.Parameters
import XmssSecurity.Statement.RandomOracleModel

/-!
# XMSS types

The data types of XMSS, in terms of
the constants of `Parameters.lean`: seeds, digests, messages, indices, encodings, keys, and
signatures. Encodings, secret keys, and signatures depend on the number `v` of WOTS chains, which
the encoding fixes (`WotsEncoding`). It also fixes the random-oracle world of XMSS: the hash
function `H` maps byte strings to `n`-bit digests and is the random oracle `HashSpec`, so every
hash call is an oracle query.
-/

open OracleComp OracleSpec

namespace XmssSecurity

/-! ## Basic types -/

abbrev MasterSeed := BitVec 256

abbrev Digest := BitVec digestBits
abbrev Message := BitVec messageBits
/-- The public parameter `P`, a hash output (`ℓ_p = n`). -/
abbrev PublicParameter := Digest
/-- A randomizer `ρ`, a hash output (`ℓ_rnd = n`). -/
abbrev Randomness := Digest
/-- `idx < L`. -/
abbrev LeafIndex := Fin lifetime
abbrev Digit := Fin chainLength
/-- A chain step; the tweak carries `2^w * i + step`. -/
abbrev ChainStep := Fin (chainLength - 1)
/-- A level of the stored tree, `0` the leaves and `h` the root. -/
abbrev MerkleHeight := Fin (treeHeight + 1)
/-- A level of the authentication path, below the root; the tweak carries `level + 1`. -/
abbrev MerkleLevel := Fin treeHeight
/-- A node within a level. Level `ℓ` only uses the values below `2^(h - ℓ)`. -/
abbrev MerkleNode := Fin lifetime
/-- A word of `v` digits, one per chain. -/
abbrev Encoding (v : Nat) := Fin v → Digit
abbrev HashInput := List UInt8

/-! ## The WOTS encoding -/

/-- A WOTS encoding: the number `v` of chains, the partial map from message digests to codewords
(`none` when a digest does not encode), and the number `A_max` of randomizer trials of the
signer. -/
structure WotsEncoding where
  numChains : Nat
  decode : Digest → Option (Encoding numChains)
  signingAttempts : Nat

/-! ## Keys and signatures -/

/-- `pk = (root, P)`. -/
structure PublicKey where
  root : Digest
  parameter : PublicParameter
deriving DecidableEq

/-- Cached chain starts, chain values and Merkle nodes of `v` chains per leaf, together with the
public parameter. -/
structure SecretKey (v : Nat) where
  parameter : PublicParameter
  chainStart : LeafIndex → Fin v → Digest
  chainValue : LeafIndex → Fin v → Digit → Digest
  treeValue : MerkleHeight → MerkleNode → Digest

/-- `sigma = (rho, sigma_OTS, path_ep)`: the encoding randomness, the `v` chain values and the `h`
authentication nodes. -/
structure Signature (v : Nat) where
  randomness : Randomness
  chainValue : Fin v → Digest
  authPath : Fin treeHeight → Digest
deriving DecidableEq

/-! ## The random-oracle world of XMSS -/

/-- A hash query takes an arbitrary byte string and returns a digest. -/
abbrev HashSpec := RandomOracleModel.HashSpec HashInput Digest

/-- Private uniform sampling and the shared hash oracle. Only hash calls count toward the query budget. -/
abbrev OracleWorld := RandomOracleModel.World HashInput Digest

end XmssSecurity
