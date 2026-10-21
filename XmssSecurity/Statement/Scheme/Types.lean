import XmssSecurity.Statement.Scheme.Parameters
import XmssSecurity.Statement.RandomOracleModel

/-!
# XMSS types

Keys and signatures are indexed by the number of WOTS chains. `WotsEncoding` supplies the
decoder and signing-attempt limit. `HashSpec` maps byte strings to digests.
-/

open OracleComp OracleSpec

namespace XmssSecurity

/-! ## Basic types -/

abbrev MasterSeed := BitVec 256

abbrev Digest := BitVec digestBits
abbrev Message := BitVec messageBits
/-- The public parameter `P`, an `n`-bit hash output. -/
abbrev PublicParameter := Digest
/-- A randomizer `ρ`, an `n`-bit hash output. -/
abbrev Randomness := Digest
/-- An epoch `ep < L`. -/
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

/-- Chain count, partial digest decoder, and maximum randomizer trials. -/
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

/-- The public parameter, chain starts, and materialized vectors of all chain values and Merkle
nodes. The vectors contain digests, so signing reads stored values without replaying key generation.
Tree rows use the common node-index type; only nodes below `2^(h - level)` are used. -/
structure SecretKey (v : Nat) where
  parameter : PublicParameter
  chainStart : LeafIndex → Fin v → Digest
  chainValues : Vector (Vector (Vector Digest chainLength) v) lifetime
  treeValues : Vector (Vector Digest lifetime) (treeHeight + 1)

/-- Read the stored value `c_{ep,i,d}`. -/
def SecretKey.chainValue (key : SecretKey v) (leafIndex : LeafIndex) (chain : Fin v)
    (digit : Digit) : Digest :=
  key.chainValues[leafIndex.val][chain.val][digit.val]

/-- Read the stored Merkle node `X_{level,node}`. -/
def SecretKey.treeValue (key : SecretKey v) (height : MerkleHeight) (node : MerkleNode) : Digest :=
  key.treeValues[height.val][node.val]

/-- `σ = (ρ, (σ_i), (A_ℓ))`: the randomizer, the `v` chain values and the `h` authentication nodes. -/
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
