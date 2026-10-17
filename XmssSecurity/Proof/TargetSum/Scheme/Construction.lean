import XmssSecurity.Proof.TargetSum.Scheme.Types
import XmssSecurity.Proof.TargetSum.Scheme.Hashing
import XmssSecurity.Statement.Scheme.TargetSum
import VCVio.OracleComp.QueryTracking.LoggingOracle

/-!
# XMSS construction (proof copy for the target-sum encoding)

The proofs about `xmssTargetSum` work with this copy of the algorithms of the statement, specialized
to the target-sum encoding (`numChains` chains): it is the construction as it read before the
statement made it generic in the encoding. `Bridge.lean` proves that the copy computes the
statement's algorithms, so that `xmssTargetSum = xmss`.

The algorithms of the XMSS instance specified in `doc/xmss/main.tex` of the leanVM repository:
verification, key generation, and signing. The types are in `Types.lean`, the hash routines in
`Hashing.lean`, and the target-sum encoding in `TargetSum.lean`.

`Concrete` contains verification and the chain and tree computations; `Seeded` contains key
generation and signing from a 256-bit master seed. Key generation derives the public parameter
and all WOTS chain starts from the master seed in separate hash domains, computes the Merkle root,
and stores every chain value and Merkle node in the secret key; signing derives its randomizers
from the master seed. Out-of-range branches only make the definitions total; honest algorithms
never reach them.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum

namespace Concrete

/-- Run the `n` computations in index order and collect their results. -/
def sequenceFin {m : Type → Type} [Monad m] {n : Nat}
    (computation : Fin n → m α) : m (Fin n → α) :=
  match n with
  | 0 => pure Fin.elim0
  | n + 1 => do
      let head ← computation 0
      let tail ← sequenceFin fun index : Fin n => computation index.succ
      return Fin.cases head tail

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-! ### Verification -/

/-- `A_level`, or `0` above the tree. -/
def signaturePath (signature : Signature) (level : Nat) : Digest :=
  if hlevel : level < treeHeight then signature.authPath ⟨level, hlevel⟩ else 0

/-- `Chain_{i,idx}(P, start, steps, value)`: the step onto position `start + steps + 1` carries tweak position `2^w * i + start + steps`. -/
def chainWalk (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex) :
    Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | position, steps + 1, value => do
      let previous ← chainWalk parameter leafIndex chain position steps value
      if hposition : position + steps < chainLength - 1 then
        chainHash parameter leafIndex chain ⟨position + steps, hposition⟩ previous
      else
        pure 0

/-- The verifier's half of a chain: walk the remaining `2^w - 1 - x_i` steps. -/
def recoverChain (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (digit : Digit) (value : Digest) : m Digest :=
  chainWalk parameter leafIndex chain digit.val (chainLength - 1 - digit.val) value

/-- `pk'_{idx,i}` for every chain. -/
def recoverEndpoints (parameter : PublicParameter) (leafIndex : LeafIndex)
    (encoding : Encoding) (signature : Signature) :
    m (ChainIndex → Digest) :=
  sequenceFin fun chain =>
    recoverChain parameter leafIndex chain (encoding chain) (signature.chainValue chain)

/-- The index of the Merkle node on the path of `leafIndex` one level above `level`. -/
def nodeIndex (leafIndex : LeafIndex) (level : Nat) : MerkleNode :=
  ⟨leafIndex.val / 2 ^ (level + 1), by
    have hle := Nat.div_le_self leafIndex.val (2 ^ (level + 1))
    exact hle.trans_lt leafIndex.isLt⟩

/-- `Z_{level+1}` from `Z_level` and `A_level`, in the order bit `level` of the leaf index dictates. -/
def authenticationNodeHash (parameter : PublicParameter) (leafIndex : LeafIndex)
    (level : Nat) (current sibling : Digest) : m Digest :=
  if hlevel : level < treeHeight then
    if leafIndex.val.testBit level then
      nodeHash parameter ⟨level, hlevel⟩ (nodeIndex leafIndex level) sibling current
    else
      nodeHash parameter ⟨level, hlevel⟩ (nodeIndex leafIndex level) current sibling
  else
    pure 0

/-- `Z_levels`, folded up from the leaf `Z_0`. -/
def authenticationRoot (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signature : Signature) : Nat → Digest → m Digest
  | 0, leaf => pure leaf
  | levels + 1, leaf => do
      let current ← authenticationRoot parameter leafIndex signature levels leaf
      authenticationNodeHash parameter leafIndex levels current (signaturePath signature levels)

/-- Accept exactly when `Z_h = root`. -/
def verifyAfterLeaf
    (publicKey : PublicKey) (leafIndex : LeafIndex) (signature : Signature) (leaf : Digest) : m Bool := do
  let root ← authenticationRoot publicKey.parameter leafIndex signature treeHeight leaf
  return decide (root = publicKey.root)

/-- `Ver(pk, idx, m, sigma)`. -/
def verify (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) : m Bool := do
  let digest ← encodingHash publicKey.parameter leafIndex message signature.randomness
  let some encoding := TargetSum.decodeDigest digest | return false
  let endpoints ← recoverEndpoints publicKey.parameter leafIndex encoding signature
  let leaf ← leafHash publicKey.parameter leafIndex endpoints
  verifyAfterLeaf publicKey leafIndex signature leaf

/-! ### Key generation: chains and tree -/

/-- `pk_{idx,i} = Chain(P, 0, 2^w - 1, sk_{idx,i})` for every chain. -/
def oneTimePublicKey (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) : m (ChainIndex → Digest) :=
  sequenceFin fun chain =>
    chainWalk parameter leafIndex chain 0 (chainLength - 1) (secret leafIndex chain)

/-- `X_{0,idx}` from the secrets. -/
def leafAt (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) : m Digest := do
  let endpoints ← oneTimePublicKey parameter secret leafIndex
  leafHash parameter leafIndex endpoints

/-- A natural read as a node index. -/
def merkleNodeOfNat (value : Nat) : MerkleNode :=
  ⟨value % lifetime,
    Nat.mod_lt _ (by simp [lifetime])⟩

/-- `2j` or `2j + 1`. -/
def childNode (node : MerkleNode) (right : Bool) : MerkleNode :=
  merkleNodeOfNat (2 * node.val + if right then 1 else 0)

/-- `X_{levels,node}`, the Merkle tree over the one-time leaves. -/
def treeNode (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    Nat → MerkleNode → m Digest
  | 0, node => leafAt parameter secret node
  | levels + 1, node => do
      let left ← treeNode parameter secret levels (childNode node false)
      let right ← treeNode parameter secret levels (childNode node true)
      if hlevel : levels < treeHeight then
        nodeHash parameter ⟨levels, hlevel⟩ node left right
      else
        pure 0

/-- The root is node `0` of level `h`. -/
def rootNode : MerkleNode :=
  ⟨0, by simp [lifetime]⟩

end Concrete

/-! ### Key generation: the stored chain values and tree nodes

Key generation computes the Merkle root through the oracle while logging its hash queries. The
secret key stores every chain value and Merkle node; they are read off that log: the chain and
tree computations are re-run with each hash query answered from the logged values
(`precomputedSecretKey`), so no further oracle query is made. -/

/-- Enter a query log into a cache, in order. -/
def extendHashCacheWithLog (initialCache : QueryCache HashSpec) :
    QueryLog HashSpec → QueryCache HashSpec
  | [] => initialCache
  | ⟨input, output⟩ :: tail =>
      extendHashCacheWithLog (initialCache.cacheQuery input output) tail

/-- The cache a query log records. -/
def hashCacheOfLog (log : QueryLog HashSpec) : QueryCache HashSpec :=
  extendHashCacheWithLog ∅ log

namespace Concrete

/-- Answer a hash query from a recorded query cache, and by 0 for an unrecorded input. -/
def replayHash (cache : QueryCache HashSpec) : QueryImpl HashSpec Id :=
  fun input => (cache input).getD 0

/-- Compute the stored chain values and Merkle nodes by replaying the key-generation query log. -/
def precomputedSecretKey (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (cache : QueryCache HashSpec) :
    SecretKey where
  parameter := parameter
  chainStart := secret
  chainValue := fun leafIndex chain digit =>
    evalWithAnswerFn (replayHash cache)
      (chainWalk parameter leafIndex chain 0 digit.val (secret leafIndex chain) :
        OracleComp HashSpec Digest)
  treeValue := fun height node =>
    evalWithAnswerFn (replayHash cache)
      (treeNode parameter secret height.val node : OracleComp HashSpec Digest)

attribute [irreducible] verifyAfterLeaf treeNode

end Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

noncomputable def sampleMasterSeed : ProbComp MasterSeed :=
  letI := SampleableType.ofFintype MasterSeed
  $ᵗ MasterSeed

namespace Seeded

/-- The seed and the chain and tree values computed during key generation. -/
abbrev SecretKey := XmssSecurity.Seeded.SecretKey numChains

def keygenFromSeed (seed : MasterSeed) : OracleComp HashSpec (PublicKey × SecretKey) := do
  let parameter ← deriveKey 0 .parameter seed
  let secret ← Concrete.sequenceFin fun leafIndex => Concrete.sequenceFin fun chain =>
    deriveKey parameter (.chain leafIndex chain) seed
  let result ← (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
    OracleComp HashSpec Digest).withQueryLog
  let precomputed := Concrete.precomputedSecretKey parameter secret (hashCacheOfLog result.2)
  return (⟨result.1, parameter⟩, ⟨seed, precomputed⟩)

end Seeded

/-! ### Signing -/

namespace Concrete

/-- `floor(idx / 2^level) xor 1`, the sibling on the path. -/
def authenticationPathNode (leafIndex : LeafIndex) (level : MerkleLevel) : MerkleNode :=
  merkleNodeOfNat (Nat.xor (leafIndex.val / 2 ^ level.val) 1)

/-- The signature once the encoding is found. -/
def precomputedSignWithEncoding (secretKey : SecretKey) (leafIndex : LeafIndex)
    (randomness : Randomness) (encoding : Encoding) : Signature :=
  { randomness := randomness
    chainValue := fun chain => secretKey.chainValue leafIndex chain (encoding chain)
    authPath := fun level => secretKey.treeValue level.castSucc (authenticationPathNode leafIndex level) }

/-- One attempt: hash once, and sign if the digest encodes. -/
def precomputedSignAttempt (secretKey : SecretKey) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) : m (Option Signature) := do
  let digest ← encodingHash secretKey.parameter leafIndex message randomness
  let some encoding := TargetSum.decodeDigest digest | return none
  return some (precomputedSignWithEncoding secretKey leafIndex randomness encoding)

end Concrete

namespace Seeded

/-- Derive trials in increasing order, stopping at the first admissible encoding. -/
def signFrom (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) : Nat → Nat → m (Option Signature)
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness ← deriveRandomizer secretKey.precomputed.parameter secretKey.seed leafIndex message (BitVec.ofNat 32 trial)
      match ← Concrete.precomputedSignAttempt secretKey.precomputed leafIndex message randomness with
      | some signature => return some signature
      | none => signFrom secretKey leafIndex message attempts (trial + 1)

def sign (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) : m (Option Signature) :=
  signFrom secretKey leafIndex message signingAttemptLimit 0

end Seeded

end XmssSecurity.TargetSum
