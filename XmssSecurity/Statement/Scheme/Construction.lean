import XmssSecurity.Statement.Scheme.Types
import XmssSecurity.Statement.Scheme.Hashing
import VCVio.OracleComp.QueryTracking.LoggingOracle

/-!
# XMSS construction

Algorithms for a WOTS encoding `E`, using the types and hash routines of `Types.lean` and
`Hashing.lean`. `Concrete` contains verification, chains, and the Merkle tree. `Seeded` derives
keys and randomizers from a 256-bit seed. Signing tries at most `E.signingAttempts` randomizers;
verification rejects digests that do not decode. Out-of-range branches make the functions total.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

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

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m] {v : Nat}

/-! ### Verification -/

/-- `A_level`, or `0` above the tree. -/
def signaturePath (signature : Signature v) (level : Nat) : Digest :=
  if hlevel : level < treeHeight then signature.authPath ⟨level, hlevel⟩ else 0

/-- `Chain(P, ep, i, start, start + steps, value)`: walk `steps` positions from `start`.
The step from position `k` to `k + 1` uses tweak position `2^w * i + k`. -/
def chainWalk (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : Fin v) :
    Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | position, steps + 1, value => do
      let previous ← chainWalk parameter leafIndex chain position steps value
      if hposition : position + steps < chainLength - 1 then
        chainHash parameter leafIndex chain ⟨position + steps, hposition⟩ previous
      else
        pure 0

/-- The verifier's half of a chain: walk the remaining `2^w - 1 - x_i` steps. -/
def recoverChain (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : Fin v)
    (digit : Digit) (value : Digest) : m Digest :=
  chainWalk parameter leafIndex chain digit.val (chainLength - 1 - digit.val) value

/-- The verifier's recovered endpoint `pk'_i` for every chain. -/
def recoverEndpoints (parameter : PublicParameter) (leafIndex : LeafIndex)
    (encoding : Encoding v) (signature : Signature v) :
    m (Fin v → Digest) :=
  sequenceFin fun chain =>
    recoverChain parameter leafIndex chain (encoding chain) (signature.chainValue chain)

/-- The index of the Merkle node on the path of `leafIndex` one level above `level`. -/
def nodeIndex (leafIndex : LeafIndex) (level : Nat) : MerkleNode :=
  ⟨leafIndex.val / 2 ^ (level + 1), by
    have hle := Nat.div_le_self leafIndex.val (2 ^ (level + 1))
    exact hle.trans_lt leafIndex.isLt⟩

/-- `X'_{level+1}` from `X'_level` and `A_level`, ordered by bit `level` of the epoch. -/
def authenticationNodeHash (parameter : PublicParameter) (leafIndex : LeafIndex)
    (level : Nat) (current sibling : Digest) : m Digest :=
  if hlevel : level < treeHeight then
    if leafIndex.val.testBit level then
      nodeHash parameter ⟨level, hlevel⟩ (nodeIndex leafIndex level) sibling current
    else
      nodeHash parameter ⟨level, hlevel⟩ (nodeIndex leafIndex level) current sibling
  else
    pure 0

/-- `X'_levels`, folded up from the leaf `X'_0`. -/
def authenticationRoot (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signature : Signature v) : Nat → Digest → m Digest
  | 0, leaf => pure leaf
  | levels + 1, leaf => do
      let current ← authenticationRoot parameter leafIndex signature levels leaf
      authenticationNodeHash parameter leafIndex levels current (signaturePath signature levels)

/-- Accept exactly when `X'_h = root`. -/
def verifyAfterLeaf
    (publicKey : PublicKey) (leafIndex : LeafIndex) (signature : Signature v) (leaf : Digest) : m Bool := do
  let root ← authenticationRoot publicKey.parameter leafIndex signature treeHeight leaf
  return decide (root = publicKey.root)

/-- `Verify(pk, ep, m, σ)`: reject a digest that does not decode. -/
def verify (E : WotsEncoding) (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature E.numChains) : m Bool := do
  let digest ← encodingHash publicKey.parameter leafIndex message signature.randomness
  let some encoding := E.decode digest | return false
  let endpoints ← recoverEndpoints publicKey.parameter leafIndex encoding signature
  let leaf ← leafHash publicKey.parameter leafIndex endpoints
  verifyAfterLeaf publicKey leafIndex signature leaf

/-! ### Key generation: chains and tree -/

/-- `pk_{ep,i} = Chain(P, ep, i, 0, 2^w - 1, sk_{ep,i})` for every chain. -/
def oneTimePublicKey (parameter : PublicParameter) (secret : LeafIndex → Fin v → Digest)
    (leafIndex : LeafIndex) : m (Fin v → Digest) :=
  sequenceFin fun chain =>
    chainWalk parameter leafIndex chain 0 (chainLength - 1) (secret leafIndex chain)

/-- `X_{0,ep}` from the chain starts. -/
def leafAt (parameter : PublicParameter) (secret : LeafIndex → Fin v → Digest)
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
def treeNode (parameter : PublicParameter) (secret : LeafIndex → Fin v → Digest) :
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

Key generation logs the hashes used to compute the root, then materializes the chain and tree
vectors from the recorded answers before returning the secret key. This makes no further oracle
queries. Signing only indexes the stored vectors. -/

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

variable {v : Nat}

/-- Answer a hash query from a recorded query cache, and by 0 for an unrecorded input. -/
def replayHash (cache : QueryCache HashSpec) : QueryImpl HashSpec Id :=
  fun input => (cache input).getD 0

/-- Materialize the chain values and Merkle nodes into vectors during key generation.
Replay is used only to fill the vectors; the resulting key stores digests, not replay functions. -/
def precomputedSecretKey (parameter : PublicParameter)
    (secret : LeafIndex → Fin v → Digest) (cache : QueryCache HashSpec) :
    SecretKey v where
  parameter := parameter
  chainStart := secret
  chainValues := Vector.ofFn fun leafIndex => Vector.ofFn fun chain => Vector.ofFn fun digit =>
    evalWithAnswerFn (replayHash cache)
      (chainWalk parameter leafIndex chain 0 digit.val (secret leafIndex chain) :
        OracleComp HashSpec Digest)
  treeValues := Vector.ofFn fun height => Vector.ofFn fun node =>
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
structure SecretKey (v : Nat) where
  seed : MasterSeed
  precomputed : XmssSecurity.SecretKey v

/-- `Gen` from the master seed, for `v` chains per leaf. -/
def keygenFromSeed (v : Nat) (seed : MasterSeed) : OracleComp HashSpec (PublicKey × SecretKey v) := do
  let parameter ← deriveKey 0 .parameter seed
  let secret ← Concrete.sequenceFin fun leafIndex => Concrete.sequenceFin fun chain : Fin v =>
    deriveKey parameter (.chain leafIndex chain.val) seed
  let result ← (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
    OracleComp HashSpec Digest).withQueryLog
  let precomputed := Concrete.precomputedSecretKey parameter secret (hashCacheOfLog result.2)
  return (⟨result.1, parameter⟩, ⟨seed, precomputed⟩)

end Seeded

/-! ### Signing -/

namespace Concrete

/-- `floor(ep / 2^level) xor 1`, the sibling on the path. -/
def authenticationPathNode (leafIndex : LeafIndex) (level : MerkleLevel) : MerkleNode :=
  merkleNodeOfNat (Nat.xor (leafIndex.val / 2 ^ level.val) 1)

variable {v : Nat}

/-- The signature once the encoding is found. -/
def precomputedSignWithEncoding (secretKey : SecretKey v) (leafIndex : LeafIndex)
    (randomness : Randomness) (encoding : Encoding v) : Signature v :=
  { randomness := randomness
    chainValue := fun chain => secretKey.chainValue leafIndex chain (encoding chain)
    authPath := fun level => secretKey.treeValue level.castSucc (authenticationPathNode leafIndex level) }

/-- One attempt: hash once, and sign if the digest encodes. -/
def precomputedSignAttempt (E : WotsEncoding) (secretKey : SecretKey E.numChains)
    (leafIndex : LeafIndex) (message : Message) (randomness : Randomness) :
    m (Option (Signature E.numChains)) := do
  let digest ← encodingHash secretKey.parameter leafIndex message randomness
  let some encoding := E.decode digest | return none
  return some (precomputedSignWithEncoding secretKey leafIndex randomness encoding)

end Concrete

namespace Seeded

/-- Derive trials in increasing order, stopping at the first admissible encoding. -/
def signFrom (E : WotsEncoding) (secretKey : SecretKey E.numChains) (leafIndex : LeafIndex)
    (message : Message) : Nat → Nat → m (Option (Signature E.numChains))
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness ← deriveRandomizer secretKey.precomputed.parameter secretKey.seed leafIndex
        message (BitVec.ofNat 32 trial)
      match ← Concrete.precomputedSignAttempt E secretKey.precomputed leafIndex message randomness with
      | some signature => return some signature
      | none => signFrom E secretKey leafIndex message attempts (trial + 1)

/-- `Sign(sk, ep, m)`: at most `K` randomizer trials, starting from trial `0`. -/
def sign (E : WotsEncoding) (secretKey : SecretKey E.numChains) (leafIndex : LeafIndex)
    (message : Message) : m (Option (Signature E.numChains)) :=
  signFrom E secretKey leafIndex message E.signingAttempts 0

end Seeded

end XmssSecurity
