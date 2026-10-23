import Xmss.Proof.Generic.Scheme.Types
import Xmss.Proof.Generic.Scheme.Hashing
import Xmss.Proof.Generic.Code
import VCVio.OracleComp.QueryTracking.LoggingOracle

/-!
# XMSS construction (proof copy)

The proofs work with this copy of the algorithms of the statement, for the code `Code`.
`Bridge.lean` proves that the copy computes the statement's algorithms for the encoding of the
code. The types are in `Types.lean` and the hash routines in `Hashing.lean`.

`Wots`, `Merkle` and `Verify` contain the chain, tree and verification computations; `Seeded` contains key
generation and signing from a 256-bit master seed. Key generation derives the public parameter
and all WOTS chain starts from the master seed in separate hash domains, computes the Merkle root,
and stores every chain value and Merkle node in the secret key; signing derives its randomizers
from the master seed. Out-of-range branches only make the definitions total; honest algorithms
never reach them.
-/

open OracleComp OracleSpec ENNReal

namespace Xmss.Generic

variable [Code]

open Hashing Wots Merkle Verify Keygen Signing

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
def Verify.signaturePath (signature : Signature) (level : Nat) : Digest :=
  if hlevel : level < treeHeight then signature.authPath ⟨level, hlevel⟩ else 0

/-- `Chain_{i,idx}(P, start, steps, value)`: the step onto position `start + steps + 1` carries tweak position `2^w * i + start + steps`. -/
def Wots.chainWalk (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex) :
    Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | position, steps + 1, value => do
      let previous ← chainWalk parameter leafIndex chain position steps value
      if hposition : position + steps < chainLength - 1 then
        chainHash parameter leafIndex chain ⟨position + steps, hposition⟩ previous
      else
        pure 0

/-- The verifier's half of a chain: walk the remaining `2^w - 1 - x_i` steps. -/
def Verify.recoverChain (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (digit : Digit) (value : Digest) : m Digest :=
  chainWalk parameter leafIndex chain digit.val (chainLength - 1 - digit.val) value

/-- `pk'_{idx,i}` for every chain. -/
def Verify.recoverEndpoints (parameter : PublicParameter) (leafIndex : LeafIndex)
    (encoding : Encoding) (signature : Signature) :
    m (ChainIndex → Digest) :=
  sequenceFin fun chain =>
    recoverChain parameter leafIndex chain (encoding chain) (signature.chainValue chain)

/-- The index of the Merkle node on the path of `leafIndex` one level above `level`. -/
def Merkle.nodeIndex (leafIndex : LeafIndex) (level : Nat) : MerkleNode :=
  ⟨leafIndex.val / 2 ^ (level + 1), by
    have hle := Nat.div_le_self leafIndex.val (2 ^ (level + 1))
    exact hle.trans_lt leafIndex.isLt⟩

/-- `Z_{level+1}` from `Z_level` and `A_level`, in the order bit `level` of the leaf index dictates. -/
def Verify.authenticationNodeHash (parameter : PublicParameter) (leafIndex : LeafIndex)
    (level : Nat) (current sibling : Digest) : m Digest :=
  if hlevel : level < treeHeight then
    if leafIndex.val.testBit level then
      nodeHash parameter ⟨level, hlevel⟩ (nodeIndex leafIndex level) sibling current
    else
      nodeHash parameter ⟨level, hlevel⟩ (nodeIndex leafIndex level) current sibling
  else
    pure 0

/-- `Z_levels`, folded up from the leaf `Z_0`. -/
def Verify.authenticationRoot (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signature : Signature) : Nat → Digest → m Digest
  | 0, leaf => pure leaf
  | levels + 1, leaf => do
      let current ← authenticationRoot parameter leafIndex signature levels leaf
      authenticationNodeHash parameter leafIndex levels current (signaturePath signature levels)

/-- Accept exactly when `Z_h = root`. -/
def Verify.verifyAfterLeaf
    (publicKey : PublicKey) (leafIndex : LeafIndex) (signature : Signature) (leaf : Digest) : m Bool := do
  let root ← authenticationRoot publicKey.parameter leafIndex signature treeHeight leaf
  return decide (root = publicKey.root)

/-- `Ver(pk, idx, m, sigma)`. -/
def Verify.verify (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) : m Bool := do
  let digest ← encodingHash publicKey.parameter leafIndex message signature.randomness
  let some encoding := Code.decodeDigest digest | return false
  let endpoints ← recoverEndpoints publicKey.parameter leafIndex encoding signature
  let leaf ← leafHash publicKey.parameter leafIndex endpoints
  verifyAfterLeaf publicKey leafIndex signature leaf

/-! ### Key generation: chains and tree -/

/-- `pk_{idx,i} = Chain(P, 0, 2^w - 1, sk_{idx,i})` for every chain. -/
def Wots.oneTimePublicKey (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) : m (ChainIndex → Digest) :=
  sequenceFin fun chain =>
    chainWalk parameter leafIndex chain 0 (chainLength - 1) (secret leafIndex chain)

/-- `X_{0,idx}` from the secrets. -/
def Merkle.leafAt (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) : m Digest := do
  let endpoints ← oneTimePublicKey parameter secret leafIndex
  leafHash parameter leafIndex endpoints

/-- A natural read as a node index. -/
def Merkle.merkleNodeOfNat (value : Nat) : MerkleNode :=
  ⟨value % lifetime,
    Nat.mod_lt _ (by simp [lifetime])⟩

/-- `2j` or `2j + 1`. -/
def Merkle.childNode (node : MerkleNode) (right : Bool) : MerkleNode :=
  merkleNodeOfNat (2 * node.val + if right then 1 else 0)

/-- `X_{levels,node}`, the Merkle tree over the one-time leaves. -/
def Merkle.treeNode (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
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
def Merkle.rootNode : MerkleNode :=
  ⟨0, by simp [lifetime]⟩

/-! ### Key generation: the stored chain values and tree nodes

Key generation computes the Merkle root through the oracle while logging its hash queries, then
materializes every chain value and Merkle node into vectors before returning. The recorded answers
fill the vectors without further oracle queries; signing only indexes the stored digests. -/

/-- Enter a query log into a cache, in order. -/
def extendHashCacheWithLog (initialCache : QueryCache HashSpec) :
    QueryLog HashSpec → QueryCache HashSpec
  | [] => initialCache
  | ⟨input, output⟩ :: tail =>
      extendHashCacheWithLog (initialCache.cacheQuery input output) tail

/-- The cache a query log records. -/
def hashCacheOfLog (log : QueryLog HashSpec) : QueryCache HashSpec :=
  extendHashCacheWithLog ∅ log

open Hashing Wots Merkle Verify Keygen Signing

/-- Answer a hash query from a recorded query cache, and by 0 for an unrecorded input. -/
def Keygen.replayHash (cache : QueryCache HashSpec) : QueryImpl HashSpec Id :=
  fun input => (cache input).getD 0

/-- Materialize the chain values and Merkle nodes into vectors during key generation.
Replay is used only to fill the vectors; the resulting key stores digests, not replay functions. -/
def Keygen.precomputedSecretKey (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (cache : QueryCache HashSpec) :
    SecretKey where
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

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

noncomputable def sampleMasterSeed : ProbComp MasterSeed :=
  letI := SampleableType.ofFintype MasterSeed
  $ᵗ MasterSeed

namespace Seeded

/-- The seed and the chain and tree values computed during key generation. -/
abbrev SecretKey := Xmss.Seeded.SecretKey Code.numChains

def keygenFromSeed (seed : MasterSeed) : OracleComp HashSpec (PublicKey × SecretKey) := do
  let parameter ← deriveKey 0 .parameter seed
  let secret ← sequenceFin fun leafIndex => sequenceFin fun chain =>
    deriveKey parameter (.chain leafIndex chain) seed
  let result ← (Merkle.treeNode parameter secret treeHeight Merkle.rootNode :
    OracleComp HashSpec Digest).withQueryLog
  let precomputed := Keygen.precomputedSecretKey parameter secret (hashCacheOfLog result.2)
  return (⟨result.1, parameter⟩, ⟨seed, precomputed⟩)

end Seeded

/-! ### Signing -/

open Hashing Wots Merkle Verify Keygen Signing

/-- `floor(idx / 2^level) xor 1`, the sibling on the path. -/
def Merkle.authenticationPathNode (leafIndex : LeafIndex) (level : MerkleLevel) : MerkleNode :=
  merkleNodeOfNat (Nat.xor (leafIndex.val / 2 ^ level.val) 1)

/-- The signature once the encoding is found. -/
def Signing.precomputedSignWithEncoding (secretKey : SecretKey) (leafIndex : LeafIndex)
    (randomness : Randomness) (encoding : Encoding) : Signature :=
  { randomness := randomness
    chainValue := fun chain => secretKey.chainValue leafIndex chain (encoding chain)
    authPath := fun level => secretKey.treeValue level.castSucc (authenticationPathNode leafIndex level) }

/-- One attempt: hash once, and sign if the digest encodes. -/
def Signing.precomputedSignAttempt (secretKey : SecretKey) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) : m (Option Signature) := do
  let digest ← encodingHash secretKey.parameter leafIndex message randomness
  let some encoding := Code.decodeDigest digest | return none
  return some (precomputedSignWithEncoding secretKey leafIndex randomness encoding)

namespace Seeded

/-- Derive trials in increasing order, stopping at the first admissible encoding. -/
def signFrom (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) : Nat → Nat → m (Option Signature)
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness ← deriveRandomizer secretKey.precomputed.parameter secretKey.seed leafIndex message (BitVec.ofNat 32 trial)
      match ← Signing.precomputedSignAttempt secretKey.precomputed leafIndex message randomness with
      | some signature => return some signature
      | none => signFrom secretKey leafIndex message attempts (trial + 1)

def sign (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) : m (Option Signature) :=
  signFrom secretKey leafIndex message Code.signingAttemptLimit 0

theorem sign_eq_signFrom (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) :
    (sign secretKey leafIndex message : m (Option Signature)) =
      signFrom secretKey leafIndex message Code.signingAttemptLimit 0 := rfl

end Seeded

open Hashing Wots Merkle Verify Keygen Signing

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- The verifier, with the decoding step written out. -/
theorem Verify.verify_eq_decode (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) :
    (verify publicKey leafIndex message signature : m Bool) = (do
      let digest ← encodingHash publicKey.parameter leafIndex message signature.randomness
      let some encoding := Code.decodeDigest digest | return false
      let endpoints ← recoverEndpoints publicKey.parameter leafIndex encoding signature
      let leaf ← leafHash publicKey.parameter leafIndex endpoints
      verifyAfterLeaf publicKey leafIndex signature leaf) := rfl

end Xmss.Generic
