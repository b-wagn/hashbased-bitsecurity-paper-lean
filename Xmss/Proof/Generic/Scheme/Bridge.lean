import Xmss.Proof.Generic.Scheme.Xmss

/-!
# The proof copy of the scheme is the statement's scheme

The proofs work with a copy of the construction for the code `Code` (`Scheme/`). This file proves
that the copy computes the same algorithms as the generic construction of the statement for the
encoding `wotsEncoding` of the code (`xmss_eq`).
-/

open OracleComp OracleSpec

namespace Xmss.Generic

variable [Code]

/-- The WOTS encoding of the statement's construction that the code induces. -/
def wotsEncoding : WotsEncoding := ⟨Code.numChains, Code.decodeDigest, Code.signingAttemptLimit⟩

namespace Bridge

attribute [local semireducible] Merkle.treeNode Xmss.Merkle.treeNode
  Verify.verifyAfterLeaf Xmss.Verify.verifyAfterLeaf

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

omit [Code] in
theorem sequenceFin_eq {m : Type → Type} [Monad m] {α : Type} :
    ∀ {n : Nat} (computation : Fin n → m α),
      sequenceFin computation = Xmss.sequenceFin computation
  | 0, _ => rfl
  | n + 1, computation => by
      simp only [sequenceFin, Xmss.sequenceFin]
      rw [sequenceFin_eq]

omit [Monad m] in
theorem chainHash_eq (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) :
    (Hashing.chainHash parameter leafIndex chain step value : m Digest) =
      Xmss.Hashing.chainHash parameter leafIndex chain step value := rfl

omit [Monad m] in
theorem leafHash_eq (parameter : PublicParameter) (leafIndex : LeafIndex)
    (endpoints : ChainIndex → Digest) :
    (Hashing.leafHash parameter leafIndex endpoints : m Digest) =
      Xmss.Hashing.leafHash parameter leafIndex endpoints := rfl

omit [Monad m] in
theorem nodeHash_eq (parameter : PublicParameter) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) :
    (Hashing.nodeHash parameter level node left right : m Digest) =
      Xmss.Hashing.nodeHash parameter level node left right := rfl

omit [Monad m] in
theorem encodingHash_eq (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) :
    (Hashing.encodingHash parameter leafIndex message randomness : m Digest) =
      Xmss.Hashing.encodingHash parameter leafIndex message randomness := rfl

omit [Monad m] in
theorem deriveKey_parameter_eq (parameter : PublicParameter) (seed : MasterSeed) :
    (deriveKey parameter .parameter seed : m Digest) =
      Xmss.deriveKey parameter .parameter seed := rfl

omit [Monad m] in
theorem deriveKey_chain_eq (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (seed : MasterSeed) :
    (deriveKey parameter (.chain leafIndex chain) seed : m Digest) =
      Xmss.deriveKey parameter (.chain leafIndex chain.val) seed := rfl

omit [Code] [Monad m] in
theorem deriveRandomizer_eq (parameter : PublicParameter) (seed : MasterSeed)
    (leafIndex : LeafIndex) (message : Message) (trial : BitVec 32) :
    (deriveRandomizer parameter seed leafIndex message trial : m Randomness) =
      Xmss.deriveRandomizer parameter seed leafIndex message trial := rfl

theorem chainWalk_eq (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position : Nat) : ∀ (steps : Nat) (value : Digest),
      (Wots.chainWalk parameter leafIndex chain position steps value : m Digest) =
        Xmss.Wots.chainWalk parameter leafIndex chain position steps value
  | 0, _ => rfl
  | steps + 1, value => by
      simp only [Wots.chainWalk, Xmss.Wots.chainWalk, chainHash_eq,
        chainWalk_eq parameter leafIndex chain position steps value]

theorem recoverEndpoints_eq (parameter : PublicParameter) (leafIndex : LeafIndex)
    (encoding : Encoding) (signature : Signature) :
    (Verify.recoverEndpoints parameter leafIndex encoding signature : m (ChainIndex → Digest)) =
      Xmss.Verify.recoverEndpoints parameter leafIndex encoding signature := by
  simp only [Verify.recoverEndpoints, Xmss.Verify.recoverEndpoints,
    Verify.recoverChain, Xmss.Verify.recoverChain, chainWalk_eq, sequenceFin_eq]

theorem authenticationRoot_eq (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signature : Signature) : ∀ (levels : Nat) (leaf : Digest),
      (Verify.authenticationRoot parameter leafIndex signature levels leaf : m Digest) =
        Xmss.Verify.authenticationRoot parameter leafIndex signature levels leaf
  | 0, _ => rfl
  | levels + 1, leaf => by
      simp only [Verify.authenticationRoot, Xmss.Verify.authenticationRoot,
        authenticationRoot_eq parameter leafIndex signature levels leaf]
      rfl

theorem verifyAfterLeaf_eq (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Signature) (leaf : Digest) :
    (Verify.verifyAfterLeaf publicKey leafIndex signature leaf : m Bool) =
      Xmss.Verify.verifyAfterLeaf publicKey leafIndex signature leaf := by
  unfold Verify.verifyAfterLeaf Xmss.Verify.verifyAfterLeaf
  rw [authenticationRoot_eq]

theorem verify_eq (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
    (signature : Signature) :
    (Verify.verify publicKey leafIndex message signature : m Bool) =
      Xmss.Verify.verify wotsEncoding publicKey leafIndex message signature := by
  simp only [Verify.verify, Xmss.Verify.verify, encodingHash_eq,
    recoverEndpoints_eq, leafHash_eq, verifyAfterLeaf_eq]
  refine bind_congr fun digest => ?_
  rw [show wotsEncoding.decodeDigest digest = Code.decodeDigest digest from rfl]
  cases Code.decodeDigest digest <;> rfl

theorem treeNode_eq (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    ∀ (levels : Nat) (node : MerkleNode),
      (Merkle.treeNode parameter secret levels node : m Digest) =
        Xmss.Merkle.treeNode parameter secret levels node
  | 0, node => by
      show Merkle.leafAt parameter secret node = Xmss.Merkle.leafAt parameter secret node
      simp only [Merkle.leafAt, Xmss.Merkle.leafAt, Wots.oneTimePublicKey,
        Xmss.Wots.oneTimePublicKey, chainWalk_eq, sequenceFin_eq, leafHash_eq]
  | levels + 1, node => by
      show (do
          let left ← Merkle.treeNode parameter secret levels (Merkle.childNode node false)
          let right ← Merkle.treeNode parameter secret levels (Merkle.childNode node true)
          if hlevel : levels < treeHeight then
            Hashing.nodeHash parameter ⟨levels, hlevel⟩ node left right
          else
            pure 0) = (do
          let left ← Xmss.Merkle.treeNode parameter secret levels
            (Xmss.Merkle.childNode node false)
          let right ← Xmss.Merkle.treeNode parameter secret levels
            (Xmss.Merkle.childNode node true)
          if hlevel : levels < treeHeight then
            Xmss.Hashing.nodeHash parameter ⟨levels, hlevel⟩ node left right
          else
            pure 0)
      simp only [treeNode_eq parameter secret levels, nodeHash_eq]
      rfl

omit [Code] in
theorem rootNode_eq : Merkle.rootNode = Xmss.Merkle.rootNode := rfl

omit [Code] in
theorem sampleMasterSeed_eq : sampleMasterSeed = Xmss.sampleMasterSeed := rfl

theorem precomputedSecretKey_eq (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (cache : QueryCache HashSpec) :
    Keygen.precomputedSecretKey parameter secret cache =
      Xmss.Keygen.precomputedSecretKey parameter secret cache := by
  simp only [Keygen.precomputedSecretKey, Xmss.Keygen.precomputedSecretKey,
    chainWalk_eq, treeNode_eq]
  rfl

omit [Code] in
theorem hashCacheOfLog_eq (log : QueryLog HashSpec) :
    hashCacheOfLog log = Xmss.hashCacheOfLog log := by
  suffices ∀ initialCache, extendHashCacheWithLog initialCache log =
      Xmss.extendHashCacheWithLog initialCache log from this ∅
  induction log with
  | nil => intro; rfl
  | cons head tail ih =>
      intro initialCache
      exact ih _

theorem keygenFromSeed_eq (seed : MasterSeed) :
    Seeded.keygenFromSeed seed = Xmss.Seeded.keygenFromSeed Code.numChains seed := by
  simp only [Seeded.keygenFromSeed, Xmss.Seeded.keygenFromSeed, deriveKey_parameter_eq,
    deriveKey_chain_eq, sequenceFin_eq, treeNode_eq, precomputedSecretKey_eq, hashCacheOfLog_eq,
    rootNode_eq]

theorem precomputedSignAttempt_eq (secretKey : SecretKey) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) :
    (Signing.precomputedSignAttempt secretKey leafIndex message randomness :
        m (Option Signature)) =
      Xmss.Signing.precomputedSignAttempt wotsEncoding secretKey leafIndex message
        randomness := by
  simp only [Signing.precomputedSignAttempt, Xmss.Signing.precomputedSignAttempt,
    encodingHash_eq]
  refine bind_congr fun digest => ?_
  rw [show wotsEncoding.decodeDigest digest = Code.decodeDigest digest from rfl]
  cases Code.decodeDigest digest <;> rfl

theorem signFrom_eq (secretKey : Seeded.SecretKey) (leafIndex : LeafIndex) (message : Message) :
    ∀ (attempts trial : Nat),
      (Seeded.signFrom secretKey leafIndex message attempts trial : m (Option Signature)) =
        Xmss.Seeded.signFrom wotsEncoding secretKey leafIndex message attempts trial
  | 0, _ => rfl
  | attempts + 1, trial => by
      simp only [Seeded.signFrom, Xmss.Seeded.signFrom, deriveRandomizer_eq,
        precomputedSignAttempt_eq, signFrom_eq secretKey leafIndex message attempts]
      refine bind_congr fun randomness => bind_congr fun attempt => ?_
      cases attempt <;> rfl

theorem sign_eq [LawfulMonad m] (secretKey : Seeded.SecretKey) (leafIndex : LeafIndex)
    (message : Message) :
    (Seeded.sign secretKey leafIndex message : m (Option Signature)) =
      Xmss.Seeded.sign wotsEncoding secretKey leafIndex message := by
  show (Seeded.signFrom secretKey leafIndex message Code.signingAttemptLimit 0 :
      m (Option Signature)) = _
  exact signFrom_eq (m := m) secretKey leafIndex message _ 0

end Bridge

/-- The statement's construction for the encoding of the code is the copy `xmss` the proofs work
with. -/
theorem xmss_eq : Xmss.xmss wotsEncoding = xmss := by
  unfold Xmss.xmss xmss
  simp only [Bridge.keygenFromSeed_eq, Bridge.sign_eq, Bridge.verify_eq, Bridge.sampleMasterSeed_eq]
  rfl

end Xmss.Generic
