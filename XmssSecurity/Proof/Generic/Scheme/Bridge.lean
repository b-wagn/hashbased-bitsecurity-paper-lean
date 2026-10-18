import XmssSecurity.Proof.Generic.Scheme.Xmss

/-!
# The proof copy of the scheme is the statement's scheme

The proofs work with a copy of the construction for the code `Code` (`Scheme/`). This file proves
that the copy computes the same algorithms as the generic construction of the statement for the
encoding `wotsEncoding` of the code (`xmss_eq`).
-/

open OracleComp OracleSpec

namespace XmssSecurity.Generic

variable [Code]

/-- The WOTS encoding of the statement's construction that the code induces. -/
def wotsEncoding : WotsEncoding := ⟨Code.numChains, Code.decodeDigest, Code.signingAttemptLimit⟩

namespace Bridge

attribute [local semireducible] Concrete.treeNode XmssSecurity.Concrete.treeNode
  Concrete.verifyAfterLeaf XmssSecurity.Concrete.verifyAfterLeaf

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

theorem sequenceFin_eq {m : Type → Type} [Monad m] {α : Type} :
    ∀ {n : Nat} (computation : Fin n → m α),
      Concrete.sequenceFin computation = XmssSecurity.Concrete.sequenceFin computation
  | 0, _ => rfl
  | n + 1, computation => by
      simp only [Concrete.sequenceFin, XmssSecurity.Concrete.sequenceFin]
      rw [sequenceFin_eq]

theorem chainHash_eq (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) :
    (Concrete.chainHash parameter leafIndex chain step value : m Digest) =
      XmssSecurity.Concrete.chainHash parameter leafIndex chain step value := rfl

theorem leafHash_eq (parameter : PublicParameter) (leafIndex : LeafIndex)
    (endpoints : ChainIndex → Digest) :
    (Concrete.leafHash parameter leafIndex endpoints : m Digest) =
      XmssSecurity.Concrete.leafHash parameter leafIndex endpoints := rfl

theorem nodeHash_eq (parameter : PublicParameter) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) :
    (Concrete.nodeHash parameter level node left right : m Digest) =
      XmssSecurity.Concrete.nodeHash parameter level node left right := rfl

theorem encodingHash_eq (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) :
    (Concrete.encodingHash parameter leafIndex message randomness : m Digest) =
      XmssSecurity.Concrete.encodingHash parameter leafIndex message randomness := rfl

theorem deriveKey_parameter_eq (parameter : PublicParameter) (seed : MasterSeed) :
    (deriveKey parameter .parameter seed : m Digest) =
      XmssSecurity.deriveKey parameter .parameter seed := rfl

theorem deriveKey_chain_eq (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (seed : MasterSeed) :
    (deriveKey parameter (.chain leafIndex chain) seed : m Digest) =
      XmssSecurity.deriveKey parameter (.chain leafIndex chain.val) seed := rfl

theorem deriveRandomizer_eq (parameter : PublicParameter) (seed : MasterSeed)
    (leafIndex : LeafIndex) (message : Message) (trial : BitVec 32) :
    (deriveRandomizer parameter seed leafIndex message trial : m Randomness) =
      XmssSecurity.deriveRandomizer parameter seed leafIndex message trial := rfl

theorem chainWalk_eq (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position : Nat) : ∀ (steps : Nat) (value : Digest),
      (Concrete.chainWalk parameter leafIndex chain position steps value : m Digest) =
        XmssSecurity.Concrete.chainWalk parameter leafIndex chain position steps value
  | 0, _ => rfl
  | steps + 1, value => by
      simp only [Concrete.chainWalk, XmssSecurity.Concrete.chainWalk, chainHash_eq,
        chainWalk_eq parameter leafIndex chain position steps value]

theorem recoverEndpoints_eq (parameter : PublicParameter) (leafIndex : LeafIndex)
    (encoding : Encoding) (signature : Signature) :
    (Concrete.recoverEndpoints parameter leafIndex encoding signature : m (ChainIndex → Digest)) =
      XmssSecurity.Concrete.recoverEndpoints parameter leafIndex encoding signature := by
  simp only [Concrete.recoverEndpoints, XmssSecurity.Concrete.recoverEndpoints,
    Concrete.recoverChain, XmssSecurity.Concrete.recoverChain, chainWalk_eq, sequenceFin_eq]

theorem authenticationRoot_eq (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signature : Signature) : ∀ (levels : Nat) (leaf : Digest),
      (Concrete.authenticationRoot parameter leafIndex signature levels leaf : m Digest) =
        XmssSecurity.Concrete.authenticationRoot parameter leafIndex signature levels leaf
  | 0, _ => rfl
  | levels + 1, leaf => by
      simp only [Concrete.authenticationRoot, XmssSecurity.Concrete.authenticationRoot,
        authenticationRoot_eq parameter leafIndex signature levels leaf]
      rfl

theorem verifyAfterLeaf_eq (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Signature) (leaf : Digest) :
    (Concrete.verifyAfterLeaf publicKey leafIndex signature leaf : m Bool) =
      XmssSecurity.Concrete.verifyAfterLeaf publicKey leafIndex signature leaf := by
  unfold Concrete.verifyAfterLeaf XmssSecurity.Concrete.verifyAfterLeaf
  rw [authenticationRoot_eq]

theorem verify_eq (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
    (signature : Signature) :
    (Concrete.verify publicKey leafIndex message signature : m Bool) =
      XmssSecurity.Concrete.verify wotsEncoding publicKey leafIndex message signature := by
  simp only [Concrete.verify, XmssSecurity.Concrete.verify, encodingHash_eq,
    recoverEndpoints_eq, leafHash_eq, verifyAfterLeaf_eq]
  refine bind_congr fun digest => ?_
  rw [show wotsEncoding.decode digest = Code.decodeDigest digest from rfl]
  cases Code.decodeDigest digest <;> rfl

theorem treeNode_eq (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    ∀ (levels : Nat) (node : MerkleNode),
      (Concrete.treeNode parameter secret levels node : m Digest) =
        XmssSecurity.Concrete.treeNode parameter secret levels node
  | 0, node => by
      show Concrete.leafAt parameter secret node = XmssSecurity.Concrete.leafAt parameter secret node
      simp only [Concrete.leafAt, XmssSecurity.Concrete.leafAt, Concrete.oneTimePublicKey,
        XmssSecurity.Concrete.oneTimePublicKey, chainWalk_eq, sequenceFin_eq, leafHash_eq]
  | levels + 1, node => by
      show (do
          let left ← Concrete.treeNode parameter secret levels (Concrete.childNode node false)
          let right ← Concrete.treeNode parameter secret levels (Concrete.childNode node true)
          if hlevel : levels < treeHeight then
            Concrete.nodeHash parameter ⟨levels, hlevel⟩ node left right
          else
            pure 0) = (do
          let left ← XmssSecurity.Concrete.treeNode parameter secret levels
            (XmssSecurity.Concrete.childNode node false)
          let right ← XmssSecurity.Concrete.treeNode parameter secret levels
            (XmssSecurity.Concrete.childNode node true)
          if hlevel : levels < treeHeight then
            XmssSecurity.Concrete.nodeHash parameter ⟨levels, hlevel⟩ node left right
          else
            pure 0)
      simp only [treeNode_eq parameter secret levels, nodeHash_eq]
      rfl

theorem rootNode_eq : Concrete.rootNode = XmssSecurity.Concrete.rootNode := rfl

theorem sampleMasterSeed_eq : sampleMasterSeed = XmssSecurity.sampleMasterSeed := rfl

theorem precomputedSecretKey_eq (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (cache : QueryCache HashSpec) :
    Concrete.precomputedSecretKey parameter secret cache =
      XmssSecurity.Concrete.precomputedSecretKey parameter secret cache := by
  simp only [Concrete.precomputedSecretKey, XmssSecurity.Concrete.precomputedSecretKey,
    chainWalk_eq, treeNode_eq]
  rfl

theorem hashCacheOfLog_eq (log : QueryLog HashSpec) :
    hashCacheOfLog log = XmssSecurity.hashCacheOfLog log := by
  suffices ∀ initialCache, extendHashCacheWithLog initialCache log =
      XmssSecurity.extendHashCacheWithLog initialCache log from this ∅
  induction log with
  | nil => intro; rfl
  | cons head tail ih =>
      intro initialCache
      exact ih _

theorem keygenFromSeed_eq (seed : MasterSeed) :
    Seeded.keygenFromSeed seed = XmssSecurity.Seeded.keygenFromSeed Code.numChains seed := by
  simp only [Seeded.keygenFromSeed, XmssSecurity.Seeded.keygenFromSeed, deriveKey_parameter_eq,
    deriveKey_chain_eq, sequenceFin_eq, treeNode_eq, precomputedSecretKey_eq, hashCacheOfLog_eq,
    rootNode_eq]

theorem precomputedSignAttempt_eq (secretKey : SecretKey) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) :
    (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
        m (Option Signature)) =
      XmssSecurity.Concrete.precomputedSignAttempt wotsEncoding secretKey leafIndex message
        randomness := by
  simp only [Concrete.precomputedSignAttempt, XmssSecurity.Concrete.precomputedSignAttempt,
    encodingHash_eq]
  refine bind_congr fun digest => ?_
  rw [show wotsEncoding.decode digest = Code.decodeDigest digest from rfl]
  cases Code.decodeDigest digest <;> rfl

theorem signFrom_eq (secretKey : Seeded.SecretKey) (leafIndex : LeafIndex) (message : Message) :
    ∀ (attempts trial : Nat),
      (Seeded.signFrom secretKey leafIndex message attempts trial : m (Option Signature)) =
        XmssSecurity.Seeded.signFrom wotsEncoding secretKey leafIndex message attempts trial
  | 0, _ => rfl
  | attempts + 1, trial => by
      simp only [Seeded.signFrom, XmssSecurity.Seeded.signFrom, deriveRandomizer_eq,
        precomputedSignAttempt_eq, signFrom_eq secretKey leafIndex message attempts]
      refine bind_congr fun randomness => bind_congr fun attempt => ?_
      cases attempt <;> rfl

theorem sign_eq [LawfulMonad m] (secretKey : Seeded.SecretKey) (leafIndex : LeafIndex)
    (message : Message) :
    (Seeded.sign secretKey leafIndex message : m (Option Signature)) =
      XmssSecurity.Seeded.sign wotsEncoding secretKey leafIndex message := by
  show (Seeded.signFrom secretKey leafIndex message Code.signingAttemptLimit 0 :
      m (Option Signature)) = _
  exact signFrom_eq (m := m) secretKey leafIndex message _ 0

end Bridge

/-- The statement's construction for the encoding of the code is the copy `xmss` the proofs work
with. -/
theorem xmss_eq : XmssSecurity.xmss wotsEncoding = xmss := by
  unfold XmssSecurity.xmss xmss
  simp only [Bridge.keygenFromSeed_eq, Bridge.sign_eq, Bridge.verify_eq, Bridge.sampleMasterSeed_eq]
  rfl

end XmssSecurity.Generic
