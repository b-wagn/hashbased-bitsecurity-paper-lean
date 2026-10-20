import XmssSecurity.Proof.Generic.RandomizedStatement

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Generic

variable [Code]

namespace Concrete

/-- `rho`, fresh per attempt. -/
noncomputable def signingRandomness : ProbComp Randomness :=
  $ᵗ Randomness

/-- At most `attempts` attempts, each with fresh randomness, stopping at the first that encodes. -/
noncomputable def precomputedSignBoundedAttempts :
    Nat → SecretKey → LeafIndex → Message →
      OracleComp OracleWorld (Option Signature)
  | 0, _secretKey, _leafIndex, _message => pure none
  | attempts + 1, secretKey, leafIndex, message => do
      let randomness ← liftM signingRandomness
      let result ← liftM
        (precomputedSignAttempt secretKey leafIndex message randomness :
          OracleComp HashSpec (Option Signature))
      match result with
      | some signature => pure (some signature)
      | none => precomputedSignBoundedAttempts attempts secretKey leafIndex message

/-- `Sig(sk, idx, m)`, at most `A_max` attempts. The once-per-leaf-index discipline is the game's, in `SigningTranscript.Valid`. -/
noncomputable def precomputedCappedSign (secretKey : SecretKey)
    (leafIndex : LeafIndex) (message : Message) :
    OracleComp OracleWorld (Option Signature) :=
  precomputedSignBoundedAttempts Code.signingAttemptLimit secretKey leafIndex message

attribute [irreducible] signingRandomness precomputedCappedSign

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

noncomputable local instance : SampleableType (LeafIndex → ChainIndex → Digest) :=
  SampleableType.ofFintype (LeafIndex → ChainIndex → Digest)

noncomputable def samplePublicParameter : ProbComp PublicParameter :=
  $ᵗ PublicParameter

noncomputable def sampleSecret : ProbComp (LeafIndex → ChainIndex → Digest) :=
  $ᵗ (LeafIndex → ChainIndex → Digest)

/-- `Gen`: sample the parameter and secrets, compute the root through the oracle, and materialize
every chain value and node in the secret key's vectors using the recorded answers. -/
noncomputable def precomputedKeygen :
    OracleComp OracleWorld (PublicKey × SecretKey) := do
  let parameter ← liftM samplePublicParameter
  let secret ← liftM sampleSecret
  let result ← liftM
    (treeNode parameter secret treeHeight rootNode :
      OracleComp HashSpec Digest).withQueryLog
  let cache := hashCacheOfLog result.2
  return (⟨result.1, parameter⟩, precomputedSecretKey parameter secret cache)

attribute [irreducible] samplePublicParameter sampleSecret precomputedKeygen

end Concrete

/-- The concrete XMSS scheme: the precomputed key generation, the capped retry signer, and the ordinary verifier defined above. -/
noncomputable def Concrete.scheme : Scheme SecretKey where
  keygen := Concrete.precomputedKeygen
  sign := Concrete.precomputedCappedSign
  verify := fun publicKey leafIndex message signature =>
    liftM (Concrete.verify publicKey leafIndex message signature : OracleComp HashSpec Bool)

end XmssSecurity.Generic
