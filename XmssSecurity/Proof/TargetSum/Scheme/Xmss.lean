import XmssSecurity.Proof.TargetSum.Scheme.Construction
import XmssSecurity.Proof.Common.LossyGames

/-!
# XMSS as an epoch-based signature scheme (proof copy for the target-sum encoding)

The proofs about `xmssTargetSum` work with this copy of the scheme of the statement, specialized to
the target-sum encoding (`numChains` chains): it is the construction as it read before the statement
made it generic in the encoding. `Bridge.lean` proves that the copy computes the statement's
algorithms, so that `xmssTargetSum = xmss`.

The instance `xmss` of `EpochBasedSignature` in the random-oracle world of the construction:
key generation samples the 256-bit master seed and derives everything else through the hash
oracle; signing and verification are the deterministic algorithms of `Construction.lean`.

The abbreviations at the end fix the SUF-CMA request, forgery, and signing-oracle types of this
instance.
-/

open OracleComp OracleSpec

namespace XmssSecurity.TargetSum

/-- `SIG = (Gen, Sig, Ver)`: sample the master seed and derive the keys,
sign with at most `A_max` randomizer trials, and verify. -/
noncomputable def xmss :
    EpochBasedSignature OracleWorld PublicKey Seeded.SecretKey Message Signature lifetime where
  keygen := do
    let seed ← liftM sampleMasterSeed
    liftM (Seeded.keygenFromSeed seed)
  sign := fun sk leafIndex message =>
    liftM (Seeded.sign sk leafIndex message : OracleComp HashSpec (Option Signature))
  verify := fun pk leafIndex message signature =>
    liftM (Concrete.verify pk leafIndex message signature : OracleComp HashSpec Bool)

/-- A signing request of the instance: a 32-bit leaf index and a 32-byte message. -/
abbrev SignRequest := SUFCMA.SignRequest Message lifetime

/-- A claimed forgery of the instance. -/
abbrev Forgery := SUFCMA.Forgery Message Signature lifetime

/-- The signing oracle of the instance. -/
abbrev SigningSpec := SUFCMA.SigningSpec Message Signature lifetime

namespace SigningTranscript

export SUFCMA.SigningTranscript (Valid Contains)

end SigningTranscript

end XmssSecurity.TargetSum
