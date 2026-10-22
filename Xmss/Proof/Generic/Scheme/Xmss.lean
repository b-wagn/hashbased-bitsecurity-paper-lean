import Xmss.Proof.Generic.Scheme.Construction
import Xmss.Proof.Common.LossyGames

/-!
# XMSS as an epoch-based signature scheme (proof copy)

The proofs work with this copy of the scheme of the statement, for the code `Code`; `Bridge.lean`
proves that it is the statement's scheme for the encoding of the code.

The instance `xmss` of `EpochBasedSignature` in the random-oracle world of the construction:
key generation samples the 256-bit master seed and derives everything else through the hash
oracle; signing and verification are the deterministic algorithms of `Construction.lean`.

The abbreviations at the end fix the SUF-CMA request, forgery, and signing-oracle types of this
instance.
-/

open OracleComp OracleSpec

namespace Xmss.Generic

variable [Code]

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
    liftM (Verify.verify pk leafIndex message signature : OracleComp HashSpec Bool)

/-- A signing request of the instance: a 32-bit leaf index and a 32-byte message. -/
abbrev SignRequest := Unforgeability.SignRequest Message lifetime

/-- A claimed forgery of the instance. -/
abbrev Forgery := Unforgeability.Forgery Message Signature lifetime

/-- The signing oracle of the instance. -/
abbrev SigningSpec := Unforgeability.SigningSpec Message Signature lifetime

namespace SigningTranscript

export Unforgeability.SigningTranscript (Valid Contains)

end SigningTranscript

end Xmss.Generic
