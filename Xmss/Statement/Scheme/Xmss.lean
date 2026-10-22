import Xmss.Statement.Scheme.Construction
import Xmss.Statement.EpochBasedSignature

/-!
# XMSS as an epoch-based signature scheme

`xmss E` packages the construction for encoding `E`. Key generation samples a 256-bit seed;
signing and verification are deterministic given the hash oracle.
-/

open OracleComp OracleSpec

namespace Xmss

/-- The epoch-based signature scheme for encoding `E`. -/
noncomputable def xmss (E : WotsEncoding) :
    EpochBasedSignature OracleWorld PublicKey (Seeded.SecretKey E.numChains) Message
      (Signature E.numChains) lifetime where
  keygen := do
    let seed ← liftM sampleMasterSeed
    liftM (Seeded.keygenFromSeed E.numChains seed)
  sign := fun sk leafIndex message =>
    liftM (Seeded.sign E sk leafIndex message : OracleComp HashSpec (Option (Signature E.numChains)))
  verify := fun pk leafIndex message signature =>
    liftM (Verify.verify E pk leafIndex message signature : OracleComp HashSpec Bool)

end Xmss
