import XmssSecurity.Statement.Scheme.Construction
import XmssSecurity.Statement.EpochBasedSignature

/-!
# XMSS as an epoch-based signature scheme

The instance `xmss E` of `EpochBasedSignature` in the random-oracle world of the construction, for
a WOTS encoding `E`: key generation samples the 256-bit master seed and derives everything else
through the hash oracle; signing and verification are the deterministic algorithms of
`Construction.lean`. The two schemes of this development are `xmssTargetSum` (`TargetSum.lean`)
and `xmssChecksum` (`Checksum.lean`).
-/

open OracleComp OracleSpec

namespace XmssSecurity

/-- `SIG = (Gen, Sig, Ver)` of the specification for the encoding `E`: sample the master seed and
derive the keys, sign with at most `A_max` randomizer trials, and verify. -/
noncomputable def xmss (E : WotsEncoding) :
    EpochBasedSignature OracleWorld PublicKey (Seeded.SecretKey E.numChains) Message
      (Signature E.numChains) lifetime where
  keygen := do
    let seed ← liftM sampleMasterSeed
    liftM (Seeded.keygenFromSeed E.numChains seed)
  sign := fun sk leafIndex message =>
    liftM (Seeded.sign E sk leafIndex message : OracleComp HashSpec (Option (Signature E.numChains)))
  verify := fun pk leafIndex message signature =>
    liftM (Concrete.verify E pk leafIndex message signature : OracleComp HashSpec Bool)

end XmssSecurity
