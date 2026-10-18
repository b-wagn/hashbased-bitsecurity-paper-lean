import XmssSecurity.Proof.TargetSum.Modes.SignerAccounting
import XmssSecurity.Proof.TargetSum.Deterministic.SignerPhaseCost
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

attribute [local irreducible] Generic.sampleMasterSeed

theorem signer_phase_eq_runSigning
    (adversary : Security.StatementAdversary) (publicKey : PublicKey)
    (secretKey : Generic.Seeded.SecretKey) :
    (simulateQ (Security.adversaryImpl secretKey) (adversary.main publicKey)).run =
      Seeded.runSigning (fun request => Generic.Seeded.sign secretKey request.epoch request.message)
        (DeterministicSigning.withRequestLog (adversary.main publicKey)) := by
  rw [Seeded.runSigning_withRequestLog]
  rfl

end XmssSecurity.TargetSum.Modes
