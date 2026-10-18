import XmssSecurity.Proof.TargetSum.Modes.SignerAccounting
import XmssSecurity.Proof.TargetSum.Deterministic.SignerPhaseCost

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

attribute [local irreducible] sampleMasterSeed

theorem signer_phase_eq_runSigning
    (adversary : Security.StatementAdversary) (publicKey : PublicKey)
    (secretKey : Seeded.SecretKey) :
    (simulateQ (Security.adversaryImpl secretKey) (adversary.main publicKey)).run =
      Seeded.runSigning (fun request => Seeded.sign secretKey request.epoch request.message)
        (DeterministicSigning.withRequestLog (adversary.main publicKey)) := by
  rw [Seeded.runSigning_withRequestLog]
  rfl

end XmssSecurity.TargetSum.Modes
