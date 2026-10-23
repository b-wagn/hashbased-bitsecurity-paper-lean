import Xmss.Proof.TargetSum.Modes.SignerAccounting
import Xmss.Proof.TargetSum.Deterministic.SignerPhaseCost
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Modes
open Xmss.Modes

attribute [local irreducible] Generic.sampleMasterSeed

theorem signer_phase_eq_runSigning
    (adversary : AdversaryBridge.StatementAdversary) (publicKey : PublicKey)
    (secretKey : Generic.Seeded.SecretKey) :
    (simulateQ (AdversaryBridge.adversaryImpl secretKey) (adversary.main publicKey)).run =
      Seeded.runSigning (fun request => Generic.Seeded.sign secretKey request.epoch request.message)
        (DeterministicSigning.withRequestLog (adversary.main publicKey)) := by
  rw [Seeded.runSigning_withRequestLog]
  rfl

end Xmss.TargetSum.Modes
