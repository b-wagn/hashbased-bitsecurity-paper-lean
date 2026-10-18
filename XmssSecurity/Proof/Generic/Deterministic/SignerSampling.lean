import XmssSecurity.Proof.Generic.Deterministic.TrialSampling

open OracleComp OracleSpec

namespace XmssSecurity.Generic.Seeded

variable [Code]

set_option backward.isDefEq.respectTransparency false

theorem evalDist_tableSign {State : Type} (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : XmssSecurity.Generic.SecretKey) (leafIndex : LeafIndex) (message : Message) (state : State) :
    𝒟[do
      let tape ← sampleTrialTape
      (simulateQ (worldHandler hash) (liftM (tableSign (fun position => tape position.2)
        secretKey leafIndex message : OracleComp HashSpec (Option Signature)) : OracleComp OracleWorld _)).run state] =
      𝒟[(simulateQ (worldHandler hash) (Concrete.precomputedCappedSign secretKey leafIndex message)).run state] := by
  unfold tableSign Concrete.precomputedCappedSign
  exact evalDist_tableSignFrom hash secretKey leafIndex message Code.signingAttemptLimit 0
    (by simpa using Code.signingAttemptLimit_le) state

end XmssSecurity.Generic.Seeded
