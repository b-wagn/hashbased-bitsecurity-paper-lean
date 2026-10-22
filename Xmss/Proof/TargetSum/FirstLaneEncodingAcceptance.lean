import Xmss.Proof.TargetSum.FirstLaneChainExpected
import Xmss.Proof.TargetSum.EncodingAcceptanceBudget
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Accepted encodings in a first-lane trace are charged to fresh encoding samples from
both direct queries and signing attempts. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open Xmss.Generic

namespace Xmss.TargetSum.FirstLaneOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

def IsEncodingSample : (FirstLaneOracleSimulation.World Index).Domain → Prop
  | .encodingQuery _ => True
  | .encodingSignAttempt _ => True
  | _ => False

noncomputable instance : DecidablePred (IsEncodingSample (Index := Index)) := Classical.decPred _

end Xmss.TargetSum.FirstLaneOracleSimulation
