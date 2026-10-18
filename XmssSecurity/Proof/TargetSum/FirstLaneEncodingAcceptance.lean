import XmssSecurity.Proof.TargetSum.FirstLaneChainExpected
import XmssSecurity.Proof.TargetSum.EncodingAcceptanceBudget
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Accepted encodings in a first-lane trace are charged to fresh encoding samples from
both direct queries and signing attempts. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.FirstLaneOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

def IsEncodingSample : (Generic.FirstLaneOracleSimulation.World Index).Domain → Prop
  | .encodingQuery _ => True
  | .encodingSignAttempt _ => True
  | _ => False

noncomputable instance : DecidablePred (IsEncodingSample (Index := Index)) := Classical.decPred _

noncomputable def acceptedEncodingAction : Generic.FirstLaneOracleSimulation.ObservedAction Index → Bool
  | .encoding (.query _ output) => decide (Generic.Code.ValidDigest (Generic.truncateHash output))
  | .encoding (.sign _ output) => decide (Generic.Code.ValidDigest (Generic.truncateHash output))
  | .chain _ => false

noncomputable def TraceHasAcceptedEncoding (trace : Generic.FirstLaneOracleSimulation.ActionTrace Index) : Prop :=
  trace.any acceptedEncodingAction = true

omit [Fintype Index] [DecidableEq Index] in
theorem traceHasAcceptedEncoding_append (left right : Generic.FirstLaneOracleSimulation.ActionTrace Index) :
    TraceHasAcceptedEncoding (left ++ right) ↔
      TraceHasAcceptedEncoding left ∨ TraceHasAcceptedEncoding right := by
  simp [TraceHasAcceptedEncoding, List.any_append, Bool.or_eq_true]

end XmssSecurity.TargetSum.FirstLaneOracleSimulation
