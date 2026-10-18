import XmssSecurity.Proof.TargetSum.FirstLaneChainExpected
import XmssSecurity.Proof.TargetSum.EncodingAcceptanceBudget

/-! Accepted encodings in a first-lane trace are charged to fresh encoding samples from
both direct queries and signing attempts. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.FirstLaneOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

def IsEncodingSample : (World Index).Domain → Prop
  | .encodingQuery _ => True
  | .encodingSignAttempt _ => True
  | _ => False

noncomputable instance : DecidablePred (IsEncodingSample (Index := Index)) := Classical.decPred _

noncomputable def acceptedEncodingAction : ObservedAction Index → Bool
  | .encoding (.query _ output) => decide (TargetSum.ValidDigest (truncateHash output))
  | .encoding (.sign _ output) => decide (TargetSum.ValidDigest (truncateHash output))
  | .chain _ => false

noncomputable def TraceHasAcceptedEncoding (trace : ActionTrace Index) : Prop :=
  trace.any acceptedEncodingAction = true

omit [Fintype Index] [DecidableEq Index] in
theorem traceHasAcceptedEncoding_append (left right : ActionTrace Index) :
    TraceHasAcceptedEncoding (left ++ right) ↔
      TraceHasAcceptedEncoding left ∨ TraceHasAcceptedEncoding right := by
  simp [TraceHasAcceptedEncoding, List.any_append, Bool.or_eq_true]

end XmssSecurity.TargetSum.FirstLaneOracleSimulation
