import XmssSecurity.Proof.TargetSum.ExpectedCountedQueries
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Forgetting auxiliary state preserves the expected count of every source-query predicate. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum

theorem expectedSimulatedQueryCount_eq_of_query_map_eq
    {Index α Left Right : Type} {spec : OracleSpec Index}
    (left : QueryImpl spec (StateT Left ProbComp)) (right : QueryImpl spec (StateT Right ProbComp))
    (project : Left → Right)
    (hproject : ∀ input state, Prod.map id project <$> (left input).run state =
      (right input).run (project state))
    (selected : spec.Domain → Prop) [DecidablePred selected]
    (computation : OracleComp spec α) (state : Left) :
    expectedSimulatedQueryCount left selected computation state =
      expectedSimulatedQueryCount right selected computation (project state) := by
  simp only [expectedSimulatedQueryCount_eq_counted]
  rw [← map_run_simulateQ_eq_of_query_map_eq left right project hproject, tsum_probOutput_map_mul]
  rfl

/-- info: 'XmssSecurity.TargetSum.expectedSimulatedQueryCount_eq_of_query_map_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expectedSimulatedQueryCount_eq_of_query_map_eq

end XmssSecurity.TargetSum
