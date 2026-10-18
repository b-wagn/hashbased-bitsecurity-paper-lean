import XmssSecurity.Proof.TargetSum.ExpectedQueryProjection
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Expected query costs can be split between a selected outer query and an auxiliary counter. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum

theorem expectedSimulatedQueryCount_simulate_le_accounting
    {Outer Inner α SourceState TargetState : Type}
    {outer : OracleSpec Outer} {inner : OracleSpec Inner}
    (source : QueryImpl outer (OracleComp inner))
    (impl : QueryImpl inner (StateT TargetState ProbComp))
    (tracked : QueryImpl outer (StateT SourceState ProbComp))
    (project : SourceState → TargetState)
    (hproject : ∀ input state, Prod.map id project <$> (tracked input).run state =
      (simulateQ impl (source input)).run (project state))
    (innerSelected : inner.Domain → Prop) [DecidablePred innerSelected]
    (outerSelected : outer.Domain → Prop) [DecidablePred outerSelected]
    (counter : SourceState → ℝ≥0∞)
    (hstep : ∀ input state,
      expectedSimulatedQueryCount impl innerSelected (source input) (project state) + counter state ≤
        (if outerSelected input then 1 else 0) +
          ∑' result, Pr[= result | (tracked input).run state] * counter result.2)
    (computation : OracleComp outer α) (state : SourceState) :
    expectedSimulatedQueryCount impl innerSelected (simulateQ source computation) (project state) +
        counter state ≤ expectedSimulatedQueryCount tracked outerSelected computation state +
      ∑' result, Pr[= result | (simulateQ tracked computation).run state] * counter result.2 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind input next ih =>
      rw [expectedSimulatedQueryCount_query_bind]
      simp only [simulateQ_bind, simulateQ_spec_query, expectedSimulatedQueryCount_bind,
        StateT.run_bind, tsum_probOutput_bind_mul]
      rw [← hproject input state, tsum_probOutput_map_mul]
      calc
        _ = (expectedSimulatedQueryCount impl innerSelected (source input) (project state) + counter state) +
            ∑' result, Pr[= result | (tracked input).run state] *
              expectedSimulatedQueryCount impl innerSelected (simulateQ source (next result.1))
                (project result.2) := by ac_rfl
        _ ≤ ((if outerSelected input then 1 else 0) +
            ∑' result, Pr[= result | (tracked input).run state] * counter result.2) +
            ∑' result, Pr[= result | (tracked input).run state] *
              expectedSimulatedQueryCount impl innerSelected (simulateQ source (next result.1))
                (project result.2) := add_le_add (hstep input state) le_rfl
        _ = (if outerSelected input then 1 else 0) +
            ∑' result, Pr[= result | (tracked input).run state] *
              (expectedSimulatedQueryCount impl innerSelected (simulateQ source (next result.1))
                (project result.2) + counter result.2) := by
          simp_rw [mul_add]
          rw [ENNReal.tsum_add]
          ac_rfl
        _ ≤ (if outerSelected input then 1 else 0) +
            ∑' result, Pr[= result | (tracked input).run state] *
              (expectedSimulatedQueryCount tracked outerSelected (next result.1) result.2 +
                ∑' final, Pr[= final | (simulateQ tracked (next result.1)).run result.2] *
                  counter final.2) := by
          apply add_le_add le_rfl
          exact ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (ih result.1 result.2)
        _ = _ := by
          simp_rw [mul_add]
          rw [ENNReal.tsum_add, add_assoc]

/-- info: 'XmssSecurity.TargetSum.expectedSimulatedQueryCount_simulate_le_accounting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expectedSimulatedQueryCount_simulate_le_accounting

end XmssSecurity.TargetSum
