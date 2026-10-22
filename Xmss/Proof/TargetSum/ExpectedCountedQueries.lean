import Xmss.Proof.Common.ExpectedQueryCount
import Xmss.Proof.Generic.ConsistentQueryBound
import Xmss.Proof.Generic.ExactKeygenQueryCount
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability
/-! Relate the recursive expected-query count to the experiment's actual charged executions. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace Xmss.TargetSum

variable [Generic.Code]

omit [Generic.Code] in
theorem expectedSimulatedQueryCount_eq_counted
    {ι : Type} {spec : OracleSpec ι} {α state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (computation : OracleComp spec α) (initialState : state) :
    expectedSimulatedQueryCount implementation predicate computation initialState =
      ∑' result, Pr[= result |
        (simulateQ implementation (QueryCounting.counted predicate computation)).run initialState] *
          (result.1.2 : ℝ≥0∞) := by
  induction computation using OracleComp.inductionOn generalizing initialState with
  | pure value => simp [QueryCounting.counted_pure, simulateQ_pure]
  | query_bind input next ih =>
      rw [expectedSimulatedQueryCount_query_bind, QueryCounting.counted_query_bind,
        simulateQ_bind, StateT.run_bind, simulateQ_spec_query, tsum_probOutput_bind_mul]
      simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
        tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
      have htail : ∀ middle : spec.Range input × state,
          (∑' result, Pr[= result |
            (simulateQ implementation (QueryCounting.counted predicate (next middle.1))).run middle.2] *
              (((if predicate input then 1 else 0) + result.1.2 : ℕ) : ℝ≥0∞)) =
            (if predicate input then 1 else 0) +
              expectedSimulatedQueryCount implementation predicate (next middle.1) middle.2 := by
        intro middle
        rw [ih middle.1 middle.2]
        push_cast
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
          tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul]
      simp_rw [htail, mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
        tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul]

end Xmss.TargetSum
