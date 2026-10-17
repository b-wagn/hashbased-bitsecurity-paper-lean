import XmssSecurity.Proof.Common.ExpectedQueryCount
import XmssSecurity.Proof.TargetSum.ConsistentQueryBound
import XmssSecurity.Proof.TargetSum.ExactKeygenQueryCount

/-! Relate the recursive expected-query count to the experiment's actual charged executions. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum

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

theorem expectedSimulatedQueryCount_le_of_counted_support
    {ι : Type} {spec : OracleSpec ι} {α state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (computation : OracleComp spec α) (initialState : state) (q : ℕ)
    (hbound : ∀ result ∈ support
      ((simulateQ implementation (QueryCounting.counted predicate computation)).run initialState),
      result.1.2 ≤ q) :
    expectedSimulatedQueryCount implementation predicate computation initialState ≤ q := by
  rw [expectedSimulatedQueryCount_eq_counted]
  calc
    _ ≤ ∑' result, Pr[= result |
        (simulateQ implementation (QueryCounting.counted predicate computation)).run initialState] *
          (q : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support
          ((simulateQ implementation (QueryCounting.counted predicate computation)).run initialState)
      · exact mul_le_mul' le_rfl (by exact_mod_cast hbound result hresult)
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact (mul_le_mul' tsum_probOutput_le_one le_rfl).trans_eq (one_mul _)

theorem expectedHashQueries_le_of_hashQueryBound
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (q : ℕ)
    (hbound : HashQueryBound computation cache q) :
    expectedSimulatedQueryCount romImpl IsHashQuery computation cache ≤ q := by
  apply (expectedSimulatedQueryCount_mono romImpl IsHashQuery
    (fun input : OracleWorld.Domain => input matches .inr _) (fun _ h => h)
    computation cache).trans
  apply expectedSimulatedQueryCount_le_of_counted_support
  exact (hashQueryBound_iff_run computation cache q).mp hbound

/-- info: 'XmssSecurity.TargetSum.expectedHashQueries_le_of_hashQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expectedHashQueries_le_of_hashQueryBound

end XmssSecurity.TargetSum
