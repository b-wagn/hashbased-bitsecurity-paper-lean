import XmssSecurity.Proof.TargetSum.ExpectedCountedQueries
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! A state counter incremented on exactly the selected queries has the same expected
increase as the recursive query count. Only supported handler outcomes are required. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum

theorem expectedStateCounter_eq_initial_add_queries
    {Index α State : Type} {spec : OracleSpec Index}
    (impl : QueryImpl spec (StateT State ProbComp)) (selected : spec.Domain → Prop) [DecidablePred selected]
    (counter : State → Nat)
    (hstep : ∀ input state result, result ∈ support ((impl input).run state) →
      counter result.2 = counter state + if selected input then 1 else 0)
    (computation : OracleComp spec α) (state : State) :
    (∑' result, Pr[= result | (simulateQ impl computation).run state] * (counter result.2 : ℝ≥0∞)) =
      (counter state : ℝ≥0∞) + expectedSimulatedQueryCount impl selected computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind input next ih =>
      have hhead : (∑' head, Pr[= head | (impl input).run state] * (counter head.2 : ℝ≥0∞)) =
          (counter state : ℝ≥0∞) + if selected input then 1 else 0 := by
        calc
          _ = ∑' head, Pr[= head | (impl input).run state] *
              ((counter state : ℝ≥0∞) + if selected input then 1 else 0) := by
            apply tsum_congr
            intro head
            by_cases hhead : head ∈ support ((impl input).run state)
            · rw [hstep input state head hhead, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
            · rw [probOutput_eq_zero_of_not_mem_support hhead, zero_mul, zero_mul]
          _ = _ := by
            rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul,
        expectedSimulatedQueryCount_query_bind]
      simp_rw [ih, mul_add]
      rw [ENNReal.tsum_add, hhead, add_assoc]

/-- info: 'XmssSecurity.TargetSum.expectedStateCounter_eq_initial_add_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expectedStateCounter_eq_initial_add_queries

end XmssSecurity.TargetSum
