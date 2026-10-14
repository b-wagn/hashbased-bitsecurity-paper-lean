import XmssSecurity.Proof.ExpectedQueryCount

/-! A state event whose one-step probability is small is charged to the expected number of
queries that can create it. The interpretation and all subsequent queries may be adaptive. -/

open OracleSpec OracleComp ENNReal

namespace XmssSecurity

theorem probEvent_state_le_initial_add_expectedQueryCount
    {ι : Type} {spec : OracleSpec ι} {α state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (event : state → Prop) [DecidablePred event] (rate : ℝ≥0∞)
    (hstep : ∀ input initialState, ¬event initialState →
      Pr[fun result => event result.2 | (implementation input).run initialState] ≤
        if predicate input then rate else 0)
    (computation : OracleComp spec α) (initialState : state) :
    Pr[fun result => event result.2 | (simulateQ implementation computation).run initialState] ≤
      (if event initialState then 1 else 0) +
        rate * expectedSimulatedQueryCount implementation predicate computation initialState := by
  induction computation using OracleComp.inductionOn generalizing initialState with
  | pure value => simp [simulateQ_pure, probEvent_pure]
  | query_bind input next ih =>
      by_cases hinitial : event initialState
      · simp only [if_pos hinitial]
        exact le_add_right probEvent_le_one
      · simp only [if_neg hinitial, zero_add]
        rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query,
          probEvent_bind_eq_tsum, expectedSimulatedQueryCount_query_bind]
        calc
          _ ≤ ∑' result, Pr[= result | (implementation input).run initialState] *
              ((if event result.2 then 1 else 0) + rate *
                expectedSimulatedQueryCount implementation predicate (next result.1) result.2) := by
            apply ENNReal.tsum_le_tsum
            intro result
            exact mul_le_mul' le_rfl (ih result.1 result.2)
          _ = Pr[fun result => event result.2 | (implementation input).run initialState] +
              rate * ∑' result, Pr[= result | (implementation input).run initialState] *
                expectedSimulatedQueryCount implementation predicate (next result.1) result.2 := by
            simp_rw [mul_add, mul_left_comm (Pr[= _ | _]) rate]
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, probEvent_eq_tsum_ite]
            congr 1
            apply tsum_congr
            intro result
            split_ifs <;> simp
          _ ≤ (if predicate input then rate else 0) +
              rate * ∑' result, Pr[= result | (implementation input).run initialState] *
                expectedSimulatedQueryCount implementation predicate (next result.1) result.2 :=
            add_le_add (hstep input initialState hinitial) le_rfl
          _ = _ := by split_ifs <;> simp [mul_add]

end XmssSecurity
