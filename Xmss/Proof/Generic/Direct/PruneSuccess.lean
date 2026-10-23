import Xmss.Proof.Generic.Direct.Prune

/-! Pruning preserves the contribution of executions that finish within the direct-query budget.
This also applies when only successful executions, rather than all executions, satisfy the bound. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace Xmss.Generic.Direct

variable [Code]

theorem expected_pruneDirect_logged_ge {α : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec)
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (budget : ℕ)
    (cache : QueryCache HashSpec)
    (payoff : (α × QueryLog SigningSpec) × QueryCache HashSpec → ℝ≥0∞) :
    (∑' result, Pr[= result | (simulateQ romImpl (simulateQ impl
        (QueryCounting.counted IsDirectHashQuery computation)).run).run cache] *
      (if result.1.1.2 ≤ budget then payoff ((result.1.1.1, result.1.2), result.2) else 0)) ≤
    ∑' result, Pr[= result | (simulateQ romImpl
      (simulateQ impl (pruneDirect budget computation)).run).run cache] * payoff result := by
  induction computation using OracleComp.inductionOn generalizing budget cache payoff with
  | pure value =>
      simp only [QueryCounting.counted_pure, pruneDirect_pure, simulateQ_pure,
        WriterT.run_pure, StateT.run_pure, tsum_probOutput_pure_mul, Nat.zero_le, if_true, le_refl]
  | query_bind input next ih =>
      rcases input with (uniformOrHash | request)
      · rcases uniformOrHash with uniformInput | hashInput
        · rw [run_logged_counted_query_bind, pruneDirect_uniform_bind, run_logged_query_bind]
          simp_rw [tsum_probOutput_bind_mul, tsum_probOutput_map_mul]
          simp only [not_isDirectHashQuery_uniform, if_false, zero_add]
          apply ENNReal.tsum_le_tsum
          intro middle
          apply mul_le_mul' le_rfl
          exact ih middle.1.1 budget middle.2
            (fun result => payoff ((result.1.1, middle.1.2 ++ result.1.2), result.2))
        · by_cases hzero : budget = 0
          · subst budget
            rw [run_logged_counted_query_bind]
            simp_rw [tsum_probOutput_bind_mul, tsum_probOutput_map_mul]
            have hpositive (count : ℕ) : ¬1 + count ≤ 0 := by omega
            simp only [isDirectHashQuery_hash, if_true, hpositive, if_false, mul_zero, tsum_zero]
            exact zero_le
          · rw [run_logged_counted_query_bind, pruneDirect_hash_bind, if_neg hzero,
              run_logged_query_bind]
            simp_rw [tsum_probOutput_bind_mul, tsum_probOutput_map_mul]
            simp only [isDirectHashQuery_hash, if_true]
            have hshift (count : ℕ) : 1 + count ≤ budget ↔ count ≤ budget - 1 := by omega
            simp_rw [hshift]
            apply ENNReal.tsum_le_tsum
            intro middle
            apply mul_le_mul' le_rfl
            exact ih middle.1.1 (budget - 1) middle.2
              (fun result => payoff ((result.1.1, middle.1.2 ++ result.1.2), result.2))
      · rw [run_logged_counted_query_bind, pruneDirect_sign_bind, run_logged_query_bind]
        simp_rw [tsum_probOutput_bind_mul, tsum_probOutput_map_mul]
        simp only [not_isDirectHashQuery_sign, if_false, zero_add]
        apply ENNReal.tsum_le_tsum
        intro middle
        apply mul_le_mul' le_rfl
        exact ih middle.1.1 budget middle.2
          (fun result => payoff ((result.1.1, middle.1.2 ++ result.1.2), result.2))

theorem run_logged_counted_forget {α : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec)
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) :
    (fun result => ((result.1.1.1, result.1.2), result.2)) <$>
        (simulateQ romImpl (simulateQ impl
          (QueryCounting.counted IsDirectHashQuery computation)).run).run cache =
      (simulateQ romImpl (simulateQ impl computation).run).run cache := by
  have h := congrArg (fun program =>
    (simulateQ romImpl (simulateQ impl program).run).run cache)
    (QueryCounting.counted_forget IsDirectHashQuery computation)
  simp only [simulateQ_map, WriterT.run_map', StateT.run_map] at h
  rw [← h]
  apply congrArg (fun project => project <$>
    (simulateQ romImpl (simulateQ impl
      (QueryCounting.counted IsDirectHashQuery computation)).run).run cache)
  funext ⟨⟨⟨value, count⟩, log⟩, finalCache⟩
  rfl

/-- A nonnegative payoff that vanishes on over-budget runs cannot decrease after pruning. -/
theorem expected_logged_le_prune_of_zero_over_budget {α : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec)
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (budget : ℕ)
    (cache : QueryCache HashSpec)
    (payoff : (α × QueryLog SigningSpec) × QueryCache HashSpec → ℝ≥0∞)
    (hzero : ∀ result ∈ support ((simulateQ romImpl (simulateQ impl
        (QueryCounting.counted IsDirectHashQuery computation)).run).run cache),
      budget < result.1.1.2 → payoff ((result.1.1.1, result.1.2), result.2) = 0) :
    (∑' result, Pr[= result | (simulateQ romImpl
        (simulateQ impl computation).run).run cache] * payoff result) ≤
      ∑' result, Pr[= result | (simulateQ romImpl
        (simulateQ impl (pruneDirect budget computation)).run).run cache] * payoff result := by
  calc
    _ = ∑' result, Pr[= result | (simulateQ romImpl (simulateQ impl
          (QueryCounting.counted IsDirectHashQuery computation)).run).run cache] *
        (if result.1.1.2 ≤ budget then payoff ((result.1.1.1, result.1.2), result.2) else 0) := by
      rw [← run_logged_counted_forget impl computation cache, tsum_probOutput_map_mul]
      apply tsum_congr
      intro result
      by_cases hsmall : result.1.1.2 ≤ budget
      · rw [if_pos hsmall]
      · rw [if_neg hsmall]
        by_cases hresult : result ∈ support ((simulateQ romImpl (simulateQ impl
            (QueryCounting.counted IsDirectHashQuery computation)).run).run cache)
        · rw [hzero result hresult (by omega)]
        · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ ≤ _ := expected_pruneDirect_logged_ge impl computation budget cache payoff

end Xmss.Generic.Direct
