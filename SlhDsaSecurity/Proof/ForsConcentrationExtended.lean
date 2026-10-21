import SlhDsaSecurity.Proof.ForsConcentrationOccupancy

/-!
# Additional uniform choices for the shared-oracle exceptional branch

This extends the independent occupancy experiment to five halves of the number
of instances. It does not assert a coupling to the adaptive ROM game.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal Classical

namespace SlhDsaSecurity.ForsConcentration

set_option exponentiation.threshold 1024 in
/-- A rate-3B Poisson count reaches 5B/2 with probability at least one half. -/
theorem poisson_count_tail_extended_half :
    (1 : ENNReal) / 2 ≤ poissonMeasure (3 * ((2 ^ 63 : Nat) : ℝ≥0)) {n | 5 * 2 ^ 62 ≤ n} := by
  let rate : Nat := 3 * 2 ^ 63
  have hr : (rate : ℝ≥0) = 3 * ((2 ^ 63 : Nat) : ℝ≥0) := by norm_num [rate]
  rw [← hr]
  have hsub : {n : Nat | n < 5 * 2 ^ 62} ⊆
      {n | (2 ^ 62 : ℝ) ^ 2 ≤ ((n : ℝ) - rate) ^ 2} := by
    intro n hn
    have hn' : (n : ℝ) ≤ 23058430092136939520 := by
      exact_mod_cast Nat.le_of_lt hn
    norm_num [rate]
    nlinarith only [hn', sq_nonneg ((n : ℝ) - 23058430092136939520)]
  have hi : Integrable (fun n : Nat => ((n : ℝ) - rate) ^ 2)
      (poissonMeasure (rate : ℝ≥0)) := by
    simpa using poisson_integrable_centered_power (rate : ℝ≥0) 1 2 (rate : ℝ)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := poissonMeasure (rate : ℝ≥0)) (f := fun n : Nat => ((n : ℝ) - rate) ^ 2)
    (Filter.Eventually.of_forall fun n => sq_nonneg ((n : ℝ) - rate)) hi ((2 ^ 62 : ℝ) ^ 2)
  rw [poisson_integral_square_sub] at hm
  have hsmall : (poissonMeasure (rate : ℝ≥0)).real {n | n < 5 * 2 ^ 62} ≤ (1 : ℝ) / 2 := by
    have hmono := measureReal_mono (μ := poissonMeasure (rate : ℝ≥0)) hsub
    have hscaled := mul_le_mul_of_nonneg_left hmono (sq_nonneg (2 ^ 62 : ℝ))
    have hscaled' := hscaled.trans hm
    norm_num [rate] at hscaled'
    linarith
  have hcompl := measureReal_add_measureReal_compl
    (μ := poissonMeasure (rate : ℝ≥0)) (s := {n : Nat | n < 5 * 2 ^ 62}) MeasurableSet.of_discrete
  simp only [probReal_univ] at hcompl
  have hrest : (poissonMeasure (rate : ℝ≥0)).real {n | n < 5 * 2 ^ 62}ᶜ =
      1 - (poissonMeasure (rate : ℝ≥0)).real {n | n < 5 * 2 ^ 62} := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hcompl
  have htail : (1 : ℝ) / 2 ≤
      (poissonMeasure (rate : ℝ≥0)).real {n | 5 * 2 ^ 62 ≤ n} := by
    have hle : (1 : ℝ) / 2 ≤
        1 - (poissonMeasure (rate : ℝ≥0)).real {n | n < 5 * 2 ^ 62} := by
      linarith only [hsmall]
    rw [← hrest] at hle
    simpa only [Set.compl_setOf, Nat.not_lt] using hle
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simpa only [measureReal_def, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat] using htail

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 10000 in
/-- Load concentration for exactly 5*2^62 independent uniform instance selections.
No assumption of independence between occupancy bins is made. -/
theorem uniform_load_tail_extended :
    uniformLoads (2 ^ 63) (5 * 2 ^ 62) {loads | (2 ^ 103 : ℝ) ≤ loadPotential loads} ≤
      (1 : ENNReal) / 2 ^ 141 := by
  have hup : ∀ {a b : Fin (2 ^ 63) → Nat}, a ≤ b →
      (2 ^ 103 : ℝ) ≤ loadPotential a → (2 ^ 103 : ℝ) ≤ loadPotential b := by
    intro a b hab ha
    refine ha.trans (Finset.sum_le_sum (fun i _ => ?_))
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (hab i)) 14
  have hcouple := uniformLoads_mul_poisson_tail_le (2 ^ 63) (5 * 2 ^ 62)
    {loads | (2 ^ 103 : ℝ) ≤ loadPotential loads} hup
  have hhalf := mul_le_mul_right poisson_count_tail_extended_half
    (uniformLoads (2 ^ 63) (5 * 2 ^ 62) {loads | (2 ^ 103 : ℝ) ≤ loadPotential loads})
  have hbound := hhalf.trans (hcouple.trans poisson_load_tail)
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  have hreal := ENNReal.toReal_mono (by finiteness) hbound
  norm_num only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_one] at hreal ⊢
  linarith

/-- The natural-number load condition used by the FORS coverage bound, for any
fixed number of independent uniform requests within the extended tape size. -/
theorem uniform_load_tail_extended_of_le (requests : Nat) (hrequests : requests ≤ 5 * 2 ^ 62) :
    uniformLoads (2 ^ 63) requests {loads | 2 ^ 103 < ∑ i, loads i ^ 14} ≤
      (1 : ENNReal) / 2 ^ 141 := by
  have hup : ∀ {a b : Fin (2 ^ 63) → Nat}, a ≤ b →
      (2 ^ 103 : ℝ) ≤ loadPotential a → (2 ^ 103 : ℝ) ≤ loadPotential b := by
    intro a b hab ha
    refine ha.trans (Finset.sum_le_sum (fun i _ => ?_))
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (hab i)) 14
  have hsub : {loads : Fin (2 ^ 63) → Nat | 2 ^ 103 < ∑ i, loads i ^ 14} ⊆
      {loads | (2 ^ 103 : ℝ) ≤ loadPotential loads} := by
    intro loads hloads
    change (2 ^ 103 : ℝ) ≤ ∑ i, (loads i : ℝ) ^ 14
    exact_mod_cast Nat.le_of_lt hloads
  exact (measure_mono hsub).trans
    ((uniformLoads_monotone (2 ^ 63) _ hup hrequests).trans uniform_load_tail_extended)

end SlhDsaSecurity.ForsConcentration
