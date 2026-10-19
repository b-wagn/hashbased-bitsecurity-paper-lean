import XmssSecurity.Proof.Generic.EncodingRejectionProbability

/-! Numerical margins for the attack that changes a uniformly chosen signature chain. -/

open ENNReal
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Generic.Attack

variable [Code]

/-- The exact probability of a distinct random starting value joining an honest path. -/
noncomputable def pathMutationProbability (steps : ℕ) : ℝ≥0∞ :=
  (1 - ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) *
    (1 - (1 - ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) ^ steps)

private theorem real_path_mutation_lower (steps : ℕ) (hsteps : steps ≤ 48) :
    ((steps : ℝ) - 1) / (2 ^ digestBits : ℕ) ≤
      (1 - (1 : ℝ) / (2 ^ digestBits : ℕ)) *
        (1 - (1 - (1 : ℝ) / (2 ^ digestBits : ℕ)) ^ steps) := by
  let p : ℝ := 1 / (2 ^ digestBits : ℕ)
  have hp : 0 ≤ p := by positivity
  have hpone : p ≤ 1 := by norm_num [p, digestBits]
  have hsmall : p ≤ 1 / 2304 := by norm_num [p, digestBits]
  have hn : (steps : ℝ) ≤ 48 := by exact_mod_cast hsteps
  have hnzero : (0 : ℝ) ≤ steps := by positivity
  have hsq : (steps : ℝ) ^ 2 ≤ 2304 := by nlinarith
  have hquad : (steps : ℝ) ^ 2 * p ≤ 1 := by
    calc
      _ ≤ 2304 * p := mul_le_mul_of_nonneg_right hsq hp
      _ ≤ 1 := by linarith
  have hdenom : 0 < 1 + (steps : ℝ) * p := by positivity
  have hpow : (1 - p) ^ steps ≤ 1 / (1 + (steps : ℝ) * p) := by
    have h := Code.rejection_power_le
      (1 / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) (by norm_num [digestBits]) steps
    have hr := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr h
    rw [ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le (by norm_num [digestBits]) ENNReal.one_ne_top] at hr
    simp only [ENNReal.toReal_div] at hr
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hr
    simpa [p, ENNReal.toReal_div, ENNReal.toReal_mul] using hr
  suffices ((steps : ℝ) - 1) * p ≤ (1 - p) * (1 - (1 - p) ^ steps) by
    simpa [p, div_eq_mul_inv] using this
  calc
    _ ≤ ((1 - p) * (steps : ℝ) * p) / (1 + (steps : ℝ) * p) := by
      apply (le_div_iff₀ hdenom).mpr
      nlinarith [mul_nonneg hp (sub_nonneg.mpr hquad)]
    _ = (1 - p) * (1 - 1 / (1 + (steps : ℝ) * p)) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sub_le_sub_left hpow 1) (sub_nonneg.mpr hpone)

/-- Losing one collision opportunity is more than enough to account for the possibility
of an unchanged starting value and all intersections between hit events. -/
theorem pathMutationProbability_lower (steps : ℕ) (hsteps : steps ≤ 48) :
    ((steps - 1 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) ≤
      pathMutationProbability steps := by
  by_cases hzero : steps = 0
  · simp [hzero]
  have hpos : 1 ≤ steps := by omega
  have hp : ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ ≤ 1 := by norm_num [digestBits]
  have hpow : (1 - ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) ^ steps ≤ 1 :=
    pow_le_one₀ zero_le tsub_le_self
  unfold pathMutationProbability
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le hp ENNReal.one_ne_top,
    ENNReal.toReal_sub_of_le hpow ENNReal.one_ne_top,
    ENNReal.toReal_pow, ENNReal.toReal_sub_of_le hp ENNReal.one_ne_top]
  rw [ENNReal.toReal_natCast, Nat.cast_sub hpos]
  simpa [ENNReal.toReal_inv, div_eq_mul_inv] using
    real_path_mutation_lower steps hsteps

end XmssSecurity.Generic.Attack
