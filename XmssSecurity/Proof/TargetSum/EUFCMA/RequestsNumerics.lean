import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsLoss

/-! The shared expected-query budget absorbs every loss. Use the ordinary
prefix estimate for E ≥ 1/128 and the one-query terminal saving below it. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum.EUFCMA.Requests
open XmssSecurity.EUFCMA

private theorem counts_finite (q : ℕ) (E S Z R : ℝ≥0∞) (hbudget : E + S + Z + R ≤ q) :
    E ≠ ⊤ ∧ S ≠ ⊤ ∧ Z ≠ ⊤ ∧ R ≠ ⊤ := by
  have hfinite : E + S + Z + R ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hbudget
  simpa only [ENNReal.add_ne_top, and_assoc] using hfinite

private theorem acceptance_real_upper : TargetSum.acceptanceProbability.toReal ≤ (1 : ℝ) / 2 ^ 14 := by
  have h := (ENNReal.toReal_le_toReal TargetSum.acceptanceProbability_ne_top
    (by finiteness)).mpr TargetSum.acceptanceProbability_upper.le
  norm_num [ENNReal.toReal_div] at h ⊢
  exact h

theorem expectedLoss_le_127 (q : ℕ) (E S Z R : ℝ≥0∞)
    (hbudget : E + S + Z + R ≤ q) (hlarge : (1 : ℝ≥0∞) / 128 ≤ E) :
    expectedLoss q E S Z R ≤ (q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞) := by
  obtain ⟨hE, hS, hZ, hR⟩ := counts_finite q E S Z R hbudget
  have hpfinite := TargetSum.acceptanceProbability_ne_top
  have hbudgetReal := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr hbudget
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_natCast] at hbudgetReal
  have hlargeReal := (ENNReal.toReal_le_toReal (by finiteness) hE).mpr hlarge
  norm_num [ENNReal.toReal_div] at hlargeReal
  have hpE := mul_le_mul_of_nonneg_right acceptance_real_upper
    (show (0 : ℝ) ≤ E.toReal + 1 by positivity)
  unfold expectedLoss Direct.prehitRate
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  norm_num [digestBits]
  nlinarith [(ENNReal.toReal_nonneg : (0 : ℝ) ≤ E.toReal), (ENNReal.toReal_nonneg : (0 : ℝ) ≤ Z.toReal)]

theorem terminalLoss_le_127 (q : ℕ) (hq : 1 ≤ q) (E S Z R : ℝ≥0∞)
    (hbudget : E + S + Z + R ≤ q) (hsmall : E ≤ (1 : ℝ≥0∞) / 128) :
    terminalLoss q E S Z R ≤ (q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞) := by
  obtain ⟨hE, hS, hZ, hR⟩ := counts_finite q E S Z R hbudget
  have hpfinite := TargetSum.acceptanceProbability_ne_top
  have hbudgetReal := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr hbudget
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_natCast] at hbudgetReal
  have hsmallReal := (ENNReal.toReal_le_toReal hE (by finiteness)).mpr hsmall
  norm_num [ENNReal.toReal_div] at hsmallReal
  have hp := acceptance_real_upper
  have hpE := mul_le_mul_of_nonneg_right hp (show (0 : ℝ) ≤ E.toReal + 1 by positivity)
  unfold terminalLoss Direct.prehitRate
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  rw [Nat.cast_sub hq]
  norm_num [digestBits]
  nlinarith [(ENNReal.toReal_nonneg : (0 : ℝ) ≤ E.toReal), (ENNReal.toReal_nonneg : (0 : ℝ) ≤ Z.toReal)]

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Requests.expectedLoss_le_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expectedLoss_le_127

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Requests.terminalLoss_le_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms terminalLoss_le_127

end XmssSecurity.TargetSum.EUFCMA.Requests
