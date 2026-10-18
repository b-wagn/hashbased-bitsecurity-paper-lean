import XmssSecurity.Proof.TargetSum.EncodingCardinalityCertificate

/-! Exact acceptance probability of the target-sum encoding. -/

open OracleComp ENNReal
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.TargetSum

theorem validDigests_card_exact :
    validDigests.card = 11539185377238682781344003244544752 := by
  rw [validDigests_card_eq_wordCount]
  exact wordCount_eight_fortyTwo_195

noncomputable def acceptanceProbability : ℝ≥0∞ :=
  11539185377238682781344003244544752 / ((2 ^ digestBits : ℕ) : ℝ≥0∞)

theorem probEvent_validDigest_uniform :
    Pr[ValidDigest | $ᵗ Digest] = acceptanceProbability := by
  rw [probEvent_uniformSample]
  change (validDigests.card : ℝ≥0∞) / Fintype.card Digest = _
  rw [validDigests_card_exact]
  simp [acceptanceProbability]

theorem acceptanceProbability_pos : 0 < acceptanceProbability := by
  simp [acceptanceProbability]

theorem acceptanceProbability_ne_top : acceptanceProbability ≠ ⊤ := by
  unfold acceptanceProbability
  finiteness

theorem acceptanceProbability_lower :
    (1 : ℝ≥0∞) / ((2 ^ 15 : ℕ) : ℝ≥0∞) < acceptanceProbability := by
  apply (ENNReal.toReal_lt_toReal (by finiteness) acceptanceProbability_ne_top).mp
  norm_num [acceptanceProbability, ENNReal.toReal_div, digestBits]

theorem acceptanceProbability_upper :
    acceptanceProbability < (1 : ℝ≥0∞) / ((2 ^ 14 : ℕ) : ℝ≥0∞) := by
  apply (ENNReal.toReal_lt_toReal acceptanceProbability_ne_top (by finiteness)).mp
  norm_num [acceptanceProbability, ENNReal.toReal_div, digestBits]

/-- info: 'XmssSecurity.TargetSum.TargetSum.validDigests_card_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validDigests_card_exact

/-- info: 'XmssSecurity.TargetSum.TargetSum.acceptanceProbability_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms acceptanceProbability_lower

/-- info: 'XmssSecurity.TargetSum.TargetSum.acceptanceProbability_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms acceptanceProbability_upper

end XmssSecurity.TargetSum.TargetSum
