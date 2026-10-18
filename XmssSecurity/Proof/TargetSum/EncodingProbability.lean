import XmssSecurity.Proof.TargetSum.EncodingCardinalityCertificate
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.Generic.EncodingRejectionProbability

/-! Exact acceptance probability of the target-sum encoding. -/

open OracleComp ENNReal
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.TargetSum

theorem validDigests_card_exact :
    Generic.Code.validDigests.card = 11539185377238682781344003244544752 := by
  rw [validDigests_card_eq_wordCount]
  exact wordCount_eight_fortyTwo_195

noncomputable def acceptanceProbability : ℝ≥0∞ :=
  11539185377238682781344003244544752 / ((2 ^ digestBits : ℕ) : ℝ≥0∞)

theorem probEvent_validDigest_uniform :
    Pr[Generic.Code.ValidDigest | $ᵗ Digest] = acceptanceProbability := by
  rw [probEvent_uniformSample]
  change (Generic.Code.validDigests.card : ℝ≥0∞) / Fintype.card Digest = _
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

namespace XmssSecurity.TargetSum

@[simp] theorem code_acceptanceProbability :
    Generic.Code.acceptanceProbability = TargetSum.acceptanceProbability := by
  unfold Generic.Code.acceptanceProbability TargetSum.acceptanceProbability
  rw [TargetSum.validDigests_card_exact]
  rfl

scoped instance signerBound : Generic.Code.SignerBound where
  capped_rejection_bound_lt := by
    rw [code_acceptanceProbability]
    show (1 - TargetSum.acceptanceProbability) ^ signingAttemptLimit +
      (signingAttemptLimit : ℝ≥0∞) * signingAttemptLimit *
        ((2 ^ randomnessBits : ℕ) : ℝ≥0∞)⁻¹ < 1 / 32
    have hpow : (1 - TargetSum.acceptanceProbability) ^ signingAttemptLimit ≤
        1 / (1 + (signingAttemptLimit : ℝ≥0∞) * (1 / ((2 ^ 15 : ℕ) : ℝ≥0∞))) :=
      (pow_le_pow_left' (tsub_le_tsub_left TargetSum.acceptanceProbability_lower.le 1)
        signingAttemptLimit).trans (Generic.Code.rejection_power_le _ (by norm_num) _)
    apply lt_of_le_of_lt (add_le_add hpow le_rfl)
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [signingAttemptLimit, randomnessBits, ENNReal.toReal_div, ENNReal.toReal_mul]

end XmssSecurity.TargetSum
