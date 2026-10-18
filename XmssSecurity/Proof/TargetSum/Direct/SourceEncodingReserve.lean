import XmssSecurity.Proof.TargetSum.Direct.SourceLossBudget
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! A larger reserve in the source budget pays for acceptance transfer in the cached case. -/

open OracleComp OracleSpec ENNReal

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.Direct

noncomputable def sourceEncodingReserve (adversary : Adversary) : ℝ≥0∞ :=
  (3 / 8 : ℝ≥0∞) * (Direct.expectedDirectEncodingQueries adversary + expectedSourceSignerHashes adversary)

theorem source_encoding_rate_add_reserve_le :
    prehitRate + TargetSum.acceptanceProbability *
        ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) +
        (3 / 8 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  unfold prehitRate TargetSum.acceptanceProbability
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div, digestBits]

theorem source_signer_rate_add_reserve_le :
    TargetSum.acceptanceProbability * ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) +
      (3 / 8 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) ≤
        (2 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  unfold TargetSum.acceptanceProbability
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div, digestBits]

theorem source_seed_rate_le :
    ((2 ^ 256 : Nat) : ℝ≥0∞)⁻¹ ≤ ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_inv, digestBits]

theorem sourceSecondaryLoss_add_encodingReserve_le (adversary : Adversary) :
    sourceSecondaryLoss adversary + sourceEncodingReserve adversary / ((2 ^ digestBits : Nat) : ℝ≥0∞) ≤
      (Direct.expectedDirectEncodingQueries adversary + Direct.expectedDirectStructuralQueries adversary +
        expectedDirectSeedQueries adversary + 2 * expectedSourceSignerHashes adversary) /
          ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  unfold sourceSecondaryLoss sourceEncodingReserve
  calc
    _ = Direct.expectedDirectEncodingQueries adversary *
          (prehitRate + TargetSum.acceptanceProbability *
            ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) +
            (3 / 8 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) +
        Direct.expectedDirectStructuralQueries adversary / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        expectedDirectSeedQueries adversary / ((2 ^ 256 : Nat) : ℝ≥0∞) +
        expectedSourceSignerHashes adversary *
          (TargetSum.acceptanceProbability * ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) +
            (3 / 8 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ Direct.expectedDirectEncodingQueries adversary * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
        Direct.expectedDirectStructuralQueries adversary / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        expectedDirectSeedQueries adversary * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
        expectedSourceSignerHashes adversary * ((2 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) := by
      exact add_le_add (add_le_add
        (add_le_add (mul_le_mul' le_rfl source_encoding_rate_add_reserve_le) le_rfl)
        (mul_le_mul' le_rfl source_seed_rate_le))
        (mul_le_mul' le_rfl source_signer_rate_add_reserve_le)
    _ = _ := by simp only [div_eq_mul_inv]; ring

/-- info: 'XmssSecurity.TargetSum.Direct.sourceSecondaryLoss_add_encodingReserve_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourceSecondaryLoss_add_encodingReserve_le

end XmssSecurity.TargetSum.Direct
