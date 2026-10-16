import XmssSecurity.Proof.Direct.SourceLossBudget

/-! A larger reserve in the source budget pays for acceptance transfer in the cached case. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Direct

noncomputable def sourceEncodingReserve (adversary : Adversary) : ℝ≥0∞ :=
  (3 / 4 : ℝ≥0∞) * (expectedDirectEncodingQueries adversary + expectedSourceSignerHashes adversary)

theorem source_encoding_rate_add_reserve_le :
    encodingPrehitRate + Checksum.acceptanceProbability *
        ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) +
        (3 / 4 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  unfold encodingPrehitRate Checksum.acceptanceProbability
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div,
    signingAttemptLimit, randomnessBits, digestBits]

theorem source_signer_rate_add_reserve_le :
    Checksum.acceptanceProbability * ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) +
      (3 / 4 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) ≤
        (2 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  unfold Checksum.acceptanceProbability
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div, digestBits]

theorem source_seed_rate_le :
    ((2 ^ 256 : Nat) : ℝ≥0∞)⁻¹ ≤ ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_inv, digestBits]

theorem sourceSecondaryLoss_add_encodingReserve_le (adversary : Adversary) :
    sourceSecondaryLoss adversary + sourceEncodingReserve adversary / ((2 ^ digestBits : Nat) : ℝ≥0∞) ≤
      (expectedDirectEncodingQueries adversary + expectedDirectStructuralQueries adversary +
        expectedDirectSeedQueries adversary + 2 * expectedSourceSignerHashes adversary) /
          ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  unfold sourceSecondaryLoss sourceEncodingReserve
  calc
    _ = expectedDirectEncodingQueries adversary *
          (encodingPrehitRate + Checksum.acceptanceProbability *
            ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) +
            (3 / 4 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) +
        expectedDirectStructuralQueries adversary / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        expectedDirectSeedQueries adversary / ((2 ^ 256 : Nat) : ℝ≥0∞) +
        expectedSourceSignerHashes adversary *
          (Checksum.acceptanceProbability * ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) +
            (3 / 4 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ expectedDirectEncodingQueries adversary * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
        expectedDirectStructuralQueries adversary / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        expectedDirectSeedQueries adversary * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
        expectedSourceSignerHashes adversary * ((2 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) := by
      exact add_le_add (add_le_add
        (add_le_add (mul_le_mul' le_rfl source_encoding_rate_add_reserve_le) le_rfl)
        (mul_le_mul' le_rfl source_seed_rate_le))
        (mul_le_mul' le_rfl source_signer_rate_add_reserve_le)
    _ = _ := by simp only [div_eq_mul_inv]; ring

theorem acceptance_credit_add_half_le_reserve (credit : ℝ≥0∞) (hcredit : 1 ≤ credit) :
    Checksum.acceptanceProbability * credit + 1 / 2 ≤ (3 / 4 : ℝ≥0∞) * credit := by
  have hprob : Checksum.acceptanceProbability ≤ (1 / 4 : ℝ≥0∞) := by
    unfold Checksum.acceptanceProbability
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div, digestBits]
  have hsum : (1 / 4 : ℝ≥0∞) + 1 / 2 = 3 / 4 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add]
    norm_num [ENNReal.toReal_div]
  calc
    _ ≤ (1 / 4 : ℝ≥0∞) * credit + (1 / 2 : ℝ≥0∞) * credit :=
      add_le_add (mul_le_mul' hprob le_rfl) (by simpa using mul_le_mul' (le_refl (1 / 2 : ℝ≥0∞)) hcredit)
    _ = _ := by rw [← add_mul, hsum]

theorem query_ratio_le_half (q : Nat) (hsmall : q < 2 ^ 127) :
    (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) ≤ 1 / 2 := by
  calc
    _ ≤ ((2 ^ 127 : Nat) : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
      ENNReal.div_le_div (by exact_mod_cast hsmall.le) le_rfl
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_div, digestBits]

/-- info: 'XmssSecurity.Direct.sourceSecondaryLoss_add_encodingReserve_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourceSecondaryLoss_add_encodingReserve_le

end XmssSecurity.Direct
