import XmssSecurity.Proof.TargetSum.Direct.SourceSignerQueries
import XmssSecurity.Proof.TargetSum.Direct.ReferenceSeedQueries

/-! The source-side losses share one budget; nonstructural costs leave at least half
their budget available for the first lane. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Direct

noncomputable def sourceSecondaryLoss (adversary : Adversary) : ℝ≥0∞ :=
  encodingPrehitRate * expectedDirectEncodingQueries adversary +
    (expectedDirectStructuralQueries adversary / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
      (expectedDirectEncodingQueries adversary + expectedSourceSignerHashes adversary) *
        (TargetSum.acceptanceProbability * ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)))) +
    expectedDirectSeedQueries adversary / ((2 ^ 256 : Nat) : ℝ≥0∞)

theorem source_encoding_loss_rate_le_half :
    encodingPrehitRate + TargetSum.acceptanceProbability *
        ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) ≤
      (1 / 2 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  unfold encodingPrehitRate TargetSum.acceptanceProbability
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add]
  norm_num [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div,
    signingAttemptLimit, randomnessBits, digestBits]

theorem source_signer_loss_rate_le :
    TargetSum.acceptanceProbability * ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  unfold TargetSum.acceptanceProbability
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div, digestBits]

theorem source_seed_loss_rate_le_half :
    ((2 ^ 256 : Nat) : ℝ≥0∞)⁻¹ ≤ (1 / 2 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_inv, ENNReal.toReal_div, digestBits]

theorem sourceSecondaryLoss_le_half_nonstructural (adversary : Adversary) :
    sourceSecondaryLoss adversary ≤
      (expectedDirectEncodingQueries adversary / 2 + expectedDirectStructuralQueries adversary +
        expectedDirectSeedQueries adversary / 2 + expectedSourceSignerHashes adversary) /
          ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  unfold sourceSecondaryLoss
  calc
    _ = expectedDirectEncodingQueries adversary *
          (encodingPrehitRate + TargetSum.acceptanceProbability *
            ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞))) +
        expectedDirectStructuralQueries adversary / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        expectedDirectSeedQueries adversary / ((2 ^ 256 : Nat) : ℝ≥0∞) +
        expectedSourceSignerHashes adversary *
          (TargetSum.acceptanceProbability * ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞))) := by ring
    _ ≤ expectedDirectEncodingQueries adversary * ((1 / 2 : ℝ≥0∞) /
          ((2 ^ digestBits : Nat) : ℝ≥0∞)) +
        expectedDirectStructuralQueries adversary / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        expectedDirectSeedQueries adversary * ((1 / 2 : ℝ≥0∞) /
          ((2 ^ digestBits : Nat) : ℝ≥0∞)) +
        expectedSourceSignerHashes adversary * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      apply add_le_add
      · apply add_le_add
        · exact add_le_add (mul_le_mul' le_rfl source_encoding_loss_rate_le_half) le_rfl
        · exact mul_le_mul' le_rfl source_seed_loss_rate_le_half
      · exact mul_le_mul' le_rfl source_signer_loss_rate_le
    _ = _ := by simp only [div_eq_mul_inv]; ring

theorem prehit_add_secondLane_add_seed_le_sourceSecondaryLoss (adversary : Adversary)
    (hcached : ∀ keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅),
      ∀ result ∈ support ((simulateQ romImpl
        (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2),
        result.2 (Concrete.CacheView.encodingInput keyResult.1.2.parameter result.1.1.epoch
          (result.1.1.message, result.1.1.signature.randomness)) ≠ none) :
    Pr[WinningEncodingPrehitOccurs | cappedDetailedGameWithEncodingTrace adversary] +
      Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
          ¬ Deciding.DecidingChainValueRevealed execution.2 execution.1 |
        detailedGameWithCache Concrete.scheme adversary] +
      expectedDirectSeedQueries adversary / ((2 ^ 256 : Nat) : ℝ≥0∞) ≤ sourceSecondaryLoss adversary := by
  apply add_le_add _ le_rfl
  apply add_le_add (winningEncodingPrehit_probability_le_expected_direct_encoding adversary)
  exact (Deciding.decidingSecondLane_probability_le_expectedEncoding adversary hcached).trans
    (add_le_add le_rfl (mul_le_mul' (expectedPrefixEncodingQueries_le adversary) le_rfl))

theorem sourceSecondaryLoss_add_reserve_le (adversary : Adversary) :
    sourceSecondaryLoss adversary +
      (expectedDirectEncodingQueries adversary / 2 + expectedDirectSeedQueries adversary / 2 +
        expectedSourceSignerHashes adversary) / ((2 ^ digestBits : Nat) : ℝ≥0∞) ≤
      (expectedDirectEncodingQueries adversary + expectedDirectStructuralQueries adversary +
        expectedDirectSeedQueries adversary + 2 * expectedSourceSignerHashes adversary) /
          ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  apply (add_le_add (sourceSecondaryLoss_le_half_nonstructural adversary) le_rfl).trans_eq
  rw [← ENNReal.add_div]
  congr 1
  calc
    _ = (expectedDirectEncodingQueries adversary / 2 + expectedDirectEncodingQueries adversary / 2) +
        expectedDirectStructuralQueries adversary +
        (expectedDirectSeedQueries adversary / 2 + expectedDirectSeedQueries adversary / 2) +
        (expectedSourceSignerHashes adversary + expectedSourceSignerHashes adversary) := by ac_rfl
    _ = _ := by rw [ENNReal.add_halves, ENNReal.add_halves, ← two_mul]

/-- info: 'XmssSecurity.TargetSum.Direct.sourceSecondaryLoss_le_half_nonstructural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourceSecondaryLoss_le_half_nonstructural

/-- info: 'XmssSecurity.TargetSum.Direct.prehit_add_secondLane_add_seed_le_sourceSecondaryLoss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prehit_add_secondLane_add_seed_le_sourceSecondaryLoss

end XmssSecurity.TargetSum.Direct
