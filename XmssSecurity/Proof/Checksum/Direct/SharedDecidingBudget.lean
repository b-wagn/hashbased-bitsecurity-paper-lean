import XmssSecurity.Proof.Generic.Direct.DecidingSecondLaneExpected
import XmssSecurity.Proof.Checksum.Direct.DecidingSecurity
import XmssSecurity.Proof.Checksum.Code
import XmssSecurity.Proof.Checksum.EncodingProbability

/-! The encoding prehit and structural collision losses share the direct-query budget. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Checksum.Direct

theorem encodingPrehitRate_le_digest_inverse :
    Generic.Direct.encodingPrehitRate ≤ ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ := by
  unfold Generic.Direct.encodingPrehitRate
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, signingAttemptLimit, randomnessBits, digestBits]

theorem prehit_add_decidingSecondLane_le (adversary : Generic.Adversary) (D : ℕ)
    (hD : Generic.Direct.IsDirectQueryBound adversary D)
    (hcached : ∀ keyResult ∈ support ((simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅),
      ∀ prefixResult ∈ support
        ((simulateQ Generic.romImpl (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2),
        prefixResult.2 (Generic.Concrete.CacheView.encodingInput keyResult.1.2.parameter
          prefixResult.1.1.epoch
          (prefixResult.1.1.message, prefixResult.1.1.signature.randomness)) ≠ none) :
    Pr[Generic.WinningEncodingPrehitOccurs | Generic.cappedDetailedGameWithEncodingTrace adversary] +
      Pr[fun execution : Generic.GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ ¬ Generic.OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
          ¬ Generic.Deciding.DecidingChainValueRevealed execution.2 execution.1 |
        Generic.detailedGameWithCache Generic.Concrete.scheme adversary] ≤
      ((D + 40 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  refine (add_le_add (Generic.Direct.winningEncodingPrehit_probability_le_expected_direct_encoding adversary)
    (Generic.Deciding.decidingSecondLane_probability_le_expected adversary hcached)).trans ?_
  calc
    _ ≤ Generic.Direct.expectedDirectEncodingQueries adversary / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (Generic.Direct.expectedDirectStructuralQueries adversary / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
          (40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) := by
      apply add_le_add _ le_rfl
      rw [div_eq_mul_inv, mul_comm]
      exact mul_le_mul' le_rfl encodingPrehitRate_le_digest_inverse
    _ = (Generic.Direct.expectedDirectEncodingQueries adversary + Generic.Direct.expectedDirectStructuralQueries adversary) /
          ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
      rw [ENNReal.add_div, add_assoc]
    _ ≤ (D : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
      gcongr
      exact Generic.Direct.expectedDirectEncodingQueries_add_structural_le adversary D hD
    _ = _ := by rw [Nat.cast_add, ENNReal.add_div]; rfl

noncomputable def sharedDecidingLoss (D : ℕ) : ℝ≥0∞ :=
  ((2 * D + 43 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
    D / ((2 ^ 256 : ℕ) : ℝ≥0∞)

/-- A linear direct-query loss with no additional encoding-query coefficient. -/
theorem seeded_forgeAdvantage_le_sharedDecidingLoss (adversary : Generic.Adversary) (D : ℕ)
    (hD : Generic.Direct.IsDirectQueryBound adversary D) :
    Generic.forgeAdvantage Generic.Seeded.scheme adversary ≤ sharedDecidingLoss D := by
  let memo := Generic.Seeded.memoAdversary adversary
  let queried := Generic.Direct.withForgedEncodingQuery memo
  have hmemo := Generic.Seeded.memoAdversary_isDirectQueryBound adversary D hD
  have hqueried := Generic.Direct.withForgedEncodingQuery_isDirectQueryBound memo D hmemo
  have hsecond := prehit_add_decidingSecondLane_le queried (D + 1) hqueried (by
    intro keyResult hkeygen prefixResult hprefix
    have hparameter := Generic.Deciding.keygen_publicKey_parameter_eq keyResult hkeygen
    rw [← hparameter]
    exact Generic.Direct.adversaryPhase_withForgedEncodingQuery_cached memo keyResult.1.1 keyResult.1.2
      keyResult.2 prefixResult hprefix)
  apply (Generic.Seeded.forgeAdvantage_deterministic_le_reference_direct adversary D hD).trans
  rw [← Generic.Direct.forgeAdvantage_withForgedEncodingQuery memo]
  have hlanes := (Generic.Deciding.forgeAdvantage_le_deciding_lanes queried).trans
    (add_le_add
      (Generic.Deciding.decidingFirstLane_withForgedEncodingQuery_probability_le memo D hmemo) hsecond)
  refine (add_le_add hlanes le_rfl).trans_eq ?_
  unfold sharedDecidingLoss
  rw [← ENNReal.add_div, ← Nat.cast_add]
  have hsum : (D + 2) + (D + 1 + 40) = 2 * D + 43 := by omega
  rw [hsum]

end XmssSecurity.Checksum.Direct
