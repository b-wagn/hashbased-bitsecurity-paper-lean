import XmssSecurity.Proof.Generic.Direct.DecidingSecondLaneExpected
import XmssSecurity.Proof.Checksum.Direct.DecidingSecurity
import XmssSecurity.Proof.Checksum.Code
import XmssSecurity.Proof.Checksum.EncodingProbability

/-! The encoding prehit and structural collision losses share the direct-query budget. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open XmssSecurity.Generic

namespace XmssSecurity.Checksum.Direct

theorem encodingPrehitRate_le_digest_inverse :
    Direct.encodingPrehitRate ≤ ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ := by
  unfold Direct.encodingPrehitRate
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, signingAttemptLimit, digestBits, digestBits]

theorem prehit_add_decidingSecondLane_le (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D)
    (hcached : ∀ keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅),
      ∀ prefixResult ∈ support
        ((simulateQ romImpl (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2),
        prefixResult.2 (Concrete.CacheView.encodingInput keyResult.1.2.parameter
          prefixResult.1.1.epoch
          (prefixResult.1.1.message, prefixResult.1.1.signature.randomness)) ≠ none) :
    Pr[WinningEncodingPrehitOccurs | cappedDetailedGameWithEncodingTrace adversary] +
      Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
          ¬ Deciding.DecidingChainValueRevealed execution.2 execution.1 |
        detailedGameWithCache Concrete.scheme adversary] ≤
      ((D + 40 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  refine (add_le_add (Direct.winningEncodingPrehit_probability_le_expected_direct_encoding adversary)
    (Deciding.decidingSecondLane_probability_le_expected adversary hcached)).trans ?_
  calc
    _ ≤ Direct.expectedDirectEncodingQueries adversary / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (Direct.expectedDirectStructuralQueries adversary / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
          (40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) := by
      apply add_le_add _ le_rfl
      rw [div_eq_mul_inv, mul_comm]
      exact mul_le_mul' le_rfl encodingPrehitRate_le_digest_inverse
    _ = (Direct.expectedDirectEncodingQueries adversary + Direct.expectedDirectStructuralQueries adversary) /
          ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
      rw [ENNReal.add_div, add_assoc]
    _ ≤ (D : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
      gcongr
      exact Direct.expectedDirectEncodingQueries_add_structural_le adversary D hD
    _ = _ := by rw [Nat.cast_add, ENNReal.add_div]; rfl

noncomputable def sharedDecidingLoss (D : ℕ) : ℝ≥0∞ :=
  ((2 * D + 43 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
    D / ((2 ^ 256 : ℕ) : ℝ≥0∞)

/-- A linear direct-query loss with no additional encoding-query coefficient. -/
theorem seeded_forgeAdvantage_le_sharedDecidingLoss (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) :
    forgeAdvantage Seeded.scheme adversary ≤ sharedDecidingLoss D := by
  let memo := Seeded.memoAdversary adversary
  let queried := Direct.withForgedEncodingQuery memo
  have hmemo := Seeded.memoAdversary_isDirectQueryBound adversary D hD
  have hqueried := Direct.withForgedEncodingQuery_isDirectQueryBound memo D hmemo
  have hsecond := prehit_add_decidingSecondLane_le queried (D + 1) hqueried (by
    intro keyResult hkeygen prefixResult hprefix
    have hparameter := Deciding.keygen_publicKey_parameter_eq keyResult hkeygen
    rw [← hparameter]
    exact Direct.adversaryPhase_withForgedEncodingQuery_cached memo keyResult.1.1 keyResult.1.2
      keyResult.2 prefixResult hprefix)
  apply (Seeded.forgeAdvantage_deterministic_le_reference_direct adversary D hD).trans
  rw [← Direct.forgeAdvantage_withForgedEncodingQuery memo]
  have hlanes := (Deciding.forgeAdvantage_le_deciding_lanes queried).trans
    (add_le_add
      (Deciding.decidingFirstLane_withForgedEncodingQuery_probability_le memo D hmemo) hsecond)
  refine (add_le_add hlanes le_rfl).trans_eq ?_
  unfold sharedDecidingLoss
  rw [← ENNReal.add_div, ← Nat.cast_add]
  have hsum : (D + 2) + (D + 1 + 40) = 2 * D + 43 := by omega
  rw [hsum]

end XmssSecurity.Checksum.Direct
