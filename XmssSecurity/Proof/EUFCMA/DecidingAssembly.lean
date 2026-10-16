import XmssSecurity.Proof.EUFCMA.SecondLane
import XmssSecurity.Proof.Direct.DecidingFirstLaneBridge

/-! Standard forgeries satisfy the existing deciding classification while retaining
standard freshness in the second lane. Encoding and structural queries share the
same direct-query budget. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.EUFCMA

open Deciding

theorem forgeAdvantage_withForgedEncodingQuery (adversary : XmssSecurity.Adversary) :
    forgeAdvantage Concrete.scheme (Direct.withForgedEncodingQuery adversary) =
      forgeAdvantage Concrete.scheme adversary := by
  rw [forgeAdvantage_eq_detailedGameWithCache, forgeAdvantage_eq_detailedGameWithCache,
    Direct.detailedGameWithCache_withForgedEncodingQuery]

theorem forgeAdvantage_le_deciding_lanes (adversary : XmssSecurity.Adversary) :
    forgeAdvantage Concrete.scheme adversary ≤
      Pr[WinningDecidingFirstLaneBadEventOccurs | cappedDetailedGameWithEncodingTrace adversary] +
        (Pr[WinningEncodingPrehitOccurs | cappedDetailedGameWithEncodingTrace adversary] +
          Pr[fun execution : GameOutcome × QueryCache HashSpec => standardWon execution.1 = true ∧
            ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
            ¬ DecidingChainValueRevealed execution.2 execution.1 |
            detailedGameWithCache Concrete.scheme adversary]) := by
  rw [forgeAdvantage_eq_detailedGameWithCache,
    ← cappedDetailedGameWithEncodingTrace_cache_projection, probEvent_map, probEvent_map]
  calc
    _ ≤ Pr[fun execution : CappedEncodingTraceExecution =>
          WinningDecidingFirstLaneBadEventOccurs execution ∨
            (WinningEncodingPrehitOccurs execution ∨
              (standardWon execution.1 = true ∧ ¬ OutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
                ¬ DecidingChainValueRevealed execution.2.1.1 execution.1)) |
          cappedDetailedGameWithEncodingTrace adversary] := by
      apply probEvent_mono
      intro execution _hmem hwin
      have hstrong := strongWon_of_standardWon execution.1 hwin
      by_cases hprehit : WinningEncodingPrehitOccurs execution
      · exact Or.inr (Or.inl hprehit)
      by_cases hencoding : OutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding
      · exact Or.inl (Or.inl ⟨⟨hstrong, hencoding⟩, hprehit⟩)
      by_cases hrevealed : DecidingChainValueRevealed execution.2.1.1 execution.1
      · exact Or.inl (Or.inr ⟨hstrong, hrevealed⟩)
      · exact Or.inr (Or.inr ⟨hwin, hencoding, hrevealed⟩)
    _ ≤ _ := by
      apply (probEvent_or_le _ WinningDecidingFirstLaneBadEventOccurs _).trans
      exact add_le_add le_rfl (probEvent_or_le _ WinningEncodingPrehitOccurs _)

theorem acceptance_forty_rate_le_digest_rate :
    Checksum.acceptanceProbability * ((40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) ≤
      (1 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  apply (mul_le_mul' Checksum.acceptanceProbability_upper.le le_rfl).trans
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_div, digestBits]

theorem decidingSecondLane_probability_le_direct (adversary : XmssSecurity.Adversary)
    (D : ℕ) (hD : Direct.IsDirectQueryBound adversary D)
    (hcached : ∀ keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅),
      ∀ result ∈ support ((simulateQ romImpl
        (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2),
        result.2 (Concrete.CacheView.encodingInput keyResult.1.2.parameter result.1.1.epoch
          (result.1.1.message, result.1.1.signature.randomness)) ≠ none) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec => standardWon execution.1 = true ∧
        ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
        ¬ DecidingChainValueRevealed execution.2 execution.1 |
      detailedGameWithCache Concrete.scheme adversary] ≤
      (D : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  apply (decidingSecondLane_probability_le_expectedEncoding adversary hcached).trans
  calc
    _ ≤ Direct.expectedDirectStructuralQueries adversary / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        Direct.expectedDirectEncodingQueries adversary *
          ((1 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) :=
      add_le_add le_rfl (mul_le_mul' le_rfl acceptance_forty_rate_le_digest_rate)
    _ = (Direct.expectedDirectEncodingQueries adversary + Direct.expectedDirectStructuralQueries adversary) /
        ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
      simp only [div_eq_mul_inv, one_mul, add_mul, add_comm]
    _ ≤ _ := ENNReal.div_le_div (Direct.expectedDirectEncodingQueries_add_structural_le adversary D hD) le_rfl

/-- info: 'XmssSecurity.EUFCMA.decidingSecondLane_probability_le_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decidingSecondLane_probability_le_direct

end XmssSecurity.EUFCMA
