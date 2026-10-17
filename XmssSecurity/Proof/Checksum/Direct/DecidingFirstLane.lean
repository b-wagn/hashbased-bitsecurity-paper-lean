import XmssSecurity.Proof.Checksum.Direct.DecidingRevealed
import XmssSecurity.Proof.Checksum.Direct.DecidingSecondLane
import XmssSecurity.Proof.Checksum.Direct.FirstLane
import XmssSecurity.Proof.Checksum.Direct.Prehit

/-!
# The refined first-lane event

The hidden-value branch includes the winning condition. Without it, invalid transcripts with
repeated signing requests could reveal a value below an earlier signature's digit at no direct
query cost. This restriction preserves the transcript-validity premise of the existing coupling.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Checksum.Deciding

def WinningDecidingFirstLaneBadEventOccurs (execution : CappedEncodingTraceExecution) : Prop :=
  (WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
      ¬ WinningEncodingPrehitOccurs execution) ∨
    (execution.1.won = true ∧ DecidingChainValueRevealed execution.2.1.1 execution.1)

theorem decidingFirstLane_implies_exactFirstLane (adversary : Adversary)
    (execution : CappedEncodingTraceExecution)
    (hmem : execution ∈ support (cappedDetailedGameWithEncodingTrace adversary))
    (hevent : WinningDecidingFirstLaneBadEventOccurs execution) :
    WinningExactFirstLaneBadEventOccurs execution := by
  rcases hevent with hencoding | ⟨hwin, hrevealed⟩
  · exact Or.inl hencoding
  · have hgame : (execution.1, execution.2.1.1) ∈ support
        (detailedGameWithCache Concrete.scheme adversary) := by
      rw [← cappedDetailedGameWithEncodingTrace_cache_projection, support_map]
      exact ⟨execution, hmem, rfl⟩
    exact Or.inr (deciding_revealed_implies_global _ _
      (capped_detailed_execution_consistent adversary _ hgame) hwin hrevealed)

/-- The first-lane estimate from the exact first-lane bound. -/
theorem decidingFirstLane_probability_le_existing (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) :
    Pr[WinningDecidingFirstLaneBadEventOccurs | cappedDetailedGameWithEncodingTrace adversary] ≤
      ((D + Direct.verifierQueryBound + numChains : ℕ) : ℝ≥0∞) /
        ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  apply le_trans (probEvent_mono (decidingFirstLane_implies_exactFirstLane adversary))
  exact CappedChain.hasExactFirstLaneBound_direct adversary D hD
    Direct.scheme_verify_hashQueryBound

theorem forgeAdvantage_le_deciding_lanes (adversary : Adversary) :
    forgeAdvantage Concrete.scheme adversary ≤
      Pr[WinningDecidingFirstLaneBadEventOccurs | cappedDetailedGameWithEncodingTrace adversary] +
        (Pr[WinningEncodingPrehitOccurs | cappedDetailedGameWithEncodingTrace adversary] +
          Pr[fun execution : GameOutcome × QueryCache HashSpec => execution.1.won = true ∧
            ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
            ¬ DecidingChainValueRevealed execution.2 execution.1 |
            detailedGameWithCache Concrete.scheme adversary]) := by
  rw [forgeAdvantage_eq_detailedGameWithCache,
    ← cappedDetailedGameWithEncodingTrace_cache_projection, probEvent_map, probEvent_map]
  calc
    _ ≤ Pr[fun execution : CappedEncodingTraceExecution =>
          WinningDecidingFirstLaneBadEventOccurs execution ∨
            (WinningEncodingPrehitOccurs execution ∨
              (execution.1.won = true ∧ ¬ OutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
                ¬ DecidingChainValueRevealed execution.2.1.1 execution.1)) |
          cappedDetailedGameWithEncodingTrace adversary] := by
      apply probEvent_mono
      intro execution _hmem hwin
      by_cases hprehit : WinningEncodingPrehitOccurs execution
      · exact Or.inr (Or.inl hprehit)
      by_cases hencoding : OutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding
      · exact Or.inl (Or.inl ⟨⟨hwin, hencoding⟩, hprehit⟩)
      by_cases hrevealed : DecidingChainValueRevealed execution.2.1.1 execution.1
      · exact Or.inl (Or.inr ⟨hwin, hrevealed⟩)
      · exact Or.inr (Or.inr ⟨hwin, hencoding, hrevealed⟩)
    _ ≤ Pr[WinningDecidingFirstLaneBadEventOccurs | cappedDetailedGameWithEncodingTrace adversary] +
        (Pr[WinningEncodingPrehitOccurs | cappedDetailedGameWithEncodingTrace adversary] +
          Pr[fun execution : CappedEncodingTraceExecution => execution.1.won = true ∧
            ¬ OutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
            ¬ DecidingChainValueRevealed execution.2.1.1 execution.1 |
            cappedDetailedGameWithEncodingTrace adversary]) := by
      apply (probEvent_or_le _ WinningDecidingFirstLaneBadEventOccurs _).trans
      exact add_le_add le_rfl (probEvent_or_le _ WinningEncodingPrehitOccurs _)

/-- An optional direct bound on the original trace event. The completed proof instead bounds the
adversary with its forged encoding query; see `DecidingFirstLaneBridge`. -/
def HasDecidingFirstLaneBound (adversary : Adversary) (D : ℕ) : Prop :=
  Pr[WinningDecidingFirstLaneBadEventOccurs | cappedDetailedGameWithEncodingTrace adversary] ≤
    ((D + 3 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞)

theorem concrete_forgeAdvantage_le_of_decidingFirstLane (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) (hfirst : HasDecidingFirstLaneBound adversary D) :
    forgeAdvantage Concrete.scheme adversary ≤
      ((D + 3 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        ((signingAttemptLimit : ℝ≥0∞) * D * ((2 ^ randomnessBits : ℕ) : ℝ≥0∞)⁻¹ +
          ((D + 41 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) :=
  (forgeAdvantage_le_deciding_lanes adversary).trans
    (add_le_add hfirst (add_le_add
      (winningEncodingPrehit_probability_le_direct adversary D hD)
      (decidingSecondLane_probability_le_direct adversary D hD)))

end XmssSecurity.Checksum.Deciding
