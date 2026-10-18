import XmssSecurity.Proof.TargetSum.Direct.DecidingRevealed
import XmssSecurity.Proof.TargetSum.Direct.DecidingSecondLane
import XmssSecurity.Proof.TargetSum.Direct.FirstLane
import XmssSecurity.Proof.TargetSum.Direct.Prehit

/-!
# The refined first-lane event

The hidden-value branch includes the winning condition. Without it, invalid transcripts with
repeated signing requests could reveal a value below an earlier signature's digit at no direct
query cost. This restriction preserves the transcript-validity premise of the existing coupling.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum.Deciding

def WinningDecidingFirstLaneBadEventOccurs (execution : CappedEncodingTraceExecution) : Prop :=
  (WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
      ¬ WinningEncodingPrehitOccurs execution) ∨
    (execution.1.won = true ∧ DecidingChainValueRevealed execution.2.1.1 execution.1)

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

end XmssSecurity.TargetSum.Deciding
