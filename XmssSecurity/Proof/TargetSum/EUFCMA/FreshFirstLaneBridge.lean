import XmssSecurity.Proof.TargetSum.EUFCMA.FreshFirstLane
import XmssSecurity.Proof.TargetSum.EUFCMA.DecidingAssembly

/-! Retain standard freshness in the first lane and transfer the full winning
event to the fresh, accepted adversary prefix. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Concrete CappedChain Deciding

def WinningFreshFirstLane (result : CappedEncodingTraceExecution) : Prop :=
  standardWon result.1 = true ∧ WinningDecidingFirstLaneBadEventOccurs result

def SourceWinningFreshFirstLane (result : SourceGlobalExactTracedProgramResult) : Prop :=
  WinningFreshFirstLane (cappedBothEncodingProjection (sourceGlobalExactProgramResult result))

theorem freshFirstLane_probability_eq_source (adversary : XmssSecurity.TargetSum.Adversary) :
    Pr[WinningFreshFirstLane | cappedDetailedGameWithEncodingTrace adversary] =
      Pr[SourceWinningFreshFirstLane | sourceGlobalExactTracedProgram adversary] := by
  calc
    _ = Pr[WinningFreshFirstLane ∘ cappedBothEncodingProjection |
        cappedDetailedGameWithKeygenCacheAndBothTraces adversary] := by
      rw [← probEvent_map]
      exact probEvent_congr' (fun _ _ => Iff.rfl) (congrArg evalDist
        (cappedDetailedGameWithKeygenCacheAndBothTraces_encodingProjection_eq adversary)).symm
    _ = Pr[WinningFreshFirstLane ∘ cappedBothEncodingProjection |
        sourceGlobalExactProgramResult <$> sourceGlobalExactTracedProgram adversary] :=
      probEvent_eq_of_evalDist_eq _ (evalDist_sourceGlobalExact_eq_cappedBothTraces adversary).symm
    _ = _ := by rw [probEvent_map]; rfl

theorem sourceWinningFreshFirstLane_implies_prefix (adversary : XmssSecurity.TargetSum.Adversary)
    (key : ProgrammedGlobalChainKeygenView) (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (prefixResult : Forgery × SourceExactTracedState)
    (hprefix : prefixResult ∈ support (sourcePrefixExecution adversary key))
    (hcached : prefixResult.2.1.1.1 (CacheView.encodingInput key.secretKey.parameter
      prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none)
    (execution : (Forgery × Bool) × SourceExactTracedState)
    (hfinish : execution ∈ support (sourcePrefixFinish key prefixResult))
    (hevent : SourceWinningFreshFirstLane (key, execution)) : FreshPrefixFirstLaneEvent key prefixResult := by
  have haccepted := sourceFirstLaneEvent_implies_acceptedPrefixEvent adversary key hkey prefixResult hprefix
    hcached execution hfinish hevent.2
  refine ⟨haccepted.1, ?_, Option.isSome_iff_exists.mp haccepted.2⟩
  have hlogs := cappedBothTracedMappedAdversaryImpl_logs_eq key.publicKey
    (materializePrecomputation key.cache key.secretKey) (adversary.main key.publicKey)
    ((((key.cache, []), []), [])) prefixResult rfl hprefix
  rw [sourcePrefixFinish, support_map] at hfinish
  obtain ⟨verified, _, rfl⟩ := hfinish
  have hwin := (standardWon_eq_true_iff _).mp hevent.1
  simpa only [cappedBothEncodingProjection, sourceGlobalExactProgramResult,
    sourceGlobalExactExecutionResult, hlogs] using hwin.2.1

theorem freshFirstLane_probability_le_prefix_of_cached (adversary : XmssSecurity.TargetSum.Adversary)
    (hcached : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      ∀ prefixResult ∈ support (sourcePrefixExecution adversary key),
        prefixResult.2.1.1.1 (CacheView.encodingInput key.secretKey.parameter
          prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none) :
    Pr[WinningFreshFirstLane | cappedDetailedGameWithEncodingTrace adversary] ≤
      Pr[fun result => FreshPrefixFirstLaneEvent result.1 result.2 | sourcePrefixProgram adversary] := by
  rw [freshFirstLane_probability_eq_source, sourceProgram_eq_prefix_finish]
  apply probEvent_bind_le_probEvent
  intro prefixPair hprefixPair hnone
  unfold sourcePrefixProgram at hprefixPair
  rw [mem_support_bind_iff] at hprefixPair
  obtain ⟨key, hkey, hprefixPair⟩ := hprefixPair
  rw [mem_support_bind_iff] at hprefixPair
  obtain ⟨prefixResult, hprefix, hpure⟩ := hprefixPair
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst prefixPair
  apply probEvent_eq_zero
  intro finalResult hfinal hevent
  rw [mem_support_bind_iff] at hfinal
  obtain ⟨execution, hfinish, hpure⟩ := hfinal
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst finalResult
  exact hnone (sourceWinningFreshFirstLane_implies_prefix adversary key hkey prefixResult hprefix
    (hcached key hkey prefixResult hprefix) execution hfinish hevent)

theorem freshFirstLane_withForgedEncodingQuery_probability_le
    (adversary : XmssSecurity.TargetSum.Adversary) (D : ℕ) (hD : Direct.IsDirectQueryBound adversary D) :
    Pr[WinningFreshFirstLane | cappedDetailedGameWithEncodingTrace (Direct.withForgedEncodingQuery adversary)] ≤
      ((D + 1 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (TargetSum.acceptanceProbability * ((D + 1 : ℕ) : ℝ≥0∞)) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) :=
  (freshFirstLane_probability_le_prefix_of_cached (Direct.withForgedEncodingQuery adversary)
    (sourcePrefixExecution_withForgedEncodingQuery_cached adversary)).trans
      (freshPrefixFirstLane_probability_le (Direct.withForgedEncodingQuery adversary) (D + 1)
        (Direct.withForgedEncodingQuery_isDirectQueryBound adversary D hD))

theorem forgeAdvantage_le_fresh_deciding_lanes (adversary : XmssSecurity.TargetSum.Adversary) :
    forgeAdvantage Concrete.scheme adversary ≤
      Pr[WinningFreshFirstLane | cappedDetailedGameWithEncodingTrace adversary] +
        (Pr[WinningEncodingPrehitOccurs | cappedDetailedGameWithEncodingTrace adversary] +
          Pr[fun execution : GameOutcome × QueryCache HashSpec => standardWon execution.1 = true ∧
            ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
            ¬ DecidingChainValueRevealed execution.2 execution.1 |
            detailedGameWithCache Concrete.scheme adversary]) := by
  rw [forgeAdvantage_eq_detailedGameWithCache,
    ← cappedDetailedGameWithEncodingTrace_cache_projection, probEvent_map, probEvent_map]
  calc
    _ ≤ Pr[fun execution : CappedEncodingTraceExecution =>
          WinningFreshFirstLane execution ∨
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
      · exact Or.inl ⟨hwin, Or.inl ⟨⟨hstrong, hencoding⟩, hprehit⟩⟩
      by_cases hrevealed : DecidingChainValueRevealed execution.2.1.1 execution.1
      · exact Or.inl ⟨hwin, Or.inr ⟨hstrong, hrevealed⟩⟩
      · exact Or.inr (Or.inr ⟨hwin, hencoding, hrevealed⟩)
    _ ≤ _ := by
      apply (probEvent_or_le _ WinningFreshFirstLane _).trans
      exact add_le_add le_rfl (probEvent_or_le _ WinningEncodingPrehitOccurs _)

/-- info: 'XmssSecurity.TargetSum.EUFCMA.freshFirstLane_withForgedEncodingQuery_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshFirstLane_withForgedEncodingQuery_probability_le

end XmssSecurity.TargetSum.EUFCMA
