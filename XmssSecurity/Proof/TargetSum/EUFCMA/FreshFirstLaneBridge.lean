import XmssSecurity.Proof.TargetSum.EUFCMA.FreshFirstLane
import XmssSecurity.Proof.TargetSum.EUFCMA.DecidingAssembly
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Retain standard freshness in the first lane and transfer the full winning
event to the fresh, accepted adversary prefix. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Concrete CappedChain Deciding

def WinningFreshFirstLane (result : Generic.CappedEncodingTraceExecution) : Prop :=
  standardWon result.1 = true ∧ Generic.Deciding.WinningDecidingFirstLaneBadEventOccurs result

def SourceWinningFreshFirstLane (result : Generic.CappedChain.SourceGlobalExactTracedProgramResult) : Prop :=
  WinningFreshFirstLane (Generic.CappedChain.cappedBothEncodingProjection (Generic.CappedChain.sourceGlobalExactProgramResult result))

theorem freshFirstLane_probability_eq_source (adversary : Generic.Adversary) :
    Pr[WinningFreshFirstLane | Generic.cappedDetailedGameWithEncodingTrace adversary] =
      Pr[SourceWinningFreshFirstLane | Generic.CappedChain.sourceGlobalExactTracedProgram adversary] := by
  calc
    _ = Pr[WinningFreshFirstLane ∘ Generic.CappedChain.cappedBothEncodingProjection |
        Generic.CappedChain.cappedDetailedGameWithKeygenCacheAndBothTraces adversary] := by
      rw [← probEvent_map]
      exact probEvent_congr' (fun _ _ => Iff.rfl) (congrArg evalDist
        (Generic.CappedChain.cappedDetailedGameWithKeygenCacheAndBothTraces_encodingProjection_eq adversary)).symm
    _ = Pr[WinningFreshFirstLane ∘ Generic.CappedChain.cappedBothEncodingProjection |
        Generic.CappedChain.sourceGlobalExactProgramResult <$> Generic.CappedChain.sourceGlobalExactTracedProgram adversary] :=
      Generic.CappedChain.probEvent_eq_of_evalDist_eq _ (Generic.CappedChain.evalDist_sourceGlobalExact_eq_cappedBothTraces adversary).symm
    _ = _ := by rw [probEvent_map]; rfl

theorem sourceWinningFreshFirstLane_implies_prefix (adversary : Generic.Adversary)
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (hkey : key ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (prefixResult : Generic.Forgery × Generic.CappedChain.SourceExactTracedState)
    (hprefix : prefixResult ∈ support (Generic.Deciding.sourcePrefixExecution adversary key))
    (hcached : prefixResult.2.1.1.1 (Generic.Concrete.CacheView.encodingInput key.secretKey.parameter
      prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none)
    (execution : (Generic.Forgery × Bool) × Generic.CappedChain.SourceExactTracedState)
    (hfinish : execution ∈ support (Generic.Deciding.sourcePrefixFinish key prefixResult))
    (hevent : SourceWinningFreshFirstLane (key, execution)) : FreshPrefixFirstLaneEvent key prefixResult := by
  have haccepted := sourceFirstLaneEvent_implies_acceptedPrefixEvent adversary key hkey prefixResult hprefix
    hcached execution hfinish hevent.2
  refine ⟨haccepted.1, ?_, (Option.isSome_iff_exists.mp haccepted.2).imp fun _ hdecode =>
    Generic.Concrete.CacheView.decodeDigest_of_decodedEncoding hdecode⟩
  have hlogs := Generic.CappedChain.cappedBothTracedMappedAdversaryImpl_logs_eq key.publicKey
    (Generic.Concrete.materializePrecomputation key.cache key.secretKey) (adversary.main key.publicKey)
    ((((key.cache, []), []), [])) prefixResult rfl hprefix
  rw [Generic.Deciding.sourcePrefixFinish, support_map] at hfinish
  obtain ⟨verified, _, rfl⟩ := hfinish
  have hwin := (standardWon_eq_true_iff _).mp hevent.1
  simpa only [Generic.CappedChain.cappedBothEncodingProjection, Generic.CappedChain.sourceGlobalExactProgramResult,
    Generic.CappedChain.sourceGlobalExactExecutionResult, hlogs] using hwin.2.1

theorem freshFirstLane_probability_le_prefix_of_cached (adversary : Generic.Adversary)
    (hcached : ∀ key ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen,
      ∀ prefixResult ∈ support (Generic.Deciding.sourcePrefixExecution adversary key),
        prefixResult.2.1.1.1 (Generic.Concrete.CacheView.encodingInput key.secretKey.parameter
          prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none) :
    Pr[WinningFreshFirstLane | Generic.cappedDetailedGameWithEncodingTrace adversary] ≤
      Pr[fun result => FreshPrefixFirstLaneEvent result.1 result.2 | Generic.Deciding.sourcePrefixProgram adversary] := by
  rw [freshFirstLane_probability_eq_source, Generic.Deciding.sourceProgram_eq_prefix_finish]
  apply probEvent_bind_le_probEvent
  intro prefixPair hprefixPair hnone
  unfold Generic.Deciding.sourcePrefixProgram at hprefixPair
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
    (adversary : Generic.Adversary) (D : ℕ) (hD : Generic.Direct.IsDirectQueryBound adversary D) :
    Pr[WinningFreshFirstLane | Generic.cappedDetailedGameWithEncodingTrace (Generic.Direct.withForgedEncodingQuery adversary)] ≤
      ((D + 1 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (TargetSum.acceptanceProbability * ((D + 1 : ℕ) : ℝ≥0∞)) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) :=
  (freshFirstLane_probability_le_prefix_of_cached (Generic.Direct.withForgedEncodingQuery adversary)
    (Generic.Deciding.sourcePrefixExecution_withForgedEncodingQuery_cached adversary)).trans
      (freshPrefixFirstLane_probability_le (Generic.Direct.withForgedEncodingQuery adversary) (D + 1)
        (Generic.Direct.withForgedEncodingQuery_isDirectQueryBound adversary D hD))

theorem forgeAdvantage_le_fresh_deciding_lanes (adversary : Generic.Adversary) :
    forgeAdvantage Generic.Concrete.scheme adversary ≤
      Pr[WinningFreshFirstLane | Generic.cappedDetailedGameWithEncodingTrace adversary] +
        (Pr[Generic.WinningEncodingPrehitOccurs | Generic.cappedDetailedGameWithEncodingTrace adversary] +
          Pr[fun execution : Generic.GameOutcome × QueryCache HashSpec => standardWon execution.1 = true ∧
            ¬ Generic.OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
            ¬ Generic.Deciding.DecidingChainValueRevealed execution.2 execution.1 |
            Generic.detailedGameWithCache Generic.Concrete.scheme adversary]) := by
  rw [forgeAdvantage_eq_detailedGameWithCache,
    ← Generic.cappedDetailedGameWithEncodingTrace_cache_projection, probEvent_map, probEvent_map]
  calc
    _ ≤ Pr[fun execution : Generic.CappedEncodingTraceExecution =>
          WinningFreshFirstLane execution ∨
            (Generic.WinningEncodingPrehitOccurs execution ∨
              (standardWon execution.1 = true ∧ ¬ Generic.OutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
                ¬ Generic.Deciding.DecidingChainValueRevealed execution.2.1.1 execution.1)) |
          Generic.cappedDetailedGameWithEncodingTrace adversary] := by
      apply probEvent_mono
      intro execution _hmem hwin
      have hstrong := strongWon_of_standardWon execution.1 hwin
      by_cases hprehit : Generic.WinningEncodingPrehitOccurs execution
      · exact Or.inr (Or.inl hprehit)
      by_cases hencoding : Generic.OutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding
      · exact Or.inl ⟨hwin, Or.inl ⟨⟨hstrong, hencoding⟩, hprehit⟩⟩
      by_cases hrevealed : Generic.Deciding.DecidingChainValueRevealed execution.2.1.1 execution.1
      · exact Or.inl ⟨hwin, Or.inr ⟨hstrong, hrevealed⟩⟩
      · exact Or.inr (Or.inr ⟨hwin, hencoding, hrevealed⟩)
    _ ≤ _ := by
      apply (probEvent_or_le _ WinningFreshFirstLane _).trans
      exact add_le_add le_rfl (probEvent_or_le _ Generic.WinningEncodingPrehitOccurs _)

/-- info: 'XmssSecurity.TargetSum.EUFCMA.freshFirstLane_withForgedEncodingQuery_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshFirstLane_withForgedEncodingQuery_probability_le

end XmssSecurity.TargetSum.EUFCMA
