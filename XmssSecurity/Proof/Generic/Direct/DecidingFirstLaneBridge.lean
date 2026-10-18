import XmssSecurity.Proof.Generic.Direct.DecidingPrefixBound
import XmssSecurity.Proof.Generic.Direct.DecidingPrefixStability
import XmssSecurity.Proof.Generic.Direct.DecidingFirstLane

/-! Relate the full first-lane event to the bounded prefix experiment. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Generic.Deciding

variable [Code]

open Concrete CappedChain

def SourceWinningDecidingFirstLaneEvent (result : SourceGlobalExactTracedProgramResult) : Prop :=
  WinningDecidingFirstLaneBadEventOccurs
    (cappedBothEncodingProjection (sourceGlobalExactProgramResult result))

theorem decidingFirstLane_probability_eq_source (adversary : Adversary) :
    Pr[WinningDecidingFirstLaneBadEventOccurs | cappedDetailedGameWithEncodingTrace adversary] =
      Pr[SourceWinningDecidingFirstLaneEvent | sourceGlobalExactTracedProgram adversary] := by
  calc
    _ = Pr[WinningDecidingFirstLaneBadEventOccurs ∘ cappedBothEncodingProjection |
        cappedDetailedGameWithKeygenCacheAndBothTraces adversary] := by
      rw [← probEvent_map]
      exact probEvent_congr' (fun _ _ => Iff.rfl) (congrArg evalDist
        (cappedDetailedGameWithKeygenCacheAndBothTraces_encodingProjection_eq adversary)).symm
    _ = Pr[WinningDecidingFirstLaneBadEventOccurs ∘ cappedBothEncodingProjection |
        sourceGlobalExactProgramResult <$> sourceGlobalExactTracedProgram adversary] :=
      probEvent_eq_of_evalDist_eq _ (evalDist_sourceGlobalExact_eq_cappedBothTraces adversary).symm
    _ = _ := by rw [probEvent_map]; rfl

noncomputable def sourcePrefixFinish (key : ProgrammedGlobalChainKeygenView)
    (prefixResult : Forgery × SourceExactTracedState) :
    ProbComp ((Forgery × Bool) × SourceExactTracedState) :=
  (fun verified : Bool × QueryCache HashSpec =>
    ((prefixResult.1, verified.1),
      (((verified.2, prefixResult.2.1.1.2),
        appendVerificationEncodingObservation (materializePrecomputation key.cache key.secretKey)
          prefixResult.1 prefixResult.2.1.1.1 verified.2 prefixResult.2.1.2), prefixResult.2.2))) <$>
      (simulateQ romImpl (Concrete.scheme.verify key.publicKey prefixResult.1.epoch
        prefixResult.1.message prefixResult.1.signature)).run prefixResult.2.1.1.1

theorem sourceDetailed_eq_prefix_finish (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView) :
    sourceGlobalExactTracedDetailedExecution adversary key =
      sourcePrefixExecution adversary key >>= sourcePrefixFinish key := by
  unfold sourceGlobalExactTracedDetailedExecution sourcePrefixExecution sourcePrefixFinish
  apply bind_congr
  intro prefixResult
  rw [sourceSigningTracedVerifierImpl_run_eq]
  simp [sourceExactSigningProjection, map_eq_bind_pure_comp]

theorem sourceProgram_eq_prefix_finish (adversary : Adversary) :
    sourceGlobalExactTracedProgram adversary = (do
      let prefixResult ← sourcePrefixProgram adversary
      let execution ← sourcePrefixFinish prefixResult.1 prefixResult.2
      pure (prefixResult.1, execution)) := by
  unfold sourceGlobalExactTracedProgram sourcePrefixProgram
  simp only [bind_assoc, pure_bind, sourceDetailed_eq_prefix_finish]

theorem sourceDetailed_encoding_support (adversary : Adversary)
    (result : SourceGlobalExactTracedProgramResult)
    (hresult : result ∈ support (sourceGlobalExactTracedProgram adversary)) :
    cappedBothEncodingProjection (sourceGlobalExactProgramResult result) ∈ support
      (cappedDetailedGameWithEncodingTrace adversary) := by
  have hmapped : sourceGlobalExactProgramResult result ∈ support
      (sourceGlobalExactProgramResult <$> sourceGlobalExactTracedProgram adversary) := by
    rw [support_map]
    exact ⟨result, hresult, rfl⟩
  have hboth := (mem_support_iff_of_evalDist_eq
    (evalDist_sourceGlobalExact_eq_cappedBothTraces adversary) _).mp hmapped
  rw [← cappedDetailedGameWithKeygenCacheAndBothTraces_encodingProjection_eq, support_map]
  exact ⟨sourceGlobalExactProgramResult result, hboth, rfl⟩

theorem sourceFirstLaneEvent_implies_prefixEvent (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (prefixResult : Forgery × SourceExactTracedState)
    (hprefix : prefixResult ∈ support (sourcePrefixExecution adversary key))
    (hcached : prefixResult.2.1.1.1 (CacheView.encodingInput key.secretKey.parameter
      prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none)
    (execution : (Forgery × Bool) × SourceExactTracedState)
    (hfinish : execution ∈ support (sourcePrefixFinish key prefixResult))
    (hevent : SourceWinningDecidingFirstLaneEvent (key, execution)) :
    PrefixFirstLaneEvent key prefixResult := by
  have hwhole : (key, execution) ∈ support (sourceGlobalExactTracedProgram adversary) := by
    unfold sourceGlobalExactTracedProgram
    rw [mem_support_bind_iff]
    refine ⟨key, hkey, ?_⟩
    rw [sourceDetailed_eq_prefix_finish, bind_assoc, mem_support_bind_iff]
    refine ⟨prefixResult, hprefix, ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨execution, hfinish, by simp⟩
  have hencodingSupport := sourceDetailed_encoding_support adversary (key, execution) hwhole
  have hlogs := cappedBothTracedMappedAdversaryImpl_logs_eq key.publicKey
    (materializePrecomputation key.cache key.secretKey) (adversary.main key.publicKey)
    ((((key.cache, []), []), [])) prefixResult rfl hprefix
  rw [sourcePrefixFinish, support_map] at hfinish
  obtain ⟨verified, hverified, rfl⟩ := hfinish
  have htrace : appendVerificationEncodingObservation
      (materializePrecomputation key.cache key.secretKey) prefixResult.1 prefixResult.2.1.1.1
      verified.2 prefixResult.2.1.2 = prefixResult.2.1.2 := by
    unfold appendVerificationEncodingObservation
    exact if_neg hcached
  rcases hevent with hencoding | ⟨hwin, hrevealed⟩
  · have hhit := cappedExactEncodingBranch_implies_monitorHit adversary _ hencodingSupport hencoding
    have hvalid := hencoding.1.signingTranscript_valid
    refine ⟨?_, Or.inl ?_⟩
    · simpa only [cappedBothEncodingProjection, sourceGlobalExactProgramResult,
        sourceGlobalExactExecutionResult, hlogs] using hvalid
    · simpa only [cappedBothEncodingProjection, sourceGlobalExactProgramResult,
        sourceGlobalExactExecutionResult, htrace] using hhit
  · let outcome : GameOutcome := ⟨key.publicKey, materializePrecomputation key.cache key.secretKey,
      prefixResult.1, prefixResult.2.2.toSigningLog, verified.1⟩
    have hafter : (outcome, verified.2) ∈ support ((simulateQ romImpl
        (verificationPhase key.publicKey (materializePrecomputation key.cache key.secretKey)
          (prefixResult.1, prefixResult.2.2.toSigningLog))).run prefixResult.2.1.1.1) := by
      unfold verificationPhase
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
      exact ⟨verified, hverified, by simp [outcome]⟩
    apply prefixFirstLaneEvent_of_winning_revealed adversary key hkey prefixResult hprefix hcached
      (outcome, verified.2) hafter
    · simpa only [cappedBothEncodingProjection, sourceGlobalExactProgramResult,
        sourceGlobalExactExecutionResult, hlogs] using hwin
    · simpa only [cappedBothEncodingProjection, sourceGlobalExactProgramResult,
        sourceGlobalExactExecutionResult, hlogs] using hrevealed

theorem decidingFirstLane_probability_le_of_cached (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D)
    (hcached : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      ∀ prefixResult ∈ support (sourcePrefixExecution adversary key),
        prefixResult.2.1.1.1 (CacheView.encodingInput key.secretKey.parameter
          prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none) :
    Pr[WinningDecidingFirstLaneBadEventOccurs | cappedDetailedGameWithEncodingTrace adversary] ≤
      ((D + 1 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  rw [decidingFirstLane_probability_eq_source]
  apply le_trans _ (prefixFirstLane_probability_le adversary D hD)
  rw [sourceProgram_eq_prefix_finish]
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
  exact hnone (sourceFirstLaneEvent_implies_prefixEvent adversary key hkey prefixResult hprefix
    (hcached key hkey prefixResult hprefix) execution hfinish hevent)

/-- One preliminary encoding query and one deciding probe, in addition to the adversary's budget. -/
theorem decidingFirstLane_withForgedEncodingQuery_probability_le (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) :
    Pr[WinningDecidingFirstLaneBadEventOccurs |
      cappedDetailedGameWithEncodingTrace (Direct.withForgedEncodingQuery adversary)] ≤
      ((D + 2 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  exact decidingFirstLane_probability_le_of_cached (Direct.withForgedEncodingQuery adversary)
    (D + 1) (Direct.withForgedEncodingQuery_isDirectQueryBound adversary D hD)
    (sourcePrefixExecution_withForgedEncodingQuery_cached adversary)

end XmssSecurity.Generic.Deciding
