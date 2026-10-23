import Xmss.Proof.Generic.Direct.ZeroHashPrefix
import Xmss.Proof.Generic.Direct.DecidingFirstLaneBridge

/-! Express the ordinary game as the exact traced prefix followed by ordinary verification. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace Xmss.Generic.Deciding

variable [Code]

open CappedExecution

noncomputable def sourcePrefixVerification (before : SourcePrefixResult) :
    ProbComp (GameOutcome × QueryCache HashSpec) :=
  (simulateQ romImpl (verificationPhase before.1.publicKey
    (Keygen.materializePrecomputation before.1.cache before.1.secretKey)
    (before.2.1, before.2.2.2.toSigningLog))).run before.2.2.1.1.1

theorem sourcePrefixProgram_support (adversary : Adversary) (before : SourcePrefixResult)
    (hbefore : before ∈ support (sourcePrefixProgram adversary)) :
    before.1 ∈ support trajectoryProgrammedGlobalChainKeygen ∧
      before.2 ∈ support (sourcePrefixExecution adversary before.1) := by
  simp only [sourcePrefixProgram, mem_support_bind_iff, mem_support_pure_iff] at hbefore
  obtain ⟨key, hkey, result, hresult, heq⟩ := hbefore
  cases heq
  exact ⟨hkey, hresult⟩

theorem probEvent_game_eq_source_prefix (adversary : Adversary)
    (event : GameOutcome × QueryCache HashSpec → Prop) :
    Pr[event | detailedGameWithCache precomputedScheme adversary] =
      ∑' before, Pr[= before | sourcePrefixProgram adversary] *
        Pr[event | sourcePrefixVerification before] := by
  let project : SourceGlobalExactTracedProgramResult → GameOutcome × QueryCache HashSpec :=
    fun result => let execution := cappedBothEncodingProjection (sourceGlobalExactProgramResult result)
      (execution.1, execution.2.1.1)
  have hprob : Pr[event | detailedGameWithCache precomputedScheme adversary] =
      Pr[event ∘ project | sourceGlobalExactTracedProgram adversary] := by
    calc
      _ = Pr[fun result : CappedEncodingTraceExecution => event (result.1, result.2.1.1) |
          cappedDetailedGameWithEncodingTrace adversary] := by
        rw [← cappedDetailedGameWithEncodingTrace_cache_projection, probEvent_map]
        rfl
      _ = Pr[(fun result : CappedEncodingTraceExecution => event (result.1, result.2.1.1)) ∘
          cappedBothEncodingProjection | cappedDetailedGameWithKeygenCacheAndBothTraces adversary] := by
        rw [← cappedDetailedGameWithKeygenCacheAndBothTraces_encodingProjection_eq, probEvent_map]
      _ = Pr[(fun result : CappedEncodingTraceExecution => event (result.1, result.2.1.1)) ∘
          cappedBothEncodingProjection |
          sourceGlobalExactProgramResult <$> sourceGlobalExactTracedProgram adversary] :=
        probEvent_eq_of_evalDist_eq _ (evalDist_sourceGlobalExact_eq_cappedBothTraces adversary).symm
      _ = _ := by rw [probEvent_map]; rfl
  rw [hprob, sourceProgram_eq_prefix_finish, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro before
  by_cases hbefore : before ∈ support (sourcePrefixProgram adversary)
  · obtain ⟨hkey, hprefix⟩ := sourcePrefixProgram_support adversary before hbefore
    have hlogs := cappedBothTracedMappedAdversaryImpl_logs_eq before.1.publicKey
      (Keygen.materializePrecomputation before.1.cache before.1.secretKey)
      (adversary.main before.1.publicKey) ((((before.1.cache, []), []), [])) before.2 rfl hprefix
    congr 1
    rw [bind_pure_comp, probEvent_map, sourcePrefixFinish, probEvent_map]
    unfold sourcePrefixVerification verificationPhase
    rw [simulateQ_bind, StateT.run_bind]
    simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp, probEvent_map]
    apply probEvent_congr' _ rfl
    intro result _
    simp only [Function.comp_def, project, cappedBothEncodingProjection,
      sourceGlobalExactProgramResult, sourceGlobalExactExecutionResult, hlogs]
  · simp [probOutput_eq_zero_of_not_mem_support hbefore]

open Classical in
theorem probEvent_verificationPhase_log (publicKey : PublicKey) (secretKey : SecretKey)
    (before : Forgery × QueryLog SigningSpec) (cache : QueryCache HashSpec)
    (predicate : QueryLog SigningSpec → Prop) :
    Pr[fun result : GameOutcome × QueryCache HashSpec => predicate result.1.signingLog |
      (simulateQ romImpl (verificationPhase publicKey secretKey before)).run cache] =
      if predicate before.2 then 1 else 0 := by
  unfold verificationPhase
  simp only [
    bind_pure_comp, simulateQ_map, StateT.run_map, probEvent_map, Function.comp_def]
  rw [probEvent_const]
  simp

theorem probEvent_game_log_eq_source (adversary : Adversary)
    (predicate : QueryLog SigningSpec → Prop) :
    Pr[fun result : GameOutcome × QueryCache HashSpec => predicate result.1.signingLog |
      detailedGameWithCache precomputedScheme adversary] =
      Pr[fun before : SourcePrefixResult => predicate before.2.2.2.toSigningLog |
        sourcePrefixProgram adversary] := by
  classical
  rw [probEvent_game_eq_source_prefix, probEvent_eq_tsum_ite (sourcePrefixProgram adversary)]
  apply tsum_congr
  intro before
  rw [sourcePrefixVerification, probEvent_verificationPhase_log]
  split_ifs <;> simp

end Xmss.Generic.Deciding
