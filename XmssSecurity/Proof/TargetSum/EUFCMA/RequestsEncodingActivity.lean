import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsStoppedSource
import XmssSecurity.Proof.TargetSum.Direct.SourceEncodingActivity
import XmssSecurity.Proof.TargetSum.Direct.LimitedAcceptanceCancellation
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.CacheDecode
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Cached fresh first-lane witnesses require a direct encoding query. A signing
request by itself does not make this event eligible for the extra terminal charge. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.EUFCMA.Requests
open XmssSecurity.EUFCMA

open Concrete CappedChain Deciding

noncomputable def encodingActive (parameter : PublicParameter) (trace : CappedChain.AttackerActionTrace) : Bool :=
  decide (0 < CappedChain.AttackerActionTrace.encodingInputCount parameter trace)

theorem encodingActive_implies_active (parameter : PublicParameter) (trace : CappedChain.AttackerActionTrace)
    (h : encodingActive parameter trace = true) : traceActive parameter trace = true := by
  have hpositive : 0 < trace.encodingInputCount parameter := of_decide_eq_true h
  apply decide_eq_true
  change 0 < trace.encodingInputCount parameter + trace.toSigningLog.length
  omega

def SourcePrefixEncoded (result : CappedChain.ProgrammedGlobalChainKeygenView × (Forgery × CappedChain.SourceExactTracedState)) : Prop :=
  encodingActive result.1.secretKey.parameter result.2.2.2 = true

theorem sourcePrefixProgram_stopped_encodingActivity_eq (adversary : Adversary) (q : ℕ)
    (hbound : IsQueryBound adversary q) :
    Pr[SourcePrefixEncoded | Deciding.sourcePrefixProgram (stoppedAdversary q adversary)] =
      Pr[SourcePrefixEncoded | Deciding.sourcePrefixProgram adversary] := by
  unfold Deciding.sourcePrefixProgram
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro key
  by_cases hkey : key ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen
  · simp only [bind_pure_comp, probEvent_map, Function.comp_def, SourcePrefixEncoded]
    rw [sourcePrefix_stopped_event_eq adversary q hbound key hkey _
      (fun result h => encodingActive_implies_active _ _ h)]
  · rw [probOutput_eq_zero_of_not_mem_support hkey, zero_mul, zero_mul]

theorem sourcePrefix_freshAccepted_encoded (adversary : Adversary)
    (key : CappedChain.ProgrammedGlobalChainKeygenView) (hkey : key ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (result : Forgery × CappedChain.SourceExactTracedState) (hresult : result ∈ support (Deciding.sourcePrefixExecution adversary key))
    (hfresh : SourcePrefixFreshAccepted key result) : encodingActive key.secretKey.parameter result.2.2 = true := by
  obtain ⟨encoding, hdecode⟩ := hfresh.2
  obtain ⟨output, houtput⟩ := TargetSum.encodingInput_cached_of_decode_some result.2.1.1.1 key.secretKey.parameter
    result.1.epoch result.1.message result.1.signature.randomness encoding hdecode
  exact decide_eq_true (sourcePrefix_fresh_encoding_cached_positive_count adversary key hkey result hresult hfresh.1
    (by rw [houtput]; simp))

theorem countedSource_encodingActivity_probability_le (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) :
    Pr[fun result => encodingActive secretKey.parameter result.2.attackerTrace = true |
      (simulateQ (countedSourceImpl secretKey) computation).run (CountedSourceState.initial cache)] ≤
      expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        (Direct.IsDirectEncodingQuery secretKey.parameter) computation cache := by
  rw [← countedSource_expectedEncoding_eq publicKey secretKey computation cache, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  split_ifs with hactive
  · apply le_mul_of_one_le_right'
    have h : 0 < result.2.attackerTrace.encodingInputCount secretKey.parameter := of_decide_eq_true hactive
    exact_mod_cast h
  · exact zero_le

theorem sourcePrefixProgram_encodingActivity_probability_le (adversary : Adversary) :
    Pr[SourcePrefixEncoded | Deciding.sourcePrefixProgram adversary] ≤ Direct.expectedDirectEncodingQueries adversary := by
  rw [← sourceCountedPrefixProgram_source_projection, probEvent_map]
  let credit := fun keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec =>
    expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
      (Direct.IsDirectEncodingQuery keyResult.1.2.parameter) (adversary.main keyResult.1.1) keyResult.2
  have hmean : (∑' key, Pr[= key | CappedChain.trajectoryProgrammedGlobalChainKeygen] *
      credit (Concrete.materializeCachedKeyResult key.keyResult)) = Direct.expectedDirectEncodingQueries adversary := by
    calc
      _ = ∑' keyResult, Pr[= keyResult | (fun key : CappedChain.ProgrammedGlobalChainKeygenView =>
          Concrete.materializeCachedKeyResult key.keyResult) <$> CappedChain.trajectoryProgrammedGlobalChainKeygen] * credit keyResult := by
        rw [tsum_probOutput_map_mul]
      _ = _ := by
        unfold Direct.expectedDirectEncodingQueries
        apply tsum_congr
        intro keyResult
        rw [probOutput_congr rfl CappedChain.evalDist_materializedTrajectoryGlobalChainKeygen_eq_cappedKeygen]
  unfold sourceCountedPrefixProgram
  rw [probEvent_bind_eq_tsum, ← hmean]
  apply ENNReal.tsum_le_tsum
  intro key
  apply mul_le_mul' le_rfl
  simp only [bind_pure_comp, probEvent_map, Function.comp_def, SourcePrefixEncoded]
  simpa only [credit, Concrete.materializeCachedKeyResult_publicKey,
    Concrete.materializeCachedKeyResult_secretKey, Concrete.materializeCachedKeyResult_cache,
    CappedChain.ProgrammedGlobalChainKeygenView.keyResult, Concrete.materializePrecomputation_parameter,
    sourceCountedPrefixExecution, CountedSourceState.toSource]
    using countedSource_encodingActivity_probability_le key.publicKey
      (Concrete.materializePrecomputation key.cache key.secretKey) (adversary.main key.publicKey) key.cache

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Requests.sourcePrefixProgram_encodingActivity_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourcePrefixProgram_encodingActivity_probability_le

end XmssSecurity.TargetSum.EUFCMA.Requests
