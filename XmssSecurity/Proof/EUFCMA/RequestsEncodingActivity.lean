import XmssSecurity.Proof.EUFCMA.RequestsStoppedSource
import XmssSecurity.Proof.Direct.SourceEncodingActivity
import XmssSecurity.Proof.Direct.LimitedAcceptanceCancellation

/-! Cached fresh first-lane witnesses require a direct encoding query. A signing
request by itself does not make this event eligible for the extra terminal charge. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.EUFCMA.Requests

open Concrete CappedChain Deciding

noncomputable def encodingActive (parameter : PublicParameter) (trace : CappedChain.AttackerActionTrace) : Bool :=
  decide (0 < CappedChain.AttackerActionTrace.encodingInputCount parameter trace)

theorem encodingActive_implies_active (parameter : PublicParameter) (trace : CappedChain.AttackerActionTrace)
    (h : encodingActive parameter trace = true) : traceActive parameter trace = true := by
  have hpositive : 0 < trace.encodingInputCount parameter := of_decide_eq_true h
  apply decide_eq_true
  change 0 < trace.encodingInputCount parameter + trace.toSigningLog.length
  omega

def SourcePrefixEncoded (result : ProgrammedGlobalChainKeygenView × (Forgery × SourceExactTracedState)) : Prop :=
  encodingActive result.1.secretKey.parameter result.2.2.2 = true

theorem sourcePrefixProgram_stopped_encodingActivity_eq (adversary : XmssSecurity.Adversary) (q : ℕ)
    (hbound : IsQueryBound adversary q) :
    Pr[SourcePrefixEncoded | sourcePrefixProgram (stoppedAdversary q adversary)] =
      Pr[SourcePrefixEncoded | sourcePrefixProgram adversary] := by
  unfold sourcePrefixProgram
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro key
  by_cases hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen
  · simp only [bind_pure_comp, probEvent_map, Function.comp_def, SourcePrefixEncoded]
    rw [sourcePrefix_stopped_event_eq adversary q hbound key hkey _
      (fun result h => encodingActive_implies_active _ _ h)]
  · rw [probOutput_eq_zero_of_not_mem_support hkey, zero_mul, zero_mul]

theorem sourcePrefix_freshAccepted_encoded (adversary : XmssSecurity.Adversary)
    (key : ProgrammedGlobalChainKeygenView) (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (result : Forgery × SourceExactTracedState) (hresult : result ∈ support (sourcePrefixExecution adversary key))
    (hfresh : SourcePrefixFreshAccepted key result) : encodingActive key.secretKey.parameter result.2.2 = true := by
  obtain ⟨encoding, hdecode⟩ := hfresh.2
  obtain ⟨output, houtput⟩ := CacheView.encodingInput_cached_of_decode_some result.2.1.1.1 key.secretKey.parameter
    result.1.epoch result.1.message result.1.signature.randomness encoding hdecode
  exact decide_eq_true (sourcePrefix_fresh_encoding_cached_positive_count adversary key hkey result hresult hfresh.1
    (by rw [houtput]; simp))

theorem countedSource_encodingActivity_probability_le (publicKey : PublicKey) (secretKey : SecretKey)
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

theorem sourcePrefixProgram_encodingActivity_probability_le (adversary : XmssSecurity.Adversary) :
    Pr[SourcePrefixEncoded | sourcePrefixProgram adversary] ≤ Direct.expectedDirectEncodingQueries adversary := by
  rw [← sourceCountedPrefixProgram_source_projection, probEvent_map]
  let credit := fun keyResult : (PublicKey × SecretKey) × QueryCache HashSpec =>
    expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
      (Direct.IsDirectEncodingQuery keyResult.1.2.parameter) (adversary.main keyResult.1.1) keyResult.2
  have hmean : (∑' key, Pr[= key | trajectoryProgrammedGlobalChainKeygen] *
      credit (materializeCachedKeyResult key.keyResult)) = Direct.expectedDirectEncodingQueries adversary := by
    calc
      _ = ∑' keyResult, Pr[= keyResult | (fun key : ProgrammedGlobalChainKeygenView =>
          materializeCachedKeyResult key.keyResult) <$> trajectoryProgrammedGlobalChainKeygen] * credit keyResult := by
        rw [tsum_probOutput_map_mul]
      _ = _ := by
        unfold Direct.expectedDirectEncodingQueries
        apply tsum_congr
        intro keyResult
        rw [probOutput_congr rfl evalDist_materializedTrajectoryGlobalChainKeygen_eq_cappedKeygen]
  unfold sourceCountedPrefixProgram
  rw [probEvent_bind_eq_tsum, ← hmean]
  apply ENNReal.tsum_le_tsum
  intro key
  apply mul_le_mul' le_rfl
  simp only [bind_pure_comp, probEvent_map, Function.comp_def, SourcePrefixEncoded]
  simpa only [credit, materializeCachedKeyResult, ProgrammedGlobalChainKeygenView.keyResult,
    materializePrecomputation, precomputedSecretKey, sourceCountedPrefixExecution, CountedSourceState.toSource]
    using countedSource_encodingActivity_probability_le key.publicKey
      (materializePrecomputation key.cache key.secretKey) (adversary.main key.publicKey) key.cache

/-- info: 'XmssSecurity.EUFCMA.Requests.sourcePrefixProgram_encodingActivity_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourcePrefixProgram_encodingActivity_probability_le

end XmssSecurity.EUFCMA.Requests
