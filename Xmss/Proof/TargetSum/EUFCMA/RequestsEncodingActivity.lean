import Xmss.Proof.TargetSum.EUFCMA.RequestsStoppedSource
import Xmss.Proof.TargetSum.Direct.SourceEncodingActivity
import Xmss.Proof.TargetSum.Direct.LimitedAcceptanceCancellation
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.CacheDecode
import Xmss.Proof.TargetSum.EncodingProbability

/-! Cached fresh first-lane witnesses require a direct encoding query. A signing
request by itself does not make this event eligible for the extra terminal charge. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.EUFCMA.Requests
open Xmss.EUFCMA

open Hashing Wots Merkle Verify Keygen Signing CappedExecution Deciding

noncomputable def encodingActive (parameter : PublicParameter) (trace : CappedExecution.AttackerActionTrace) : Bool :=
  decide (0 < CappedExecution.AttackerActionTrace.encodingInputCount parameter trace)

theorem encodingActive_implies_active (parameter : PublicParameter) (trace : CappedExecution.AttackerActionTrace)
    (h : encodingActive parameter trace = true) : traceActive parameter trace = true := by
  have hpositive : 0 < trace.encodingInputCount parameter := of_decide_eq_true h
  apply decide_eq_true
  change 0 < trace.encodingInputCount parameter + trace.toSigningLog.length
  omega

def SourcePrefixEncoded (result : CappedExecution.ProgrammedGlobalChainKeygenView × (Forgery × CappedExecution.SourceExactTracedState)) : Prop :=
  encodingActive result.1.secretKey.parameter result.2.2.2 = true

theorem sourcePrefixProgram_stopped_encodingActivity_eq (adversary : Adversary) (q : ℕ)
    (hbound : IsQueryBound adversary q) :
    Pr[SourcePrefixEncoded | Deciding.sourcePrefixProgram (stoppedAdversary q adversary)] =
      Pr[SourcePrefixEncoded | Deciding.sourcePrefixProgram adversary] := by
  unfold Deciding.sourcePrefixProgram
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro key
  by_cases hkey : key ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen
  · simp only [bind_pure_comp, probEvent_map, Function.comp_def, SourcePrefixEncoded]
    rw [sourcePrefix_stopped_event_eq adversary q hbound key hkey _
      (fun result h => encodingActive_implies_active _ _ h)]
  · rw [probOutput_eq_zero_of_not_mem_support hkey, zero_mul, zero_mul]

theorem sourcePrefix_freshAccepted_encoded (adversary : Adversary)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView) (hkey : key ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (result : Forgery × CappedExecution.SourceExactTracedState) (hresult : result ∈ support (Deciding.sourcePrefixExecution adversary key))
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
  have hmean : (∑' key, Pr[= key | CappedExecution.trajectoryProgrammedGlobalChainKeygen] *
      credit (Keygen.materializeCachedKeyResult key.keyResult)) = Direct.expectedDirectEncodingQueries adversary := by
    calc
      _ = ∑' keyResult, Pr[= keyResult | (fun key : CappedExecution.ProgrammedGlobalChainKeygenView =>
          Keygen.materializeCachedKeyResult key.keyResult) <$> CappedExecution.trajectoryProgrammedGlobalChainKeygen] * credit keyResult := by
        rw [tsum_probOutput_map_mul]
      _ = _ := by
        unfold Direct.expectedDirectEncodingQueries
        apply tsum_congr
        intro keyResult
        rw [probOutput_congr rfl CappedExecution.evalDist_materializedTrajectoryGlobalChainKeygen_eq_cappedKeygen]
  unfold sourceCountedPrefixProgram
  rw [probEvent_bind_eq_tsum, ← hmean]
  apply ENNReal.tsum_le_tsum
  intro key
  apply mul_le_mul' le_rfl
  simp only [bind_pure_comp, probEvent_map, Function.comp_def, SourcePrefixEncoded]
  simpa only [credit, Keygen.materializeCachedKeyResult_publicKey,
    Keygen.materializeCachedKeyResult_secretKey, Keygen.materializeCachedKeyResult_cache,
    CappedExecution.ProgrammedGlobalChainKeygenView.keyResult, Keygen.materializePrecomputation_parameter,
    sourceCountedPrefixExecution, CountedSourceState.toSource]
    using countedSource_encodingActivity_probability_le key.publicKey
      (Keygen.materializePrecomputation key.cache key.secretKey) (adversary.main key.publicKey) key.cache

/-- info: 'Xmss.TargetSum.EUFCMA.Requests.sourcePrefixProgram_encodingActivity_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourcePrefixProgram_encodingActivity_probability_le

end Xmss.TargetSum.EUFCMA.Requests
