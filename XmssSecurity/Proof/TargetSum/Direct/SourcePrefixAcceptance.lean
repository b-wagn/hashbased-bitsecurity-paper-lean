import XmssSecurity.Proof.TargetSum.Direct.SourceSignerQueries
import XmssSecurity.Proof.TargetSum.Direct.LimitedPrefixProbability
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Accepted encodings in the counted source prefix are charged to reference encoding
queries and signer hashes, with the original key-generation distribution. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.CappedChain

theorem countedSource_cache_projection {α : Type} (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CountedSourceState) :
    (fun result => (result.1, result.2.counts.cache)) <$>
      (simulateQ (countedSourceImpl secretKey) computation).run state =
        (simulateQ (cappedUnloggedMappedAdversaryImpl publicKey secretKey) computation).run state.counts.cache :=
  map_run_simulateQ_eq_of_query_map_eq (countedSourceImpl secretKey)
    (cappedUnloggedMappedAdversaryImpl publicKey secretKey) (fun state => state.counts.cache)
    (countedSourceImpl_cache_projection publicKey secretKey) computation state

theorem countedSource_accepted_probability_le {α : Type} (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (hcache : ¬HasAcceptedEncoding secretKey.parameter cache) :
    Pr[fun result => HasAcceptedEncoding secretKey.parameter result.2.counts.cache |
      (simulateQ (countedSourceImpl secretKey) computation).run (CountedSourceState.initial cache)] ≤
      TargetSum.acceptanceProbability *
        (expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
          (Direct.IsDirectEncodingQuery secretKey.parameter) computation cache +
          ∑' result, Pr[= result | (simulateQ (countedSourceImpl secretKey) computation).run
            (CountedSourceState.initial cache)] * (result.2.counts.signing : ℝ≥0∞)) := by
  have hproject := countedSource_cache_projection publicKey secretKey computation (CountedSourceState.initial cache)
  have hprob := congrArg (fun run => Pr[fun result => HasAcceptedEncoding secretKey.parameter result.2 | run]) hproject
  rw [probEvent_map, CappedEncodingMonitor.cappedUnloggedMappedAdversary_simulateQ_run_eq_source] at hprob
  simp only [Function.comp_def, CountedSourceState.initial] at hprob
  apply le_of_eq_of_le hprob
  apply (probEvent_hasAcceptedEncoding_le_expectedQueries secretKey.parameter _ cache hcache).trans
  apply mul_le_mul' le_rfl
  have h := countedSource_expected_selected_le publicKey secretKey
    (CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter)
    (fun input h => by cases input with
      | inl input => exact h.elim
      | inr input => simp only [IsHashQuery]) computation cache
  have hpred : Direct.IsDirectWorldQuery (CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter) =
      Direct.IsDirectEncodingQuery secretKey.parameter := by
    funext input
    rcases input with (uniform | input) | request <;> rfl
  apply h.trans
  apply add_le_add _ le_rfl
  apply expectedSimulatedQueryCount_mono
  intro input hinput
  simpa only [hpred] using hinput

end XmssSecurity.TargetSum.CappedChain

namespace XmssSecurity.TargetSum.Deciding

open CappedChain

noncomputable def sourceCountedPrefixExecution (adversary : Adversary) (key : CappedChain.ProgrammedGlobalChainKeygenView) :
    ProbComp (Forgery × CountedSourceState) :=
  (simulateQ (countedSourceImpl (Concrete.materializePrecomputation key.cache key.secretKey))
    (adversary.main key.publicKey)).run (CountedSourceState.initial key.cache)

noncomputable def sourceCountedPrefixProgram (adversary : Adversary) :
    ProbComp (CappedChain.ProgrammedGlobalChainKeygenView × (Forgery × CountedSourceState)) := do
  let key ← CappedChain.trajectoryProgrammedGlobalChainKeygen
  let result ← sourceCountedPrefixExecution adversary key
  pure (key, result)

def SourceCountedPrefixAccepted (result : CappedChain.ProgrammedGlobalChainKeygenView × (Forgery × CountedSourceState)) : Prop :=
  HasAcceptedEncoding result.1.secretKey.parameter result.2.2.counts.cache

theorem sourceCountedPrefix_accepted_probability_le (adversary : Adversary) :
    Pr[SourceCountedPrefixAccepted | sourceCountedPrefixProgram adversary] ≤
      TargetSum.acceptanceProbability *
        (Direct.expectedDirectEncodingQueries adversary + Direct.expectedSourceSignerHashes adversary) := by
  let credit := fun keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec =>
    expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
      (Direct.IsDirectEncodingQuery keyResult.1.2.parameter) (adversary.main keyResult.1.1) keyResult.2 +
      ∑' result, Pr[= result | (simulateQ (countedSourceImpl keyResult.1.2) (adversary.main keyResult.1.1)).run
        (CountedSourceState.initial keyResult.2)] * (result.2.counts.signing : ℝ≥0∞)
  have hmean : (∑' key, Pr[= key | CappedChain.trajectoryProgrammedGlobalChainKeygen] *
      credit (Concrete.materializeCachedKeyResult key.keyResult)) =
      Direct.expectedDirectEncodingQueries adversary + Direct.expectedSourceSignerHashes adversary := by
    calc
      _ = ∑' keyResult, Pr[= keyResult | (fun key : CappedChain.ProgrammedGlobalChainKeygenView =>
          Concrete.materializeCachedKeyResult key.keyResult) <$> CappedChain.trajectoryProgrammedGlobalChainKeygen] *
          credit keyResult := by rw [tsum_probOutput_map_mul]
      _ = ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] * credit keyResult := by
        apply tsum_congr
        intro keyResult
        rw [probOutput_congr rfl CappedChain.evalDist_materializedTrajectoryGlobalChainKeygen_eq_cappedKeygen]
      _ = _ := by
        simp only [credit, mul_add, ENNReal.tsum_add]
        rfl
  unfold sourceCountedPrefixProgram
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' key, Pr[= key | CappedChain.trajectoryProgrammedGlobalChainKeygen] *
        (TargetSum.acceptanceProbability * credit (Concrete.materializeCachedKeyResult key.keyResult)) := by
      apply ENNReal.tsum_le_tsum
      intro key
      by_cases hkey : key ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen
      · apply mul_le_mul' le_rfl
        simp only [bind_pure_comp, probEvent_map, Function.comp_def, SourceCountedPrefixAccepted,
          sourceCountedPrefixExecution, credit, Concrete.materializeCachedKeyResult_publicKey,
          Concrete.materializeCachedKeyResult_secretKey, Concrete.materializeCachedKeyResult_cache,
          CappedChain.ProgrammedGlobalChainKeygenView.keyResult, Concrete.materializePrecomputation_parameter]
        rw [← Concrete.materializePrecomputation_parameter key.cache key.secretKey]
        apply countedSource_accepted_probability_le key.publicKey
          (Concrete.materializePrecomputation key.cache key.secretKey) (adversary.main key.publicKey) key.cache
        apply Concrete.precomputedKeygen_no_acceptedEncoding (Concrete.materializeCachedKeyResult key.keyResult)
        apply (mem_support_iff_of_evalDist_eq CappedChain.evalDist_materializedTrajectoryGlobalChainKeygen_eq_cappedKeygen _).mp
        rw [support_map]
        exact ⟨key, hkey, rfl⟩
      · rw [probOutput_eq_zero_of_not_mem_support hkey, zero_mul, zero_mul]
    _ = _ := by
      simp_rw [mul_left_comm _ TargetSum.acceptanceProbability]
      rw [ENNReal.tsum_mul_left, hmean]

/-- info: 'XmssSecurity.TargetSum.Deciding.sourceCountedPrefix_accepted_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourceCountedPrefix_accepted_probability_le

end XmssSecurity.TargetSum.Deciding
