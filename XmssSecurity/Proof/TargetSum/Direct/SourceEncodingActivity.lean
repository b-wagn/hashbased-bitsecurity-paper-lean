import XmssSecurity.Proof.TargetSum.Direct.SourcePrefixAcceptance
import XmssSecurity.Proof.TargetSum.Direct.CachedEncodingCost
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The probability of any direct encoding query or signer hash is at most their
expected total cost. The activity count is taken in the source execution. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.CappedChain

def CountedSourceEncodingActivity (parameter : PublicParameter) (state : CountedSourceState) : Prop :=
  0 < state.attackerTrace.encodingInputCount parameter + state.counts.signing

theorem CountedSourceEncodingBudget.activity_of_accepted {parameter : PublicParameter}
    {state : CountedSourceState} (hbudget : CountedSourceEncodingBudget parameter state)
    (haccepted : HasAcceptedEncoding parameter state.counts.cache) :
    CountedSourceEncodingActivity parameter state := by
  obtain ⟨input, output, hcached, hencoding, _hvalid⟩ := haccepted
  obtain ⟨leaf, hleaf⟩ := Option.isSome_iff_exists.mp hencoding
  obtain ⟨payload, rfl⟩ := Generic.exists_encodingInput_of_encodingInputLeafIndex?_eq_some parameter input leaf hleaf
  have hone := (one_le_cachedEncodingInputCount_of_cached parameter state.counts.cache leaf payload
    (by simp [hcached])).trans hbudget
  change 0 < state.attackerTrace.encodingInputCount parameter + state.counts.signing
  exact_mod_cast hone

theorem countedSourceImpl_encodingInputCount_eq_cost (secretKey : Generic.SecretKey)
    (input : (OracleWorld + Generic.SigningSpec).Domain) (state : CountedSourceState)
    (result : (OracleWorld + Generic.SigningSpec).Range input × CountedSourceState)
    (hresult : result ∈ support ((countedSourceImpl secretKey input).run state)) :
    result.2.attackerTrace.encodingInputCount secretKey.parameter =
      state.attackerTrace.encodingInputCount secretKey.parameter +
        if Generic.Direct.IsDirectEncodingQuery secretKey.parameter input then 1 else 0 := by
  simp only [countedSourceImpl, StateT.run, support_map] at hresult
  obtain ⟨handled, _hhandled, rfl⟩ := hresult
  simp only [countedSourceUpdate, AttackerActionTrace.encodingInputCount_append,
    attackerActionFragment_encodingInputCount]
  rcases input with (n | input) | request <;>
    simp only [Generic.Direct.IsDirectEncodingQuery, Generic.CappedEncodingMonitor.IsEncodingHashQuery, if_false]

theorem countedSource_expectedEncoding_eq {α : Type} (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) (cache : QueryCache HashSpec) :
    (∑' result, Pr[= result | (simulateQ (countedSourceImpl secretKey) computation).run
      (CountedSourceState.initial cache)] *
        (result.2.attackerTrace.encodingInputCount secretKey.parameter : ℝ≥0∞)) =
      expectedSimulatedQueryCount (Generic.cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        (Generic.Direct.IsDirectEncodingQuery secretKey.parameter) computation cache := by
  have h := expectedStateCounter_eq_initial_add_queries (countedSourceImpl secretKey)
    (Generic.Direct.IsDirectEncodingQuery secretKey.parameter)
    (fun state => state.attackerTrace.encodingInputCount secretKey.parameter)
    (countedSourceImpl_encodingInputCount_eq_cost secretKey) computation (CountedSourceState.initial cache)
  simpa only [CountedSourceState.initial, Generic.CappedChain.AttackerActionTrace.encodingInputCount,
    Generic.CappedChain.AttackerActionTrace.hashInputs, List.filterMap_nil, List.countP_nil, Nat.cast_zero,
    zero_add, countedSource_expectedQuery_eq publicKey] using h

theorem countedSource_encodingActivity_probability_le {α : Type}
    (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) (cache : QueryCache HashSpec) :
    Pr[fun result => CountedSourceEncodingActivity secretKey.parameter result.2 |
      (simulateQ (countedSourceImpl secretKey) computation).run (CountedSourceState.initial cache)] ≤
      expectedSimulatedQueryCount (Generic.cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        (Generic.Direct.IsDirectEncodingQuery secretKey.parameter) computation cache +
      ∑' result, Pr[= result | (simulateQ (countedSourceImpl secretKey) computation).run
        (CountedSourceState.initial cache)] * (result.2.counts.signing : ℝ≥0∞) := by
  rw [← countedSource_expectedEncoding_eq publicKey secretKey computation cache, ← ENNReal.tsum_add,
    probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  rw [← mul_add, ← Nat.cast_add]
  by_cases hactivity : CountedSourceEncodingActivity secretKey.parameter result.2
  · rw [if_pos hactivity]
    apply le_mul_of_one_le_right'
    exact_mod_cast hactivity
  · simp only [if_neg hactivity]
    exact zero_le

end XmssSecurity.TargetSum.CappedChain

namespace XmssSecurity.TargetSum.Deciding

open CappedChain

def SourceCountedPrefixEncodingActivity
    (result : Generic.CappedChain.ProgrammedGlobalChainKeygenView × (Generic.Forgery × CountedSourceState)) : Prop :=
  CountedSourceEncodingActivity result.1.secretKey.parameter result.2.2

theorem sourceCountedPrefix_encodingActivity_probability_le (adversary : Generic.Adversary) :
    Pr[SourceCountedPrefixEncodingActivity | sourceCountedPrefixProgram adversary] ≤
      Generic.Direct.expectedDirectEncodingQueries adversary + Direct.expectedSourceSignerHashes adversary := by
  let credit := fun keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec =>
    expectedSimulatedQueryCount (Generic.cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
      (Generic.Direct.IsDirectEncodingQuery keyResult.1.2.parameter) (adversary.main keyResult.1.1) keyResult.2 +
      ∑' result, Pr[= result | (simulateQ (countedSourceImpl keyResult.1.2) (adversary.main keyResult.1.1)).run
        (CountedSourceState.initial keyResult.2)] * (result.2.counts.signing : ℝ≥0∞)
  have hmean : (∑' key, Pr[= key | Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen] *
      credit (Generic.Concrete.materializeCachedKeyResult key.keyResult)) =
      Generic.Direct.expectedDirectEncodingQueries adversary + Direct.expectedSourceSignerHashes adversary := by
    calc
      _ = ∑' keyResult, Pr[= keyResult | (fun key : Generic.CappedChain.ProgrammedGlobalChainKeygenView =>
          Generic.Concrete.materializeCachedKeyResult key.keyResult) <$> Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen] *
          credit keyResult := by rw [tsum_probOutput_map_mul]
      _ = ∑' keyResult, Pr[= keyResult | (simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅] * credit keyResult := by
        apply tsum_congr
        intro keyResult
        rw [probOutput_congr rfl Generic.CappedChain.evalDist_materializedTrajectoryGlobalChainKeygen_eq_cappedKeygen]
      _ = _ := by
        simp only [credit, mul_add, ENNReal.tsum_add]
        rfl
  unfold sourceCountedPrefixProgram
  rw [probEvent_bind_eq_tsum, ← hmean]
  apply ENNReal.tsum_le_tsum
  intro key
  apply mul_le_mul' le_rfl
  simp only [bind_pure_comp, probEvent_map]
  exact countedSource_encodingActivity_probability_le key.publicKey
    (Generic.Concrete.materializePrecomputation key.cache key.secretKey) (adversary.main key.publicKey) key.cache

/-- info: 'XmssSecurity.TargetSum.Deciding.sourceCountedPrefix_encodingActivity_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourceCountedPrefix_encodingActivity_probability_le

end XmssSecurity.TargetSum.Deciding
