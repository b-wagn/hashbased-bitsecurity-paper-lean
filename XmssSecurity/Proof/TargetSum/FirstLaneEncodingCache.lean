import XmssSecurity.Proof.TargetSum.FirstLaneEncodingAcceptance
import XmssSecurity.Proof.TargetSum.Direct.DecidingAcceptedProbe

/-! Every accepted encoding in the first-lane cache has an accepted sampling observation. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.CappedChain

open FirstLaneOracleSimulation

def AcceptedEncodingGrowth (parameter : PublicParameter) (initial final : QueryCache HashSpec)
    (trace : ActionTrace GlobalChainValueIndex) : Prop :=
  HasAcceptedEncoding parameter final →
    HasAcceptedEncoding parameter initial ∨ TraceHasAcceptedEncoding trace

theorem AcceptedEncodingGrowth.refl (parameter : PublicParameter) (cache : QueryCache HashSpec) :
    AcceptedEncodingGrowth parameter cache cache [] := fun h => Or.inl h

theorem AcceptedEncodingGrowth.trans {parameter : PublicParameter}
    {initial middle final : QueryCache HashSpec} {head tail : ActionTrace GlobalChainValueIndex}
    (hhead : AcceptedEncodingGrowth parameter initial middle head)
    (htail : AcceptedEncodingGrowth parameter middle final tail) :
    AcceptedEncodingGrowth parameter initial final (head ++ tail) := by
  intro hfinal
  rcases htail hfinal with hmiddle | htail
  · rcases hhead hmiddle with hinitial | hhead
    · exact Or.inl hinitial
    · exact Or.inr ((traceHasAcceptedEncoding_append _ _).2 (Or.inl hhead))
  · exact Or.inr ((traceHasAcceptedEncoding_append _ _).2 (Or.inr htail))

theorem AcceptedEncodingGrowth.cacheQuery (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (input : HashInput) (output : HashOutput) (trace : ActionTrace GlobalChainValueIndex)
    (htrace : TargetSum.ValidDigest (truncateHash output) → TraceHasAcceptedEncoding trace) :
    AcceptedEncodingGrowth parameter cache (cache.cacheQuery input output) trace := by
  intro haccepted
  by_cases hinitial : HasAcceptedEncoding parameter cache
  · exact Or.inl hinitial
  · exact Or.inr (htrace ((hasAcceptedEncoding_cacheQuery_iff _ _ _ _ hinitial).1 haccepted).2)

theorem randomOracle_support_cache_shape (input : HashInput) (cache : QueryCache HashSpec)
    (result : HashOutput × QueryCache HashSpec)
    (hresult : result ∈ support ((randomOracle input).run cache)) :
    result.2 = cache ∨ ∃ output, result.2 = cache.cacheQuery input output := by
  cases hcached : cache input with
  | some output =>
      rw [QueryImpl.withCaching_run_some _ hcached] at hresult
      simp only [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Or.inl rfl
  | none =>
      rw [randomOracle_run_none_eq_uniformHashOutput _ _ hcached, support_map] at hresult
      obtain ⟨output, _, rfl⟩ := hresult
      exact Or.inr ⟨output, rfl⟩

theorem globalCausalAttackerHashQueryFromHigh_cache_shape
    (table high : GlobalChainValueIndex → Digest) (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) × RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((globalCausalAttackerHashQueryFromHigh high secretKey input).run state)).run)) :
    result.1.2.cache = state.cache ∨ ∃ output, result.1.2.cache = state.cache.cacheQuery input output := by
  generalize hplan : globalFilteredCausalAttackerHashPlan secretKey input state = plan
  cases plan with
  | cached output =>
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan] at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Or.inl (globalCausalRecordedState_cache secretKey input state)
  | redirect output =>
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan] at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Or.inr ⟨output, by
        simp only [globalFilteredCausalRedirectResultState, globalCausalRecordedState_cache]⟩
  | fresh =>
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan,
        simulate_eagerTrace_globalCausalHashQuery, support_map] at hresult
      obtain ⟨sample, hsample, rfl⟩ := hresult
      simp only [globalCausalRecordedState_cache] at hsample
      exact randomOracle_support_cache_shape input state.cache sample hsample
  | reveal index =>
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan,
        simulate_eagerTrace_globalCausalRevealHashQueryFromHigh] at hresult
      simp only [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Or.inr ⟨_, rfl⟩
  | probeThenFresh index target =>
      rw [simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_probeThenFresh
        table high secretKey input state index target hplan, support_map] at hresult
      obtain ⟨sample, hsample, rfl⟩ := hresult
      exact randomOracle_support_cache_shape input state.cache sample hsample

end XmssSecurity.TargetSum.CappedChain

namespace XmssSecurity.TargetSum.Deciding

open CappedChain FirstLaneOracleSimulation

end XmssSecurity.TargetSum.Deciding
