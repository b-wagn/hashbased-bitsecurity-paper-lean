import XmssSecurity.Proof.TargetSum.FirstLaneEncodingAcceptance
import XmssSecurity.Proof.TargetSum.Direct.DecidingAcceptedProbe
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Every accepted encoding in the first-lane cache has an accepted sampling observation. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.CappedChain

open FirstLaneOracleSimulation

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
    (table high : CappedChain.GlobalChainValueIndex → Digest) (secretKey : Generic.SecretKey) (input : HashInput)
    (state : CappedChain.GlobalCausalHashState)
    (result : (HashOutput × CappedChain.GlobalCausalHashState) × RevealProbeOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((CappedChain.globalCausalAttackerHashQueryFromHigh high secretKey input).run state)).run)) :
    result.1.2.cache = state.cache ∨ ∃ output, result.1.2.cache = state.cache.cacheQuery input output := by
  generalize hplan : CappedChain.globalFilteredCausalAttackerHashPlan secretKey input state = plan
  cases plan with
  | cached output =>
      rw [CappedChain.globalCausalAttackerHashQueryFromHigh_run, hplan] at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Or.inl (CappedChain.globalCausalRecordedState_cache secretKey input state)
  | redirect output =>
      rw [CappedChain.globalCausalAttackerHashQueryFromHigh_run, hplan] at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Or.inr ⟨output, by
        simp only [CappedChain.globalFilteredCausalRedirectResultState, CappedChain.globalCausalRecordedState_cache]⟩
  | fresh =>
      rw [CappedChain.globalCausalAttackerHashQueryFromHigh_run, hplan,
        CappedChain.simulate_eagerTrace_globalCausalHashQuery, support_map] at hresult
      obtain ⟨sample, hsample, rfl⟩ := hresult
      simp only [CappedChain.globalCausalRecordedState_cache] at hsample
      exact randomOracle_support_cache_shape input state.cache sample hsample
  | reveal index =>
      rw [CappedChain.globalCausalAttackerHashQueryFromHigh_run, hplan,
        CappedChain.simulate_eagerTrace_globalCausalRevealHashQueryFromHigh] at hresult
      simp only [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Or.inr ⟨_, rfl⟩
  | probeThenFresh index target =>
      rw [CappedChain.simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_probeThenFresh
        table high secretKey input state index target hplan, support_map] at hresult
      obtain ⟨sample, hsample, rfl⟩ := hresult
      exact randomOracle_support_cache_shape input state.cache sample hsample

end XmssSecurity.TargetSum.CappedChain

namespace XmssSecurity.TargetSum.Deciding

open CappedChain FirstLaneOracleSimulation

end XmssSecurity.TargetSum.Deciding
