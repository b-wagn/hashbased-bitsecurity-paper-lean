import Xmss.Proof.TargetSum.FirstLaneEncodingAcceptance
import Xmss.Proof.TargetSum.Direct.DecidingAcceptedProbe
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Every accepted encoding in the first-lane cache has an accepted sampling observation. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open Xmss.Generic

namespace Xmss.TargetSum.CappedExecution

open FirstLaneOracleSimulation

theorem randomOracle_support_cache_shape (input : HashInput) (cache : QueryCache HashSpec)
    (result : Digest × QueryCache HashSpec)
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

theorem globalCausalAttackerHashQuery_cache_shape
    (table : CappedExecution.GlobalChainValueIndex → Digest) (secretKey : Generic.SecretKey) (input : HashInput)
    (state : CappedExecution.GlobalCausalHashState)
    (result : (Digest × CappedExecution.GlobalCausalHashState) × RevealProbeOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((CappedExecution.globalCausalAttackerHashQuery secretKey input).run state)).run)) :
    result.1.2.cache = state.cache ∨ ∃ output, result.1.2.cache = state.cache.cacheQuery input output := by
  generalize hplan : CappedExecution.globalFilteredCausalAttackerHashPlan secretKey input state = plan
  cases plan with
  | cached output =>
      rw [CappedExecution.globalCausalAttackerHashQuery_run, hplan] at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Or.inl (CappedExecution.globalCausalRecordedState_cache secretKey input state)
  | redirect output =>
      rw [CappedExecution.globalCausalAttackerHashQuery_run, hplan] at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Or.inr ⟨output, by
        simp only [CappedExecution.globalFilteredCausalRedirectResultState, CappedExecution.globalCausalRecordedState_cache]⟩
  | fresh =>
      rw [CappedExecution.globalCausalAttackerHashQuery_run, hplan,
        CappedExecution.simulate_eagerTrace_globalCausalHashQuery, support_map] at hresult
      obtain ⟨sample, hsample, rfl⟩ := hresult
      simp only [CappedExecution.globalCausalRecordedState_cache] at hsample
      exact randomOracle_support_cache_shape input state.cache sample hsample
  | reveal index =>
      rw [CappedExecution.globalCausalAttackerHashQuery_run, hplan,
        CappedExecution.simulate_eagerTrace_globalCausalRevealHashQuery] at hresult
      simp only [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Or.inr ⟨_, rfl⟩
  | probeThenFresh index target =>
      rw [CappedExecution.simulate_eagerTrace_globalCausalAttackerHashQuery_probeThenFresh
        table secretKey input state index target hplan, support_map] at hresult
      obtain ⟨sample, hsample, rfl⟩ := hresult
      exact randomOracle_support_cache_shape input state.cache sample hsample

end Xmss.TargetSum.CappedExecution

namespace Xmss.TargetSum.Deciding

open CappedExecution FirstLaneOracleSimulation

end Xmss.TargetSum.Deciding
