import Xmss.Proof.TargetSum.Direct.CountedSourceCoupling
import Xmss.Proof.TargetSum.EncodingAcceptanceBudget
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! An exhausted source budget freezes the hash cache. Free private sampling and
zero-cost signing continuations cannot create a new accepted encoding. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum

theorem romImpl_noAcceptedEncoding_of_nonencoding
    (parameter : PublicParameter) (input : OracleWorld.Domain) (cache : QueryCache HashSpec)
    (hcache : ¬HasAcceptedEncoding parameter cache)
    (hinput : ¬CappedEncodingMonitor.IsEncodingHashQuery parameter input)
    (result : OracleWorld.Range input × QueryCache HashSpec)
    (hresult : result ∈ support ((romImpl input).run cache)) :
    ¬HasAcceptedEncoding parameter result.2 := by
  have hzero : Pr[fun result => HasAcceptedEncoding parameter result.2 | (romImpl input).run cache] = 0 := by
    apply le_antisymm _ zero_le
    simpa only [if_neg hinput] using hasAcceptedEncoding_romImpl_step_le parameter input cache hcache
  exact probEvent_eq_zero_iff.mp hzero result hresult

theorem romImpl_uniform_cache (input : unifSpec.Domain) (cache : QueryCache HashSpec)
    (result : unifSpec.Range input × QueryCache HashSpec)
    (hresult : result ∈ support ((romImpl (.inl input)).run cache)) : result.2 = cache := by
  change result ∈ support ((fun value => (value, cache)) <$>
    (liftM (unifSpec.query input) : ProbComp _)) at hresult
  rw [support_map] at hresult
  obtain ⟨value, _, rfl⟩ := hresult
  rfl

theorem countHashQueries_zero_cache {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (result : (α × Nat) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (countHashQueries computation)).run cache))
    (hzero : result.1.2 = 0) : result.2 = cache := by
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value =>
      simp only [countHashQueries_pure, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      rfl
  | query_bind input next ih =>
      simp only [countHashQueries_query_bind, simulateQ_bind, simulateQ_spec_query,
        StateT.run_bind, bind_pure_comp, simulateQ_map, StateT.run_map,
        mem_support_bind_iff, support_map] at hresult
      obtain ⟨head, hhead, tail, htail, rfl⟩ := hresult
      cases input with
      | inl input =>
          have htailzero : tail.1.2 = 0 := by simpa using hzero
          exact (ih head.1 head.2 tail htail htailzero).trans (romImpl_uniform_cache input cache head hhead)
      | inr input =>
          change 1 + tail.1.2 = 0 at hzero
          omega

namespace CappedExecution

open Seeded

theorem phaseCountsImpl_cache_eq_of_counts_eq
    (signing : SignRequest → OracleComp OracleWorld (Option Generic.Signature))
    (input : (OracleWorld + SigningSpec).Domain) (state : PhaseCounts)
    (result : (OracleWorld + SigningSpec).Range input × PhaseCounts)
    (hresult : result ∈ support ((phaseCountsImpl signing input).run state))
    (hdirect : result.2.direct = state.direct) (hsigning : result.2.signing = state.signing) :
    result.2.cache = state.cache := by
  cases input with
  | inl input =>
      simp only [phaseCountsImpl, StateT.run, support_map] at hresult
      obtain ⟨sample, hsample, rfl⟩ := hresult
      cases input with
      | inl input => exact romImpl_uniform_cache input state.cache sample hsample
      | inr input =>
          change state.direct + 1 = state.direct at hdirect
          omega
  | inr request =>
      simp only [phaseCountsImpl, StateT.run, support_map] at hresult
      obtain ⟨sample, hsample, rfl⟩ := hresult
      change state.signing + sample.1.2 = state.signing at hsigning
      exact countHashQueries_zero_cache (signing request) state.cache sample hsample (by omega)

theorem countedSourceImpl_cache_eq_of_counts_eq (secretKey : Generic.SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CountedSourceState)
    (result : (OracleWorld + SigningSpec).Range input × CountedSourceState)
    (hresult : result ∈ support ((countedSourceImpl secretKey input).run state))
    (hdirect : result.2.counts.direct = state.counts.direct)
    (hsigning : result.2.counts.signing = state.counts.signing) :
    result.2.counts.cache = state.counts.cache := by
  apply phaseCountsImpl_cache_eq_of_counts_eq
    (fun request => Signing.precomputedCappedSign secretKey request.epoch request.message)
    input state.counts (result.1, result.2.counts) _ hdirect hsigning
  change (result.1, result.2.counts) ∈ support ((referencePhaseCountsImpl secretKey input).run state.counts)
  rw [← countedSourceImpl_counts_projection secretKey input state, support_map]
  exact ⟨result, hresult, rfl⟩

theorem countedSourceImpl_world_noAcceptedEncoding_of_nonencoding (secretKey : Generic.SecretKey)
    (input : OracleWorld.Domain) (state : CountedSourceState)
    (hcache : ¬HasAcceptedEncoding secretKey.parameter state.counts.cache)
    (hinput : ¬CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter input)
    (result : OracleWorld.Range input × CountedSourceState)
    (hresult : result ∈ support ((countedSourceImpl secretKey (.inl input)).run state)) :
    ¬HasAcceptedEncoding secretKey.parameter result.2.counts.cache := by
  simp only [countedSourceImpl, StateT.run, support_map] at hresult
  obtain ⟨handled, hhandled, rfl⟩ := hresult
  simp only [referencePhaseCountsImpl, phaseCountsImpl, StateT.run, support_map] at hhandled
  obtain ⟨sample, hsample, rfl⟩ := hhandled
  exact romImpl_noAcceptedEncoding_of_nonencoding secretKey.parameter input state.counts.cache
    hcache hinput sample hsample

theorem countedSource_cache_eq_of_charge_le {α : Type} (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CountedSourceState)
    (result : α × CountedSourceState)
    (hresult : result ∈ support ((simulateQ (countedSourceImpl secretKey) computation).run state))
    (hcharge : result.2.charge ≤ state.charge) : result.2.counts.cache = state.counts.cache := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      rfl
  | query_bind input next ih =>
      rw [Direct.run_simulateQ_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      have hstep := countedSourceImpl_counts_mono secretKey input state head hhead
      have hrest := countedSource_counts_mono secretKey (next head.1) head.2 result htail
      unfold CountedSourceState.charge at hcharge
      have hdirect : head.2.counts.direct = state.counts.direct := by omega
      have hsigning : head.2.counts.signing = state.counts.signing := by omega
      exact (ih head.1 head.2 result htail (by
        unfold CountedSourceState.charge
        omega)).trans (countedSourceImpl_cache_eq_of_counts_eq secretKey input state head hhead hdirect hsigning)

theorem CountedSourceBudget.cache_eq_of_exhausted {α : Type}
    {secretKey : Generic.SecretKey} {limit : Nat} {computation : OracleComp (OracleWorld + SigningSpec) α}
    {state : CountedSourceState} (hbudget : CountedSourceBudget secretKey limit computation state)
    (hexhausted : limit ≤ state.charge) (result : α × CountedSourceState)
    (hresult : result ∈ support ((simulateQ (countedSourceImpl secretKey) computation).run state)) :
    result.2.counts.cache = state.counts.cache :=
  countedSource_cache_eq_of_charge_le secretKey computation state result hresult
    ((hbudget result hresult).trans hexhausted)

theorem CountedSourceBudget.noAcceptedEncoding_of_exhausted {α : Type}
    {secretKey : Generic.SecretKey} {limit : Nat} {computation : OracleComp (OracleWorld + SigningSpec) α}
    {state : CountedSourceState} (hbudget : CountedSourceBudget secretKey limit computation state)
    (hexhausted : limit ≤ state.charge) (hcache : ¬HasAcceptedEncoding secretKey.parameter state.counts.cache)
    (result : α × CountedSourceState)
    (hresult : result ∈ support ((simulateQ (countedSourceImpl secretKey) computation).run state)) :
    ¬HasAcceptedEncoding secretKey.parameter result.2.counts.cache := by
  rw [hbudget.cache_eq_of_exhausted hexhausted result hresult]
  exact hcache

theorem CountedSourceBudget.noAcceptedEncoding_after_last_nonencoding {α : Type}
    {secretKey : Generic.SecretKey} {limit : Nat} {input : HashInput}
    {next : Digest → OracleComp (OracleWorld + SigningSpec) α} {state : CountedSourceState}
    (hbudget : CountedSourceBudget secretKey limit
      (liftM ((OracleWorld + SigningSpec).query (.inl (.inr input))) >>= next) state)
    (hlast : limit ≤ state.charge + 1)
    (hcache : ¬HasAcceptedEncoding secretKey.parameter state.counts.cache)
    (hinput : ¬CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter (.inr input))
    (result : α × CountedSourceState)
    (hresult : result ∈ support ((simulateQ (countedSourceImpl secretKey)
      (liftM ((OracleWorld + SigningSpec).query (.inl (.inr input))) >>= next)).run state)) :
    ¬HasAcceptedEncoding secretKey.parameter result.2.counts.cache := by
  rw [Direct.run_simulateQ_query_bind, mem_support_bind_iff] at hresult
  obtain ⟨head, hhead, htail⟩ := hresult
  have hnext := (hbudget.query_step head hhead).2
  have hdirect := countedSourceImpl_direct_eq secretKey (.inl (.inr input)) state head hhead
  have hmono := countedSourceImpl_counts_mono secretKey (.inl (.inr input)) state head hhead
  have hexhausted : limit ≤ head.2.charge := by
    change head.2.counts.direct = state.counts.direct + 1 at hdirect
    unfold CountedSourceState.charge at hlast ⊢
    omega
  exact hnext.noAcceptedEncoding_of_exhausted hexhausted
    (countedSourceImpl_world_noAcceptedEncoding_of_nonencoding secretKey (.inr input) state
      hcache hinput head hhead) result htail

/-- info: 'Xmss.TargetSum.CappedExecution.CountedSourceBudget.noAcceptedEncoding_of_exhausted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CountedSourceBudget.noAcceptedEncoding_of_exhausted

/-- info: 'Xmss.TargetSum.CappedExecution.CountedSourceBudget.noAcceptedEncoding_after_last_nonencoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CountedSourceBudget.noAcceptedEncoding_after_last_nonencoding

end CappedExecution
end Xmss.TargetSum
