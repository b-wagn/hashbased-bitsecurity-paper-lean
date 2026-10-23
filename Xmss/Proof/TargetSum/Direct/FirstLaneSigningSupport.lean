import Xmss.Proof.TargetSum.Direct.CountedSourceCoupling
import Xmss.Proof.TargetSum.Direct.FirstLaneSampleBudget
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Every supported ideal signing call has a supported counted source witness with
the same encoding cache. This remains true when the call triggers a monitored collision. -/

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum

theorem exists_left_of_relTriple_support {α β : Type} {left : ProbComp α} {right : ProbComp β}
    {relation : α → β → Prop} (hrel : RelTriple left right relation)
    (result : β) (hresult : result ∈ support right) :
    ∃ source ∈ support left, relation source result := by
  rw [relTriple_iff_relWP, relWP_iff_couplingPost] at hrel
  obtain ⟨coupling, hcoupling⟩ := hrel
  have hright : result ∈ support 𝒟[right] := by
    rw [mem_support_iff_evalDist_apply_ne_zero] at hresult ⊢
    simpa using hresult
  rw [← coupling.2.map_snd, support_map] at hright
  obtain ⟨pair, hpair, rfl⟩ := hright
  have hleft : pair.1 ∈ support 𝒟[left] := by
    rw [← coupling.2.map_fst, support_map]
    exact ⟨pair, hpair, rfl⟩
  refine ⟨pair.1, ?_, hcoupling pair hpair⟩
  rw [mem_support_iff_evalDist_apply_ne_zero] at hleft ⊢
  simpa using hleft

namespace CappedExecution

open Seeded FirstLaneOracleSimulation

theorem countedSourceImpl_cache_projection (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CountedSourceState) :
    (fun result => (result.1, result.2.counts.cache)) <$>
      (countedSourceImpl secretKey input).run state =
        (cappedUnloggedMappedAdversaryImpl publicKey secretKey input).run state.counts.cache := by
  have h := congrArg (fun computation => (fun result => (result.1, result.2.cache)) <$> computation)
    (countedSourceImpl_counts_projection secretKey input state)
  simp only [Functor.map_map] at h
  apply h.trans
  have hphase := phaseCountsImpl_cache_query_projection
    (fun (request : SignRequest) => Signing.precomputedCappedSign secretKey request.epoch request.message)
    input state.counts
  exact hphase.trans (by cases input <;> rfl)

theorem exists_source_signing_of_firstLane_support
    (left : CappedExecution.ProgrammedGlobalChainKeygenView)
    (right : CappedExecution.ProgrammedGlobalChainKeygenView × (CappedExecution.GlobalChainValueIndex → Digest))
    (hrel : CappedExecution.ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleftSupport : left ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (leftCache : QueryCache HashSpec) (rightState : CappedExecution.GlobalCausalHashState)
    (hstate : CappedExecution.GlobalFilteredCausalStateRelation left right leftCache rightState)
    (request : SignRequest)
    (result : (Option Generic.Signature × CappedExecution.GlobalCausalHashState) × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2)
      (CappedExecution.globalFirstLaneSigningQuery right.1 request rightState)).run)) :
    ∃ source ∈ support ((simulateQ romImpl
      (precomputedScheme.sign (Keygen.materializePrecomputation left.cache left.secretKey)
        request.epoch request.message)).run leftCache),
      HashCachesAgreeOn (CappedExecution.GlobalSigningComparableHashInput left.secretKey.parameter)
        source.2 result.1.2.cache := by
  have hprojected : (result.1, result.2.chainActions) ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
        (CappedExecution.globalFirstLaneErase (CappedExecution.globalFirstLaneSigningQuery right.1 request rightState))).run) := by
    rw [← CappedExecution.simulate_globalFirstLaneEagerTrace_chainProjection, support_map]
    exact ⟨result, hresult, rfl⟩
  rw [CappedExecution.globalFirstLaneErase_signingQuery] at hprojected
  obtain ⟨source, hsource, hrelated⟩ := exists_left_of_relTriple_support
    (CappedExecution.relTriple_programmed_globalFilteredCausalSigningQuery left right hrel hleftSupport hrightSupport
      leftCache rightState hstate request) (result.1, result.2.chainActions) hprojected
  exact ⟨source, hsource, hrelated.2.1⟩

theorem exists_countedSource_signing_of_firstLane_support
    (left : CappedExecution.ProgrammedGlobalChainKeygenView)
    (right : CappedExecution.ProgrammedGlobalChainKeygenView × (CappedExecution.GlobalChainValueIndex → Digest))
    (hrel : CappedExecution.ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleftSupport : left ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (leftState : CountedSourceState) (rightState : CappedExecution.GlobalCausalHashState)
    (hstate : CappedExecution.GlobalFilteredCausalStateRelation left right leftState.counts.cache rightState)
    (request : SignRequest)
    (result : (Option Generic.Signature × CappedExecution.GlobalCausalHashState) × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2)
      (CappedExecution.globalFirstLaneSigningQuery right.1 request rightState)).run)) :
    ∃ source ∈ support ((countedSourceImpl
      (Keygen.materializePrecomputation left.cache left.secretKey) (.inr request)).run leftState),
      HashCachesAgreeOn (CappedExecution.GlobalSigningComparableHashInput left.secretKey.parameter)
        source.2.counts.cache result.1.2.cache := by
  obtain ⟨source, hsource, hagrees⟩ := exists_source_signing_of_firstLane_support left right hrel
    hleftSupport hrightSupport leftState.counts.cache rightState hstate request result hresult
  change source ∈ support ((cappedUnloggedMappedAdversaryImpl left.publicKey
    (Keygen.materializePrecomputation left.cache left.secretKey) (.inr request)).run leftState.counts.cache)
    at hsource
  rw [← countedSourceImpl_cache_projection left.publicKey
    (Keygen.materializePrecomputation left.cache left.secretKey) (.inr request) leftState,
    support_map] at hsource
  obtain ⟨counted, hcounted, hprojection⟩ := hsource
  refine ⟨counted, hcounted, ?_⟩
  have hcache : counted.2.counts.cache = source.2 := congrArg Prod.snd hprojection
  rw [hcache]
  exact hagrees

/-- info: 'Xmss.TargetSum.CappedExecution.exists_countedSource_signing_of_firstLane_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_countedSource_signing_of_firstLane_support

end CappedExecution
end Xmss.TargetSum
