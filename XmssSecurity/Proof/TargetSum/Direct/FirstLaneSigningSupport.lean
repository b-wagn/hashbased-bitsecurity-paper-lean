import XmssSecurity.Proof.TargetSum.Direct.CountedSourceCoupling
import XmssSecurity.Proof.TargetSum.Direct.FirstLaneSampleBudget
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Every supported ideal signing call has a supported counted source witness with
the same encoding cache. This remains true when the call triggers a monitored collision. -/

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum

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

namespace CappedChain

open Seeded FirstLaneOracleSimulation

theorem countedSourceImpl_cache_projection (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (input : (OracleWorld + Generic.SigningSpec).Domain) (state : CountedSourceState) :
    (fun result => (result.1, result.2.counts.cache)) <$>
      (countedSourceImpl secretKey input).run state =
        (Generic.cappedUnloggedMappedAdversaryImpl publicKey secretKey input).run state.counts.cache := by
  have h := congrArg (fun computation => (fun result => (result.1, result.2.cache)) <$> computation)
    (countedSourceImpl_counts_projection secretKey input state)
  simp only [Functor.map_map] at h
  apply h.trans
  have hphase := phaseCountsImpl_cache_query_projection
    (fun (request : Generic.SignRequest) => Generic.Concrete.precomputedCappedSign secretKey request.epoch request.message)
    input state.counts
  exact hphase.trans (by cases input <;> rfl)

theorem exists_source_signing_of_firstLane_support
    (left : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (right : (Generic.CappedChain.ProgrammedGlobalChainKeygenView × (Generic.CappedChain.GlobalChainValueIndex → Digest)) ×
      (Generic.CappedChain.GlobalChainEdgeIndex → Digest))
    (hrel : Generic.CappedChain.ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (leftCache : QueryCache HashSpec) (rightState : Generic.CappedChain.GlobalCausalHashState)
    (hstate : Generic.CappedChain.GlobalFilteredCausalStateRelation left right.1 leftCache rightState)
    (request : Generic.SignRequest)
    (result : (Option Generic.Signature × Generic.CappedChain.GlobalCausalHashState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
      (Generic.CappedChain.globalFirstLaneSigningQuery right.1.1 request rightState)).run)) :
    ∃ source ∈ support ((simulateQ Generic.romImpl
      (Generic.Concrete.scheme.sign (Generic.Concrete.materializePrecomputation left.cache left.secretKey)
        request.epoch request.message)).run leftCache),
      Generic.HashCachesAgreeOn (Generic.CappedChain.GlobalSigningComparableHashInput left.secretKey.parameter)
        source.2 result.1.2.cache := by
  have hprojected : (result.1, result.2.chainActions) ∈ support
      ((simulateQ (Generic.RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        (Generic.CappedChain.globalFirstLaneErase (Generic.CappedChain.globalFirstLaneSigningQuery right.1.1 request rightState))).run) := by
    rw [← Generic.CappedChain.simulate_globalFirstLaneEagerTrace_chainProjection, support_map]
    exact ⟨result, hresult, rfl⟩
  rw [Generic.CappedChain.globalFirstLaneErase_signingQuery] at hprojected
  obtain ⟨source, hsource, hrelated⟩ := exists_left_of_relTriple_support
    (Generic.CappedChain.relTriple_programmed_globalFilteredCausalSigningQuery left right hrel hleftSupport hrightSupport
      leftCache rightState hstate request) (result.1, result.2.chainActions) hprojected
  exact ⟨source, hsource, hrelated.2.1⟩

theorem exists_countedSource_signing_of_firstLane_support
    (left : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (right : (Generic.CappedChain.ProgrammedGlobalChainKeygenView × (Generic.CappedChain.GlobalChainValueIndex → Digest)) ×
      (Generic.CappedChain.GlobalChainEdgeIndex → Digest))
    (hrel : Generic.CappedChain.ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (leftState : CountedSourceState) (rightState : Generic.CappedChain.GlobalCausalHashState)
    (hstate : Generic.CappedChain.GlobalFilteredCausalStateRelation left right.1 leftState.counts.cache rightState)
    (request : Generic.SignRequest)
    (result : (Option Generic.Signature × Generic.CappedChain.GlobalCausalHashState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
      (Generic.CappedChain.globalFirstLaneSigningQuery right.1.1 request rightState)).run)) :
    ∃ source ∈ support ((countedSourceImpl
      (Generic.Concrete.materializePrecomputation left.cache left.secretKey) (.inr request)).run leftState),
      Generic.HashCachesAgreeOn (Generic.CappedChain.GlobalSigningComparableHashInput left.secretKey.parameter)
        source.2.counts.cache result.1.2.cache := by
  obtain ⟨source, hsource, hagrees⟩ := exists_source_signing_of_firstLane_support left right hrel
    hleftSupport hrightSupport leftState.counts.cache rightState hstate request result hresult
  change source ∈ support ((Generic.cappedUnloggedMappedAdversaryImpl left.publicKey
    (Generic.Concrete.materializePrecomputation left.cache left.secretKey) (.inr request)).run leftState.counts.cache)
    at hsource
  rw [← countedSourceImpl_cache_projection left.publicKey
    (Generic.Concrete.materializePrecomputation left.cache left.secretKey) (.inr request) leftState,
    support_map] at hsource
  obtain ⟨counted, hcounted, hprojection⟩ := hsource
  refine ⟨counted, hcounted, ?_⟩
  have hcache : counted.2.counts.cache = source.2 := congrArg Prod.snd hprojection
  rw [hcache]
  exact hagrees

/-- info: 'XmssSecurity.TargetSum.CappedChain.exists_countedSource_signing_of_firstLane_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_countedSource_signing_of_firstLane_support

end CappedChain
end XmssSecurity.TargetSum
