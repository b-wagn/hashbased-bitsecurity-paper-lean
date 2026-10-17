import XmssSecurity.Proof.TargetSum.Direct.FirstLane

/-!
# First-lane coupling stopped before verification

Only the adversary's direct hash queries consume the coupling budget. This exposes the good
state relation at the point where the cached forged encoding determines the deciding probe.
-/

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.CappedChain

theorem relTriple_sourceExact_firstLane_adversary_boundedHit_direct
    (D hitLimit : ℕ) (hlimit : D ≤ hitLimit) (adversary : Adversary)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView × (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hD : (adversary.main left.publicKey).IsQueryBoundP Direct.IsDirectHashQuery D) :
    RelTriple
      ((simulateQ (cappedBothTracedMappedAdversaryImpl left.publicKey
          (Concrete.materializePrecomputation left.cache left.secretKey))
        (adversary.main left.publicKey)).run ((((left.cache, []), []), [])))
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
        ((simulateQ (globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2)
          (adversary.main left.publicKey)).run
            (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState right.1.1)))).run)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1.1 ∧
          SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2 rightResult.1.2
            rightResult.2 ∧ FirstLaneOracleSimulation.hazardCount rightResult.2 ≤ D) ∨
          FirstLaneOracleSimulation.CombinedHit right.1.2
            (FirstLaneOracleSimulation.enforceHazardTrace hitLimit rightResult.2)) := by
  let secretKey := Concrete.materializePrecomputation left.cache left.secretKey
  let sourceInitial : SourceExactTracedState := ((((left.cache, []), []), []))
  let highInitial : GlobalMonitoredTracedState :=
    (⟨globalFilteredCausalKeygenState right.1.1, []⟩, [])
  let firstLaneInitial := GlobalHighDirectTracedState.initial
    (globalFilteredCausalKeygenState right.1.1)
  have hinitial : SourceFirstLaneExactGoodStateRelation left right.1 sourceInitial firstLaneInitial
      [] := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [sourceInitial, highInitial, firstLaneInitial, globalStateOfFirstLane,
        sourceExactSigningProjection, FirstLaneOracleSimulation.ActionTrace.chainActions] using
        globalSigningMonitoredTracedStateRelation_initial left right hrel hleftSupport hrightSupport
    · simp [sourceInitial, FirstLaneOracleSimulation.ActionTrace.encodingActions]
    · simp [CappedEncodingMonitor.validObservedSignLeafIndices,
        FirstLaneOracleSimulation.ActionTrace.encodingActions, CappedEncodingMonitor.validActions,
        EncodingMonitor.observedSignLeafIndices]
  let Budget := fun (rest : OracleComp (OracleWorld + SigningSpec) Forgery) (fuel : ℕ)
    (_state : SourceExactTracedState) => rest.IsQueryBoundP Direct.IsDirectHashQuery fuel
  have hcoupling := relTriple_simulateQ_bind_bounded_firstLane right.1.2
    (cappedBothTracedMappedAdversaryImpl left.publicKey secretKey)
    (globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2)
    (fun forgery state => pure (forgery, state))
    (fun forgery state => pure (forgery, state))
    directHashActionCost (SourceFirstLaneExactGoodStateRelation left right.1)
    (fun state spent => state.2.hashInputs.length = spent) Budget
    (by
      intro input next remaining state result hrest _hresult
      change (liftM ((OracleWorld + SigningSpec).query input) >>= next).IsQueryBoundP
        Direct.IsDirectHashQuery remaining at hrest
      rw [isQueryBoundP_query_bind_iff] at hrest
      obtain ⟨hpos, hnext⟩ := hrest
      rw [Direct.directHashActionCost_eq_if]
      by_cases hdirect : Direct.IsDirectHashQuery input
      · have hpositive := hpos.resolve_left (not_not.mpr hdirect)
        refine ⟨by simp only [if_pos hdirect]; omega, ?_⟩
        simpa only [Budget, if_pos hdirect] using hnext result.1
      · simpa only [Budget, if_neg hdirect, Nat.sub_zero] using
          And.intro (Nat.zero_le remaining) (hnext result.1))
    (by
      intro spent input state firstState history hstates hprefix hacct
      apply relTriple_post_mono
        (relTriple_sourceExact_firstLane_action spent left right hrel hleftSupport hrightSupport
          input state firstState history hstates hprefix)
      intro leftResult firstResult hresult
      rcases hresult with hgood | hhit
      · exact Or.inl ⟨hgood.1, hgood.2.1, hgood.2.2.1, by rw [hgood.2.2.2, hacct]⟩
      · exact Or.inr hhit)
    D hitLimit
    (by
      intro forgery spent remaining state firstState history _hremaining hstates hcount _hacct htotal
      simp only [simulateQ_pure, WriterT.run_pure']
      apply relTriple_pure_pure
      simpa using Or.inl (b := FirstLaneOracleSimulation.CombinedHit right.1.2
        (FirstLaneOracleSimulation.enforceHazardTrace hitLimit history))
        (And.intro (Eq.refl forgery)
          (And.intro hstates (hcount.trans (show spent ≤ D by omega)))))
    0 D (adversary.main left.publicKey) sourceInitial firstLaneInitial hD [] hinitial
    (by simp [FirstLaneOracleSimulation.hazardCount]) (by rfl) (by omega) hlimit
  simpa only [simulateQ_pure, WriterT.run_pure', Prod.mk.eta, bind_pure,
    List.nil_append] using hcoupling

end XmssSecurity.TargetSum.CappedChain
