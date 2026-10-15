import XmssSecurity.Proof.Direct.CountedSourceCoupling

/-! Couple an entire adversary prefix using the supported source budget. The good
branch retains the actual direct count instead of replacing it by the maximum budget. -/

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.CappedChain

open Seeded FirstLaneOracleSimulation

theorem relTriple_countedSource_firstLane_prefix {α : Type}
    (limit hitLimit : Nat) (hlimit : limit ≤ hitLimit)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView × (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hbudget : CountedSourceBudget (Concrete.materializePrecomputation left.cache left.secretKey)
      limit computation (CountedSourceState.initial left.cache)) :
    RelTriple
      ((simulateQ (countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey))
        computation).run (CountedSourceState.initial left.cache))
      ((simulateQ (eagerTraceImpl right.1.2)
        ((simulateQ (globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2)
          computation).run
            (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState right.1.1)))).run)
      (fun leftResult rightResult =>
        leftResult.2.charge ≤ limit ∧
        ((leftResult.1 = rightResult.1.1 ∧
          SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2.toSource
            rightResult.1.2 rightResult.2 ∧
          hazardCount rightResult.2 ≤ leftResult.2.counts.direct) ∨
          CombinedHit right.1.2 (enforceHazardTrace hitLimit rightResult.2))) := by
  let secretKey := Concrete.materializePrecomputation left.cache left.secretKey
  let sourceInitial := CountedSourceState.initial left.cache
  let firstLaneInitial := GlobalHighDirectTracedState.initial
    (globalFilteredCausalKeygenState right.1.1)
  let stateRel := fun (source : CountedSourceState) (target : GlobalHighDirectTracedState)
      (trace : ActionTrace GlobalChainValueIndex) =>
    SourceFirstLaneExactGoodStateRelation left right.1 source.toSource target trace ∧
      hazardCount trace ≤ source.counts.direct
  let Budget := fun (rest : OracleComp (OracleWorld + SigningSpec) α) (fuel : Nat)
      (state : CountedSourceState) =>
    CountedSourceBudget secretKey limit rest state ∧ state.counts.direct + fuel = limit
  have hinitial : stateRel sourceInitial firstLaneInitial [] := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simpa [sourceInitial, firstLaneInitial, CountedSourceState.initial,
        CountedSourceState.toSource, globalStateOfFirstLane, sourceExactSigningProjection,
        ActionTrace.chainActions] using
        globalSigningMonitoredTracedStateRelation_initial left right hrel hleftSupport hrightSupport
    · simp [sourceInitial, CountedSourceState.initial, CountedSourceState.toSource,
        ActionTrace.encodingActions]
    · simp [firstLaneInitial, CappedEncodingMonitor.validObservedSignLeafIndices,
        ActionTrace.encodingActions, CappedEncodingMonitor.validActions,
        EncodingMonitor.observedSignLeafIndices]
    · simp [hazardCount]
  have hcoupling := relTriple_simulateQ_bind_bounded_firstLane right.1.2
    (countedSourceImpl secretKey)
    (globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2)
    (fun value state => pure (value, state))
    (fun value state => pure (value, state))
    directHashActionCost stateRel (fun state spent => state.counts.direct = spent) Budget
    (by
      intro input next fuel state result hrest hresult
      obtain ⟨hrest, hfuel⟩ := hrest
      have hnext := hrest.query_step result hresult
      have hdirect := countedSourceImpl_direct_eq secretKey input state result hresult
      have hcharged : result.2.counts.direct ≤ limit :=
        (Nat.le_add_right _ _).trans hnext.1
      have hcost : directHashActionCost input ≤ fuel := by omega
      exact ⟨hcost, hnext.2, by omega⟩)
    (by
      intro spent input state firstState history hstates hprefix hacct
      have hlift := relTriple_countedSource_source_action left.publicKey secretKey input state
      have hstep := relTriple_sourceExact_firstLane_action spent left right hrel
        hleftSupport hrightSupport input state.toSource firstState history hstates.1 hprefix
      apply relTriple_post_mono (relTriple_trans_exists hlift hstep)
      intro leftResult rightResult hresult
      obtain ⟨source, ⟨hprojection, hleft⟩, hstep⟩ := hresult
      subst source
      have hdirect := countedSourceImpl_direct_eq secretKey input state leftResult hleft
      rcases hstep with hgood | hhit
      · refine Or.inl ⟨hgood.1, ⟨hgood.2.1, ?_⟩, hgood.2.2.1, ?_⟩
        · rw [hdirect, hacct]
          exact hgood.2.2.1
        · rw [hdirect, hacct]
      · exact Or.inr hhit)
    limit hitLimit
    (by
      intro value spent fuel state firstState history _hremaining hstates hcount _hacct htotal
      simp only [simulateQ_pure, WriterT.run_pure']
      apply relTriple_pure_pure
      simpa using Or.inl
        (b := CombinedHit right.1.2 (enforceHazardTrace hitLimit history))
        (And.intro (Eq.refl value)
          (And.intro hstates (hcount.trans (show spent ≤ limit by omega)))))
    0 limit computation sourceInitial firstLaneInitial
    ⟨hbudget, by simp [sourceInitial, CountedSourceState.initial]⟩ [] hinitial
    (by simp [hazardCount]) rfl (by omega) hlimit
  simp only [Prod.mk.eta, bind_pure, List.nil_append]
    at hcoupling
  apply relTriple_post_mono (relTriple_with_support hcoupling)
  intro leftResult rightResult hresult
  refine ⟨hbudget leftResult hresult.2.1, ?_⟩
  rcases hresult.1 with hgood | hhit
  · exact Or.inl ⟨hgood.1, hgood.2.1⟩
  · exact Or.inr hhit

/-- info: 'XmssSecurity.CappedChain.relTriple_countedSource_firstLane_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relTriple_countedSource_firstLane_prefix

end XmssSecurity.CappedChain
