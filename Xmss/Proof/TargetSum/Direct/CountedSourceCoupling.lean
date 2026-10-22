import Xmss.Proof.TargetSum.Direct.CountedSourceBudget
import Xmss.Proof.Generic.CappedExactFirstLaneBound
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability
/-! Lift the existing first-lane coupling to the counted source. Its postcondition
retains the actual supported continuation budget, including the random signer cost. -/

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.CappedExecution

open Seeded FirstLaneOracleSimulation

theorem phaseCountsImpl_direct_eq
    (signing : SignRequest → OracleComp OracleWorld (Option Generic.Signature))
    (input : (OracleWorld + SigningSpec).Domain) (state : PhaseCounts)
    (result : (OracleWorld + SigningSpec).Range input × PhaseCounts)
    (hresult : result ∈ support ((phaseCountsImpl signing input).run state)) :
    result.2.direct = state.direct + CappedExecution.directHashActionCost input := by
  cases input with
  | inl input =>
      simp only [phaseCountsImpl, StateT.run, support_map] at hresult
      obtain ⟨sample, _, rfl⟩ := hresult
      cases input <;> rfl
  | inr request =>
      simp only [phaseCountsImpl, StateT.run, support_map] at hresult
      obtain ⟨sample, _, rfl⟩ := hresult
      rfl

theorem countedSourceImpl_direct_eq (secretKey : Generic.SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CountedSourceState)
    (result : (OracleWorld + SigningSpec).Range input × CountedSourceState)
    (hresult : result ∈ support ((countedSourceImpl secretKey input).run state)) :
    result.2.counts.direct = state.counts.direct + CappedExecution.directHashActionCost input := by
  apply phaseCountsImpl_direct_eq _ input state.counts (result.1, result.2.counts)
  change (result.1, result.2.counts) ∈ support
    ((referencePhaseCountsImpl secretKey input).run state.counts)
  rw [← countedSourceImpl_counts_projection secretKey input state, support_map]
  exact ⟨result, hresult, rfl⟩

theorem relTriple_countedSource_source_action
    (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CountedSourceState) :
    RelTriple ((countedSourceImpl secretKey input).run state)
      ((CappedExecution.cappedBothTracedMappedAdversaryImpl publicKey secretKey input).run state.toSource)
      (fun counted source =>
        (counted.1, counted.2.toSource) = source ∧
        counted ∈ support ((countedSourceImpl secretKey input).run state)) := by
  classical
  letI : DecidableEq ((OracleWorld + SigningSpec).Range input × CappedExecution.SourceExactTracedState) :=
    Classical.decEq _
  have hmap : evalDist (Prod.map id CountedSourceState.toSource <$>
      (countedSourceImpl secretKey input).run state) = evalDist
        (id <$> (CappedExecution.cappedBothTracedMappedAdversaryImpl publicKey secretKey input).run
          state.toSource) := by
    rw [id_map, countedSourceImpl_source_projection]
  apply relTriple_post_mono
    (relTriple_of_evalDist_map_eq_with_support_general _ _
      (Prod.map id CountedSourceState.toSource) id hmap)
  intro counted source hresult
  exact ⟨hresult.1, hresult.2.1⟩

theorem relTriple_countedSource_firstLane_action {α : Type}
    (left : CappedExecution.ProgrammedGlobalChainKeygenView)
    (right : CappedExecution.ProgrammedGlobalChainKeygenView × (CappedExecution.GlobalChainValueIndex → Digest))
    (hrel : CappedExecution.ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleftSupport : left ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (limit : Nat) (leftState : CountedSourceState) (rightState : CappedExecution.GlobalDirectTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hstate : CappedExecution.SourceFirstLaneExactGoodStateRelation left right leftState.toSource rightState trace)
    (hcount : FirstLaneOracleSimulation.hazardCount trace ≤ leftState.counts.direct)
    (hbudget : CountedSourceBudget (Keygen.materializePrecomputation left.cache left.secretKey)
      limit (liftM ((OracleWorld + SigningSpec).query input) >>= next) leftState) :
    RelTriple
      ((countedSourceImpl (Keygen.materializePrecomputation left.cache left.secretKey) input).run
        leftState)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2)
        ((CappedExecution.globalFirstLaneExactTracedMappedAdversaryImpl right.1 input).run rightState)).run)
      (fun leftResult rightResult =>
        leftResult.2.charge ≤ limit ∧
        CountedSourceBudget (Keygen.materializePrecomputation left.cache left.secretKey)
          limit (next leftResult.1) leftResult.2 ∧
        FirstLaneOracleSimulation.hazardCount (trace ++ rightResult.2) ≤ leftResult.2.counts.direct ∧
        ((leftResult.1 = rightResult.1.1 ∧
          CappedExecution.SourceFirstLaneExactGoodStateRelation left right leftResult.2.toSource
            rightResult.1.2 (trace ++ rightResult.2)) ∨
          FirstLaneOracleSimulation.CombinedHit right.2 (trace ++ rightResult.2))) := by
  have hlift := relTriple_countedSource_source_action left.publicKey
    (Keygen.materializePrecomputation left.cache left.secretKey) input leftState
  have hstep := CappedExecution.relTriple_sourceExact_firstLane_action leftState.counts.direct left right hrel
    hleftSupport hrightSupport input leftState.toSource rightState trace hstate hcount
  apply relTriple_post_mono (relTriple_trans_exists hlift hstep)
  intro leftResult rightResult hresult
  obtain ⟨source, ⟨hprojection, hleft⟩, hstep⟩ := hresult
  subst source
  have hnext := hbudget.query_step leftResult hleft
  have hdirect := countedSourceImpl_direct_eq _ input leftState leftResult hleft
  refine ⟨hnext.1, hnext.2, ?_⟩
  rcases hstep with hgood | hhit
  · exact ⟨hdirect ▸ hgood.2.2.1, Or.inl ⟨hgood.1, hgood.2.1⟩⟩
  · exact ⟨hdirect ▸ hhit.2, Or.inr hhit.1⟩

/-- info: 'Xmss.TargetSum.CappedExecution.relTriple_countedSource_firstLane_action' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relTriple_countedSource_firstLane_action

end Xmss.TargetSum.CappedExecution
