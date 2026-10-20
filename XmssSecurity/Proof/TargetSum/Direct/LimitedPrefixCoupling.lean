import XmssSecurity.Proof.TargetSum.Direct.FirstLaneBudgetEnforcement
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The limited public experiment agrees with the source until a collision has been
recorded. Later aborts retain that collision, so no equality of post-collision costs is
needed to transfer the source winning event. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.CappedChain

open Seeded FirstLaneOracleSimulation

def LimitedFirstLaneOutcomeRelation {α : Type}
    (left : CappedChain.ProgrammedGlobalChainKeygenView)
    (right : CappedChain.ProgrammedGlobalChainKeygenView × (CappedChain.GlobalChainValueIndex → Digest))
    (history : FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex) (source : α × CountedSourceState)
    (target : (Option (α × CappedChain.GlobalDirectTracedState) × EncodingBudgetCounters) ×
      FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex) : Prop :=
  (∃ state, target.1.1 = some (source.1, state) ∧
    CappedChain.SourceFirstLaneExactGoodStateRelation left right source.2.toSource state (history ++ target.2) ∧
    target.1.2 = firstLaneCounters right.1.secretKey.parameter state (history ++ target.2) ∧
    FirstLaneOracleSimulation.hazardCount (history ++ target.2) ≤ source.2.counts.direct) ∨
  FirstLaneOracleSimulation.CombinedHit right.2 (history ++ target.2)

theorem relTriple_firstLaneHit_append {α β : Type}
    (table : CappedChain.GlobalChainValueIndex → Digest) (history fragment : FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hhit : FirstLaneOracleSimulation.CombinedHit table (history ++ fragment)) (left : ProbComp α)
    (right : ProbComp (β × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)) :
    RelTriple left (Prod.map id (fun suffix => fragment ++ suffix) <$> right)
      (fun _ result => FirstLaneOracleSimulation.CombinedHit table (history ++ result.2)) := by
  have hmapped : RelTriple (id <$> left)
      (Prod.map id (fun suffix => fragment ++ suffix) <$> right)
      (fun _ result => FirstLaneOracleSimulation.CombinedHit table (history ++ result.2)) := by
    apply relTriple_map
    apply relTriple_post_mono (relTriple_prod (fun _ _ => True.intro) (fun _ _ => True.intro))
    intro _ result _
    simpa [Prod.map, List.append_assoc] using FirstLaneOracleSimulation.CombinedHit.append_of_prefix table
      (history ++ fragment) result.2 hhit
  simpa only [id_map] using hmapped

theorem relTriple_countedSource_limitedPrefix_of_related {α : Type}
    (left : CappedChain.ProgrammedGlobalChainKeygenView)
    (right : CappedChain.ProgrammedGlobalChainKeygenView × (CappedChain.GlobalChainValueIndex → Digest))
    (hrel : CappedChain.ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleftSupport : left ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (limit : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftState : CountedSourceState) (rightState : CappedChain.GlobalDirectTracedState)
    (history : FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hstate : CappedChain.SourceFirstLaneExactGoodStateRelation left right leftState.toSource rightState history)
    (hcacheCount : cachedEncodingInputCount rightState.causalState.cache right.1.secretKey.parameter =
      (history.encodingActions.length : ℝ≥0∞))
    (hencoding : CountedSourceEncodingBudget left.secretKey.parameter leftState)
    (hcount : FirstLaneOracleSimulation.hazardCount history ≤ leftState.counts.direct)
    (hsourceTrace : leftState.counts.direct = leftState.attackerTrace.hashInputs.length)
    (hbudget : CountedSourceBudget (Concrete.materializePrecomputation left.cache left.secretKey)
      limit computation leftState) :
    RelTriple
      ((simulateQ (countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey))
        computation).run leftState)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2)
        (limitedFirstLanePrefix limit right.1 computation rightState
          (firstLaneCounters right.1.secretKey.parameter rightState history))).run)
      (LimitedFirstLaneOutcomeRelation left right history) := by
  induction computation using OracleComp.inductionOn generalizing leftState rightState history with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, limitedFirstLanePrefix_pure, WriterT.run_pure]
      apply relTriple_pure_pure
      apply Or.inl
      exact ⟨rightState, rfl, by simpa using hstate, by simp, by simpa using hcount⟩
  | query_bind input next ih =>
      rw [Direct.run_simulateQ_query_bind, limitedFirstLanePrefix_query_bind, simulateQ_bind,
        WriterT.run_bind', limitedFirstLaneAction_eq_of_related left right hrel hleftSupport
          hrightSupport input next limit leftState rightState history hstate hcacheCount hencoding
            hcount hsourceTrace hbudget, bind_map_left]
      change RelTriple
        ((countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey) input).run leftState >>=
          fun head => (simulateQ (countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey))
            (next head.1)).run head.2)
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2)
          ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl right.1 input).run rightState)).run >>=
          fun head => Prod.map id (fun tail => head.2 ++ tail) <$>
            (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2)
              (limitedFirstLanePrefix limit right.1 (next head.1.1) head.1.2
                (firstLaneCounters right.1.secretKey.parameter head.1.2 (history ++ head.2)))).run)
        (LimitedFirstLaneOutcomeRelation left right history)
      apply relTriple_bind (relTriple_with_support (relTriple_countedSource_firstLane_action left right
        hrel hleftSupport hrightSupport input next limit leftState rightState history hstate hcount hbudget))
      intro headLeft headRight hhead
      obtain ⟨⟨_hcharge, hnextBudget, hnextCount, hnext⟩, hleft, hright⟩ := hhead
      rcases hnext with ⟨hvalue, hnextState⟩ | hhit
      · have hnextCache := globalFirstLaneExactTraced_query_encodingCountGrowth right.2 right.1
          input rightState headRight hright
        change cachedEncodingInputCount headRight.1.2.causalState.cache right.1.secretKey.parameter = _
          at hnextCache
        rw [hcacheCount] at hnextCache
        have hnextCache' : cachedEncodingInputCount headRight.1.2.causalState.cache right.1.secretKey.parameter =
            ((history ++ headRight.2).encodingActions.length : ℝ≥0∞) := by
          simpa only [FirstLaneOracleSimulation.ActionTrace.encodingActions_append, List.length_append, Nat.cast_add] using hnextCache
        have hnextEncoding := countedSourceImpl_encodingBudget
          (Concrete.materializePrecomputation left.cache left.secretKey) input leftState
          (by rw [Concrete.materializePrecomputation_parameter]; exact hencoding) headLeft hleft
        rw [Concrete.materializePrecomputation_parameter] at hnextEncoding
        have hnextTrace : headLeft.2.counts.direct = headLeft.2.attackerTrace.hashInputs.length := by
          rw [countedSourceImpl_direct_eq _ input leftState headLeft hleft,
            countedSourceImpl_hashInputs_update _ input leftState headLeft hleft, hsourceTrace]
        rw [hvalue] at hnextBudget
        have hrec := ih headRight.1.1 headLeft.2 headRight.1.2 (history ++ headRight.2) hnextState
          hnextCache' hnextEncoding hnextCount hnextTrace hnextBudget
        have hmapped : RelTriple
            (id <$> ((simulateQ (countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey))
              (next headRight.1.1)).run headLeft.2))
            (Prod.map id (fun tail => headRight.2 ++ tail) <$>
              (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2)
                (limitedFirstLanePrefix limit right.1 (next headRight.1.1) headRight.1.2
                  (firstLaneCounters right.1.secretKey.parameter headRight.1.2 (history ++ headRight.2)))).run)
            (LimitedFirstLaneOutcomeRelation left right history) := by
          apply relTriple_map
          apply relTriple_post_mono hrec
          intro source target hresult
          simpa only [LimitedFirstLaneOutcomeRelation, Prod.map, id_eq, List.append_assoc] using hresult
        rw [hvalue]
        simpa only [id_map] using hmapped
      · apply relTriple_post_mono (relTriple_firstLaneHit_append right.2 history headRight.2 hhit
          ((simulateQ (countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey))
            (next headLeft.1)).run headLeft.2)
          ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2)
            (limitedFirstLanePrefix limit right.1 (next headRight.1.1) headRight.1.2
              (firstLaneCounters right.1.secretKey.parameter headRight.1.2 (history ++ headRight.2)))).run))
        intro _ _ hhit
        exact Or.inr hhit

theorem relTriple_countedSource_limitedPrefix {α : Type}
    (left : CappedChain.ProgrammedGlobalChainKeygenView)
    (right : CappedChain.ProgrammedGlobalChainKeygenView × (CappedChain.GlobalChainValueIndex → Digest))
    (hrel : CappedChain.ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleftSupport : left ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (limit : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hbudget : CountedSourceBudget (Concrete.materializePrecomputation left.cache left.secretKey)
      limit computation (CountedSourceState.initial left.cache)) :
    RelTriple
      ((simulateQ (countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey))
        computation).run (CountedSourceState.initial left.cache))
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2)
        (limitedFirstLanePrefix limit right.1 computation
          (CappedChain.GlobalDirectTracedState.initial (CappedChain.globalFilteredCausalKeygenState right.1)) ⟨0, 0, 0⟩)).run)
      (fun source target => source.2.charge ≤ limit ∧ target.1.2.charge ≤ limit ∧
        target.1.2.samples = target.2.encodingActions.length ∧
        FirstLaneOracleSimulation.hazardCount target.2 ≤ target.1.2.direct ∧
        LimitedFirstLaneOutcomeRelation left right [] source target) := by
  let sourceInitial := CountedSourceState.initial left.cache
  let targetInitial := CappedChain.GlobalDirectTracedState.initial (CappedChain.globalFilteredCausalKeygenState right.1)
  have hstate : CappedChain.SourceFirstLaneExactGoodStateRelation left right sourceInitial.toSource targetInitial [] := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [sourceInitial, targetInitial, CountedSourceState.initial,
        CountedSourceState.toSource, CappedChain.globalStateOfFirstLane, CappedChain.sourceExactSigningProjection,
        FirstLaneOracleSimulation.ActionTrace.chainActions] using
        CappedChain.globalSigningMonitoredTracedStateRelation_initial left right hrel hleftSupport hrightSupport
    · simp [sourceInitial, CountedSourceState.initial, CountedSourceState.toSource,
        FirstLaneOracleSimulation.ActionTrace.encodingActions]
    · simp [targetInitial, CappedEncodingMonitor.validObservedSignLeafIndices,
        FirstLaneOracleSimulation.ActionTrace.encodingActions, CappedEncodingMonitor.validActions, EncodingMonitor.observedSignLeafIndices]
  have hcacheCount : cachedEncodingInputCount targetInitial.causalState.cache right.1.secretKey.parameter = 0 := by
    exact globalFilteredCausalKeygenState_encodingCount_zero right.1 hrightSupport
  have hencoding : CountedSourceEncodingBudget left.secretKey.parameter sourceInitial := by
    change cachedEncodingInputCount left.cache left.secretKey.parameter ≤ _
    rw [cachedEncodingInputCount_eq_zero_of_no_encodingInputs left.cache left.secretKey.parameter
      (Concrete.keygen_cache_none_encodingInput left.keyResult
        (CappedChain.trajectoryProgrammedGlobalChainKeygen_support_keyResult left hleftSupport))]
    exact zero_le
  have hcoupling := relTriple_countedSource_limitedPrefix_of_related left right hrel hleftSupport hrightSupport
    limit computation sourceInitial targetInitial [] hstate
    (by simpa [FirstLaneOracleSimulation.ActionTrace.encodingActions] using hcacheCount) hencoding
    (by simp [FirstLaneOracleSimulation.hazardCount]) rfl hbudget
  change RelTriple _ ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2)
    (limitedFirstLanePrefix limit right.1 computation targetInitial ⟨0, 0, 0⟩)).run) _ at hcoupling
  apply relTriple_post_mono (relTriple_with_support hcoupling)
  intro source target hresult
  have hlimited := limitedFirstLanePrefix_trace_budget right.2 limit right.1 computation
    targetInitial ⟨0, 0, 0⟩ (by simp [EncodingBudgetCounters.charge]) target hresult.2.2
  have hcount := limitedFirstLanePrefix_trace_direct right.2 limit right.1 computation
    targetInitial ⟨0, 0, 0⟩ target hresult.2.2
  exact ⟨hbudget source hresult.2.1, hlimited.1, by simpa using hlimited.2,
    by simpa using hcount, hresult.1⟩

/-- info: 'XmssSecurity.TargetSum.CappedChain.relTriple_countedSource_limitedPrefix_of_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relTriple_countedSource_limitedPrefix_of_related

/-- info: 'XmssSecurity.TargetSum.CappedChain.relTriple_countedSource_limitedPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relTriple_countedSource_limitedPrefix

end XmssSecurity.TargetSum.CappedChain
